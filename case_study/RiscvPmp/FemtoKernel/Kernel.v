(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel, Dominique Devriese, Sander Huyghebaert  *)
(* All rights reserved.                                                       *)
(*                                                                            *)
(* Redistribution and use in source and binary forms, with or without         *)
(* modification, are permitted provided that the following conditions are     *)
(* met:                                                                       *)
(*                                                                            *)
(* 1. Redistributions of source code must retain the above copyright notice,  *)
(*    this list of conditions and the following disclaimer.                   *)
(*                                                                            *)
(* 2. Redistributions in binary form must reproduce the above copyright       *)
(*    notice, this list of conditions and the following disclaimer in the     *)
(*    documentation and/or other materials provided with the distribution.    *)
(*                                                                            *)
(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS        *)
(* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED  *)
(* TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR *)
(* PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR          *)
(* CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,      *)
(* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,        *)
(* PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR         *)
(* PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF     *)
(* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING       *)
(* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS         *)
(* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.               *)
(******************************************************************************)

From Stdlib Require Import
     ZArith.ZArith
     Lists.List
     Strings.String.
From Katamaran Require Import
     Base
     Bitvector
     Notations
     RiscvPmp.BlockVer.Spec
     RiscvPmp.Machine
     RiscvPmp.PmpCheck
     RiscvPmp.Sig.
From Stdlib Require Import ssreflect.
From stdpp Require Import base list.

Import RiscvPmpProgram.

Set Implicit Arguments.
Import ctx.notations.
Import env.notations.
Import ListNotations.
Open Scope ctx_scope.

Import Assembly.

Section FemtoKernel.
  Import bv.notations.
  Import ListNotations.
  Import TermNotations.

  Open Scope hex_Z_scope.


  (* FIXED ADDRESSES *)
  (* The first address that is no longer used by the adversary, and hence the address at which the PMP entries should stop granting permission. Note that this address is currently also the first MMIO address. *)
  Definition adv_addr_end : N := maxAddr. (* Change once adversary gets access to MMIO*)
  (* Address where we will write in MMIO memory, and proof that our writes will indeed be within the MMIO region*)
  Definition mmio_write_addr : N := mmioStartAddr.
  Lemma write_word_is_MMIO: withinMMIO (bv.of_N mmio_write_addr) bytes_per_word.
  Proof. apply bounds_withinMMIO; now compute. Qed.

  (* We choose a start addr from which adversary (U-mode) is allowed to
     requests writes to MMIO. Currently we only reserve the first word of
     MMIO addresses as exclusive to M-mode. *)
  Definition mmio_write_adv : N := mmioStartAddr + (N.of_nat bytes_per_word).

  Lemma write_word_adv_is_MMIO :
      withinMMIO (bv.of_N mmio_write_adv) bytes_per_word.
  Proof. apply bounds_withinMMIO; now compute. Qed.

  (* Aliases for registers *)
  Definition zero : RegIdx := [bv 0].
  Definition ra : RegIdx := [bv 1].
  Definition t0 : RegIdx := [bv 5].
  Definition mmio_write_arg_reg : RegIdx := [bv 10]. (* x10 = a0 *)
  Definition mmio_write_val_reg : RegIdx := [bv 11]. (* x11 = a1 *)
  (* The system call number (passed in mmio_write_arg_reg, i.e. a0) with which
     U-mode asks the trap handler to power off the machine. The handler
     interprets a0 as follows:
     - mmio_write_adv: the public MMIO write, which also logs the secret
       (dispatch, not_zero and is_zero blocks);
     - shutdown_code: power off the machine (shutdown_check and shutdown blocks);
     - any other value: the secret write (secret_write block).
     The value 1 is arbitrary, but it must differ from mmio_write_adv (which
     is checked first) and fit in the 12-bit immediate of an ADDI. We avoid 0,
     as that is the value of a0 when U-mode does not set an argument. *)
  Definition shutdown_code : N := 1.

  Definition pure_privilege_to_bits {n} : Privilege -> bv n :=
    fun p => match p with | Machine => bv.of_N 3 | Supervisor => bv.one | User => bv.zero end.

  Definition pure_pmpAddrMatchType_to_bits : PmpAddrMatchType -> bv 4 :=
    fun mt => match mt with
              | OFF => bv.zero
              | TOR => bv.one
              end.

  Definition pure_pmpcfg_ent_to_bits : Pmpcfg_ent -> Val (ty.bvec byte) :=
    fun ent =>
      match ent with
      | MkPmpcfg_ent L A X W R =>
          let l : bv 1 := bv.of_bool L in
          let a : bv 4 := pure_pmpAddrMatchType_to_bits A in
          let x : bv 1 := bv.of_bool X in
          let w : bv 1 := bv.of_bool W in
          let r : bv 1 := bv.of_bool R in
          bv.app r (bv.app w (bv.app x (bv.app a l)))
      end%Z.

  (* Definitions for configuration bits of PMP entries *)
  Definition femto_pmpcfg_ent0 : Pmpcfg_ent := MkPmpcfg_ent false OFF false false false.
  Definition femto_pmpcfg_ent0_bits : Val (ty.bvec byte) := pure_pmpcfg_ent_to_bits femto_pmpcfg_ent0.
  Definition femto_pmpcfg_ent1 : Pmpcfg_ent := MkPmpcfg_ent false TOR true true true.
  Definition femto_pmpcfg_ent1_bits : Val (ty.bvec byte) := pure_pmpcfg_ent_to_bits femto_pmpcfg_ent1.
  Definition femto_pmp0cfg_bits : Val (ty.bvec 32) := bv.zext (bv.app femto_pmpcfg_ent0_bits femto_pmpcfg_ent1_bits).

  (* Because of sign extension in the 12-bit immediate of ADDI/SW/LW, one cannot just take subranges to split immediates. Rather, the following function is used: *)
  (* See e.g.: https://stackoverflow.com/questions/50742420/risc-v-build-32-bit-constants-with-lui-and-addi *)
  Definition imm_split_bv (imm : bv 32) : (bv 12 * bv 20) :=
    let (lo , hi) := bv.appView 12 _ imm in
      if bv.eqb hi (bv.ones 20) then (lo , hi) (* Small negative numbers *)
      else if (bv.msb lo) (* Avoid incorrect sign-extension *)
           then (bv.of_Z (bv.unsigned lo - 4096), (hi + bv.one)%bv)
           else (lo , hi).

  (* TODO: prove this spec for `imm_split_bv`*)
  (* Lemma imm_split_bv_spec lo hi imm : *)
  (*    (lo , hi) = imm_split_bv imm -> imm = bv.add (bv.shiftl (bv.zext hi) (@bv.of_N 12 12)) (bv.sext lo). *)

  Definition femto_pmp0cfg_bits_1 : Val (ty.bvec 12) := fst (imm_split_bv femto_pmp0cfg_bits).
  Definition femto_pmp0cfg_bits_2 : Val (ty.bvec 20) := snd (imm_split_bv femto_pmp0cfg_bits).

  (* ASTs with a very limited form of labels, that allow us to refer to the address of the current instruction *)
  (* TODO: have the symbolic executor work with these types of instructions directly? *)
  Inductive ASM :=
    | Instr (a: AnnotInstr)
    | RelInstr (f : N -> AnnotInstr).
  Local Coercion AST_AnnotAST (a : AST) := AnnotAST (a).
  Local Coercion AnnotAST_ASM (a : AnnotInstr) := Instr (a).
  Local Notation "'Λ' x , a" := (RelInstr (fun x => a))
    (at level 200) : list_scope.
  Local Arguments List.cons {_} & _ _. (* Allow projecting individual ASM into AST  - TODO: wrap `cons` in another definition so this bidirectionality does not interfere with lists *)

  (* The following definitions are required for layouting in memory, because otherwise we will count other things than instructions as taking up space *)
  Definition ASM_extract_AST (a : ASM) :=
    extract_AST
    (match a with
    | Instr a => a
    | RelInstr f => f 0%N end).
  Definition filter_ASM_AST (l : list ASM) := base.omap ASM_extract_AST l.

  (* Address resolution *)
  Fixpoint resolve_ASM (la : list ASM) (cur_off : N) : list AnnotInstr :=
    match la with
    | nil => nil
    | cons hd tl =>
        let hd' := (match hd with
        | Instr a => a
        | RelInstr f => f cur_off end) in
        let new_off : N :=
          (* Only instructions should increase the current offset, whereas lemma and debug calls will be filtered out in the end! *)
          (match extract_AST hd' with
          | Some _ => (cur_off + N.of_nat xlenbytes)%N
          | _ => cur_off
          end) in
            cons hd' (resolve_ASM tl new_off)
     end.

  (* Init code is the same in both versions of the femtokernel, since MMIO memory is placed after the adversary code, hence not affecting initialization *)
  Example femtokernel_init_asm (handler_start : N) (adv_start : N): list ASM :=
    [
      UTYPE bv.zero ra RISCV_AUIPC
    ; Λ x, ITYPE (bv.of_N (adv_start - (x - 4))) ra ra RISCV_ADDI
    ; CSR MPMPADDR0 ra zero false CSRRW
    ; ITYPE (bv.of_N adv_addr_end) zero ra RISCV_ADDI
    ; CSR MPMPADDR1 ra zero false CSRRW
    ; UTYPE femto_pmp0cfg_bits_2 ra RISCV_LUI
    ; ITYPE femto_pmp0cfg_bits_1 ra ra RISCV_ADDI
    ; CSR MPMP0CFG ra zero false CSRRW
    ; UTYPE bv.zero ra RISCV_AUIPC
    ; Λ x, ITYPE (bv.of_N (handler_start - (x - 4))) ra ra RISCV_ADDI
    ; CSR MTvec ra zero false CSRRW
    ; ITYPE (bv.of_N (adv_start - handler_start)) ra ra RISCV_ADDI
    ; CSR MEpc ra zero false CSRRW
    ; ITYPE [bv 0x80] zero ra RISCV_ADDI
    ; CSR MStatus ra zero false CSRRW
    ; MRET
    ].

  Example femtokernel_init' (init_start : N) (handler_start : N) (adv_start : N) : list AnnotInstr :=
    resolve_ASM (femtokernel_init_asm handler_start adv_start) init_start.

  Example femtokernel_handler_asm : list ASM :=
    [
      ITYPE (bv.of_N 42) zero t0 RISCV_ADDI
    ; AnnotLemmaInvocation (close_mmio_write (bv.of_N mmio_write_addr) WORD) [nenv exp_val ty_xlenbits bv.zero;  exp_val ty_regno t0]%nenv (* TODO: notation to avoid lemma call copying LOAD instruction/internalize immediate as well?*)
    ; STORE (bv.of_N mmio_write_addr) t0 zero WORD (* works because mmio_write_addr fits into 12 bits. *)
    ; MRET
    ].
  Example femtokernel_handler' (handler_start : N) : list AnnotInstr :=
    resolve_ASM (femtokernel_handler_asm) handler_start.

  (* The trap handler is invoked for writes to MMIO. Only M-mode can access
     the MMIO addresses directly, but we provide (the only) a syscall that
     performs writes for U-mode for certain MMIO addresses. This requires
     some extra blocks, one for the entry, in which we check that the address,
     expected as an argument in `mmio_write_arg_reg` register, is one that
     can be written to be U-mode. If so, we perform the write with the value
     from the `mmio_write_val_reg` register. If not, we perform a "secret"
     write to an MMIO address that is only accessible to M-mode.
     Finally, we return control to the invoker of the syscall. *)
  (* Block structure:
     - femtokernel_handler_entry_asm
       -> Jumps to femtokernel_handler_shutdown_check_asm
       -> OR falls through to femtokernel_handler_dispatch_asm
     - femtokernel_handler_dispatch_asm
       -> Jumps to femtokernel_handler_is_zero_asm if the secret is zero
       -> OR falls through to femtokernel_handler_not_zero_asm
     - femtokernel_handler_not_zero_asm
       -> ALWAYS jumps to femtokernel_handler_exit_asm
     - femtokernel_handler_is_zero_asm
       -> ALWAYS jumps to femtokernel_handler_exit_asm
     - femtokernel_handler_shutdown_check_asm
       -> Jumps to femtokernel_handler_secret_write_asm
       -> OR falls through to femtokernel_handler_shutdown_asm
     - femtokernel_handler_shutdown_asm
       -> Powers off the machine. End of execution.
     - femtokernel_handler_secret_write_asm
       -> ALWAYS falls through to femtokernel_exit_asm
     - femtokernel_handler_exit_asm
       -> Jumps back to U-mode (MRET). End of handler code. *)
  Example femtokernel_handler_entry_asm (handler_skip_size : N) : list AnnotInstr :=
    [ ADDI t0 zero (bv.of_N mmio_write_adv)
    ; BNE mmio_write_arg_reg t0 (bv.of_N (handler_skip_size + N.of_nat bytes_per_instr)) (* If the requested write argument is not one the trap invoker can write to, we need to jump over (hence the + bytes_per_instr) the dispatch, not_zero and is_zero blocks. *)
    ].

  (* Perform the requested MMIO write on behalf of U-mode (the public
     acknowledgement, writing 42 to the adversary-visible MMIO address), and
     log the secret to the M-mode only MMIO address. The order in which both
     writes happen depends on the secret: if it is zero, the secret is logged
     first (is_zero block), otherwise the acknowledgement happens first (not_zero
     block). Both orders result in the same adversary-observable trace, but
     the two executions differ in their control flow. *)
  Example femtokernel_handler_dispatch_asm' (data_addr not_zero_size : N) : list ASM :=
    [ UTYPE bv.zero ra RISCV_AUIPC
    ; Λ x, LOAD (bv.of_N (data_addr - (x - 4))) ra ra false WORD
    ; BEQ ra zero (bv.of_N (not_zero_size + N.of_nat bytes_per_instr)) (* Jump over the not_zero block if the secret is zero. *)
    ].
  Example femtokernel_handler_dispatch_asm (dispatch_addr data_addr not_zero_size : N) : list AnnotInstr :=
    resolve_ASM (femtokernel_handler_dispatch_asm' data_addr not_zero_size) dispatch_addr.

  (* First performs the public write, then the private write. *)
  Example femtokernel_handler_not_zero_asm' (data_addr exit_addr : N) : list ASM :=
    [ ADDI t0 zero (bv.of_N 42)
    ; AnnotLemmaInvocation (close_mmio_write (bv.of_N mmio_write_adv) WORD) [nenv exp_val ty_xlenbits bv.zero; exp_val ty_regno t0]%nenv
    ; STORE (bv.of_N mmio_write_adv) t0 zero WORD (* works because mmio_write_adv fits into 12 bits. *)
    ; UTYPE bv.zero ra RISCV_AUIPC
    ; Λ x, LOAD (bv.of_N (data_addr - (x - 4))) ra ra false WORD
    ; AnnotLemmaInvocation (close_mmio_write (bv.of_N mmio_write_addr) WORD) [nenv exp_val ty_xlenbits bv.zero; exp_val ty_regno ra]%nenv
    ; STORE (bv.of_N mmio_write_addr) ra zero WORD
    ; ADD ra zero zero (* We need to clear ra, as it contains the secret *)
    ; RISCV_JALR (bv.of_N exit_addr) zero zero (* works because the exit block addr fits into 12 bits *)
    ].
  Example femtokernel_handler_not_zero_asm (not_zero_addr data_addr exit_addr : N) : list AnnotInstr :=
    resolve_ASM (femtokernel_handler_not_zero_asm' data_addr exit_addr) not_zero_addr.

  (* First performs the private write, then the public write. *)
  Example femtokernel_handler_is_zero_asm' (data_addr exit_addr : N) : list ASM :=
    [ UTYPE bv.zero ra RISCV_AUIPC
    ; Λ x, LOAD (bv.of_N (data_addr - (x - 4))) ra ra false WORD
    ; AnnotLemmaInvocation (close_mmio_write (bv.of_N mmio_write_addr) WORD) [nenv exp_val ty_xlenbits bv.zero; exp_val ty_regno ra]%nenv
    ; STORE (bv.of_N mmio_write_addr) ra zero WORD
    ; ADDI t0 zero (bv.of_N 42)
    ; AnnotLemmaInvocation (close_mmio_write (bv.of_N mmio_write_adv) WORD) [nenv exp_val ty_xlenbits bv.zero; exp_val ty_regno t0]%nenv
    ; STORE (bv.of_N mmio_write_adv) t0 zero WORD
    ; ADD ra zero zero (* We need to clear ra, as it contains the secret *)
    ; RISCV_JALR (bv.of_N exit_addr) zero zero
    ].
  Example femtokernel_handler_is_zero_asm (is_zero_addr data_addr exit_addr : N) : list AnnotInstr :=
    resolve_ASM (femtokernel_handler_is_zero_asm' data_addr exit_addr) is_zero_addr.

  (* Checks whether the trap invoker requests to power off the machine, by
     passing shutdown_code as argument. If so, we fall through to the shutdown
     block, otherwise we jump over it to the secret write. In both cases, the
     shutdown address is prepared in t0 (it does not fit in a 12-bit
     immediate, hence the two ADDIs).
     NOTE: preparing t0 here, rather than in the shutdown block itself, is a
     limitation of WP2_loop_semTripleBlock_power_off, which only supports a
     block of a single instruction: the power tokens are handed to the block
     after the power check that precedes its (only) instruction, so they
     are not available for the power checks in between the instructions of
     a longer block. Lifting this would require a variant of that lemma for
     blocks `instrs ++ [instr]`, where only the final instruction uses the
     power tokens. *)
  Example femtokernel_handler_shutdown_check_asm (shutdown_size : N) : list AnnotInstr :=
    [ ADDI t0 zero (bv.of_N 2047)
    ; ADDI t0 t0 (bv.of_N 1021) (* t0 = mmioShutdownAddr *)
    ; ADDI ra zero (bv.of_N shutdown_code)
    ; BNE mmio_write_arg_reg ra (bv.of_N (shutdown_size + N.of_nat bytes_per_instr))
    ].

  (* Powers off the machine, with exit value 0. *)
  Example femtokernel_handler_shutdown_asm : list AnnotInstr :=
    [ AnnotLemmaInvocation (close_mmio_write (bv.of_N 0) WORD) [nenv exp_val ty_xlenbits mmioShutdownAddr; exp_val ty_regno zero]%nenv
    ; STORE (bv.of_N 0) zero t0 WORD
    ].

  (* Performs a "secret" MMIO write. The secret itself is read from the
     `data` address and then written to the MMIO address.
     Block falls through to femtokernel_handler_exit_asm. *)
  Example femtokernel_handler_secret_write_asm' (data_addr : N) : list ASM :=
    [ UTYPE bv.zero ra RISCV_AUIPC
    ; Λ x, LOAD (bv.of_N (data_addr - (x - 4))) ra ra false WORD
    ; AnnotLemmaInvocation (close_mmio_write (bv.of_N mmio_write_addr) WORD) [nenv exp_val ty_xlenbits bv.zero; exp_val ty_regno ra]%nenv
    ; STORE (bv.of_N mmio_write_addr) ra zero WORD (* works because mmio_write_adv fits into 12 bits. *)
    ; ADD ra zero zero (* We need to clear ra, as it contains the secret *)
    ].
  Example femtokernel_handler_secret_write_asm (secret_write_addr data_addr : N) : list AnnotInstr :=
    resolve_ASM (femtokernel_handler_secret_write_asm' data_addr) secret_write_addr.

  (* Recover from the trap. *)
  Example femtokernel_handler_exit_asm : list AnnotInstr :=
    [ MRET ].

  Definition Label       : Set := string.
  Definition Block       : Set := list AnnotInstr.

  Definition init                 : Label := "init".
  Definition handler_entry        : Label := "handler_entry".
  Definition handler_dispatch     : Label := "handler_dispatch".
  Definition handler_not_zero     : Label := "handler_not_zero".
  Definition handler_is_zero      : Label := "handler_is_zero".
  Definition handler_shutdown_check : Label := "handler_shutdown_check".
  Definition handler_shutdown     : Label := "handler_shutdown".
  Definition handler_secret_write : Label := "handler_secret_write".
  Definition handler_exit         : Label := "handler_exit".

  Definition femtokernel_block_layout : list (Label * Block) :=
    [ (init                 , femtokernel_init' 0 0 0)
    ; (handler_entry        , femtokernel_handler_entry_asm 0)
    ; (handler_dispatch     , femtokernel_handler_dispatch_asm 0 0 0)
    ; (handler_not_zero     , femtokernel_handler_not_zero_asm 0 0 0)
    ; (handler_is_zero      , femtokernel_handler_is_zero_asm 0 0 0)
    ; (handler_shutdown_check, femtokernel_handler_shutdown_check_asm 0)
    ; (handler_shutdown     , femtokernel_handler_shutdown_asm)
    ; (handler_secret_write , femtokernel_handler_secret_write_asm 0 0)
    ; (handler_exit         , femtokernel_handler_exit_asm) ]%list.

  Definition map_with_label {A B} (f : A -> B) (l : list (Label * A)) : list (Label * B) :=
    map (λ '(l, b), (l, f b)) l.

  Definition find_label {A} (label : Label) (l : list (Label * A)) (default : A) : A :=
    match find (λ '(l', _), String.eqb label l') l with
    | None   => default
    | Some e => snd e
    end.

  Fixpoint from_label {A} (label : Label) (l : list (Label * A)) : list (Label * A) :=
    match l with
    | [] => []
    | (e , a) :: l' =>
        if String.eqb e label
        then l
        else from_label label l'
    end%list.

  Definition block_size : list AST -> N :=
    N.of_nat ∘ Nat.mul bytes_per_instr  ∘ List.length.

  Definition annot_block_size : list AnnotInstr -> N :=
    block_size ∘ filter_AST.

  Definition femtokernel_block_sizes : list (Label * N) :=
    map_with_label annot_block_size femtokernel_block_layout.

  (* SIZES *)
  Definition init_size : N := find_label init femtokernel_block_sizes 0%N.
  Definition handler_entry_size : N := find_label handler_entry femtokernel_block_sizes 0%N.
  Definition handler_dispatch_size : N := find_label handler_dispatch femtokernel_block_sizes 0%N.
  Definition handler_not_zero_size : N := find_label handler_not_zero femtokernel_block_sizes 0%N.
  Definition handler_is_zero_size : N := find_label handler_is_zero femtokernel_block_sizes 0%N.
  Definition handler_shutdown_check_size : N := find_label handler_shutdown_check femtokernel_block_sizes 0%N.
  Definition handler_shutdown_size : N := find_label handler_shutdown femtokernel_block_sizes 0%N.
  Definition handler_secret_write_size : N := find_label handler_secret_write femtokernel_block_sizes 0%N.
  Definition handler_exit_size : N := find_label handler_exit femtokernel_block_sizes 0%N.
  Definition handler_size : N := handler_entry_size + handler_dispatch_size + handler_not_zero_size + handler_is_zero_size + handler_shutdown_check_size + handler_shutdown_size + handler_secret_write_size + handler_exit_size.

  (* addrs_for_blocks returns a list of the same length as the given list of
     blocks, but with the address each block is located at. An initial address
     needs to be given for the first block, and all other blocks will be
     placed in sequence after another. *)
  Definition addrs_for_blocks (bs : list (Label * list AST)) (init_addr : N) : list (Label * N) :=
    let f (acc : list (Label * N) * N) (b : Label * list AST) : list (Label * N) * N :=
      let '(label, b) := b in
      let '(addrs, curr) := acc in
      (cons (label , curr) addrs, (curr + block_size b)%N) in
    let '(addrs, end_addr) := foldl f ([]%list, init_addr) bs in
    reverse (cons ("_", end_addr) addrs). (* We choose the label _ for the end addr. *)

  (* ADDRESSES *)
  (* We fix the init addr to 0 for our femtokernel blocks *)
  Definition init_addr : N := 0.

  (* We compute all addresses w.r.t. the FemtoKernel block layout at once.
     Note that we also get the "end" or "exit" address of our kernel as
     part of this definition. So the resulting list has a length of:
     number of blocks + 1. *)
  Definition femtokernel_block_addrs : list (Label * N) :=
    addrs_for_blocks (map_with_label filter_AST femtokernel_block_layout) init_addr.

  (* Note that we need to use "Eval compute in ..." for all addresses.
     In proofs below, we often use cbn/simpl/..., which will hang if we
     don't compute here. *)
  Definition handler_entry_addr        : N :=
    Eval compute in find_label handler_entry femtokernel_block_addrs 0%N.
  Definition handler_dispatch_addr     : N :=
    Eval compute in find_label handler_dispatch femtokernel_block_addrs 0%N.
  Definition handler_not_zero_addr          : N :=
    Eval compute in find_label handler_not_zero femtokernel_block_addrs 0%N.
  Definition handler_is_zero_addr         : N :=
    Eval compute in find_label handler_is_zero femtokernel_block_addrs 0%N.
  Definition handler_shutdown_check_addr : N :=
    Eval compute in find_label handler_shutdown_check femtokernel_block_addrs 0%N.
  Definition handler_shutdown_addr     : N :=
    Eval compute in find_label handler_shutdown femtokernel_block_addrs 0%N.
  Definition handler_secret_write_addr : N :=
    Eval compute in find_label handler_secret_write femtokernel_block_addrs 0%N.
  Definition handler_exit_addr         : N :=
    Eval compute in find_label handler_exit femtokernel_block_addrs 0%N.
  Definition data_addr                 : N :=
    Eval compute in snd (List.last femtokernel_block_addrs ("_", 0%N)).
  (* We allocate one word for the data addr *)
  Definition adv_addr                  : N :=
    data_addr + (N.of_nat bytes_per_word).

  Definition femtokernel_handler : list AnnotInstr :=
    (foldl app []%list ∘ map snd ∘ from_label handler_entry) femtokernel_block_layout.

  (* CODE AND CONFIG SHORTANDS*)

  Definition pmp_cfg_to_term {Σ} : list PmpEntryCfg -> list (Term Σ (ty.prod ty_pmpcfg_ent ty_xlenbits)) :=
    let term_cfg cfg := term_val ty_pmpcfg_ent cfg in
    let term_addr a  := term_val ty_xlenbits a in
    map (fun '(cfg , addr) => term_binop bop.pair (term_cfg cfg) (term_addr addr)).

  Definition femto_pmpentries : list PmpEntryCfg := [(femto_pmpcfg_ent0, bv.of_N adv_addr); (femto_pmpcfg_ent1, bv.of_N adv_addr_end)]%list.

  Definition term_femto_pmpentries {Σ} : Term Σ (ty.list (ty.prod ty_pmpcfg_ent ty_xlenbits)) :=
    term_list (pmp_cfg_to_term femto_pmpentries).

  (* Definition of the femtokernel initialization procedure that works both for the legacy and the MMIO case, since the address of the adversary is equal in both cases *)
  (* note that the addresses we supply assume base address 0 but the code actually only uses relative addresses, so it's okay if it's placed elsewhere in memory.    *)
  Definition femtokernel_init_gen := femtokernel_init' init_addr handler_entry_addr adv_addr.

  Definition femtokernel_handler_entry := femtokernel_handler_entry_asm (handler_dispatch_size + handler_not_zero_size + handler_is_zero_size).
  Definition femtokernel_handler_dispatch := femtokernel_handler_dispatch_asm handler_dispatch_addr data_addr handler_not_zero_size.
  Definition femtokernel_handler_not_zero := femtokernel_handler_not_zero_asm handler_not_zero_addr data_addr handler_exit_addr.
  Definition femtokernel_handler_is_zero := femtokernel_handler_is_zero_asm handler_is_zero_addr data_addr handler_exit_addr.
  Definition femtokernel_handler_shutdown_check := femtokernel_handler_shutdown_check_asm handler_shutdown_size.
  Definition femtokernel_handler_shutdown := femtokernel_handler_shutdown_asm.
  Definition femtokernel_handler_secret_write := femtokernel_handler_secret_write_asm handler_secret_write_addr data_addr.
  Definition femtokernel_handler_exit := femtokernel_handler_exit_asm.

  Definition advAddrs : list (bv xlenbits) := bv.seq (bv.of_N adv_addr) (Z.of_N (adv_addr_end - adv_addr)).

  Global Instance dec_has_some_access {ents p1} : forall x, Decision (∃ p2, Pmp_access x (bv.of_nat 1) ents p1 p2).
  Proof.
    intros x.
    eapply finite.exists_dec.
    intros p2.
    unfold Pmp_access, Gen_Pmp_access.
    destruct (pmp_check_aux x (bv.of_nat 1) bv.zero ents p1 p2); [left|right]; easy.
  Defined.

  Lemma adv_is_live y : (y ∈ advAddrs)%stdpp → (y ∈ liveAddrs)%stdpp.
  Proof. unfold advAddrs, liveAddrs.
         apply bv.seq_subseteq; now compute.
  Qed.

  Ltac case_if H :=
    let go P := (destruct P eqn:H) in
      match goal with
      | |- context [if ?P then _ else _] => go P
      | K: context [if ?P then _ else _] |- _ => go P
      end.

  Lemma adv_in_pmp x : (x ∈ advAddrs)%stdpp -> (∃ p : Val ty_access_type, Pmp_access x (bv.of_nat 1) femto_pmpentries User p).
  Proof.
    intro Hin. rewrite /femto_pmpentries.
    exists Read.
    cbv [Pmp_access Gen_Pmp_access pmp_check_aux pmp_check_rec pmp_match_entry].
    apply bv.elem_of_seq_bounds in Hin as [Hlo Hhi]; [|clear Hin; now compute].
    cbn in *. eassert (Ha : adv_addr = _) by now compute.
    eassert (He : adv_addr_end = _) by now compute.
    rewrite Ha He in Hlo Hhi |- *. change (bv.unsigned (bv.of_N ?y)) with (Z.of_N y) in *.
    assert (bv.unsigned (bv.add x (bv.of_nat 1)) = bv.unsigned x + 1)%Z as H1.
    { rewrite -bv.unsigned_add_small; change (bv.unsigned (bv.of_nat 1)) with 1%Z; lia. }
    case_if H; [now compute | clear H].
    case_if H.
    { apply orb_prop in H as [H|H]; apply bv.uleb_ule, bv.ule_iff_unsigned_le in H;
        change (bv.unsigned (bv.of_N ?y)) with (Z.of_N y) in H; lia. }
    clear H. case_if H; first easy.
    apply andb_false_iff in H as [H|H]; apply bv.uleb_ugt, bv.ult_iff_unsigned_lt in H;
      change (bv.unsigned (bv.of_N ?y)) with (Z.of_N y) in H; lia.
  Qed.

  Lemma pmp_in_adv x : (∃ p : Val ty_access_type, Pmp_access x (bv.of_nat 1) femto_pmpentries User p) → (x ∈ advAddrs)%stdpp.
  Proof.
    intros [p HPmp]. rewrite /femto_pmpentries.
    cbv [Pmp_access Gen_Pmp_access pmp_check_aux pmp_check_rec pmp_match_entry] in HPmp.
    cbn in HPmp.
    case_if H; first now compute. clear H.
    case_if H; first by exfalso.
    apply orb_false_elim in H as [_ Hhi]. apply bv.uleb_ugt, bv.ult_iff_unsigned_lt in Hhi.
    case_if H'; last by exfalso.
    apply andb_prop in H' as [Hlo _]. apply bv.uleb_ule, bv.ule_iff_unsigned_le in Hlo.
    apply bv.elem_of_seq_bounds; first now compute.
    revert Hlo Hhi. rewrite -!bv.of_Z_N -!bv.unsigned_of_Z_small; try lia; now compute.
  Qed.

  (* Use permutation rather than membership to avoid indexes *)
  Lemma allAddr_filter_advAddr : filter
                 (λ x : Val ty_word ,
                    (∃ p : Val ty_access_type, Pmp_access x (bv.of_nat 1) femto_pmpentries User p)%type)
                 all_addrs ≡ₚ advAddrs.
  Proof. rewrite (list_filter_iff _ (fun x => x ∈ advAddrs)); last split; auto using adv_in_pmp, pmp_in_adv.
    apply NoDup_Permutation.
    - apply NoDup_filter. rewrite all_addrs_eq. apply bv.NoDup_seq.
      pose proof (Z.pow_nonneg 2 (Z.of_nat xlenbits)). lia.
    - apply bv.NoDup_seq. now compute.
    - intros x. rewrite list_elem_of_filter.
      split.
      + now intros [? ?].
      + split; [auto | apply addr_in_all_addrs].
  Qed.

  Definition mem_has_word (μ : Memory) (a : Val ty_word) (w : Val ty_word) : Prop :=
    ∃ v0 v1 v2 v3, map (memory_ram μ) (bv.seq a 4) = [v0; v1; v2; v3]%list /\ bv.app v0 (bv.app v1 (bv.app v2 (bv.app v3 bv.nil))) = w.

  (* byte order correct? *)
  Definition mem_has_instr (μ : Memory) (a : Val ty_word) (instr : AST) : Prop :=
    ∃ w, mem_has_word μ a w /\ pure_decode w = instr.

  Fixpoint mem_has_instrs (μ : Memory) (a : Val ty_word) (instrs : list AST) : Prop :=
    match instrs with
    | cons inst instrs => mem_has_instr μ a inst /\ mem_has_instrs μ (bv.add (bv.of_N 4) a) instrs
    | nil => True
    end.

  (* The memory contains the code of the FemtoKernel, and the secret at the
     data address. *)
  Definition mem_has_femtokernel (μ : Memory) (secret : Val ty_xlenbits) : Prop :=
    mem_has_instrs μ (bv.of_N init_addr) (filter_AST femtokernel_init_gen) ∧
    mem_has_instrs μ (bv.of_N handler_entry_addr) (filter_AST femtokernel_handler_entry) ∧
    mem_has_instrs μ (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) ∧
    mem_has_instrs μ (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) ∧
    mem_has_instrs μ (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) ∧
    mem_has_instrs μ (bv.of_N handler_shutdown_check_addr) (filter_AST femtokernel_handler_shutdown_check) ∧
    mem_has_instrs μ (bv.of_N handler_shutdown_addr) (filter_AST femtokernel_handler_shutdown) ∧
    mem_has_instrs μ (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) ∧
    mem_has_instrs μ (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) ∧
    mem_has_word μ (bv.of_N data_addr) secret.

  (* The initial register values that the FemtoKernel relies on. *)
  Definition femto_init_regs (γ : RegStore) : Prop :=
    read_register γ mstatus = {| MPP := User; SPP := User; MPIE := false; SPIE := false; MIE := false; SIE := false |} ∧
    read_register γ cur_privilege = Machine ∧
    read_register γ pmp0cfg = default_pmpcfg_ent ∧
    read_register γ pmpaddr0 = bv.zero ∧
    read_register γ pmp1cfg = default_pmpcfg_ent ∧
    read_register γ pmpaddr1 = bv.zero ∧
    read_register γ pc = bv.of_N init_addr ∧
    read_register γ mideleg = Minterrupts_zero ∧
    read_register γ medeleg = Medeleg_zero.

  (* Note that the split differs depending on whether or not we have an MMIO region! *)
  Lemma liveAddrs_split : (liveAddrs = bv.seq (bv.of_N init_addr) (Z.of_N init_size) ++ bv.seq (bv.of_N handler_entry_addr) (Z.of_N handler_size) ++ bv.seq (bv.of_N data_addr) (Z.of_nat bytes_per_word) ++ advAddrs)%list.
  Proof.
    (* TODO: scalable proof *)
    by compute.
  Qed.

  Lemma handlerAddrs_split : (@bv.seq xlenbits (bv.of_N handler_entry_addr) (Z.of_N handler_size) = bv.seq (bv.of_N handler_entry_addr) (Z.of_N handler_entry_size) ++ bv.seq (bv.of_N handler_dispatch_addr) (Z.of_N handler_dispatch_size) ++ bv.seq (bv.of_N handler_not_zero_addr) (Z.of_N handler_not_zero_size) ++ bv.seq (bv.of_N handler_is_zero_addr) (Z.of_N handler_is_zero_size) ++ bv.seq (bv.of_N handler_shutdown_check_addr) (Z.of_N handler_shutdown_check_size) ++ bv.seq (bv.of_N handler_shutdown_addr) (Z.of_N handler_shutdown_size) ++ bv.seq (bv.of_N handler_secret_write_addr) (Z.of_N handler_secret_write_size) ++ bv.seq (bv.of_N handler_exit_addr) (Z.of_N handler_exit_size))%list.
  Proof.
    (* TODO: scalable proof *)
    by compute.
  Qed.
End FemtoKernel.
