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
     SmallStep.Step
     RiscvPmp.PmpCheck
     RiscvPmp.GVT.Spec
     RiscvPmp.GVT.TotalVerifier
     RiscvPmp.GVT.IrisModel
     RiscvPmp.GVT.IrisInstance
     RiscvPmp.Machine
     RiscvPmp.GVT.Logic
     RiscvPmp.GVT.trace
     RiscvPmp.iostate
     RiscvPmp.GVT.Sig.
From Katamaran Require
     RiscvPmp.GVT.Contracts
     RiscvPmp.GVT.LoopVerification
     RiscvPmp.GVT.Model.
From iris.base_logic Require lib.gen_heap lib.iprop invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac big_op.
From iris.program_logic Require weakestpre adequacy.
From iris.proofmode Require string_ident proofmode.
From stdpp Require namespaces.

Import RiscvPmpProgram
.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.
Import ListNotations.
Open Scope ctx_scope.

Module inv := invariants.

  Import ctx.resolution.
  Import ctx.notations.
  Import env.notations.
  Import iris.program_logic.weakestpre.
  Import iris.proofmode.proofmode.

  Import MicroSail.ShallowExecutor.

  Import RiscvPmp.GVT.Contracts.
  Import RiscvPmpIrisPrelims RiscvPmpIrisBase.
  Import RiscvPmpIrisInstancePredicates.
  Import RiscvPmpIrisInstance.
  Import RiscvPmpBlockVerifSpec.
  Import RiscvPmpIrisInstanceWithContracts.
  Import RiscvPmpShallowExec.

  Section FemtoKernel.
    Import bv.notations.
    Import ListNotations.
    Import TermNotations.

    Open Scope hex_Z_scope.

    (* FIXED ADDRESSES *)
    (* The first address that is no longer used by the adversary, and hence the address at which the PMP entries should stop granting permission. Note that this address is currently also the first MMIO address. *)
    Definition adv_addr_end : N := maxAddr. (* Change once adversary gets access to MMIO*)
    (* Address where we will write in MMIO memory, and proof that our writes will indeed be within the MMIO region*)
    Definition mmio_dev_addr : N := mmioStartAddr.
    Definition mmio_read_addr : N := mmioStartAddr + 4.

    Lemma write_word_is_MMIO: withinMMIO (bv.of_N mmio_dev_addr) bytes_per_word.
    Proof. apply bounds_withinMMIO; now compute. Qed.

    Lemma write_interrupt_is_MMIO: withinMMIO (bv.of_N mmio_read_addr) bytes_per_word.
    Proof. apply bounds_withinMMIO; now compute. Qed.

    (* Aliases for registers *)
    Definition zero : RegIdx := [bv 0].
    Definition ra : RegIdx := [bv 1].
    Definition t0 : RegIdx := [bv 5].
    Definition t1 : RegIdx := [bv 6].
    Definition t2 : RegIdx := [bv 7].
    Definition t3 : RegIdx := [bv 28].
    Definition t4 : RegIdx := [bv 29].
    Definition a0 : RegIdx := [bv 10].

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
    Definition filter_AnnotInstr_AST (l : list AnnotInstr) := base.omap extract_AST l.
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
    Example femtokernel_init_asm (handler_start : N) (adv_start : N) : list ASM :=
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

    (* dispatch *)
    Example femtokernel_mmio_handler_asm_block0 (mmio_handler_start_block2 : N) : list ASM :=
      [
        CSR MCause zero t1 false CSRRS (* t1 <- mcause *)
        ; UTYPE (bv.drop 12 (bv.of_N 0x80000000)) t0 RISCV_LUI   (* load upper 20 bits of immediate *)
        ; ITYPE (@bv.take 12 xlenbits (bv.of_N 0x80000000)) t0 t0 RISCV_ADDI    (* load lower 12 bits of immediate *)
        ; RTYPE t0 t1 t1 RISCV_AND (* t1 <- mask mcause with msb *)
        ; Λ current_pc, BTYPE (bv.of_N (mmio_handler_start_block2 - current_pc)) t1 zero RISCV_BEQ (* branch if t1 = zero *)
      ].

    Example femtokernel_mmio_handler_block0' (handler_start : N) (mmio_handler_start_block2 : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_mmio_handler_asm_block0 mmio_handler_start_block2) handler_start.


    (* handle interrupts *)
    Example femtokernel_mmio_handler_asm_block1 (data_start : N) (mmio_interrupt_addr : N) : list ASM :=
      [
          UTYPE (bv.drop 12 (@bv.of_N xlenbits mmio_interrupt_addr)) t0 RISCV_LUI   (* load upper 20 bits of mmio_interrupt_addr *)
        ; ITYPE (@bv.take 12 xlenbits (bv.of_N mmio_interrupt_addr)) t0 t0 RISCV_ADDI    (* load lower 12 bits of mmio_interrupt_addr *)
        ; LOAD bv.zero t0 t1 true WORD (* t1 <- mmio_interrupt_state *)
        ; STORE bv.zero t1 t0 WORD (* mmio_interrupt_addr <- t1 // clear interrupt pending of all pins *)

        (* Set up t2 as flag for current IOSTATE (stored at data) *)
        ; UTYPE (bv.drop 12 (@bv.of_N xlenbits data_start)) t0 RISCV_LUI   (* load upper 20 bits of data *)
        ; ITYPE (@bv.take 12 xlenbits (bv.of_N data_start)) t0 t0 RISCV_ADDI    (* load lower 12 bits of data *)
        ; LOAD bv.zero t0 t2 true WORD (* t2 <- data *)
        ; ITYPE (bv.one) t2 t2 RISCV_ANDI (* set all irrelevant bits to 0 *)

        (* Set up t3 as flag for interrupt RESET value (stored at bit 3 of t1) *)
        ; RTYPE t1 zero t3 RISCV_ADD (* t3 <- t1 *)
        ; SHIFTIOP (bv.of_N 3) t3 t3 RISCV_SRLI (* t3 >> 3 *)
        ; ITYPE (bv.one) t3 t3 RISCV_ANDI (* set all irrelevant bits to 0 *)

        (* Set up t4 as flag for interrupt STOP value (stored at bit 4 of t1) *)
        ; RTYPE t1 zero t4 RISCV_ADD (* t4 <- t1 *)
        ; SHIFTIOP (bv.of_N 4) t4 t4 RISCV_SRLI (* t4 >> 4 *)
        ; ITYPE (bv.one) t4 t4 RISCV_ANDI (* set all irrelevant bits to 0 *)

        (* if STOP set, then set IOSTATE else if RESET set, then unset IOSTATE else leave IOSTATE as it is. *)
        (* this is ensured by the formula [ iostate <- (¬reset /\ iostate) || stop ] which is implemented below *)
        ; ITYPE (bv.one) t3 t3 RISCV_XORI (* flip t3 *)
        ; RTYPE t2 t3 t2 RISCV_AND (* t2 <- t2 && t3 *)
        ; RTYPE t2 t4 t2 RISCV_OR  (* t2 <- t2 || t4 *)

        ; STORE bv.zero t2 t0 WORD (* store new iostate in data *)

        ; MRET (* return to where left of, no need to adapt MEPC *)
      ].

    Example femtokernel_mmio_handler_block1' (handler_start: N) (data_start : N) (mmio_interrupt_addr : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_mmio_handler_asm_block1 data_start mmio_interrupt_addr) handler_start.

    (* handle access faults *)
    Example femtokernel_mmio_handler_asm_block2 (data_start : N) (mmio_dev_addr : N) : list ASM :=
      [

        (* Set up t2 as flag for current IOSTATE (stored at data) *)
          UTYPE (bv.drop 12 (bv.of_N data_start)) t0 RISCV_LUI   (* load upper 20 bits of data *)
        ; ITYPE (@bv.take 12 xlenbits (bv.of_N data_start)) t0 t0 RISCV_ADDI    (* load lower 12 bits of data *)
        ; LOAD bv.zero t0 t2 true WORD (* t2 <- data *)
        ; ITYPE (bv.one) t2 t2 RISCV_ANDI (* set all irrelevant bits to 0 *)

        (* setup t2 as an inverted bitmask for bit 5 (LED) *)
        ; ITYPE bv.one t2 t2 RISCV_XORI (* invert IOSTATE because SGo = 0 and SStop = 1 *)
        ; SHIFTIOP (bv.of_N 5) t2 t2 RISCV_SLLI (* t2 << 5, mask bit 5 *)


        (* apply bitmask to a0 ensuring that bit 5 (LED) is only set to 1 if IOSTATE is 0 *)
        ; RTYPE a0 t2 a0 RISCV_AND (* [a0 <- t2 /\ a0] *)

        (* store a0 to mmio_dev_addr *)
        ; UTYPE (bv.drop 12 (bv.of_N mmio_dev_addr)) t0 RISCV_LUI   (* load upper 20 bits of mmio_dev_addr *)
        ; ITYPE (@bv.take 12 xlenbits (bv.of_N mmio_dev_addr)) t0 t0 RISCV_ADDI    (* load lower 12 bits of mmio_dev_addr *)
        ; STORE bv.zero a0 t0 WORD (* MMIO@t0 <- a0 *)

        ; CSR MEpc zero ra false CSRRS (* ra <- pc of calling instruction *)
        ; ITYPE (bv.of_N 4) ra ra RISCV_ADDI    (* ra <- ra + 4 *)
        ; CSR MEpc ra zero false CSRRW (* mepc <- ra *)

        ; MRET (* return one instruction further to where we left of *)
      ].

    Example femtokernel_mmio_handler_block2' (handler_start : N) (data_start : N) (mmio_dev_addr : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_mmio_handler_asm_block2 data_start mmio_dev_addr) handler_start.

    Definition Label       : Set := string.
    Definition Block       : Set := list AnnotInstr.

    Definition init           : Label := "init".
    Definition handler_block0 : Label := "handler_block0".
    Definition handler_block1 : Label := "handler_block1".
    Definition handler_block2 : Label := "handler_block2".

    Definition femtokernel_block_layout : list (Label * Block) :=
      [ (init                 , femtokernel_init' 0 0 0)
      ; (handler_block0, femtokernel_mmio_handler_block0' 0 0 )
      ; (handler_block1, femtokernel_mmio_handler_block1' 0 0 0)
      ; (handler_block2, femtokernel_mmio_handler_block2' 0 0 0)]%list.

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
      block_size ∘ filter_AnnotInstr_AST.

    Definition femtokernel_block_sizes : list (Label * N) :=
      map_with_label annot_block_size femtokernel_block_layout.


    (* SIZES *)
    Definition instruction_size : N := N.of_nat bytes_per_instr.
    Definition data_size : N := N.of_nat xlenbytes.

    Definition init_size : N := find_label init femtokernel_block_sizes 0%N.
    Definition mmio_handler_size_block0: N := find_label handler_block0 femtokernel_block_sizes 0%N.
    Definition mmio_handler_size_block1: N := find_label handler_block1 femtokernel_block_sizes 0%N.
    Definition mmio_handler_size_block2 : N := find_label handler_block2 femtokernel_block_sizes 0%N.

    (* ADDRESSES *)

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
      addrs_for_blocks (map_with_label filter_AnnotInstr_AST femtokernel_block_layout) init_addr.

    (* Note that we need to use "Eval compute in ..." for all addresses.
       In proofs below, we often use cbn/simpl/..., which will hang if we
       don't compute here. *)
    Definition mmio_handler_addr_block0        : N :=
      Eval compute in find_label handler_block0 femtokernel_block_addrs 0%N.
    Definition mmio_handler_addr_block1       : N :=
      Eval compute in find_label handler_block1 femtokernel_block_addrs 0%N.
    Definition mmio_handler_addr_block2 : N :=
      Eval compute in find_label handler_block2 femtokernel_block_addrs 0%N.

    Definition data_addr                 : N :=
      Eval compute in snd (List.last femtokernel_block_addrs ("_", 0%N)).
    (* We allocate one word for the data addr *)
    Definition adv_addr                  : N :=
      data_addr + (N.of_nat bytes_per_word).

    (* CODE AND CONFIG SHORTANDS *)
    Local Notation "e1 ',ₜ' e2" := (term_binop bop.pair e1 e2) (at level 100).
    (* Shorthand for the pmp entries in both Katamaran and Iris *)

    (* Shorthand for the pmp entries in both Katamaran and Iris *)
    Local Abbreviation asn_femto_pmpentries a :=
      ([(term_val ty_pmpcfg_ent femto_pmpcfg_ent0 ,ₜ (a +ᵇ term_val ty_xlenbits (bv.of_N adv_addr)));
        (term_val ty_pmpcfg_ent femto_pmpcfg_ent1 ,ₜ (term_val ty_xlenbits (bv.of_N adv_addr_end)))])%list.

    Definition pmp_cfg_to_term {Σ} : list PmpEntryCfg -> list (Term Σ (ty.prod ty_pmpcfg_ent ty_xlenbits)) :=
      let term_cfg cfg := term_val ty_pmpcfg_ent cfg in
      let term_addr a  := term_val ty_xlenbits a in
      map (fun '(cfg , addr) => term_binop bop.pair (term_cfg cfg) (term_addr addr)).

    Definition femto_pmpentries : list PmpEntryCfg := [(femto_pmpcfg_ent0, bv.of_N adv_addr); (femto_pmpcfg_ent1, bv.of_N adv_addr_end)]%list.

    Definition term_femto_pmpentries {Σ} : Term Σ (ty.list (ty.prod ty_pmpcfg_ent ty_xlenbits)) :=
      term_list (pmp_cfg_to_term femto_pmpentries).

    (* Definition of the femtokernel initialization procedure. *)
    (* Note that the addresses we supply assume a base address of 0. The code however uses relative addresses and could be placed elsewhere in memory. *)
    Definition femtokernel_init_gen := femtokernel_init' init_addr mmio_handler_addr_block0 adv_addr.

    Definition femtokernel_mmio_handler_block0 := femtokernel_mmio_handler_block0' mmio_handler_addr_block0.
    Definition femtokernel_mmio_handler_block1 := femtokernel_mmio_handler_block1' mmio_handler_addr_block1.
    Definition femtokernel_mmio_handler_block2 := femtokernel_mmio_handler_block2' mmio_handler_addr_block2.
    (* We reflect the booleans present in the contracts, but now at the meta level. This allows us to recycle large parts of the Katamaran and Iris contracts as part of the verification. *)
    Definition femtokernel_handler_gen_block0 := femtokernel_mmio_handler_block0.
    Definition femtokernel_handler_gen_block1 := femtokernel_mmio_handler_block1.
    Definition femtokernel_handler_gen_block2 := femtokernel_mmio_handler_block2.

    Import asn.notations.
    Import RiscvPmp.GVT.Sig.
    (* Fix word length at 4 for this example, as we do not perform any other writes*)
    Local Notation asn_mmio_trace_state_inv := (asn.chunk (chunk_user (mmio_state_trace bytes_per_word) [env])).
    Local Notation asn_mmio_state_pred s := (asn.chunk (chunk_user (mmio_state bytes_per_word) [s])).
    Local Notation asn_mmio_read_valid a s := (asn.formula (formula_user (mmio_read_valid bytes_per_word) [a; s])).
    Local Notation asn_mmio_event a v t s s' := (asn.formula (formula_user (mmio_event bytes_per_word) [a; v; t; s; s'])).

    Local Notation asn_pmp_addr_access l m := (asn.chunk (chunk_user pmp_addr_access [l; m])).
    Local Notation asn_pmp_entries l := (asn.chunk (chunk_user pmp_entries [l])).

    Definition post_mip_val : Val ty_Minterrupts :=
      MkMinterrupts false false false false false false false false false.
    Definition term_post_mip_val {Σ} : Term Σ ty_Minterrupts :=
      term_val ty_Minterrupts post_mip_val.

    Definition Σ__csrs : LCtx :=
      ["mtvec" :: ty_xlenbits;
       "mcause" :: ty_xlenbits;
       "mscratch" :: ty_xlenbits;
       "mepc" :: ty_xlenbits;
       "mie" :: ty_Minterrupts;
       "mip" :: ty_Minterrupts;
       "mstatus_mpie" :: ty.bool;
       "mstatus_mpp" :: ty_privilege;
       "mstatus_spp" :: ty_privilege;
       "mstatus_spie" :: ty.bool;
       "mstatus_sie" :: ty.bool;
       "mideleg" :: ty_Minterrupts;
       "medeleg" :: ty_Medeleg;
       "scause" :: ty_xlenbits;
       "sscratch" :: ty_xlenbits;
       "sepc" :: ty_xlenbits;
       "stvec" :: ty_xlenbits].

    Record CSRVals := mkCSRVals {
        vmtvec  : Val ty_xlenbits;
        vmcause : Val ty_xlenbits;
        vmscratch: Val ty_xlenbits;
        vmepc   : Val ty_xlenbits;
        vmie    : Val ty_Minterrupts;
        vmip    : Val ty_Minterrupts;
        vmstatus_mpie : Val ty.bool;
        vmstatus_mpp  : Val ty_privilege;
        vmstatus_spp  : Val ty_privilege;
        vmstatus_spie : Val ty.bool;
        vmstatus_sie  : Val ty.bool;
        vmideleg : Val ty_Minterrupts;
        vmedeleg : Val ty_Medeleg;
        vscause  : Val ty_xlenbits;
        vsscratch  : Val ty_xlenbits;
        vsepc  : Val ty_xlenbits;
        vstvec  : Val ty_xlenbits;
      }.

    Definition CSRVals_Valuation (vals : CSRVals) : Valuation Σ__csrs :=
      [env]
        .["mtvec" ∷ ty_xlenbits ↦ vmtvec vals]
        .["mcause" ∷ ty_xlenbits ↦ vmcause vals]
        .["mscratch" ∷ ty_xlenbits ↦ vmscratch vals]
        .["mepc" ∷ ty_xlenbits ↦ vmepc vals]
        .["mie" ∷ ty_Minterrupts ↦ vmie vals]
        .["mip" ∷ ty_Minterrupts ↦ vmip vals]
        .["mstatus_mpie" ∷ ty.bool ↦ vmstatus_mpie vals]
        .["mstatus_mpp" ∷ ty_privilege ↦ vmstatus_mpp vals]
        .["mstatus_spp" ∷ ty_privilege ↦ vmstatus_spp vals]
        .["mstatus_spie" ∷ ty.bool ↦ vmstatus_spie vals]
        .["mstatus_sie" ∷ ty.bool ↦ vmstatus_sie vals]
        .["mideleg" ∷ ty_Minterrupts ↦ vmideleg vals]
        .["medeleg" ∷ ty_Medeleg ↦ vmedeleg vals]
        .["scause" ∷ ty_xlenbits ↦ vscause vals]
        .["sscratch" ∷ ty_xlenbits ↦ vsscratch vals]
        .["sepc" ∷ ty_xlenbits ↦ vsepc vals]
        .["stvec" ∷ ty_xlenbits ↦ vstvec vals].

    Example femtokernel_init_pre : Assertion ["a"::ty_xlenbits] :=
      (term_unop uop.unsigned (term_var "a") + term_val ty.int (Z.of_N adv_addr) < term_val ty.int (Z.of_N maxAddr))%asn ∗
      (∃ "v", mtvec ↦ term_var "v") ∗
      (∃ "v", mcause ↦ term_var "v") ∗
      (mideleg ↦ term_val ty_Minterrupts Minterrupts_zero) ∗ (medeleg ↦ term_val ty_Medeleg Medeleg_zero) ∗
      (∃ "v", mip ↦ term_var "v") ∗ (∃ "v", mie ↦ term_var "v") ∗
      (∃ "v", mepc ↦ term_var "v") ∗
      (∃ "v" , mscratch ↦ term_var "v") ∗
      (∃ "v", stvec ↦ term_var "v") ∗ (∃ "v", sepc ↦ term_var "v") ∗
      (∃ "v", scause ↦ term_var "v") ∗ (∃ "v", sscratch ↦ term_var "v") ∗
      mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_val ty_privilege User; term_val ty.bool false; term_val ty.bool false; term_val ty.bool false; term_val ty.bool false ] ∗
      cur_privilege ↦ term_val ty_privilege Machine ∗
      asn_regs_ptsto ∅ ∗
      asn_pmp_entries (term_list [(term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ term_val ty_xlenbits bv.zero);
                                  (term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ term_val ty_xlenbits bv.zero)])
    .

    Import TermNotations.

    Example femtokernel_init_post: Assertion  ["a"::ty_xlenbits; ("an"::ty_xlenbits)] :=
      (
        (term_var "an" = term_var "a" +ᵇ (term_val ty_xlenbits (bv.of_N adv_addr)))%asn ∗
          (mtvec ↦ term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N mmio_handler_addr_block0)) ∗
          (∃ "v", mcause ↦ term_var "v") ∗
          (mideleg ↦ term_val ty_Minterrupts Minterrupts_zero) ∗ (medeleg ↦ term_val ty_Medeleg Medeleg_zero) ∗
          (∃ "v", mip ↦ term_var "v") ∗ (∃ "v", mie ↦ term_var "v") ∗
          (mepc ↦ term_var "an") ∗
          (∃ "v" , mscratch ↦ term_var "v") ∗
          (∃ "v", stvec ↦ term_var "v") ∗ (∃ "v", sepc ↦ term_var "v") ∗
          (∃ "v", scause ↦ term_var "v") ∗ (∃ "v", sscratch ↦ term_var "v") ∗
          mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_val ty_privilege User; term_val ty.bool true; term_val ty.bool false; term_val ty.bool true; term_val ty.bool false ] ∗
          cur_privilege ↦ term_val ty_privilege User ∗
          asn_regs_ptsto ∅ ∗
          asn_pmp_entries (term_list (asn_femto_pmpentries (term_var "a")))
      ).


    (* (* note that this computation takes longer than directly proving sat__femtoinit below *) *)
    (* Time Example t_vc__femtoinit : 𝕊 Σ__femtoinit := *)
    (*   Eval vm_compute in *)
    (*   simplify (VC__addr femtokernel_init_pre femtokernel_init femtokernel_init_post). *)

    Definition vc__femtoinit : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition femtokernel_init_pre femtokernel_init_gen femtokernel_init_post wnil).
    Definition vc__femtoinit_unq : 𝕊 [] :=
      Postprocessing.unquantify vc__femtoinit.

    Lemma sat__femtoinit : safeE vc__femtoinit.
    Proof.
      vm_compute.
      constructor; cbn.
      intuition bv_solve_Ltac.solveBvManual.
    Qed.

    (* Precondition that is shared by all handler blocks *)
    Definition femtokernel_handler_shared_pre (addr : N) : Assertion (Σ__csrs ▻▻ ["a" :: ty_xlenbits]) :=
      (term_unop uop.unsigned (term_var "a") + term_val ty.int (Z.of_N (adv_addr - mmio_handler_addr_block0)) < term_val ty.int (Z.of_N maxAddr))%asn ∗
      term_var "a" = term_val ty_xlenbits (bv.of_N addr) ∗
      cur_privilege ↦ term_val ty_privilege Machine ∗
      (mtvec ↦ term_val ty_word (bv.of_N mmio_handler_addr_block0)) ∗
      mcause ↦ term_var "mcause" ∗
      mscratch ↦ term_var "mscratch" ∗
      (∃ "v", mip ↦ term_var "v") ∗ mie ↦ term_var "mie" ∗
      mepc ↦ term_var "mepc" ∗
      sepc ↦ term_var "sepc" ∗
      scause ↦ term_var "scause" ∗
      sscratch ↦ term_var "sscratch" ∗
      stvec ↦ term_var "stvec" ∗
      mideleg ↦ term_val ty_Minterrupts Minterrupts_zero ∗
      medeleg ↦ term_val ty_Medeleg Medeleg_zero ∗
      asn_regs_ptsto ∅ ∗
      asn_pmp_entries term_femto_pmpentries ∗
      asn_mmio_trace_state_inv.

    (* Postcondition that is shared by all handler blocks *)
    Definition femtokernel_handler_shared_post
      (priv : Term (Σ__csrs ▻▻ ["a" :: ty_xlenbits; "an" :: ty_xlenbits]) ty_privilege)
      (epc  : Term (Σ__csrs ▻▻ ["a" :: ty_xlenbits; "an" :: ty_xlenbits]) ty_xlenbits)
      : Assertion (Σ__csrs ▻▻ ["a" :: ty_xlenbits; "an" :: ty_xlenbits]) :=
        cur_privilege ↦ priv ∗
        mtvec ↦ term_val ty_word (bv.of_N mmio_handler_addr_block0) ∗
        mcause ↦ term_var "mcause" ∗
        mscratch ↦ term_var "mscratch" ∗
        (∃ "v", mip ↦ term_var "v") ∗ mie ↦ term_var "mie" ∗
        mepc ↦ epc ∗
        sepc ↦ term_var "sepc" ∗
        scause ↦ term_var "scause" ∗
        sscratch ↦ term_var "sscratch" ∗
        stvec ↦ term_var "stvec" ∗
        mideleg ↦ term_val ty_Minterrupts Minterrupts_zero ∗
        medeleg ↦ term_val ty_Medeleg Medeleg_zero ∗
        asn_regs_ptsto ∅ ∗
        asn_pmp_entries term_femto_pmpentries ∗
        asn_mmio_trace_state_inv.

    Example femtokernel_handler_pre : Assertion (Σ__csrs ▻▻ ["a" :: ty_xlenbits]) :=
      femtokernel_handler_shared_pre mmio_handler_addr_block0 ∗
      mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie";
                                      term_val ty.bool false; term_var "mstatus_sie"] ∗
      (∃ "s", ∃ "sv",  (
        term_val ty_xlenbits (bv.of_N data_addr) ↦ₘ (term_var "sv") ∗ (* statevalue stored at data_addr *)
        term_unop (uop.bvtake 1) (term_var "sv") = term_var "s" ∗ (* statevalue corresponds to ghost state *)
        asn_mmio_state_pred (term_var "s")
      )).

    Example femtokernel_handler_post_block0 : Assertion (Σ__csrs ▻▻ ["a" :: ty_xlenbits; "an" :: ty_xlenbits]) :=
      femtokernel_handler_shared_post (term_val ty_privilege Machine) (term_var "mepc") ∗
      mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
      (∃ "s", ∃ "sv", (
        (asn.or
           (* msb of mcause = 0, no interrupt, jump to block2 *)
           (term_binop bop.bvand (term_var "mcause") (term_val ty_xlenbits (bv.of_N 0x80000000)) = term_val (ty.bvec _) bv.zero ∗
            term_var "an" = term_val ty_word (bv.of_N mmio_handler_addr_block2))
           (* msb of mcause = 1, interrupt, continue to block1 *)
           (term_binop bop.bvand (term_var "mcause") (term_val ty_xlenbits (bv.of_N 0x80000000)) = term_val (ty.bvec _) (bv.of_N 0x80000000) ∗
            term_var "an" = term_val ty_word (bv.of_N mmio_handler_addr_block1))) ∗
        term_val ty_xlenbits (bv.of_N data_addr) ↦ₘ (term_var "sv") ∗ (* statevalue stored at data_addr *)
        term_unop (uop.bvtake 1) (term_var "sv") = term_var "s" ∗ (* statevalue corresponds to ghost state *)
        asn_mmio_state_pred (term_var "s"))).

  Example femtokernel_handler_pre_block1 : Assertion (Σ__csrs ▻▻ ["a" :: ty_xlenbits]) :=
    femtokernel_handler_shared_pre mmio_handler_addr_block1 ∗
    mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie";
                                     term_val ty.bool false; term_var "mstatus_sie"] ∗
    (∃ "s", ∃ "sv", (
      asn_mmio_state_pred (term_var "s") ∗
      term_val ty_xlenbits (bv.of_N data_addr) ↦ₘ (term_var "sv") ∗ (* statevalue stored at data_addr *)
      term_unop (uop.bvtake 1) (term_var "sv") = term_var "s" ∗ (* statevalue corresponds to ghost state *)
      asn_mmio_read_valid (term_val ty_xlenbits (bv.of_N mmio_read_addr)) (term_var "s") (* reading from mmio_read_addr yields a valid value, currently always the case *)
    )).

  Example femtokernel_handler_post_block1 : Assertion (Σ__csrs ▻▻ ["a" :: ty_xlenbits; "an" :: ty_xlenbits]) :=
    femtokernel_handler_shared_post (term_var "mstatus_mpp") (term_var "mepc") ∗
    mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_var "mstatus_spp"; term_val ty.bool true; term_var "mstatus_spie"; term_var "mstatus_mpie"; term_var "mstatus_sie"] ∗
    term_var "an" = term_var "mepc" ∗
    (∃ "s", ∃ "s'", ∃ "sv", (
      asn_mmio_state_pred (term_var "s'") ∗
      (∃ "w", asn_mmio_event (term_val ty_xlenbits (bv.of_N mmio_read_addr)) (term_var "w") (term_val ty_ioeventType IORead) (term_var "s") (term_var "s'")) ∗ (* successful read event allows state change from s to s' *)
      term_val ty_xlenbits (bv.of_N data_addr) ↦ₘ (term_var "sv") ∗ (* statevalue stored at data_addr *)
      term_unop (uop.bvtake 1) (term_var "sv") = term_var "s'" (* statevalue corresponds to new ghost state *)
    )).

  Example femtokernel_handler_pre_block2 : Assertion (Σ__csrs ▻▻ ["a" :: ty_xlenbits]) :=
    femtokernel_handler_shared_pre mmio_handler_addr_block2 ∗
    mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie";
                                      term_val ty.bool false; term_var "mstatus_sie"] ∗
    (∃ "s", ∃ "sv", (
      asn_mmio_state_pred (term_var "s") ∗
      term_val ty_xlenbits (bv.of_N data_addr) ↦ₘ (term_var "sv") ∗ (* statevalue stored at data_addr *)
      term_unop (uop.bvtake 1) (term_var "sv") = term_var "s" (* statevalue corresponds to ghost state *)
    )).

  Example femtokernel_handler_post : Assertion (Σ__csrs ▻▻ ["a" :: ty_xlenbits; "an"::ty_xlenbits]) :=
    femtokernel_handler_shared_post (term_var "mstatus_mpp") (term_var "an") ∗
    mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_var "mstatus_spp"; term_val ty.bool true; term_var "mstatus_spie"; term_var "mstatus_mpie"; term_var "mstatus_sie"] ∗
    term_var "an" = term_var "mepc" +ᵇ term_val ty_xlenbits (bv.of_N 4) ∗
    (∃ "s", ∃ "sv", (
      asn_mmio_state_pred (term_var "s") ∗
      term_val ty_xlenbits (bv.of_N data_addr) ↦ₘ (term_var "sv") ∗ (* statevalue stored at data_addr *)
      term_unop (uop.bvtake 1) (term_var "sv") = term_var "s" (* statevalue corresponds to ghost state *)
    )).

    (* Time Example t_vc__femtohandler : 𝕊 [] := *)
    (*   Eval vm_compute in *)
    (*     simplify (VC__addr femtokernel_handler_pre femtokernel_handler femtokernel_handler_post). *)

    (* let vc1 := VC__addr femtokernel_handler_pre femtokernel_handler femtokernel_handler_post in *)
    (* let vc2 := Postprocessing.prune vc1 in *)
    (* let vc3 := Postprocessing.solve_evars vc2 in *)
    (* let vc4 := Postprocessing.solve_uvars vc3 in *)
    (* let vc5 := Postprocessing.prune vc4 in *)
    (* vc5. *)
    (* Import SymProp.notations. *)
    (* Set Printing Depth 200. *)
    (* Eval vm_compute in vc__femtohandler. *)


    Definition vc__femtohandler_block0 : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                     (femtokernel_handler_pre)
                     (femtokernel_handler_gen_block0 mmio_handler_addr_block2)
                     (femtokernel_handler_post_block0) wnil).

    Definition vc__femtohandler_block1 : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                     (femtokernel_handler_pre_block1)
                     (femtokernel_handler_gen_block1 data_addr mmio_read_addr)
                     (femtokernel_handler_post_block1) wnil).

    Definition vc__femtohandler_block2 : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                     (femtokernel_handler_pre_block2)
                     (femtokernel_handler_gen_block2 data_addr mmio_dev_addr)
                     (femtokernel_handler_post) wnil).

  Import Erasure.notations.
  (* Eval vm_compute in Erasure.erase_symprop vc__femtohandler_block0. *)
  (* Locate erase_symprop. *)

  (* Prove that the verification condition that Katamaran creates for this block holds.
        I.e. we're just proving the verification condition for block0. *)
  Import Erasure.notations.
  Lemma sat__femtohandler_block0 : safeE (vc__femtohandler_block0).
  Proof.
    vm_compute. constructor. cbn. intros.
    repeat split; intros; auto.
     destruct (@bv.appView 31 1 v);
      change (bv.mk 0x80000000 _) with (@bv.app 31 1 bv.zero bv.one) in *;
      rewrite (@bv.land_app 31 1 _ bv.zero _ bv.one);
      rewrite bv.land_zero_r; rewrite bv.land_ones_r;
      destruct (bv.view ys); destruct (bv.view xs0); destruct b; auto;
      simpl in H0; rewrite (@bv.land_app 31 1 _ bv.zero _ bv.one) in H0;
      rewrite bv.land_zero_r in H0; rewrite bv.land_zero_l in H0;
      contradiction.
  Qed.


  (* for debugging *)
  (* Set Printing Depth 200. *)
  (* Eval vm_compute in Erasure.erase_symprop vc__femtohandler_block1. *)


  Lemma sat__femtohandler_block1 : safeE (vc__femtohandler_block1).
  Proof.
    vm_compute. constructor; cbn. intros.
    intuition.
    1: apply bounds_withinMMIO; now compute.
    exists v6. split. apply IOW__sme; auto.
    right. right. exists (bv.take 1 v5), v7. repeat split; auto.

    inversion H1; subst; try discriminate;            (* IOW0, IOW, IOW__sme: IORead = IOWrite *)
    try (exfalso; match goal with
                    | Hn : _ ≠ mmio_interrupt_addr |- _ => apply Hn; now vm_compute   (* IOR *)
                    end).

    match goal with Hw : context [mmio_interrupt_w2s] |- _ => rename Hw into Hw2s end.

    cbn [event_contents event_nbbytes event_type event_addr] in *.
    unfold mmio_interrupt_w2s in *.

    (* shifts *)
    destruct (bv.view v7).
    destruct (bv.view xs). destruct (bv.view xs). destruct (bv.view xs). destruct (bv.view xs).
    change (bv.mk 0x4 _)  with (@bv.of_nat 5 0x4).
    change (bv.mk 0x3 _)  with (@bv.of_nat 5 0x3).
    change (bv.of_nat 4) with (@bv.add 5 bv.one (bv.of_nat 3)).
    change (bv.of_nat 3) with (@bv.add 5 bv.one (@bv.add 5 bv.one (@bv.add 5 bv.one (bv.of_nat 0)))).
    rewrite !bv.shiftr_cons; try (simpl; lia). rewrite !bv.shiftr_zero.
    rewrite <- !Eqdep.EqdepTheory.eq_rec_eq.

    unfold bv.zext'. rewrite !bv.app_cons.

    (* further simplifications of goal *)
    destruct (bv.view v5).  rewrite bv.take_cons in Hw2s.
    change (bv.mk 1 _) with (@bv.cons 31 true bv.zero).
    rewrite !bv.land_cons. rewrite !bv.land_zero_r.

    change (bv.of_N 24) with (bv.cons false (bv.cons false (bv.cons false (bv.cons true (@bv.cons 27 true (bv.zero)))))) in Hw2s.
    repeat rewrite bv.land_cons in Hw2s. rewrite bv.land_zero_r in Hw2s. rewrite !andb_false_r in Hw2s.
    rewrite !andb_true_r.
    rewrite !andb_true_r in Hw2s.

    destruct (bv.view v6). destruct (bv.view xs1). simpl in *.

    destruct b, b0, b1, b2, b3, b4, b5; simpl in *; auto; inversion Hw2s.
  Qed.

  Import Erasure.notations.
  Lemma sat__femtohandler_block2 : safeE (vc__femtohandler_block2).
  Proof.
    vm_compute.
    constructor; cbn. right. exists (bv.take 1 v6).
    intuition.
    1: apply bounds_withinMMIO; now compute.
    destruct (bv.view v6). rewrite bv.take_cons.
    change (@bv.mk 32 1 I) with (@bv.cons 31 true bv.zero).
    rewrite bv.land_cons. rewrite bv.land_zero_r. simpl.
    destruct b eqn: B; simpl.
    - apply IOW0; eauto.
    - apply IOW; eauto. simpl. lia.
  Qed.

  Section WithEnvNotations.
    Import env.notations.

    Definition contract_femtohandler_builder `{sailGS Σ, iostateG IOState Σ}
      (PRE : Assertion (Σ__csrs ▻▻ ["a" :: ty_xlenbits]))
      (b : Block)
      (POST : Assertion (Σ__csrs ▻▻ ["a" :: ty_xlenbits; "an" :: ty_xlenbits]))
      : Val ty_xlenbits -> CSRVals -> iProp Σ :=
      fun a csrs =>
        let ι__csrs := CSRVals_Valuation csrs in
        semTripleBlock
          (λ a, asn.interpret PRE ι__csrs.["a" ∷ ty_xlenbits ↦ a])
          a (filter_AST b)
          (λ a an, asn.interpret POST ι__csrs.["a" ∷ ty_xlenbits ↦ a].["an" ∷ ty_xlenbits ↦ an]).

    (* This is needed to prove the contract_femtohandler_blockX_verified lemma below. *)
    Local Strategy expand [vc__femtohandler_block0 vc__femtohandler_block1 vc__femtohandler_block2].

    Definition contract_femtohandler_block0 `{sailGS Σ, iostateG IOState Σ} : Val ty_xlenbits -> CSRVals -> iProp Σ :=
      contract_femtohandler_builder
        femtokernel_handler_pre
        (femtokernel_handler_gen_block0 mmio_handler_addr_block2)
        femtokernel_handler_post_block0.

    Opaque femtokernel_handler_pre.

    Lemma contract_femtohandler_block0_verified : ∀ `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits) (csrs : CSRVals),
        ⊢ contract_femtohandler_block0 a csrs.
    Proof.
      unfold contract_femtohandler_block0. iIntros (Σ sg ioG a csrs).
      iApply (sound_sannotated_block_verification_condition lemSemBlockVerif).
      exact sat__femtohandler_block0.
    Qed.

    Transparent femtokernel_handler_pre.

    Definition contract_femtohandler_block1 `{sailGS Σ, iostateG IOState Σ} : Val ty_xlenbits -> CSRVals -> iProp Σ :=
      contract_femtohandler_builder
        femtokernel_handler_pre_block1
        (femtokernel_handler_gen_block1 data_addr mmio_read_addr)
        femtokernel_handler_post_block1.

    Opaque femtokernel_handler_pre_block1.


    Lemma contract_femtohandler_block1_verified : ∀ `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits) (csrs : CSRVals),
        ⊢ contract_femtohandler_block1 a csrs.
    Proof.
      unfold contract_femtohandler_block1. iIntros (Σ sg ioG a csrs).
      iApply (sound_sannotated_block_verification_condition lemSemBlockVerif).
      exact sat__femtohandler_block1.
    Qed.

    Transparent femtokernel_handler_pre_block1.
    Opaque femtokernel_handler_pre_block2.

    Definition contract_femtohandler_block2 `{sailGS Σ, iostateG IOState Σ} : Val ty_xlenbits -> CSRVals -> iProp Σ :=
      contract_femtohandler_builder
        femtokernel_handler_pre_block2
        (femtokernel_handler_gen_block2  data_addr mmio_dev_addr)
        femtokernel_handler_post.

    Lemma contract_femtohandler_block2_verified : ∀ `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits) (csrs : CSRVals),
        ⊢ contract_femtohandler_block2 a csrs.
    Proof.
      unfold contract_femtohandler_block2. iIntros (Σ sg ioG a csrs).
      iApply (sound_sannotated_block_verification_condition lemSemBlockVerif).
      exact sat__femtohandler_block2.
    Qed.

   Transparent femtokernel_handler_pre_block2.

  End WithEnvNotations.

  End FemtoKernel.

  (* Avoid expanding interp_ptstomem when doing simplifications *)
  Arguments interp_ptstomem : simpl never.

  Definition advAddrs : list (bv xlenbits) := bv.seq (bv.of_N adv_addr) (Z.of_N (adv_addr_end - adv_addr)).

  Global Instance dec_has_some_access {ents p1} : forall x, Decision (exists p2, Pmp_access x (bv.of_nat 1) ents p1 p2).
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

  Lemma big_sepL_filter `{BiAffine PROP} {A : Type} {l : list A}
      {φ : A → Prop} (dec : ∀ x, Decision (φ x)) (Φ : A -> PROP) :
    ([∗ list] x ∈ filter φ l, Φ x) ⊣⊢
    ([∗ list] x ∈ l, ⌜φ x⌝ -∗ Φ x).
  Proof. induction l.
    - now cbn.
    - cbn.
      destruct (decide (φ a)) as [Hφ|Hnφ].
      + rewrite big_opL_cons.
        rewrite <-IHl.
        iSplit; iIntros "[Ha Hl]"; iFrame; try done.
        now iApply ("Ha" $! Hφ).
      + rewrite <-IHl.
        iSplit.
        * iIntros "Hl"; iFrame; iIntros "%Hφ"; intuition.
        * iIntros "[Ha Hl]"; now iFrame.
  Qed.

  Lemma memAdv_pmpPolicy `{sailGS Σ, iostateG IOState Σ} :
    (ptstoSthL advAddrs ⊢
      interp_pmp_addr_access liveAddrs mmioAddrs femto_pmpentries User)%I.
  Proof.
    iIntros "Hadv".
    unfold interp_pmp_addr_access.
    rewrite <-(big_sepL_filter).
    unfold ptstoSthL.
    rewrite -> (big_opL_permutation _ _ _ allAddr_filter_advAddr).
    iApply (big_sepL_mono with "Hadv"). iIntros (? ? Hsom) "Hptsto".
    unfold interp_addr_access_byte.
    apply list_elem_of_lookup_2, adv_is_live in Hsom.
    repeat case_decide; auto.
    iPureIntro. eapply mmio_ram_False; eauto.
  Qed.

  Opaque interp_pmp_entries.

  (* Needed when introducing the below conditional *)
  Local Instance if_persistent `{sailGS Σ} (b : bool) (A B : iProp Σ) (P: Persistent A) (P' : Persistent B)  : Persistent (if b then A else B).
  Proof. destruct b; apply _. Qed.

  Ltac set_to_list s l Hl Hel :=
    remember (elements s) as l eqn:Hel;
    assert (Hl : list_to_set l = s) by (subst; apply list_to_set_elements_L).

  Ltac set_subseteq_to_list :=
    match goal with
    | |- ?s1 ⊆@{gset _} ?s2 =>
        let l1 := fresh "l" in
        let l2 := fresh "l" in
        let Hl1 := fresh "Hl" in
        let Hl2 := fresh "Hl" in
        let Hel1 := fresh "Hel" in
        let Hel2 := fresh "Hel" in
        set_to_list s1 l1 Hl1 Hel1;
        set_to_list s2 l2 Hl2 Hel2;
        vm_compute in Hel1;
        vm_compute in Hel2;
        rewrite <- Hl1, <- Hl2;
        apply list_to_set_subseteq;
        rewrite Hel1 Hel2
    end.

  Ltac solve_elem_of :=
    repeat (try apply list_elem_of_here;
            try apply list_elem_of_further).

  Ltac solve_list_subseteq :=
    repeat
      match goal with
      | |- []%list ⊆ ?l =>
          apply list_subseteq_nil
      | |- ?l1 ⊆ ?l2 =>
          apply list_subseteq_cons_iff
      | |- ?P ∧ ?q =>
          split
      | |- ?e ∈ ?l =>
          solve_elem_of
      end.

  Ltac solve_subseteq :=
    set_subseteq_to_list;
    solve_list_subseteq.

  Ltac reduce_big_sepS_big_sepL :=
    repeat
      match goal with
      | |- context[big_opS ?op ?f ?s] =>
          let l := fresh "l" in
          let Hl := fresh "Hl" in
          let Hel := fresh "Hel" in
          set_to_list s l Hl Hel;
          rewrite <- Hl;
          assert (Hdup : NoDup l) by (subst; apply NoDup_elements);
          rewrite (big_sepS_list_to_set _ _ Hdup);
          vm_compute in Hel;
          rewrite Hel
      end.

  Definition femtokernel_safe_shared_pre `{sailGS Σ, iostateG IOState Σ} (addr : N) (b : Block) : iProp Σ :=
    exec_instructions_prologue (bv.of_N addr) (filter_AST b) ∗
    interp_pmp_addr_access liveAddrs mmioAddrs femto_pmpentries User. (* Not needed for handler, but required for the rest of execution *)

  Definition asn_iprop_pre `{sailGS Σ, iostateG IOState Σ} (asn : Assertion (Σ__csrs ▻▻ ["a" :: ty_xlenbits])) (csrs : CSRVals) (addr : Val ty_xlenbits) : iProp Σ :=
    asn.interpret asn (CSRVals_Valuation csrs).["a" ∷ ty_xlenbits ↦ addr].

  Import LoopVerification.
  Import ArchState (ArchState).

  Definition femto_archstate (priv : Privilege) (ms : ArchState.MState) (ss : ArchState.SState) (pc : Xlenbits) : ArchState :=
    {| ArchState.m := priv;
      ArchState.mstate :=
        {| ArchState.mtvec      := bv.of_N mmio_handler_addr_block0;
          ArchState.pmpentries := femto_pmpentries;
          ArchState.mpp        := ArchState.mpp ms;
          ArchState.mcause     := ArchState.mcause ms;
          ArchState.mscratch   := ArchState.mscratch ms;
          ArchState.mepc       := ArchState.mepc ms;
          ArchState.mpie       := ArchState.mpie ms;
          ArchState.mie        := ArchState.mie ms;
          ArchState.mideleg    := Minterrupts_zero;
          ArchState.medeleg    := Medeleg_zero |};
      ArchState.sstate := ss;
      ArchState.pc := pc |}.

  (* What the handler needs again on the next trap, but M_Trap doesn't give back:
     the data word and the ghost IO state. *)
  Definition femto_handler_data `{sailGS Σ, iostateG IOState Σ} : iProp Σ :=
    ∃ (s : Val ty_iostate) (sv : Val ty_xlenbits),
      interp_mmio_state_pred s ∗ interp_ptstomem (bv.of_N data_addr) sv ∗ ⌜bv.take 1 sv = s⌝.

  Definition ptsto_instrs_handler `{sailGS Σ, iostateG IOState Σ} : iProp Σ :=
    ptsto_instrs (bv.of_N mmio_handler_addr_block0) (filter_AST (femtokernel_handler_gen_block0 mmio_handler_addr_block2)) ∗
    ptsto_instrs (bv.of_N mmio_handler_addr_block1) (filter_AST (femtokernel_handler_gen_block1 data_addr mmio_read_addr)) ∗
    ptsto_instrs (bv.of_N mmio_handler_addr_block2) (filter_AST (femtokernel_handler_gen_block2 data_addr mmio_dev_addr)).

  Opaque ptsto_instrs.
  Opaque femtokernel_init_gen.
  Opaque femtokernel_handler_gen_block0.
  Opaque femtokernel_handler_gen_block1.
  Opaque femtokernel_handler_gen_block2.

  (* The continuation every handler block ends in: "handling the next trap is safe". *)
  Definition femto_handler_cont `{sailGS Σ, iostateG IOState Σ} : iProp Σ :=
    ∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
                                         ptsto_instrs_handler ∗ femto_handler_data -∗
                                                                                      M_Trap (femto_archstate priv ms ss pc) -∗ WP_loop.
  Lemma femtokernel_handler_safe_block2 `{sailGS Σ, iostateG IOState Σ} (csrs : CSRVals) (Hmpp : vmstatus_mpp csrs ≠ Machine) :
    ⊢ femtokernel_safe_shared_pre mmio_handler_addr_block2 (femtokernel_handler_gen_block2 data_addr mmio_dev_addr) ∗
      asn_iprop_pre femtokernel_handler_pre_block2 csrs (bv.of_N mmio_handler_addr_block2) ∗
      ptsto_instrs (bv.of_N mmio_handler_addr_block0) (filter_AST (femtokernel_handler_gen_block0 mmio_handler_addr_block2)) ∗
      ptsto_instrs (bv.of_N mmio_handler_addr_block1) (filter_AST (femtokernel_handler_gen_block1 data_addr mmio_read_addr)) ∗
      ▷ femto_handler_cont
      -∗ WP_loop.
  Proof.
    iIntros "((Hpro & HaccU) & Hpre & Hinstrs0 & Hinstrs1 & Hk)".
    iPoseProof (contract_femtohandler_block2_verified (bv.of_N mmio_handler_addr_block2) csrs) as "H".
    iApply (WP_loop_semTripleBlock with "Hpro Hpre H"). iClear "H".
    iIntros (an) "(Hpost & Hepi)".
    iDestruct "Hepi" as "(Hpc & Hinstrs2 & Hnpc)".
    cbn - [interp_ptstomem interp_pmp_entries].
    iDestruct "Hpost" as "((Hcurpriv & Hmtvec & Hmcause & Hmscratch & Hmip & Hmie & Hmepc & Hsepc & Hscause & Hsscratch
                            & Hstvec & Hmideleg & Hmedeleg & Hgprs & Hpmp & _)
                           & Hmstatus & [%Han _] & [%s [%sv (Hst & Hmem & [%Hsv _])]])".
    iPoseProof (LoopVerification.valid_semTriple_loop $!
        (femto_archstate (vmstatus_mpp csrs)
           {| ArchState.mtvec      := bv.of_N mmio_handler_addr_block0;
              ArchState.pmpentries := femto_pmpentries;
              ArchState.mpp        := User;
              ArchState.mcause     := vmcause csrs;
              ArchState.mscratch   := vmscratch csrs;
              ArchState.mepc       := an;
              ArchState.mpie       := true;
              ArchState.mie        := vmstatus_mpie csrs;
              ArchState.mideleg    := Minterrupts_zero;
              ArchState.medeleg    := Medeleg_zero |}
           {| ArchState.stvec    := vstvec csrs;
              ArchState.spp      := vmstatus_spp csrs;
              ArchState.scause   := vscause csrs;
              ArchState.sscratch := vsscratch csrs;
              ArchState.sepc     := vsepc csrs;
              ArchState.spie     := vmstatus_spie csrs;
              ArchState.sie      := vmstatus_sie csrs |}
           an)
        with "[-]") as "Hloop".
    - unfold loop_pre.
      iSplitR "Hk Hinstrs0 Hinstrs1 Hinstrs2 Hst Hmem".
      + unfold Step_pre; cbn.
        assert (HU : User ≠ Machine) by auto. rewrite gprs_equiv.
        iPoseProof (interp_pmp_addr_access_not_machine _ _ _ HU Hmpp with "HaccU") as "Hacc".
        now iFrame "Hacc Hgprs Hpmp Hmie Hmip Hcurpriv Hpc Hnpc Hmtvec Hstvec Hmstatus Hmepc Hsepc Hmideleg Hmedeleg Hmscratch Hmcause Hsscratch Hscause".
      + iSplitR; last iSplitL "Hk Hinstrs0 Hinstrs1 Hinstrs2 Hst Hmem"; repeat iSplitL; iModIntro; cbn.
        * now iIntros "(? & ? & ? & [%eq _] & ?)".
        * iIntros "Htrap".
          iApply ("Hk" $! (vmstatus_mpp csrs) with "[//] [Hinstrs0 Hinstrs1 Hinstrs2 Hst Hmem] Htrap").
          unfold ptsto_instrs_handler, femto_handler_data.
          iFrame "Hinstrs0 Hinstrs1 Hinstrs2". iExists s, sv. by iFrame.
        * now iIntros "(? & ? & ? & [%eq _] & ?)".
        * now iIntros "(? & ? & ? & [%eq _] & ?)".
    - iApply (semWP_mono with "Hloop"); auto.
  Qed.

  Lemma femtokernel_handler_safe_block1 `{sailGS Σ, iostateG IOState Σ} (csrs : CSRVals) (Hmpp : vmstatus_mpp csrs ≠ Machine) :
    ⊢ femtokernel_safe_shared_pre mmio_handler_addr_block1 (femtokernel_handler_gen_block1 data_addr mmio_read_addr) ∗
      asn_iprop_pre femtokernel_handler_pre_block1 csrs (bv.of_N mmio_handler_addr_block1) ∗
      ptsto_instrs (bv.of_N mmio_handler_addr_block0) (filter_AST (femtokernel_handler_gen_block0 mmio_handler_addr_block2)) ∗
      ptsto_instrs (bv.of_N mmio_handler_addr_block2) (filter_AST (femtokernel_handler_gen_block2 data_addr mmio_dev_addr)) ∗
      ▷ femto_handler_cont
      -∗ WP_loop.
  Proof.
    iIntros "((Hpro & HaccU) & Hpre & Hinstrs0 & Hinstrs2 & Hk)".
    iPoseProof (contract_femtohandler_block1_verified (bv.of_N mmio_handler_addr_block1) csrs) as "H".
    iApply (WP_loop_semTripleBlock with "Hpro Hpre H"). iClear "H".
    iIntros (an) "(Hpost & Hepi)".
    iDestruct "Hepi" as "(Hpc & Hinstrs1 & Hnpc)".
    cbn - [interp_ptstomem interp_pmp_entries].
    iDestruct "Hpost" as "((Hcurpriv & Hmtvec & Hmcause & Hmscratch & Hmip & Hmie & Hmepc & Hsepc & Hscause & Hsscratch
                            & Hstvec & Hmideleg & Hmedeleg & Hgprs & Hpmp & _)
                           & Hmstatus & [%Han _] & [%s [%s' [%sv (Hst & _ & Hmem & [%Hsv _])]]])".
    iPoseProof (LoopVerification.valid_semTriple_loop $!
        (femto_archstate (vmstatus_mpp csrs)
           {| ArchState.mtvec      := bv.of_N mmio_handler_addr_block0;
              ArchState.pmpentries := femto_pmpentries;
              ArchState.mpp        := User;
              ArchState.mcause     := vmcause csrs;
              ArchState.mscratch   := vmscratch csrs;
              ArchState.mepc       := vmepc csrs;
              ArchState.mpie       := true;
              ArchState.mie        := vmstatus_mpie csrs;
              ArchState.mideleg    := Minterrupts_zero;
              ArchState.medeleg    := Medeleg_zero |}
           {| ArchState.stvec    := vstvec csrs;
              ArchState.spp      := vmstatus_spp csrs;
              ArchState.scause   := vscause csrs;
              ArchState.sscratch := vsscratch csrs;
              ArchState.sepc     := vsepc csrs;
              ArchState.spie     := vmstatus_spie csrs;
              ArchState.sie      := vmstatus_sie csrs |}
           an)
        with "[-]") as "Hloop".
    - unfold loop_pre.
      iSplitR "Hk Hinstrs0 Hinstrs1 Hinstrs2 Hst Hmem".
      + unfold Step_pre; cbn.
        assert (HU : User ≠ Machine) by auto. rewrite gprs_equiv.
        iPoseProof (interp_pmp_addr_access_not_machine _ _ _ HU Hmpp with "HaccU") as "Hacc".
        now iFrame "Hacc Hgprs Hpmp Hmie Hmip Hcurpriv Hpc Hnpc Hmtvec Hstvec Hmstatus Hmepc Hsepc Hmideleg Hmedeleg Hmscratch Hmcause Hsscratch Hscause".
      + iSplitR; last iSplitL "Hk Hinstrs0 Hinstrs1 Hinstrs2 Hst Hmem"; repeat iSplitL; iModIntro; cbn.
        * now iIntros "(? & ? & ? & [%eq _] & ?)".
        * iIntros "Htrap".
          iApply ("Hk" $! (vmstatus_mpp csrs) with "[//] [Hinstrs0 Hinstrs1 Hinstrs2 Hst Hmem] Htrap").
          unfold ptsto_instrs_handler, femto_handler_data.
          iFrame "Hinstrs0 Hinstrs1 Hinstrs2". iExists s', sv. by iFrame.
        * now iIntros "(? & ? & ? & [%eq _] & ?)".
        * now iIntros "(? & ? & ? & [%eq _] & ?)".
    - iApply (semWP_mono with "Hloop"); auto.
  Qed.

  Lemma femtokernel_handler_safe_block0 `{sailGS Σ, iostateG IOState Σ} (csrs : CSRVals) (Hmpp : vmstatus_mpp csrs ≠ Machine) :
    ⊢ femtokernel_safe_shared_pre mmio_handler_addr_block0 (femtokernel_handler_gen_block0 mmio_handler_addr_block2) ∗
      asn_iprop_pre femtokernel_handler_pre csrs (bv.of_N mmio_handler_addr_block0) ∗
      ptsto_instrs (bv.of_N mmio_handler_addr_block1) (filter_AST (femtokernel_handler_gen_block1 data_addr mmio_read_addr)) ∗
      ptsto_instrs (bv.of_N mmio_handler_addr_block2) (filter_AST (femtokernel_handler_gen_block2 data_addr mmio_dev_addr)) ∗
      ▷ femto_handler_cont
      -∗ WP_loop.
  Proof.
    iIntros "((Hpro & HaccU) & Hpre & Hinstrs1 & Hinstrs2 & Hk)".
    iPoseProof (contract_femtohandler_block0_verified (bv.of_N mmio_handler_addr_block0) csrs) as "H".
    iApply (WP_loop_semTripleBlock with "Hpro Hpre H"). iClear "H".
    iIntros (an) "(Hpost & Hepi)".
    iDestruct "Hepi" as "(Hpc & Hinstrs0 & Hnpc)".
    cbn - [interp_ptstomem interp_pmp_entries].
    iDestruct "Hpost" as "((Hcurpriv & Hmtvec & Hmcause & Hmscratch & Hmip & Hmie & Hmepc & Hsepc & Hscause & Hsscratch
                            & Hstvec & Hmideleg & Hmedeleg & Hgprs & Hpmp & Hinv)
                           & Hmstatus & [%s [%sv (Hbranch & Hmem & [%Hsv _] & Hst)]])".
    iDestruct "Hbranch" as "[([%Hc _] & [%Han _]) | ([%Hc _] & [%Han _])]"; subst an.
    - (* msb of mcause = 0: access fault, go to block2 *)
      iApply (femtokernel_handler_safe_block2 csrs Hmpp).
      unfold femtokernel_safe_shared_pre, exec_instructions_prologue, asn_iprop_pre.
      cbn - [interp_ptstomem interp_pmp_entries].
      iFrame "Hk Hinstrs0 Hinstrs1 Hinstrs2 HaccU Hpc Hnpc
              Hcurpriv Hmtvec Hmcause Hmscratch Hmip Hmie Hmepc Hsepc Hscause Hsscratch Hstvec
              Hmideleg Hmedeleg Hgprs Hpmp Hinv Hmstatus".
      iSplitL "". auto. 
      iExists s, sv. iFrame "Hst Hmem".
      repeat iSplit; iPureIntro; first [done | exact Hsv | now vm_compute].
    - (* msb of mcause = 1: interrupt, go to block1 *)
      iApply (femtokernel_handler_safe_block1 csrs Hmpp).
      unfold femtokernel_safe_shared_pre, exec_instructions_prologue, asn_iprop_pre.
      cbn - [interp_ptstomem interp_pmp_entries].
      iFrame "Hk Hinstrs0 Hinstrs1 Hinstrs2 HaccU Hpc Hnpc
              Hcurpriv Hmtvec Hmcause Hmscratch Hmip Hmie Hmepc Hsepc Hscause Hsscratch Hstvec
              Hmideleg Hmedeleg Hgprs Hpmp Hinv Hmstatus".
      iSplitL "". auto.
      iExists s, sv. iFrame "Hst Hmem".
      repeat iSplit; iPureIntro; first [done | exact Hsv | exact I | now vm_compute].
  Qed.

  Lemma femtokernel_handler_safe `{sailGS Σ, iostateG IOState Σ} :
    ⊢ interp_mmio_trace_state_inv -∗
      ∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
      ptsto_instrs_handler ∗ femto_handler_data -∗
      M_Trap (femto_archstate priv ms ss pc) -∗ WP_loop.
  Proof.
    iIntros "#Hinv". iLöb as "IH".
    iIntros (priv ms ss pc Hpriv) "(Hhandler & Hdata) Htrap".
    assert (HU : User ≠ Machine) by auto.
    iPoseProof (M_Trap_SU_irrelevant (femto_archstate priv ms ss pc) (femto_archstate User ms ss pc)
                  Hpriv HU eq_refl with "Htrap") as "Htrap".
    iEval (unfold M_Trap, transition; cbn - [interp_pmp_entries]) in "Htrap".
    iDestruct "Htrap" as "(HaccU & Hgprs & Hpmp & [%vmie Hmie] & [%vmip Hmip] & Hcurpriv & Hpc & Hnpc & Hmtvec
                           & [%vstvec Hstvec]
                           & [%vspp [%vmpie [%vspie [%vsie [%vmpp (Hmstatus & [%Hmpp _])]]]]]
                           & [%vmepc Hmepc] & [%vsepc Hsepc] & Hmideleg & Hmedeleg
                           & [%vmscratch Hmscratch] & [%vmcause Hmcause] & [%vsscratch Hsscratch] & [%vscause Hscause])".
    iDestruct "Hdata" as "(%s & %sv & Hst & Hmem & %Hsv)".
    iDestruct "Hhandler" as "(Hinstrs0 & Hinstrs1 & Hinstrs2)".
    iApply (femtokernel_handler_safe_block0
              {| vmtvec        := bv.of_N mmio_handler_addr_block0;
                 vmcause       := vmcause;
                 vmscratch     := vmscratch;
                 vmepc         := vmepc;
                 vmie          := vmie;
                 vmip          := vmip;
                 vmstatus_mpie := vmpie;
                 vmstatus_mpp  := vmpp;
                 vmstatus_spp  := vspp;
                 vmstatus_spie := vspie;
                 vmstatus_sie  := vsie;
                 vmideleg      := Minterrupts_zero;
                 vmedeleg      := Medeleg_zero;
                 vscause       := vscause;
                 vsscratch     := vsscratch;
                 vsepc         := vsepc;
                 vstvec        := vstvec |} Hmpp).
    iFrame "IH".
    unfold femtokernel_safe_shared_pre, exec_instructions_prologue, asn_iprop_pre.
    cbn - [interp_ptstomem interp_pmp_entries].
    rewrite <- gprs_equiv.
    iFrame "Hinstrs0 Hinstrs1 Hinstrs2 HaccU Hpc Hnpc Hcurpriv Hmtvec Hmcause Hmscratch Hmip Hmie
            Hmepc Hsepc Hscause Hsscratch Hstvec Hmideleg Hmedeleg Hgprs Hpmp Hinv Hmstatus Hmem Hst".
    repeat iSplit; iPureIntro; try done; by vm_compute.
  Qed.

  Lemma femtokernel_manualStep2 `{sailGS Σ, iostateG IOState Σ} :
    ⊢ (∃ mpp mpie mie, mstatus ↦ᵣ {| MPP := mpp; SPP := User; MPIE := mpie; SPIE := false; MIE := mie; SIE := false |}) ∗
      mtvec ↦ᵣ bv.of_N mmio_handler_addr_block0 ∗
      (∃ v, mcause ↦ᵣ v) ∗ (∃ v, mip ↦ᵣ v) ∗ (∃ v, mie ↦ᵣ v) ∗
      (∃ v, mscratch ↦ᵣ v) ∗ (∃ v, mepc ↦ᵣ v) ∗
      (∃ v, scause ↦ᵣ v) ∗ (∃ v, sscratch ↦ᵣ v) ∗ (∃ v, sepc ↦ᵣ v) ∗ (∃ v, stvec ↦ᵣ v) ∗
      mideleg ↦ᵣ Minterrupts_zero ∗ medeleg ↦ᵣ Medeleg_zero ∗
      cur_privilege ↦ᵣ User ∗
      interp_gprs ∅ ∗
      interp_pmp_entries femto_pmpentries ∗
      interp_mmio_trace_state_inv ∗
      pc ↦ᵣ bv.of_N adv_addr ∗ (∃ v, nextpc ↦ᵣ v) ∗
      ptsto_instrs_handler ∗
      femto_handler_data ∗
      ptstoSthL advAddrs
      ={⊤}=∗
      ∃ mpp mcause mscratch mepc scause sscratch sepc stvec mpie mie,
        LoopVerification.loop_pre
          (femto_archstate User
             {| ArchState.mtvec      := bv.of_N mmio_handler_addr_block0;
                ArchState.pmpentries := femto_pmpentries;
                ArchState.mpp        := mpp;
                ArchState.mcause     := mcause;
                ArchState.mscratch   := mscratch;
                ArchState.mepc       := mepc;
                ArchState.mpie       := mpie;
                ArchState.mie        := mie;
                ArchState.mideleg    := Minterrupts_zero;
                ArchState.medeleg    := Medeleg_zero |}
             {| ArchState.stvec    := stvec;
                ArchState.spp      := User;
                ArchState.scause   := scause;
                ArchState.sscratch := sscratch;
                ArchState.sepc     := sepc;
                ArchState.spie     := false;
                ArchState.sie      := false |}
             (bv.of_N adv_addr)).
  Proof.
    iIntros "((%mpp & %mpie & %mie & Hmst) & Hmtvec & [%vmcause Hmcause] & Hmip & Hmie & [%vmscratch Hmscratch] & [%vmepc Hmepc] & [%vscause Hscause] & [%vsscratch Hsscratch] & [%vsepc Hsepc] & [%vstvec Hstvec] & Hmideleg & Hmedeleg & Hcurpriv & Hgprs & Hpmpcfg & #Hinv & Hpc & Hnpc & Hhandler & Hdata & Hmemadv)".
    iExists mpp, vmcause, vmscratch, vmepc, vscause, vsscratch, vsepc, vstvec, mpie, mie.
    iModIntro. unfold LoopVerification.loop_pre.
    iSplitR "Hhandler Hdata".
    - unfold LoopVerification.Step_pre. cbn - [ptstoSthL interp_ptstomem].
      (* rewrite gprs_equiv if Step_pre still uses the other gprs form, as in the old proof *)
      iFrame "Hgprs Hpmpcfg Hmie Hmip Hcurpriv Hpc Hnpc Hmtvec Hstvec Hmst Hmepc Hsepc Hmideleg Hmedeleg Hmscratch Hmcause Hsscratch Hscause".
      iSplitR; first auto.
      by iApply memAdv_pmpPolicy.
    - iSplitR.
      { iIntros "!> H'". iDestruct (M_CSRMod_machine with "H'") as %Heq. cbn in Heq; discriminate Heq. }
      iSplitL "Hhandler Hdata".
      { iIntros "!> H'".
        iApply (femtokernel_handler_safe with "Hinv [] [$Hhandler $Hdata] H'").
        iPureIntro; discriminate. }
      iSplitR.
      { iIntros "!> H'". iDestruct (MRET_machine with "H'") as %Heq. cbn in Heq; discriminate Heq. }
      iIntros "!> H'". iDestruct (SRET_machine with "H'") as %Heq. cbn in Heq; discriminate Heq.
  Qed.

  Definition femto_init_pre `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits) : iProp Σ :=
    asn.interpret femtokernel_init_pre [env].["a" ∷ ty_xlenbits ↦ a].

  Definition femto_init_post `{sailGS Σ, iostateG IOState Σ} (a an : Val ty_xlenbits) : iProp Σ :=
    asn.interpret femtokernel_init_post [env].["a" ∷ ty_xlenbits ↦ a].["an" ∷ ty_xlenbits ↦ an].

  Definition contract_femtoinit `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits) : iProp Σ :=
    semTripleBlock femto_init_pre a (filter_AST femtokernel_init_gen) femto_init_post.

  (* Same trick as for the handler blocks: let the kernel unfold the VC name first. *)
  Local Strategy expand [vc__femtoinit].
  Opaque femtokernel_init_pre.

  Lemma contract_femtoinit_verified : ∀ `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits),
      ⊢ contract_femtoinit a.
  Proof.
    unfold contract_femtoinit, femto_init_pre, femto_init_post. iIntros (Σ sg ioG a).
    iApply (sound_sannotated_block_verification_condition lemSemBlockVerif).
    exact sat__femtoinit.
  Qed.

  Transparent femtokernel_init_pre.

  Lemma femtokernel_init_safe `{sailGS Σ, iostateG IOState Σ} :
    ⊢ exec_instructions_prologue (bv.of_N init_addr) (filter_AST femtokernel_init_gen) ∗
      femto_init_pre (bv.of_N init_addr) ∗
      ptsto_instrs_handler ∗
      femto_handler_data ∗
      interp_mmio_trace_state_inv ∗
      ptstoSthL advAddrs -∗
      WP_loop.
  Proof.
    iIntros "(Hpro & Hpre & Hhandler & Hdata & #Hinv & Hadv)".
    iPoseProof (contract_femtoinit_verified (bv.of_N init_addr)) as "H".
    iApply (WP_loop_semTripleBlock with "Hpro Hpre H"). iClear "H".
    iIntros (an) "(Hpost & Hepi)".
    iDestruct "Hepi" as "(Hpc & Hinstrs & Hnpc)".
    unfold femto_init_post; cbn - [ptstoSthL interp_ptstomem].
    iDestruct "Hpost" as "([-> _] & Hmtvec & Hmcause & Hmideleg & Hmedeleg & Hmip & Hmie & Hmepc & Hmscratch
                           & Hstvec & Hsepc & Hscause & Hsscratch & Hmstatus & Hcurpriv & Hgprs & Hpmpentries)".
    rewrite ?bv.add_zero_l.
    iAssert (∃ mpp mpie mie, mstatus ↦ᵣ {| MPP := mpp; SPP := User; MPIE := mpie; SPIE := false; MIE := mie; SIE := false |})%I
      with "[Hmstatus]" as "Hmstatus".
    { iExists User, true, true. iExact "Hmstatus". }
    iApply (fupd_semWP ⊤). 
    iMod (femtokernel_manualStep2 with
           "[$Hmstatus $Hmtvec $Hmcause $Hmip $Hmie $Hmscratch $Hmepc $Hscause $Hsscratch $Hsepc $Hstvec
             $Hmideleg $Hmedeleg $Hcurpriv Hgprs $Hpmpentries $Hinv $Hpc $Hnpc $Hhandler $Hdata $Hadv]")
      as "(%mpp & %mcause & %mscratch & %mepc & %scause & %sscratch & %sepc & %stvec & %mpie & %mie & Hlooppre)".
    { by rewrite gprs_equiv. }
    iModIntro.
    iPoseProof (LoopVerification.valid_semTriple_loop with "Hlooppre") as "Hk".
    iApply (semWP_mono with "Hk"); auto.
  Qed.

  Definition mem_has_word (μ : Memory) (a : Val ty_word) (w : Val ty_word) : Prop :=
    exists v0 v1 v2 v3, map (memory_ram μ) (bv.seq a 4) = [v0; v1; v2; v3]%list /\ bv.app v0 (bv.app v1 (bv.app v2 (bv.app v3 bv.nil))) = w.

  (* byte order correct? *)
  Definition mem_has_instr (μ : Memory) (a : Val ty_word) (instr : AST) : Prop :=
    exists w, mem_has_word μ a w /\ pure_decode w = instr.

  Fixpoint mem_has_instrs (μ : Memory) (a : Val ty_word) (instrs : list AST) : Prop :=
    match instrs with
    | cons inst instrs => mem_has_instr μ a inst /\ mem_has_instrs μ (bv.add (bv.of_N 4) a) instrs
    | nil => True
    end.

  Import RiscvPmpSemantics.
  Import RiscvPmpIrisAdeqParameters.
  Import SmallStepNotations.

  Import iris.bi.big_op.
  Import iris.algebra.big_op.

  (* Note that the split differs depending on whether or not we have an MMIO region! *)
  Lemma liveAddrs_split : liveAddrs = bv.seq (bv.of_N init_addr) (Z.of_N init_size) ++
                                        bv.seq (bv.of_N mmio_handler_addr_block0) (Z.of_N mmio_handler_size_block0) ++
                                        bv.seq (bv.of_N mmio_handler_addr_block1) (Z.of_N mmio_handler_size_block1) ++
                                        bv.seq (bv.of_N mmio_handler_addr_block2) (Z.of_N mmio_handler_size_block2) ++
                                       (bv.seq (bv.of_N data_addr) (Z.of_N data_size) (* There is no data; conjunct is just here for conformity *)) ++ advAddrs.
  Proof.
    (* TODO: scalable proof *)
    by compute.
  Qed.

  Lemma intro_ptstomem_word `{sailGS Σ, iostateG IOState Σ} v0 v1 v2 v3 (a : Val ty_word) :
    interp_ptsto (bv.of_Z (0 + bv.unsigned a)) v0 ∗
    interp_ptsto (bv.of_Z (1 + bv.unsigned a)) v1 ∗
    interp_ptsto (bv.of_Z (2 + bv.unsigned a)) v2 ∗
    interp_ptsto (bv.of_Z (3 + bv.unsigned a)) v3 ⊢
      interp_ptstomem (width := 4) a (bv.app v0 (bv.app v1 (bv.app v2 (bv.app v3 bv.nil)))).
  Proof.
    iIntros "(Hmema & Hmema1 & Hmema2 & Hmema3)".
    unfold interp_ptstomem.
    rewrite ?bv.appView_app.
    replace (@bv.of_Z xlenbits (0 + bv.unsigned a)%Z) with a by now rewrite bv.of_Z_unsigned.
    replace (@bv.of_Z xlenbits (1 + bv.unsigned a)%Z) with (bv.add bv.one a) by now rewrite <-bv.of_Z_add, bv.of_Z_unsigned.
    replace (@bv.of_Z xlenbits (2 + bv.unsigned a)%Z) with (bv.add bv.one (bv.add bv.one a)).
    replace (@bv.of_Z xlenbits (3 + bv.unsigned a)%Z) with (bv.add bv.one (bv.add bv.one (bv.add bv.one a))).
    now iFrame.
    rewrite ?bv.add_assoc.
    change (bv.add _ bv.one) with (@bv.of_Z xlenbits 3).
    now rewrite <-bv.of_Z_add, bv.of_Z_unsigned.
    rewrite ?bv.add_assoc.
    now rewrite <-bv.of_Z_add, bv.of_Z_unsigned.
  Qed.

  Lemma intro_ptstomem_word2 `{sailGS Σ, iostateG IOState Σ} {μ : Memory} {a : Val ty_word} {v : Val ty_word} :
    mem_has_word μ a v ->
    ([∗ list] a' ∈ bv.seq a 4, interp_ptsto a' ((memory_ram μ) a')) ⊢ interp_ptstomem a v.
  Proof.
    iIntros (Hmhw) "Hmem".
    destruct Hmhw as (v0 & v1 & v2 & v3 & Heqμ & Heqv).
    unfold bv.seq, seqZ. change (seq 0 ?x) with [0;1;2;3].
    cbn -[bv.add interp_ptstomem word].
    iDestruct "Hmem" as "(Hmema & Hmema1 & Hmema2 & Hmema3 & _)".
    inversion Heqμ; subst.
    now iApply (intro_ptstomem_word with "[$Hmema $Hmema1 $Hmema2 $Hmema3]").
  Qed.

  Lemma intro_ptsto_instr `{sailGS Σ, iostateG IOState Σ} {μ : Memory} {a : Val ty_word} {instr : AST} :
    (4 + bv.unsigned a < 2 ^ Z.of_nat xlenbits)%Z ->
    mem_has_instr μ a instr ->
    ([∗ list] a' ∈ bv.seq a 4, interp_ptsto a' ((memory_ram μ) a'))
      ⊢ interp_ptsto_instr a instr.
  Proof.
    iIntros (Hrep (v & Hmhw & Heq)) "Hmem".
    iExists v.
    iSplitL; last done.
    now iApply (intro_ptstomem_word2 Hmhw).
  Qed.

  Lemma intro_ptsto_instrs `{sailGS Σ, iostateG IOState Σ} {μ : Memory} {a : Val ty_word} {instrs : list AST} :
    (4 * Z.of_nat (length instrs) + bv.unsigned a < 2 ^ Z.of_nat xlenbits)%Z ->
    mem_has_instrs μ a instrs ->
    ([∗ list] a' ∈ bv.seq a (4 * Z.of_nat (length instrs)), interp_ptsto a' ((memory_ram μ) a'))
      ⊢ ptsto_instrs a instrs.
  Proof.
    assert (word > 0) by now compute; Lia.lia.
    iIntros (Hrep Hmeminstrs) "Hmem".
    iInduction instrs as [|instr instrs] "IH" forall (a Hrep Hmeminstrs).
    - done.
    - replace (4 * Z.of_nat (length (instr :: instrs)))%Z
        with (4 + 4 * Z.of_nat (length instrs))%Z in * by (cbn; lia).
      rewrite bv.seq_add ?big_opL_app; [|lia..].
      destruct Hmeminstrs as [Hinstr Hmeminstrs].
      iDestruct "Hmem" as "[Hmema Hmema4]".
      cbv [ptsto_instrs].
      iSplitL "Hmema".
      + iApply (intro_ptsto_instr with "Hmema"); auto; Lia.lia.
      + rewrite (@bv.add_comm _ a bv_instrsize).
        iApply ("IH" with "[%] [% //] [-]"); last done.
        pose proof (bv.unsigned_bounds a). change word with xlenbits in *.
        rewrite -bv.unsigned_add_small; change (bv.unsigned (bv.of_N 4)) with 4%Z; lia.
  Qed.

  Lemma intro_ptstoSthL `{sailGS Σ, iostateG IOState Σ} (μ : Memory) (addrs : list Xlenbits)  :
    ([∗ list] a' ∈ addrs, interp_ptsto a' ((memory_ram μ) a')) ⊢ ptstoSthL addrs.
  Proof.
    induction addrs as [|a l]; cbn.
    - now iIntros "_".
    - iIntros "[Hmema Hmem]".
      iSplitL "Hmema".
      + now iExists ((memory_ram μ) a).
      + now iApply IHl.
  Qed.

  Lemma sub_heap_mapsto_interp_ptsto {Σ : gFunctors} {sG : sailGS Σ} {rG : iostateG IOState Σ} {s e} (μ : Memory):
    (Z.of_N minAddr <= bv.unsigned s)%Z → (bv.unsigned s + e <= Z.of_N (minAddr + lenAddr))%Z →
    ([∗ list] y ∈ bv.seq s e, gen_heap.pointsto y (dfrac.DfracOwn 1) (memory_ram μ y)) ⊢ [∗ list] a' ∈ bv.seq s e, interp_ptsto a' (memory_ram μ a').
  Proof.
    iIntros (Hlow Hhi) "Hlist".
    iApply (big_sepL_mono with "Hlist"). intros ? ? Hsom. cbn.
    iIntros "$". iPureIntro.
    rewrite /= withinMMIO_one /not; apply mmio_ram_False.
    eapply bv.seq_subseteq, list_elem_of_lookup_2, Hsom;
      change (bv.unsigned (bv.of_N minAddr)) with (Z.of_N minAddr); lia.
  Qed.

  Lemma femtokernel_splitMemory `{sailGS Σ, iostate_preG IOState Σ} {μ : Memory} {s} {v} :
    mem_has_instrs μ (bv.of_N init_addr) (filter_AnnotInstr_AST femtokernel_init_gen) ->
    mem_has_instrs μ (bv.of_N mmio_handler_addr_block0) (filter_AnnotInstr_AST (femtokernel_handler_gen_block0 mmio_handler_addr_block2)) ->
    mem_has_instrs μ (bv.of_N mmio_handler_addr_block1) (filter_AnnotInstr_AST (femtokernel_handler_gen_block1 data_addr mmio_read_addr)) ->
    mem_has_instrs μ (bv.of_N mmio_handler_addr_block2) (filter_AnnotInstr_AST (femtokernel_handler_gen_block2 data_addr mmio_dev_addr)) ->
    mmio_trace_state_pred (memory_trace μ) s -> (* Demand a sensible history of trace events. Note that the extra handler instruction in the case of mmio is already captured by the previous conjunct *)
    mem_has_word μ (bv.of_N data_addr) v ->
    @mem_res _ sailGS_memGS μ ⊢ |={⊤}=>
          ∃ (rG : iostateG IOState Σ),
          ptsto_instrs (bv.of_N init_addr) (filter_AnnotInstr_AST femtokernel_init_gen) ∗
          ptsto_instrs (bv.of_N mmio_handler_addr_block0) (filter_AnnotInstr_AST (femtokernel_handler_gen_block0 mmio_handler_addr_block2)) ∗
          ptsto_instrs (bv.of_N mmio_handler_addr_block1) (filter_AnnotInstr_AST (femtokernel_handler_gen_block1 data_addr mmio_read_addr)) ∗
          ptsto_instrs (bv.of_N mmio_handler_addr_block2) (filter_AnnotInstr_AST (femtokernel_handler_gen_block2 data_addr mmio_dev_addr)) ∗
          interp_mmio_trace_state_inv ∗
          (@interp_ptstomem _ _ xlenbytes (bv.of_N data_addr) v) ∗
          (interp_mmio_state_pred (s2bv s)) ∗
          ptstoSthL advAddrs.
  Proof.
    iIntros (Hinit Hhandler0 Hhandler1 Hhandler2 Hpred Hdata) "Hmres".
    unfold iost_res, mem_res, initMemMap.
    rewrite (liveAddrs_split).
    rewrite ?big_sepL_app.
    iDestruct "Hmres" as "[(Hinit & Hhandler0 & Hhandler1 & Hhandler2 & Hmem & Hadv) Htrfrag]".
    iMod (state_alloc_names s) as "(%iostate_name & Hstauth & Hstfrag)".
    pose (rG := IOStateG _ _ _ iostate_name : iostateG IOState Σ ).
    iExists rG.
    iSplitL "Hinit".
    { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
      iApply (sub_heap_mapsto_interp_ptsto with "Hinit"); now compute. }
    iSplitL "Hhandler0".
    { iApply (intro_ptsto_instrs (μ := μ)); auto. cbn. reflexivity.
      iApply (sub_heap_mapsto_interp_ptsto with "Hhandler0"); now compute. }
    iSplitL "Hhandler1".
    { iApply (intro_ptsto_instrs (μ := μ)); auto. cbn. reflexivity.
      iApply (sub_heap_mapsto_interp_ptsto with "Hhandler1"); now compute. }
    iSplitL "Hhandler2".
    { iApply (intro_ptsto_instrs (μ := μ)); auto. cbn. reflexivity.
      iApply (sub_heap_mapsto_interp_ptsto with "Hhandler2"); now compute. }
    iSplitL "Htrfrag Hstauth".
    { unfold interp_mmio_trace_state_inv.
      iMod (inv.inv_alloc femto_inv_mmio_ns ⊤ (∃ s t, tr_frag1 t ∗ st_auth1 s ∗ ⌜mmio_trace_state_pred t s⌝)%I with "[Htrfrag Hstauth]") as "Hinv".
      { iNext. iExists _, _. iFrame. auto. }
      iModIntro.
      unfold interp_mmio_state_pred.
      now iFrame. }
    iSplitL "Hmem".
    { iApply intro_ptstomem_word2; eauto.
      iApply sub_heap_mapsto_interp_ptsto; auto; by compute. }
    iSplitL "Hstfrag".
    { destruct s; by iFrame. }
    iApply (intro_ptstoSthL μ).
    iApply (sub_heap_mapsto_interp_ptsto with "Hadv"); now compute.
  Qed.

  Lemma interp_ptsto_valid `{sailGS Σ, iostateG IOState Σ} {μ a v} :
    ⊢ mem_state_interp _ μ -∗ interp_ptsto a v -∗ ⌜(memory_ram μ) a = v⌝.
  Proof.
    unfold interp_ptsto, mem_state_interp.
    iIntros "(%memmap & Hinv & %link & Htr) [Hptsto %Hmmio]".
    iDestruct (gen_heap.gen_heap_valid with "Hinv Hptsto") as "%x".
    iPureIntro.
    now apply (map_Forall_lookup_1 _ _ _ _ link).
  Qed.

  (* TODO: move to bitvector *)
  Lemma bv0_is_nil (x : bv 0) : x = bv.nil.
  Proof. now destruct (bv.view x). Qed.

  (* TODO: use this lemma in earlier proofs, like `read_ram_works`? *)
  Lemma interp_ptstomem_valid `{sailGS Σ, iostateG IOState Σ} {μ a v} :
    ⊢ mem_state_interp _ μ -∗ interp_ptstomem a v -∗ ⌜mem_has_word μ a v⌝.
  Proof.
    iIntros "Hinv Hptstomem".

    (* Prep hypotheses first *)
    do 4 destruct (bv.appView byte _ v) as [? v].
    (* rewrite (bv0_is_nil v). *)

    repeat iExists _.
    rewrite bv.app_nil_r. (* Get rid of annoying `nil` bv *)
    iSplit; last eauto.

    rewrite !ptstomem_bv_app.
    iDestruct "Hptstomem" as "(Ha0 & Ha1 & Ha2 & Ha3 & Htail)".
    iDestruct (interp_ptsto_valid with "Hinv Ha0") as "%Hm0".
    iDestruct (interp_ptsto_valid with "Hinv Ha1") as "%Hm1".
    iDestruct (interp_ptsto_valid with "Hinv Ha2") as "%Hm2".
    iDestruct (interp_ptsto_valid with "Hinv Ha3") as "%Hm3".

    iPureIntro.
    rewrite (bv0_is_nil v) bv.app_nil_r.
    change 4%Z with (Z.succ (Z.succ (Z.succ (Z.succ 0)))).
    rewrite !bv.seq_succ ?map_cons; [|lia..].
    repeat f_equal; auto.
  Qed.

  Transparent ptsto_instrs.
  Opaque gprs_equiv.

  Lemma femtokernel_endToEnd  {γ γ' : RegStore} {μ μ' : Memory} {σ : IOState}
    {δ δ' : CStore [ctx]} {s' : Stm [ctx] ty.unit} :
    mem_has_instrs μ (bv.of_N init_addr) (filter_AnnotInstr_AST femtokernel_init_gen) ->
    mem_has_instrs μ (bv.of_N mmio_handler_addr_block0) (filter_AnnotInstr_AST (femtokernel_handler_gen_block0 mmio_handler_addr_block2)) ->
    mem_has_instrs μ (bv.of_N mmio_handler_addr_block1) (filter_AnnotInstr_AST (femtokernel_handler_gen_block1 data_addr mmio_read_addr)) ->
    mem_has_instrs μ (bv.of_N mmio_handler_addr_block2) (filter_AnnotInstr_AST (femtokernel_handler_gen_block2 data_addr mmio_dev_addr)) ->
    mmio_trace_state_pred (memory_trace μ) σ -> (* Demand sensible history of trace events. Note that the extra handler instruction in the case of mmio is already captured by the previous conjunct *)
    read_register γ cur_privilege = Machine ->
    read_register γ mstatus = {| MPP := User; SPP := User; MPIE := false; SPIE := false; MIE := false; SIE := false |} ->
    read_register γ mideleg = Minterrupts_zero ->
    read_register γ medeleg = Medeleg_zero ->
    read_register γ pmp0cfg = default_pmpcfg_ent ->
    read_register γ pmpaddr0 = bv.zero ->
    read_register γ pmp1cfg = default_pmpcfg_ent ->
    read_register γ pmpaddr1 = bv.zero ->
    read_register γ pc = (bv.of_N init_addr) ->
    ⟨ γ, μ, δ, fun_loop ⟩ --->* ⟨ γ', μ', δ', s' ⟩ ->
    mem_has_word μ (bv.of_N data_addr) (match σ with
                                        | SGo   => bv.of_N  0
                                        | SStop   => bv.of_N 1
                                        end)
                 ->
    (∃ σ', mmio_trace_state_pred (memory_trace μ') σ'). (* The initial demands hold over the final state *)
  Proof.
    intros μinit μhandler0 μhandler1 μhandler2 μft γcurpriv γmstatus γmideleg γmedeleg γpmp0cfg γpmpaddr0 γpmp1cfg γpmpaddr1 γpc steps Hmem.
    refine (adequacy_gen (Q := fun _ _ _ _ => True%I) _ steps _). (* inv trace satisfies protocol state *)
    iIntros (Σ' sG mpG).
    cbn.
    iIntros "(Hmem & Hpc & Hnpc & Hmstatus & Hmie & Hmip & Hmideleg & Hmedeleg & Hmtvec & Hmscratch & Hmepc & Hmcause & Hstvec & Hsscratch & Hsepc & Hscause & Hcurpriv & H')".
    rewrite γcurpriv γpmp0cfg γpmpaddr0 γpmp1cfg γpmpaddr1 γpc γmstatus γmideleg γmedeleg.
    iMod (femtokernel_splitMemory with "Hmem") as "(%rG & Hinit & Hhandler0 & Hhandler1 & Hhandler2 & #Hinv & Hdata & Hstate & Hadv)"; try eassumption.
    iModIntro.
    iSplitR "".
    - destruct (nenv.view δ).  (* INV and frag of state *)
      iApply femtokernel_init_safe.
      cbn -[femtokernel_handler_gen_block0 femtokernel_handler_gen_block1 femtokernel_handler_gen_block2].
      iSplitL "Hpc Hnpc Hinit".
      { unfold exec_instructions_prologue. iFrame "Hpc Hinit Hnpc". }
      iSplitL "Hmstatus Hmie Hmip Hmideleg Hmedeleg Hmtvec Hmscratch Hmepc Hmcause Hstvec Hsscratch Hsepc Hscause Hcurpriv H'".
      { iSplitR. iSplit; auto. cbn.
        iFrame "Hmtvec Hmcause Hmip Hmie Hmideleg Hmedeleg Hmepc Hmscratch Hmstatus Hstvec Hsscratch Hsepc Hscause Hcurpriv".
        cbn.
        iDestruct "H'" as "(Hx01 & Hx02 & Hx03 & Hx04 & Hx05 & Hx06 & Hx07 & Hx08 & Hx09 & H')".
        iDestruct "H'" as "(Hx10 & Hx11 & Hx12 & Hx13 & Hx14 & Hx15 & Hx16 & Hx17 & Hx18 & Hx19 & H')".
        iDestruct "H'" as "(Hx20 & Hx21 & Hx22 & Hx23 & Hx24 & Hx25 & Hx26 & Hx27 & Hx28 & Hx29 & H')".
        iDestruct "H'" as "(Hx30 & Hx31 & Hpmp0cfg & Hpmpaddr0 & Hpmp1cfg & Hpmpaddr1 & _)".
        iFrame "Hx25 Hx17 Hx09 Hx21 Hx29 Hx13 Hx05".
        iFrame "Hx01 Hx23 Hx31 Hx15 Hx07 Hx19 Hx27".
        iFrame "Hx11 Hx03 Hx24 Hx16 Hx08 Hx20 Hx28".
        iFrame "Hx12 Hx04 Hx22 Hx30 Hx14 Hx06 Hx18".
        iFrame "Hx26 Hx10 Hx02".
        Transparent interp_pmp_entries. unfold interp_pmp_entries. iFrame "Hpmp0cfg Hpmpaddr0 Hpmp1cfg Hpmpaddr1".
        eauto.
      }
      unfold ptsto_instrs_handler.
      iFrame "Hhandler0 Hhandler1 Hhandler2 Hdata Hstate Hadv Hinv".
      iPureIntro. destruct σ; auto.
   -
     iIntros "Hmem". (* INV only *)
     iInv "Hinv" as ">( %s & %t & Htrf & Hsta & %Hpred)" "_".
     iDestruct "Hmem" as "(%memmap & Hinv2 & %link & Htra)".
     iDestruct (trace.trace_full_frag_eq with "Htra Htrf") as "->".
     iApply fupd_mask_intro; first apply empty_subseteq. iIntros "_".
     iPureIntro. now eexists s.
Qed.

Print Assumptions femtokernel_endToEnd.

(* Local Variables: *)
(* proof-omit-proofs-option: t *)
(* End: *)
