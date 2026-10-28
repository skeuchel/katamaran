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
     Bool.Bool
     Strings.String
     ZArith.ZArith.
From Equations Require Import
     Equations.
Require Import Equations.Prop.EqDec.
From Katamaran Require Import
     Program
     Bitvector
     Semantics
     Semantics.Registers
     Syntax.BinOps.
From Katamaran Require Export
     RiscvPmp.Base.

From stdpp Require Import decidable finite.

Set Implicit Arguments.
Import ctx.notations.
Import ctx.resolution.
Import env.notations.
Open Scope string_scope.

Module RiscvNotations.
  Notation "'rs'"           := "rs" : string_scope.
  Notation "'rs1'"          := "rs1" : string_scope.
  Notation "'rs2'"          := "rs2" : string_scope.
  Notation "'rd'"           := "rd" : string_scope.
  Notation "'op'"           := "op" : string_scope.
  Notation "'v'"            := "v" : string_scope.
  Notation "'imm'"          := "imm" : string_scope.
  Notation "'shamt'"        := "shamt" : string_scope.
  Notation "'t'"            := "t" : string_scope.
  Notation "'addr'"         := "addr" : string_scope.
  Notation "'paddr'"        := "paddr" : string_scope.
  Notation "'addr_int'"     := "addr_int" : string_scope.
  Notation "'vaddr'"        := "vaddr" : string_scope.
  Notation "'typ'"          := "typ" : string_scope.
  Notation "'acc'"          := "acc" : string_scope.
  Notation "'value'"        := "value" : string_scope.
  Notation "'data'"         := "data" : string_scope.
  Notation "'ent'"          := "ent" : string_scope.
  Notation "'pmpaddr'"      := "pmpaddr" : string_scope.
  Notation "'prev_pmpaddr'" := "prev_pmpaddr" : string_scope.
  Notation "'cfg'"          := "cfg" : string_scope.
  Notation "'rng'"          := "rng" : string_scope.
  Notation "'bv'"           := "bv" : string_scope.
  Notation "'width'"        := "width" : string_scope.
  Notation "'is_unsigned'"  := "is_unsigned" : string_scope.
  Notation "'is_imm'"       := "is_imm" : string_scope.
  Notation "'isWrite'"      := "isWrite" : string_scope.
  Notation "'new_val'"      := "new_val" : string_scope.
  Notation "'e'"            := "e" : string_scope.
  Notation "'ctl'"          := "ctl" : string_scope.
  Notation "'c'"            := "c" : string_scope.
  Notation "'cause'"        := "cause" : string_scope.
  Notation "'m'"            := "m" : string_scope.
  Notation "'priv'"         := "priv" : string_scope.
  Notation "'cur_priv'"     := "cur_priv" : string_scope.
  Notation "'del_priv'"     := "del_priv" : string_scope.
  Notation "'p'"            := "p" : string_scope.
  Notation "'signed1'"      := "signed1" : string_scope.
  Notation "'signed2'"      := "signed2" : string_scope.
  Notation "'high'"         := "high" : string_scope.
  Notation "'rs1_val'"      := "rs1_val" : string_scope.
  Notation "'rs2_val'"      := "rs2_val" : string_scope.
  Notation "'csr_val'"      := "csr_val" : string_scope.
  Notation "'op'"           := "op" : string_scope.
  Notation "'result'"       := "result" : string_scope.
  Notation "'res'"          := "res" : string_scope.
  Notation "'immext'"       := "immext" : string_scope.
  Notation "'off'"          := "off" : string_scope.
  Notation "'offset'"       := "offset" : string_scope.
  Notation "'ret'"          := "ret" : string_scope.
  Notation "'tmp'"          := "tmp" : string_scope.
  Notation "'tmp1'"         := "tmp1" : string_scope.
  Notation "'tmp2'"         := "tmp2" : string_scope.
  Notation "'tmp3'"         := "tmp3" : string_scope.
  Notation "'rs1_int'"      := "rs1_int" : string_scope.
  Notation "'rs2_int'"      := "rs2_int" : string_scope.
  Notation "'result_wide'"  := "result_wide" : string_scope.
  Notation "'taken'"        := "taken" : string_scope.
  Notation "'check'"        := "check" : string_scope.
  Notation "'L'"            := "L" : string_scope.
  Notation "'A'"            := "A" : string_scope.
  Notation "'X'"            := "X" : string_scope.
  Notation "'W'"            := "W" : string_scope.
  Notation "'R'"            := "R" : string_scope.
  Notation "'lo'"           := "lo" : string_scope.
  Notation "'hi'"           := "hi" : string_scope.
  Notation "'f'"            := "f" : string_scope.
  Notation "'w'"            := "w" : string_scope.
  Notation "'r'"            := "r" : string_scope.
  Notation "'tvec'"         := "tvec" : string_scope.
  Notation "'epc'"          := "epc" : string_scope.
  Notation "'prev_priv'"    := "prev_priv" : string_scope.
  Notation "'MPP'"          := "MPP" : string_scope.
  Notation "'SPP'"          := "SPP" : string_scope.
  Notation "'csr'"          := "csr" : string_scope.
  Notation "'csrrw'"        := "csrrw" : string_scope.
  Notation "'csrpr'"        := "csrpr" : string_scope.
  Notation "'idx'"          := "idx" : string_scope.
  Notation "'locked'"       := "locked" : string_scope.
End RiscvNotations.

(* We postulate a pure decode function and assume that that's what the decode primitive implements. *)
(* Similarly for *_{from,to}_bits functions, ideally we would move to actual bitvectors for values... *)
Axiom pure_decode : bv 32 -> string + AST.

Module Import RiscvPmpProgram <: Program RiscvPmpBase.

  Section FunDeclKit.
  Definition width_constraint (width : nat) : bool :=
    (0 <? width)%nat && (width <=? xlenbytes)%nat.

  #[export] Instance IsTrue_width_constraint_byte_multiplier (bytes : nat)
    (H: IsTrue (width_constraint bytes)) :
    IsTrue (bytes * byte <=? xlenbytes * byte)%nat :=
    IsTrue_bytes_xlenbytes bytes xlenbytes (IsTrue.andb_r H).

  Inductive restrict_bytes : nat -> Prop :=
  | restrict_bytes_one : restrict_bytes 1%nat
  | restrict_bytes_two : restrict_bytes 2%nat
  | restrict_bytes_four : restrict_bytes 4%nat.

  Import RiscvNotations.

  (** Functions **)
  Inductive Fun : PCtx -> Ty -> Set :=
  | rX                    : Fun [rs ∷ ty_regno] ty_xlenbits
  | wX                    : Fun [rd ∷ ty_regno; v ∷ ty_xlenbits] ty.unit
  | bool_to_bits          : Fun ["x" :: ty.bool] (ty.bvec 1)
  | shift_right_arith32   : Fun [v :: ty.bvec 32; "shift" :: ty.bvec 5] (ty.bvec 32)
  | extend_value (bytes : nat) {p : IsTrue (width_constraint bytes)} : Fun [is_unsigned :: ty.bool; value :: ty_memory_op_result bytes] (ty_memory_op_result xlenbytes)
  | get_arch_pc           : Fun ctx.nil ty_xlenbits
  | get_next_pc           : Fun ctx.nil ty_xlenbits
  | set_next_pc           : Fun [addr ∷ ty_xlenbits] ty.unit
  | tick_pc               : Fun ctx.nil ty.unit
  | to_bits (l : nat)     : Fun [value :: ty.int] (ty.bvec l)
  (* | abs                   : Fun [v ∷ ty.int] ty.int *)
  | within_phys_mem       : Fun [paddr ∷ ty_xlenbits; width :: ty.int] ty.bool
  | mem_read (bytes : nat) {H : restrict_bytes bytes} : Fun [typ ∷ ty_access_type; paddr ∷ ty_xlenbits] (ty_memory_op_result bytes)
  | checked_mem_read (bytes : nat) {H : restrict_bytes bytes} : Fun [t ∷ ty_access_type; paddr ∷ ty_xlenbits] (ty_memory_op_result bytes)
  | checked_mem_write (bytes : nat) {H : restrict_bytes bytes} : Fun [paddr ∷ ty_xlenbits; data ∷ ty_bytes bytes] (ty_memory_op_result 1)
  | pmp_mem_read (bytes : nat) {H : restrict_bytes bytes} : Fun [t∷ ty_access_type; p ∷ ty_privilege; paddr ∷ ty_xlenbits] (ty_memory_op_result bytes)
  | pmp_mem_write (bytes : nat) {H : restrict_bytes bytes} : Fun [paddr ∷ ty_xlenbits; data ∷ ty_bytes bytes; typ ∷ ty_access_type; priv ∷ ty_privilege] (ty_memory_op_result 1)
  | pmpLocked             : Fun [cfg ∷ ty_pmpcfg_ent] ty.bool
  | pmpWriteCfgReg        : Fun ["n" :: ty.int; value :: ty_xlenbits] ty.unit
  | pmpWriteCfg           : Fun [cfg :: ty_pmpcfg_ent; value :: ty_byte] ty_pmpcfg_ent
  | pmpWriteAddr          : Fun [locked :: ty.bool; addr :: ty_xlenbits; value :: ty_xlenbits] ty_xlenbits
  | pmpCheck (bytes : nat) {H : restrict_bytes bytes} : Fun [addr ∷ ty_xlenbits; acc ∷ ty_access_type; priv ∷ ty_privilege] (ty.option ty_exception_type)
  | pmpCheckPerms         : Fun [ent ∷ ty_pmpcfg_ent; acc ∷ ty_access_type; priv ∷ ty_privilege] ty.bool
  | pmpCheckRWX           : Fun [ent ∷ ty_pmpcfg_ent; acc ∷ ty_access_type] ty.bool
  | pmpMatchEntry         : Fun [addr ∷ ty_xlenbits; width :: ty_xlenbits; acc ∷ ty_access_type; priv ∷ ty_privilege; ent ∷ ty_pmpcfg_ent; pmpaddr ∷ ty_xlenbits; prev_pmpaddr ∷ ty_xlenbits] ty_pmpmatch
  | pmpAddrRange          : Fun [cfg ∷ ty_pmpcfg_ent; pmpaddr ∷ ty_xlenbits; prev_pmpaddr ∷ ty_xlenbits] ty_pmp_addr_range
  | pmpMatchAddr          : Fun [addr ∷ ty_xlenbits; width :: ty_xlenbits; rng ∷ ty_pmp_addr_range] ty_pmpaddrmatch
  | process_load (bytes : nat) {p : IsTrue (width_constraint bytes)} : Fun [rd ∷ ty_regno; vaddr ∷ ty_xlenbits; value ∷ ty_memory_op_result bytes; is_unsigned :: ty.bool] ty_retired
  | mem_write_value (bytes : nat) {H : restrict_bytes bytes} : Fun [paddr ∷ ty_xlenbits; value ∷ ty_bytes bytes] (ty_memory_op_result 1)
  | main                  : Fun ctx.nil ty.unit
  | init_model            : Fun ctx.nil ty.unit
  | loop                  : Fun ctx.nil ty.unit
  | step                  : Fun ctx.nil ty.unit
  | fetch                 : Fun ctx.nil ty_fetch_result
  | init_sys              : Fun ctx.nil ty.unit
  | init_pmp              : Fun ctx.nil ty.unit
  | exceptionType_to_bits : Fun [e ∷ ty_exception_type] ty_exc_code
  | interruptType_to_bits : Fun ["i" ∷ ty_interruptType ] ty_exc_code
  | Minterrupts_to_bits   : Fun ["i" ∷ ty_Minterrupts ] ty_xlenbits
  | Minterrupts_from_bits : Fun ["i" ∷ ty_xlenbits ] ty_Minterrupts
  | Medeleg_to_bits       : Fun ["i" ∷ ty_Medeleg ] ty_xlenbits
  | Medeleg_from_bits     : Fun ["i" ∷ ty_xlenbits ] ty_Medeleg
  | idx_medeleg_record    : Fun ["i" ∷ ty_Medeleg; e ∷ ty_exception_type] ty.bool
  | privLevel_to_bits     : Fun [p ∷ ty_privilege] ty_priv_level
  | handle_mem_exception  : Fun [addr ∷ ty_xlenbits; e ∷ ty_exception_type] ty.unit
  | exception_handler     : Fun [cur_priv ∷ ty_privilege; ctl ∷ ty_ctl_result; "pc" ∷ ty_xlenbits] ty_xlenbits
  | exception_delegatee   : Fun [e ∷ ty_exception_type; p ∷ ty_privilege] ty_privilege
  | trap_handler          : Fun [del_priv ∷ ty_privilege; "intr" ∷ ty.bool; c ∷ ty_exc_code; "pc" ∷ ty_xlenbits] ty_xlenbits
  | prepare_trap_vector   : Fun [p ∷ ty_privilege; cause ∷ ty_mcause] ty_xlenbits
  | tvec_addr             : Fun [m ∷ ty_xlenbits; c ∷ ty_mcause] (ty.option ty_xlenbits)
  | handle_illegal        : Fun ctx.nil ty.unit
  | lower_mstatus         : Fun [m ∷ ty_mstatus] ty_sstatus
  | lower_mip             : Fun [m ∷ ty_Minterrupts; "d" ∷ ty_Minterrupts] ty_Sinterrupts
  | lower_mie             : Fun [m ∷ ty_Minterrupts; "d" ∷ ty_Minterrupts] ty_Sinterrupts
  | lift_sip              : Fun [m ∷ ty_Minterrupts; "d" ∷ ty_Minterrupts; "s" ∷ ty_Sinterrupts] ty_Minterrupts
  | legalize_sip          : Fun [m ∷ ty_Minterrupts; "d" ∷ ty_Minterrupts; v ∷ ty_xlenbits] ty_Minterrupts
  | lift_sie              : Fun [m ∷ ty_Minterrupts; "d" ∷ ty_Minterrupts; "s" ∷ ty_Sinterrupts] ty_Minterrupts
  | legalize_sie          : Fun [m ∷ ty_Minterrupts; "d" ∷ ty_Minterrupts; v ∷ ty_xlenbits] ty_Minterrupts
  | check_CSR             : Fun [csr ∷ ty_csridx; p ∷ ty_privilege] ty.bool
  | is_CSR_defined        : Fun [csr ∷ ty_csridx; p ∷ ty_privilege] ty.bool
  | csrAccess             : Fun [csr ∷ ty_csridx] ty_access_type
  | csrPriv               : Fun [csr ∷ ty_csridx] ty_privilege
  | check_CSR_access      : Fun [csrrw ∷ ty_access_type; csrpr ∷ ty_privilege; p ∷ ty_privilege] ty.bool
  | readCSR               : Fun [csr ∷ ty_csridx] ty_xlenbits
  | writeCSR              : Fun [csr ∷ ty_csridx; value ∷ ty_xlenbits] ty.unit
  | dispatchInterrupt     : Fun ["priv" ∷ ty_privilege] (ty.option (ty.prod ty_interruptType ty_privilege))
  | handle_interrupt      : Fun ["i" ∷ ty_interruptType; del_priv ∷ ty_privilege] ty.unit
  | and_Minterrupts       : Fun ["ints1" ∷ ty_Minterrupts; "ints2" ∷ ty_Minterrupts] ty_Minterrupts
  | processPending        : Fun ["xip" ∷ ty_Minterrupts; "xie" ∷ ty_Minterrupts; "xideleg" ∷ ty_Minterrupts; "priv_enabled" ∷ ty.bool] ty_interrupt_set
  | getPendingSet         : Fun ["priv" ∷ ty_privilege] (ty.option (ty.prod ty_Minterrupts ty_privilege))
  | findPendingInterrupt  : Fun ["ip" ∷ ty_Minterrupts] (ty.option ty_interruptType)
  | execute               : Fun ["ast" ∷ ty_ast] ty_retired
  | execute_RTYPE         : Fun [rs2 ∷ ty_regno; rs1 ∷ ty_regno; rd ∷ ty_regno; op ∷ ty_rop] ty_retired
  | execute_ITYPE         : Fun [imm ∷ ty.bvec 12; rs1 ∷ ty_regno; rd ∷ ty_regno; op ∷ ty_iop] ty_retired
  | execute_SHIFTIOP      : Fun [shamt ∷ ty.bvec 6; rs1 ∷ ty_regno; rd ∷ ty_regno; op ∷ ty_sop] ty_retired
  | execute_UTYPE         : Fun [imm ∷ ty.bvec 20; rd ∷ ty_regno; op ∷ ty_uop] ty_retired
  | execute_BTYPE         : Fun [imm ∷ ty.bvec 13; rs2 ∷ ty_regno; rs1 ∷ ty_regno; op ∷ ty_bop] ty_retired
  | execute_RISCV_JAL     : Fun [imm ∷ ty.bvec 21; rd ∷ ty_regno] ty_retired
  | execute_RISCV_JALR    : Fun [imm ∷ ty.bvec 12; rs1 ∷ ty_regno; rd ∷ ty_regno] ty_retired
  | execute_LOAD          : Fun [imm ∷ ty.bvec 12; rs1 ∷ ty_regno; rd ∷ ty_regno; is_unsigned :: ty.bool; width :: ty_word_width] ty_retired
  | execute_STORE         : Fun [imm ∷ ty.bvec 12; rs2 ∷ ty_regno; rs1 ∷ ty_regno; width :: ty_word_width] ty_retired
  | execute_ECALL         : Fun ctx.nil ty_retired
  | execute_EBREAK        : Fun ctx.nil ty_retired
  | execute_SRET          : Fun ctx.nil ty_retired
  | execute_MRET          : Fun ctx.nil ty_retired
  | execute_CSR           : Fun [csr :: ty_csridx; rs1 :: ty_regno; rd :: ty_regno; is_imm :: ty.bool; op :: ty_csrop] ty_retired
  | execute_MUL           : Fun [rs2 ∷ ty_regno; rs1 ∷ ty_regno; rd ∷ ty_regno; high :: ty.bool; signed1 :: ty.bool; signed2 :: ty.bool] ty_retired
  | execute_ILLEGAL       : Fun [w ∷ ty_word] ty_retired
  .

  (* Restrictions on MMIO needed, because MMIO operations leave a trace and are disallowed for 0-length data *)
  Inductive FunX : PCtx -> Ty -> Set :=
  | read_ram (bytes : nat)                 : FunX [paddr ∷ ty_xlenbits] (ty_bytes bytes)
  | write_ram (bytes : nat)                : FunX [paddr ∷ ty_xlenbits; data ∷ (ty_bytes bytes)] ty.bool
  | mmio_read `(H: restrict_bytes bytes)   : FunX [paddr ∷ ty_xlenbits] (ty_bytes bytes)
  | mmio_write `(H: restrict_bytes bytes)  : FunX [paddr ∷ ty_xlenbits; data ∷ (ty_bytes bytes)] ty.bool
  | within_mmio `(H: restrict_bytes bytes) : FunX [paddr ∷ ty_xlenbits] ty.bool
  | decode                                 : FunX [bv ∷ ty_word] ty_ast
  (* A method that is invoked once per cycle in the step function.
   * It updates pseudo-registers based on external world changes.
   * Particularly, the method models interrupt requests by peripherals that enable
   * bits in the mip pseudo-register.
   *)
  | externalWorldUpdates                   : FunX [] ty.unit
  (* Whether the machine is still powered on, i.e., no device powered it off. *)
  | powered_on                             : FunX [] ty.bool
  .

  Inductive Lem : PCtx -> Set :=
  | open_gprs                       : Lem ctx.nil
  | close_gprs                      : Lem ctx.nil
  | open_pmp_entries                : Lem ctx.nil
  | close_pmp_entries               : Lem ctx.nil
  | extract_pmp_ptsto (bytes : nat) : Lem [paddr :: ty_xlenbits]
  | return_pmp_ptsto  (bytes : nat) : Lem [paddr :: ty_xlenbits]
  | open_ptsto_instr                : Lem [paddr :: ty_xlenbits]
  | close_ptsto_instr               : Lem [paddr :: ty_xlenbits; w :: ty_xlenbits]
  | close_mmio_write (imm : Bitvector.bv.bv 12) (width : WordWidth) : Lem [paddr :: ty_xlenbits; r :: ty_regno] (* Statically known quantities; lemma is called in between instructions! *)
  .

  Definition 𝑭  : PCtx -> Ty -> Set := Fun.
  Definition 𝑭𝑿  : PCtx -> Ty -> Set := FunX.
  Definition 𝑳  : PCtx -> Set := Lem.
  End FunDeclKit.

  Include FunDeclMixin RiscvPmpBase.

  Module RiscvμSailNotations.
    Notation "'rs'"           := (exp_var "rs") : exp_scope.
    Notation "'rs1'"          := (exp_var "rs1") : exp_scope.
    Notation "'rs1_val'"      := (exp_var "rs1_val") : exp_scope.
    Notation "'rs2'"          := (exp_var "rs2") : exp_scope.
    Notation "'rs2_val'"      := (exp_var "rs2_val") : exp_scope.
    Notation "'csr_val'"      := (exp_var "csr_val") : exp_scope.
    Notation "'rd'"           := (exp_var "rd") : exp_scope.
    Notation "'op'"           := (exp_var "op") : exp_scope.
    Notation "'result'"       := (exp_var "result") : exp_scope.
    Notation "'res'"          := (exp_var "res") : exp_scope.
    Notation "'v'"            := (exp_var "v") : exp_scope.
    Notation "'imm'"          := (exp_var "imm") : exp_scope.
    Notation "'shamt'"        := (exp_var "shamt") : exp_scope.
    Notation "'immext'"       := (exp_var "immext") : exp_scope.
    Notation "'off'"          := (exp_var "off") : exp_scope.
    Notation "'offset'"       := (exp_var "offset") : exp_scope.
    Notation "'ret'"          := (exp_var "ret") : exp_scope.
    Notation "'tmp'"          := (exp_var "tmp") : exp_scope.
    Notation "'tmp1'"         := (exp_var "tmp1") : exp_scope.
    Notation "'tmp2'"         := (exp_var "tmp2") : exp_scope.
    Notation "'tmp3'"         := (exp_var "tmp3") : exp_scope.
    Notation "'rs1_int'"      := (exp_var "rs1_int") : exp_scope.
    Notation "'rs2_int'"      := (exp_var "rs2_int") : exp_scope.
    Notation "'result_wide'"  := (exp_var "result_wide") : exp_scope.
    Notation "'signed1'"      := (exp_var "signed1") : exp_scope.
    Notation "'signed2'"      := (exp_var "signed2") : exp_scope.
    Notation "'high'   "      := (exp_var "high") : exp_scope.
    Notation "'t'"            := (exp_var "t") : exp_scope.
    Notation "'e'"            := (exp_var "e") : exp_scope.
    Notation "'addr'"         := (exp_var "addr") : exp_scope.
    Notation "'paddr'"        := (exp_var "paddr") : exp_scope.
    Notation "'addr_int'"     := (exp_var "addr_int") : exp_scope.
    Notation "'vaddr'"        := (exp_var "vaddr") : exp_scope.
    Notation "'taken'"        := (exp_var "taken") : exp_scope.
    Notation "'typ'"          := (exp_var "typ") : exp_scope.
    Notation "'acc'"          := (exp_var "acc") : exp_scope.
    Notation "'value'"        := (exp_var "value") : exp_scope.
    Notation "'data'"         := (exp_var "data") : exp_scope.
    Notation "'check'"        := (exp_var "check") : exp_scope.
    Notation "'ent'"          := (exp_var "ent") : exp_scope.
    Notation "'pmpaddr'"      := (exp_var "pmpaddr") : exp_scope.
    Notation "'prev_pmpaddr'" := (exp_var "prev_pmpaddr") : exp_scope.
    Notation "'rng'"          := (exp_var "rng") : exp_scope.
    Notation "'cfg'"          := (exp_var "cfg") : exp_scope.
    Notation "'L'"            := (exp_var "L") : exp_scope.
    Notation "'A'"            := (exp_var "A") : exp_scope.
    Notation "'X'"            := (exp_var "X") : exp_scope.
    Notation "'W'"            := (exp_var "W") : exp_scope.
    Notation "'R'"            := (exp_var "R") : exp_scope.
    Notation "'lo'"           := (exp_var "lo") : exp_scope.
    Notation "'hi'"           := (exp_var "hi") : exp_scope.
    Notation "'f'"            := (exp_var "f") : exp_scope.
    Notation "'w'"            := (exp_var "w") : exp_scope.
    Notation "'ctl'"          := (exp_var "ctl") : exp_scope.
    Notation "'c'"            := (exp_var "c") : exp_scope.
    Notation "'cause'"        := (exp_var "cause") : exp_scope.
    Notation "'tvec'"         := (exp_var "tvec") : exp_scope.
    Notation "'m'"            := (exp_var "m") : exp_scope.
    Notation "'epc'"          := (exp_var "epc") : exp_scope.
    Notation "'priv'"         := (exp_var "priv") : exp_scope.
    Notation "'cur_priv'"     := (exp_var "cur_priv") : exp_scope.
    Notation "'del_priv'"     := (exp_var "del_priv") : exp_scope.
    Notation "'prev_priv'"    := (exp_var "prev_priv") : exp_scope.
    Notation "'p'"            := (exp_var "p") : exp_scope.
    Notation "'MPP'"          := (exp_var "MPP") : exp_scope.
    Notation "'SPP'"          := (exp_var "SPP") : exp_scope.
    Notation "'csr'"          := (exp_var "csr") : exp_scope.
    Notation "'csrrw'"        := (exp_var "csrrw") : exp_scope.
    Notation "'csrpr'"        := (exp_var "csrpr") : exp_scope.
    Notation "'idx'"          := (exp_var "idx") : exp_scope.
    Notation "'locked'"       := (exp_var "locked") : exp_scope.
    Notation "'width'"        := (exp_var "width") : exp_scope.
    Notation "'is_unsigned'"  := (exp_var "is_unsigned") : exp_scope.
    Notation "'is_imm'"       := (exp_var "is_imm") : exp_scope.
    Notation "'isWrite'"      := (exp_var "isWrite") : exp_scope.
    Notation "'new_val'"      := (exp_var "new_val") : exp_scope.

    Notation "'Read'" := (exp_union access_type KRead (exp_val ty.unit tt)) : exp_scope.
    Notation "'Write'" := (exp_union access_type KWrite (exp_val ty.unit tt)) : exp_scope.
    Notation "'ReadWrite'" := (exp_union access_type KReadWrite (exp_val ty.unit tt)) : exp_scope.
    Notation "'Execute'" := (exp_union access_type KExecute (exp_val ty.unit tt)) : exp_scope.

    Notation "'E_Fetch_Access_Fault'" := (exp_union exception_type KE_Fetch_Access_Fault (exp_val ty.unit tt)) : exp_scope.
    Notation "'E_Load_Access_Fault'" := (exp_union exception_type KE_Load_Access_Fault (exp_val ty.unit tt)) : exp_scope.
    Notation "'E_SAMO_Access_Fault'" := (exp_union exception_type KE_SAMO_Access_Fault (exp_val ty.unit tt)) : exp_scope.
    Notation "'E_U_EnvCall'" := (exp_union exception_type KE_U_EnvCall (exp_val ty.unit tt)) : exp_scope.
    Notation "'E_S_EnvCall'" := (exp_union exception_type KE_S_EnvCall (exp_val ty.unit tt)) : exp_scope.
    Notation "'E_M_EnvCall'" := (exp_union exception_type KE_M_EnvCall (exp_val ty.unit tt)) : exp_scope.
    Notation "'E_Illegal_Instr'" := (exp_union exception_type KE_Illegal_Instr (exp_val ty.unit tt)) : exp_scope.

    Notation "'None'" := (exp_inr (exp_val ty.unit tt)) : exp_scope.
    Notation "'Some' va" := (exp_inl va) (at level 10, va at next level) : exp_scope.

    Notation "'MemValue' bs memv" := (exp_union (memory_op_result bs) KMemValue memv) (at level 10, memv at next level) : exp_scope.
    Notation "'MemException' bs meme" := (exp_union (memory_op_result bs) KMemException meme) (at level 10, meme at next level) : exp_scope.

    Notation "'F_Base' memv" := (exp_union fetch_result KF_Base memv) (at level 10, memv at next level) : exp_scope.
    Notation "'F_Error' meme memv" := (exp_union fetch_result KF_Error (exp_binop bop.pair meme memv)) (at level 10, meme at next level, memv at next level) : exp_scope.

    Notation "'CTL_TRAP' exc" := (exp_union ctl_result KCTL_TRAP exc) (at level 10, exc at next level) : exp_scope.
    Notation "'CTL_SRET'" := (exp_union ctl_result KCTL_SRET (exp_val ty.unit tt)) : exp_scope.
    Notation "'CTL_MRET'" := (exp_union ctl_result KCTL_MRET (exp_val ty.unit tt)) : exp_scope.
  End RiscvμSailNotations.

  Section FunDefKit.
  Import RiscvNotations.
  Import RiscvμSailNotations.
  Import Bitvector.bv.notations.
  Local Coercion stm_exp : Exp >-> Stm.

  Notation "'use' 'lemma' lem args" := (stm_lemma lem args%env) (at level 10, lem at next level) : exp_scope.
  Notation "'use' 'lemma' lem" := (stm_lemma lem env.nil) (at level 10, lem at next level) : exp_scope.

  Definition zero_reg {Γ} : Stm Γ ty_xlenbits := exp_val ty_xlenbits (Bitvector.bv.of_N 0).

  Definition exp_testbit {Γ : PCtx} {n} (eb : Exp Γ (ty.bvec n)) (i : N) : Exp Γ ty.bool :=
    let em := exp_val (ty.bvec n) (Bitvector.bv.of_N (N.shiftl 1 i)) in
    exp_binop bop.bvand eb em = em.

  (** Pure inlined functions **)
  Definition stm_mstatus_from_bits {Γ} (b : Stm Γ ty_xlenbits) : Stm Γ ty_mstatus :=
    let: "b"   := b in
    let: "mpp" := let: "mstatus_mpp" := exp_binop bop.bvand (exp_var "b") (exp_val ty_xlenbits (Bitvector.bv.of_N (N.shiftl 3 11))) in
                  if: exp_var "mstatus_mpp" = (exp_val ty_xlenbits (Bitvector.bv.of_N (N.shiftl 0 11))) then stm_val ty_privilege User else
                  if: exp_var "mstatus_mpp" = (exp_val ty_xlenbits (Bitvector.bv.of_N (N.shiftl 1 11))) then stm_val ty_privilege Supervisor else
                  if: exp_var "mstatus_mpp" = (exp_val ty_xlenbits (Bitvector.bv.of_N (N.shiftl 3 11))) then stm_val ty_privilege Machine else
                  stm_fail ty_privilege "mstatus_from_bits" in
    let: "spp" := if: exp_testbit (exp_var "b") 8 then stm_val ty_privilege Supervisor else stm_val ty_privilege User in
    let: "mpie" := exp_testbit (exp_var "b") 7 in
    let: "spie" := exp_testbit (exp_var "b") 5 in
    let: "mie" := exp_testbit (exp_var "b") 3 in
    let: "sie" := exp_testbit (exp_var "b") 1 in
    stm_exp (exp_record rmstatus [ exp_var "mpp"; exp_var "spp"; exp_var "mpie"; exp_var "spie"; exp_var "mie"; exp_var "sie" ]).

  Definition stm_mstatus_to_bits {Γ} (mst : Stm Γ ty_mstatus) : Stm Γ ty_xlenbits :=
    let: "mst" := mst in
    match: exp_var "mst" in rmstatus with
      ["mpp"; "spp"; "mpie"; "spie"; "mie"; "sie"] =>
        let: "mppb" := match: exp_var "mpp" in privilege with
                       | User       => stm_val (ty.bvec 2) [bv 0x0]
                       | Supervisor => stm_val (ty.bvec 2) [bv[2] 0x1]
                       | Machine    => stm_val (ty.bvec 2) [bv[2] 0x3]
                       end in
        let: "sppb" := match: exp_var "spp" in privilege with
                          | User       => stm_val (ty.bvec 1) [bv 0x0]
                          | Supervisor => stm_val (ty.bvec 1) [bv 0x1]
                          | Machine    => stm_fail (ty.bvec 1) "mstatus_to_bits: Can never have Machine as privilege level in SPP, this case should be unreachable"
                          end in
        let: "mpieb" := call bool_to_bits (exp_var "mpie") in
        let: "spieb" := call bool_to_bits (exp_var "spie") in
        let: "mieb" := call bool_to_bits (exp_var "mie") in
        let: "sieb" := call bool_to_bits (exp_var "sie") in
         exp_bvapp (exp_val (ty.bvec 1)      Bitvector.bv.zero)
        (exp_bvapp (exp_var (σ := ty.bvec 1) "sieb")
        (exp_bvapp (exp_val (ty.bvec 1)      Bitvector.bv.zero)
        (exp_bvapp (exp_var (σ := ty.bvec 1) "mieb")
        (exp_bvapp (exp_val (ty.bvec 1)      Bitvector.bv.zero)
        (exp_bvapp (exp_var (σ := ty.bvec 1) "spieb")
        (exp_bvapp (exp_val (ty.bvec 1)      Bitvector.bv.zero)
        (exp_bvapp (exp_var (σ := ty.bvec 1) "mpieb")
        (exp_bvapp (exp_var (σ := ty.bvec 1) "sppb")
        (exp_bvapp (exp_val (ty.bvec 2)      Bitvector.bv.zero)
        (exp_bvapp (exp_var (σ := ty.bvec 2) "mppb")
                   (exp_val (ty.bvec (xlenbits - 13)) Bitvector.bv.zero)))))))))))
    end.

  Definition stm_sstatus_from_bits {Γ} (b : Stm Γ ty_xlenbits) : Stm Γ ty_sstatus :=
    let: "mst" := stm_mstatus_from_bits b in
    match: exp_var "mst" in rmstatus with
      ["mpp"; "spp"; "mpie"; "spie"; "mie"; "sie"] =>
        stm_exp (exp_record rsstatus [exp_var "spp"; exp_var "spie"; exp_var "sie"])
    end.

  Definition stm_sstatus_to_bits {Γ} (sst : Stm Γ ty_sstatus) : Stm Γ ty_xlenbits :=
    let: "sst" := sst in
    match: exp_var "sst" in rsstatus with
      ["spp"; "spie"; "sie"] =>
        (* We need to use zeroes (or zero values) when converting sstatus to
           bits using the mstatus functions. Hence the following bindings. *)
        let: "mpp" := exp_val ty_privilege User in
        let: "mpie" := exp_val ty.bool false in
        let: "mie" := exp_val ty.bool false in
        let: "mst" := (exp_record rmstatus [exp_var "mpp";
                                            exp_var "spp";
                                            exp_var "mpie";
                                            exp_var "spie";
                                            exp_var "mie";
                                            exp_var "sie"]) in
        stm_mstatus_to_bits (exp_var "mst")
    end.

  Definition stm_Sinterrupts_to_bits {Γ} (stm_s : Stm Γ ty_Sinterrupts) : Stm Γ ty_xlenbits :=
    let: "s" := stm_s in
    match: exp_var "s" in rsinterrupts with
      ["SEI"; "UEI"; "STI"; "UTI"; "SSI"; "USI"] =>
          let: "v" := stm_exp (exp_record rminterrupts [nenv exp_val ty.bool false;
                                                             exp_var "SEI";
                                                             exp_var "UEI";
                                                             exp_val ty.bool false;
                                                             exp_var "STI";
                                                             exp_var "UTI";
                                                             exp_val ty.bool false;
                                                             exp_var "SSI";
                                                             exp_var "USI"]) in
          call Minterrupts_to_bits (exp_var "v")
    end.

  Definition stm_Sinterrupts_from_bits {Γ} (stm_s : Stm Γ ty_xlenbits) : Stm Γ ty_Sinterrupts :=
    let: "s" := stm_s in
    let: "m" := call Minterrupts_from_bits (exp_var "s") in
    match: exp_var "m" in rminterrupts with
      ["MEI"; "SEI"; "UEI"; "MTI"; "STI"; "UTI"; "MSI"; "SSI"; "USI"] =>
        stm_exp (exp_record rsinterrupts [exp_var "SEI";
                                          exp_var "UEI";
                                          exp_var "STI";
                                          exp_var "UTI";
                                          exp_var "SSI";
                                          exp_var "USI"])
    end.

  Definition fun_Medeleg_to_bits : Stm ["i" ∷ ty_Medeleg] ty_xlenbits :=
    match: exp_var "i" in rmedeleg with
      [ "SAMO_Page_Fault"
      ; "Load_Page_Fault"
      ; "Fetch_Page_Fault"
      ; "MEnvCall"
      ; "SEnvCall"
      ; "UEnvCall"
      ; "SAMO_Access_Fault"
      ; "SAMO_Addr_Align"
      ; "Load_Access_Fault"
      ; "Load_Addr_Align"
      ; "Breakpoint"
      ; "Illegal_Instr"
      ; "Fetch_Access_Fault"
      ; "Fetch_Addr_Align"
      ] =>
      let: "b15" := stm_call bool_to_bits [nenv exp_var "SAMO_Page_Fault"] in
      let: "b13" := stm_call bool_to_bits [nenv exp_var "Load_Page_Fault"] in
      let: "b12" := stm_call bool_to_bits [nenv exp_var "Fetch_Page_Fault"] in
      let: "b10" := stm_call bool_to_bits [nenv exp_var "MEnvCall"] in
      let: "b9" := stm_call bool_to_bits [nenv exp_var "SEnvCall"] in
      let: "b8" := stm_call bool_to_bits [nenv exp_var "UEnvCall"] in
      let: "b7" := stm_call bool_to_bits [nenv exp_var "SAMO_Access_Fault"] in
      let: "b6" := stm_call bool_to_bits [nenv exp_var "SAMO_Addr_Align"] in
      let: "b5" := stm_call bool_to_bits [nenv exp_var "Load_Access_Fault"] in
      let: "b4" := stm_call bool_to_bits [nenv exp_var "Load_Addr_Align"] in
      let: "b3" := stm_call bool_to_bits [nenv exp_var "Breakpoint"] in
      let: "b2" := stm_call bool_to_bits [nenv exp_var "Illegal_Instr"] in
      let: "b1" := stm_call bool_to_bits [nenv exp_var "Fetch_Access_Fault"] in
      let: "b0" := stm_call bool_to_bits [nenv exp_var "Fetch_Addr_Align"] in
      let r16 : Exp _ (ty.bvec 16) :=
         exp_bvapp (exp_var (σ := ty.bvec 1) "b0")
        (exp_bvapp (exp_var (σ := ty.bvec 1) "b1")
        (exp_bvapp (exp_var (σ := ty.bvec 1) "b2")
        (exp_bvapp (exp_var (σ := ty.bvec 1) "b3")
        (exp_bvapp (exp_var (σ := ty.bvec 1) "b4")
        (exp_bvapp (exp_var (σ := ty.bvec 1) "b5")
        (exp_bvapp (exp_var (σ := ty.bvec 1) "b6")
        (exp_bvapp (exp_var (σ := ty.bvec 1) "b7")
        (exp_bvapp (exp_var (σ := ty.bvec 1) "b8")
        (exp_bvapp (exp_var (σ := ty.bvec 1) "b9")
        (exp_bvapp (exp_var (σ := ty.bvec 1) "b10")
        (exp_bvapp (exp_val (ty.bvec 1) Bitvector.bv.zero)
        (exp_bvapp (exp_var (σ := ty.bvec 1) "b12")
        (exp_bvapp (exp_var (σ := ty.bvec 1) "b13")
        (exp_bvapp (exp_val (ty.bvec 1) Bitvector.bv.zero)
                   (exp_var (σ := ty.bvec 1) "b15"))))))))))))))) in
      stm_exp (exp_unop uop.zext r16)
    end.

  Definition fun_Minterrupts_to_bits : Stm ["i" ∷ ty_Minterrupts] ty_xlenbits :=
    match: exp_var "i" in rminterrupts with
      ["MEI"; "SEI"; "UEI"; "MTI"; "STI"; "UTI"; "MSI"; "SSI"; "USI"] =>
        let: "b11" := stm_call bool_to_bits [nenv exp_var "MEI"] in
        let: "b9" := stm_call bool_to_bits [nenv exp_var "SEI"] in
        let: "b8" := stm_call bool_to_bits [nenv exp_var "UEI"] in
        let: "b7" := stm_call bool_to_bits [nenv exp_var "MTI"] in
        let: "b5" := stm_call bool_to_bits [nenv exp_var "STI"] in
        let: "b4" := stm_call bool_to_bits [nenv exp_var "UTI"] in
        let: "b3" := stm_call bool_to_bits [nenv exp_var "MSI"] in
        let: "b1" := stm_call bool_to_bits [nenv exp_var "SSI"] in
        let: "b0" := stm_call bool_to_bits [nenv exp_var "USI"] in
        let r12 : Exp _ (ty.bvec 12) :=
          (exp_bvapp
             (exp_var (σ := ty.bvec 1) "b0")
             (exp_bvapp
                (exp_bvapp
                   (exp_bvapp (exp_bvapp (exp_var (σ := ty.bvec 1) "b1")
                                         (exp_val (ty.bvec 1) Bitvector.bv.zero))
                              (exp_var (σ := ty.bvec 1) "b3"))
                   (exp_bvapp (exp_var (σ := ty.bvec 1) "b4")
                              (exp_bvapp (exp_var (σ := ty.bvec 1) "b5")
                                         (exp_val (ty.bvec 1) Bitvector.bv.zero))))
                (exp_bvapp
                   (exp_bvapp (exp_var (σ := ty.bvec 1) "b7")
                      (exp_var (σ := ty.bvec 1) "b8"))
                   (exp_bvapp (exp_bvapp (exp_var (σ := ty.bvec 1) "b9")
                                         (exp_val (ty.bvec 1) Bitvector.bv.zero))
                      (exp_var (σ := ty.bvec 1) "b11"))
                )
            )) in
        stm_exp (exp_unop uop.zext r12)
    end.

  Definition stm_pmpcfg_ent_from_bits {Γ} (b : Stm Γ ty_byte) : Stm Γ ty_pmpcfg_ent :=
    let: "b" := b in
    let: "L" := exp_testbit (exp_var "b") 7 in
    let: "A" := if: exp_testbit (exp_var "b") 4
                then if: exp_testbit (exp_var "b") 3
                     then stm_fail ty_pmpaddrmatchtype "stm_pmpcfg_ent_from_bits NAPOT"
                     else stm_fail ty_pmpaddrmatchtype "stm_pmpcfg_ent_from_bits NA4"
                else if: exp_testbit (exp_var "b") 3
                     then exp_val ty_pmpaddrmatchtype TOR
                     else exp_val ty_pmpaddrmatchtype OFF in
    let: "X" := exp_testbit (exp_var "b") 2 in
    let: "W" := exp_testbit (exp_var "b") 1 in
    let: "R" := exp_testbit (exp_var "b") 0 in
    exp_record rpmpcfg_ent [L; A; X; W; R].

  Definition fun_Minterrupts_from_bits : Stm ["i" ∷ ty_xlenbits] ty_Minterrupts :=
    let: "MEI" := exp_testbit (exp_var "i") 11 in
    let: "SEI" := exp_testbit (exp_var "i") 9 in
    let: "UEI" := exp_testbit (exp_var "i") 8 in
    let: "MTI" := exp_testbit (exp_var "i") 7 in
    let: "STI" := exp_testbit (exp_var "i") 5 in
    let: "UTI" := exp_testbit (exp_var "i") 4 in
    let: "MSI" := exp_testbit (exp_var "i") 3 in
    let: "SSI" := exp_testbit (exp_var "i") 1 in
    let: "USI" := exp_testbit (exp_var "i") 0 in
    exp_record rminterrupts [exp_var "MEI"; exp_var "SEI"; exp_var "UEI"; exp_var "MTI"; exp_var "STI"; exp_var "UTI"; exp_var "MSI"; exp_var "SSI"; exp_var "USI"].

  Definition fun_Medeleg_from_bits : Stm ["i" ∷ ty_xlenbits] ty_Medeleg :=
      let: "SAMO_Page_Fault"    := exp_testbit (exp_var "i") 15 in
      let: "Load_Page_Fault"    := exp_testbit (exp_var "i") 13 in
      let: "Fetch_Page_Fault"   := exp_testbit (exp_var "i") 12 in
      let: "MEnvCall"           := exp_testbit (exp_var "i") 10 in
      let: "SEnvCall"           := exp_testbit (exp_var "i") 9 in
      let: "UEnvCall"           := exp_testbit (exp_var "i") 8 in
      let: "SAMO_Access_Fault"  := exp_testbit (exp_var "i") 7 in
      let: "SAMO_Addr_Align"    := exp_testbit (exp_var "i") 6 in
      let: "Load_Access_Fault"  := exp_testbit (exp_var "i") 5 in
      let: "Load_Addr_Align"    := exp_testbit (exp_var "i") 4 in
      let: "Breakpoint"         := exp_testbit (exp_var "i") 3 in
      let: "Illegal_Instr"      := exp_testbit (exp_var "i") 2 in
      let: "Fetch_Access_Fault" := exp_testbit (exp_var "i") 1 in
      let: "Fetch_Addr_Align"   := exp_testbit (exp_var "i") 0 in
      exp_record rmedeleg [ exp_var "SAMO_Page_Fault"
                          ; exp_var "Load_Page_Fault"
                          ; exp_var "Fetch_Page_Fault"
                          ; exp_var "MEnvCall"
                          ; exp_var "SEnvCall"
                          ; exp_var "UEnvCall"
                          ; exp_var "SAMO_Access_Fault"
                          ; exp_var "SAMO_Addr_Align"
                          ; exp_var "Load_Access_Fault"
                          ; exp_var "Load_Addr_Align"
                          ; exp_var "Breakpoint"
                          ; exp_var "Illegal_Instr"
                          ; exp_var "Fetch_Access_Fault"
                          ; exp_var "Fetch_Addr_Align"
                          ].

  Notation "x '|bv|' y" := (exp_binop bop.bvor x y)
      (at level 60) : exp_scope.
  Definition stm_pmpcfg_ent_to_bits {Γ} (cfgent : Stm Γ ty_pmpcfg_ent) : Stm Γ ty_byte :=
    let: "cfgent" := cfgent in
    match: exp_var "cfgent" in rpmpcfg_ent with
      ["L";"A";"X";"W";"R"] =>
      let: "L'" := if: exp_var "L"
                   then exp_val ty_byte [bv (N.shiftl 1 7)]
                   else exp_val ty_byte [bv 0] in
      let: "A'" := match: A in pmpaddrmatchtype with
                   | OFF => exp_val ty_byte [bv (N.shiftl 0 3)]
                   | TOR => exp_val ty_byte [bv (N.shiftl 1 3)]
                   end in
      let: "X'" := if: exp_var "X" then exp_val ty_byte [bv (N.shiftl 1 2)] else exp_val ty_byte [bv 0] in
      let: "W'" := if: exp_var "W" then exp_val ty_byte [bv (N.shiftl 1 1)] else exp_val ty_byte [bv 0] in
      let: "R'" := if: exp_var "R" then exp_val ty_byte [bv (N.shiftl 1 0)] else exp_val ty_byte [bv 0] in
      exp_var "L'" |bv| exp_var "A'" |bv| exp_var "X'" |bv| exp_var "W'" |bv| exp_var "R'"
    end.

  (** Functions **)
  Import Bitvector.bv.notations.
  Definition fun_rX : Stm [rs ∷ ty_regno] ty_xlenbits :=
    use lemma open_gprs ;;
    let: v := match: rs in bvec 5 with
              | 00000 => exp_val ty_xlenbits [bv 0]
              | 00001 => stm_read_register x1
              | 00010 => stm_read_register x2
              | 00011 => stm_read_register x3
              | 00100 => stm_read_register x4
              | 00101 => stm_read_register x5
              | 00110 => stm_read_register x6
              | 00111 => stm_read_register x7
              | 01000 => stm_read_register x8
              | 01001 => stm_read_register x9
              | 01010 => stm_read_register x10
              | 01011 => stm_read_register x11
              | 01100 => stm_read_register x12
              | 01101 => stm_read_register x13
              | 01110 => stm_read_register x14
              | 01111 => stm_read_register x15
              | 10000 => stm_read_register x16
              | 10001 => stm_read_register x17
              | 10010 => stm_read_register x18
              | 10011 => stm_read_register x19
              | 10100 => stm_read_register x20
              | 10101 => stm_read_register x21
              | 10110 => stm_read_register x22
              | 10111 => stm_read_register x23
              | 11000 => stm_read_register x24
              | 11001 => stm_read_register x25
              | 11010 => stm_read_register x26
              | 11011 => stm_read_register x27
              | 11100 => stm_read_register x28
              | 11101 => stm_read_register x29
              | 11110 => stm_read_register x30
              | 11111 => stm_read_register x31
              end in
    use lemma close_gprs ;;
    v.

  Definition fun_wX : Stm [rd ∷ ty_regno; v ∷ ty_xlenbits] ty.unit :=
    use lemma open_gprs ;;
    match: rd in bvec 5 with
    | 00000 => exp_val ty_xlenbits [bv 0]
    | 00001 => stm_write_register x1 v
    | 00010 => stm_write_register x2 v
    | 00011 => stm_write_register x3 v
    | 00100 => stm_write_register x4 v
    | 00101 => stm_write_register x5 v
    | 00110 => stm_write_register x6 v
    | 00111 => stm_write_register x7 v
    | 01000 => stm_write_register x8 v
    | 01001 => stm_write_register x9 v
    | 01010 => stm_write_register x10 v
    | 01011 => stm_write_register x11 v
    | 01100 => stm_write_register x12 v
    | 01101 => stm_write_register x13 v
    | 01110 => stm_write_register x14 v
    | 01111 => stm_write_register x15 v
    | 10000 => stm_write_register x16 v
    | 10001 => stm_write_register x17 v
    | 10010 => stm_write_register x18 v
    | 10011 => stm_write_register x19 v
    | 10100 => stm_write_register x20 v
    | 10101 => stm_write_register x21 v
    | 10110 => stm_write_register x22 v
    | 10111 => stm_write_register x23 v
    | 11000 => stm_write_register x24 v
    | 11001 => stm_write_register x25 v
    | 11010 => stm_write_register x26 v
    | 11011 => stm_write_register x27 v
    | 11100 => stm_write_register x28 v
    | 11101 => stm_write_register x29 v
    | 11110 => stm_write_register x30 v
    | 11111 => stm_write_register x31 v
    end ;;
    use lemma close_gprs.

  Definition fun_bool_to_bits : Stm ["x" :: ty.bool] (ty.bvec 1) :=
    if: exp_var "x"
    then exp_val (ty.bvec 1) Bitvector.bv.one
    else exp_val (ty.bvec 1) Bitvector.bv.zero.

  Definition fun_shift_right_arith32 : Stm [v :: ty.bvec 32; "shift" :: ty.bvec 5] (ty.bvec 32) :=
    let: "v64" :: ty.bvec 64 := exp_sext v in
    let: tmp := exp_binop bop.shiftr (exp_var "v64") (exp_var "shift") in
    exp_vector_subrange 0 32 tmp.

  Definition fun_extend_value (bytes : nat) {pr : IsTrue (width_constraint bytes)} : Stm [is_unsigned :: ty.bool; value :: ty_memory_op_result bytes] (ty_memory_op_result xlenbytes) :=
    match: value in union (memory_op_result bytes) with
    |> KMemValue (pat_var "result") =>
      let: tmp := if: is_unsigned
                  then exp_unop (@uop.zext _ (bytes * byte) (xlenbytes * byte) _) result
                  else exp_unop (@uop.sext _ (bytes * byte) (xlenbytes * byte) _) result in
      stm_exp (exp_union (memory_op_result xlenbytes) KMemValue tmp)
    |> KMemException (pat_var "e")  =>
      stm_exp (exp_union (memory_op_result xlenbytes) KMemException (exp_var "e"))
    end.

  Definition fun_get_arch_pc : Stm ctx.nil ty_xlenbits :=
    stm_read_register pc.

  Definition fun_get_next_pc : Stm ctx.nil ty_xlenbits :=
    stm_read_register nextpc.

  Definition fun_set_next_pc : Stm [addr ∷ ty_xlenbits] ty.unit :=
    stm_write_register nextpc addr ;;
    stm_val ty.unit tt.

  Definition fun_tick_pc : Stm ctx.nil ty.unit :=
    let: tmp := stm_read_register nextpc in
    stm_write_register pc tmp ;;
    stm_val ty.unit tt.

  Definition fun_to_bits (l : nat) : Stm [value :: ty.int] (ty.bvec l) :=
    exp_get_slice_int value.

  Definition fun_abs : Stm [v ∷ ty.int] ty.int :=
    if: v < exp_int 0
    then v * exp_int (-1)
    else v.

  Definition fun_within_phys_mem : Stm [paddr :: ty_xlenbits; width :: ty.int] ty.bool :=
    let: addr_int := exp_unsigned paddr in
    ((exp_int (Z.of_N minAddr) <= addr_int)%exp && (addr_int + width <= exp_int (Z.of_N maxAddr)))%exp.

  (* TODO: it is currently possible to read/write from/to a mix of MMIO and non-MMIO memory! We can ignore this for now, since we avoid this situation in our examples.
     Concretely, trusted code reads/writes are aligned manually, and untrusted read/writes will never gain access to MMIO regions.
     It is worth keeping in mind, as the sail model does perform this check (under certain conditions) in `mem_[read/write_value]_priv_meta`. *)
  Definition fun_mem_read (bytes : nat) {H : restrict_bytes bytes} : Stm [typ ∷ ty_access_type; paddr ∷ ty_xlenbits] (ty_memory_op_result bytes) :=
    let: tmp := stm_read_register cur_privilege in
    stm_call (@pmp_mem_read bytes H) [typ; tmp; paddr].

  Definition fun_checked_mem_read (bytes : nat) {H : restrict_bytes bytes} : Stm [t ∷ ty_access_type; paddr ∷ ty_xlenbits] (ty_memory_op_result bytes) :=
    let: tmp := stm_foreign (within_mmio H) [paddr] in
    if: tmp
    then
      let: tmp := stm_foreign (mmio_read H) [paddr] in
      stm_exp (exp_union (memory_op_result bytes) KMemValue tmp)
    else
      let: tmp := call within_phys_mem paddr (exp_int (Z.of_nat bytes)) in
      if: tmp
      then (use lemma (extract_pmp_ptsto bytes) [paddr] ;;
            let: tmp := stm_foreign (read_ram bytes) [paddr] in
            use lemma (return_pmp_ptsto bytes) [paddr] ;;
            stm_exp (exp_union (memory_op_result bytes) KMemValue tmp))
      else match: t in union access_type with
          |> KRead pat_unit      =>
              stm_exp (exp_union (memory_op_result bytes) KMemException E_Load_Access_Fault)
          |> KWrite pat_unit     =>
              stm_exp (exp_union (memory_op_result bytes) KMemException E_SAMO_Access_Fault)
          |> KReadWrite pat_unit =>
              stm_exp (exp_union (memory_op_result bytes) KMemException E_SAMO_Access_Fault)
          |> KExecute pat_unit   =>
              stm_exp (exp_union (memory_op_result bytes) KMemException E_Fetch_Access_Fault)
          end.

  (* NOTE: normally the return values of both `write_ram` and `mmio_write` should be wrapped in MemValue but this constructor is currently restricted to bytes and write_ram *ALWAYS* returns true, so we just return a byte representation of 1 *)
  Definition fun_checked_mem_write (bytes : nat) {H : restrict_bytes bytes} : Stm [paddr ∷ ty_xlenbits; data :: ty_bytes bytes] (ty_memory_op_result 1) :=
    let: tmp := stm_foreign (within_mmio H) [paddr] in
    if: tmp
    then
      let: tmp := stm_foreign (mmio_write H) [paddr; data] in
      stm_exp (exp_union (memory_op_result 1) KMemValue (exp_val ty_byte [bv 1]))
    else
      let: tmp := call within_phys_mem paddr (exp_int (Z.of_nat bytes)) in
      if: tmp
      then (use lemma (extract_pmp_ptsto bytes) [paddr] ;;
            stm_foreign (write_ram bytes) [paddr; data] ;;
            use lemma (return_pmp_ptsto bytes) [paddr] ;;
            stm_exp (exp_union (memory_op_result 1) KMemValue (exp_val ty_byte [bv 1])))
      else
        stm_exp (exp_union (memory_op_result 1) KMemException E_SAMO_Access_Fault).

  (* NOTE: One might think it more elegant to have a universal contract for each individual PMP location (saying the location is either MMIO/RAM/out of range), and extract that after passing the PMP check. This would allow simplifying the contract of `checked_mem_read/write`. Morally, those contracts should not mention PMP, since they are only ever called after the PMP checks succeed. This would also allow us to remove the PMP stuff from the contract of `within_MMIO`. *)
  (* HOWEVER, the Sail model does not check for overflow as part of the PMP checks; this only happens later, when checking whether an address is an MMIO/RAM/... address. Hence, it would complicate lemma's to extract this pointer early, as the extracted pointer might not be contiguous in memory... *)
  Definition fun_pmp_mem_read (bytes : nat) {H : restrict_bytes bytes} : Stm [t∷ ty_access_type; p ∷ ty_privilege; paddr ∷ ty_xlenbits] (ty_memory_op_result bytes) :=
    let: tmp := stm_call (@pmpCheck bytes H) [paddr; t; p] in
    match: tmp with
    | inl e => stm_exp (exp_union (memory_op_result bytes) KMemException e)
    | inr v => stm_call (@checked_mem_read bytes H) [t; paddr]
    end.

  Definition fun_pmp_mem_write (bytes : nat) {H : restrict_bytes bytes} : Stm [paddr ∷ ty_xlenbits; data ∷ ty_bytes bytes; typ ∷ ty_access_type; priv ∷ ty_privilege] (ty_memory_op_result 1) :=
    let: tmp := stm_call (@pmpCheck bytes H) [paddr; typ; priv] in
    match: tmp with
    | inl e => stm_exp (exp_union (memory_op_result 1) KMemException e)
    | inr v => stm_call (@checked_mem_write bytes H) [paddr; data]
    end.

  Definition fun_pmpLocked : Stm [cfg ∷ ty_pmpcfg_ent] ty.bool :=
    match: cfg in rpmpcfg_ent with [L; A; X; W; R] => L end.

  Definition fun_pmpWriteCfgReg : Stm ["n" :: ty.int; value :: ty_xlenbits] ty.unit :=
    if: exp_var "n" = exp_int 0%Z
    then
      let: tmp  := stm_read_register pmp0cfg in
      let: tmp1 := exp_vector_subrange 0 8 value in
      let: tmp2 := call pmpWriteCfg tmp tmp1 in
      stm_write_register pmp0cfg tmp2 ;;
      let: tmp  := stm_read_register pmp1cfg in
      let: tmp1 := exp_vector_subrange 8 8 value in
      let: tmp2 := call pmpWriteCfg tmp tmp1 in
      stm_write_register pmp1cfg tmp2 ;;
      stm_val ty.unit tt
    else fail "writing to non-existent cfg".

  Definition fun_pmpWriteCfg : Stm [cfg :: ty_pmpcfg_ent; value :: ty_byte] ty_pmpcfg_ent :=
    let: locked := call pmpLocked cfg in
    if: locked then cfg else stm_pmpcfg_ent_from_bits value.

  Definition fun_pmpWriteAddr : Stm [locked :: ty.bool; addr :: ty_xlenbits; value :: ty_xlenbits] ty_xlenbits :=
    if: locked then addr else value.

  Definition fun_pmpCheck (bytes : nat) {H : restrict_bytes bytes} : Stm [addr ∷ ty_xlenbits; acc ∷ ty_access_type; priv ∷ ty_privilege] (ty.option ty_exception_type) :=
    use lemma open_pmp_entries ;;
    let: "width" :: ty_xlenbits := stm_call (to_bits xlen) [exp_val ty.int (Z.of_nat bytes)] in
    let: check%string :=
      let: tmp1 := stm_read_register pmp0cfg in
      let: tmp2 := stm_read_register pmpaddr0 in
      let: tmp3 := exp_val ty_xlenbits [bv 0] in
      let: tmp := call pmpMatchEntry addr width acc priv tmp1 tmp2 tmp3 in
      match: tmp in pmpmatch with
      | PMP_Success  => stm_val ty.bool true
      | PMP_Fail     => stm_val ty.bool false
      | PMP_Continue =>
      let: tmp1 := stm_read_register pmp1cfg in
      let: tmp2 := stm_read_register pmpaddr1 in
      let: tmp3 := stm_read_register pmpaddr0 in
      let: tmp := call pmpMatchEntry addr width acc priv tmp1 tmp2 tmp3 in
      match: tmp in pmpmatch with
      | PMP_Success  => stm_val ty.bool true
      | PMP_Fail     => stm_val ty.bool false
      | PMP_Continue =>
          match: priv in privilege with
          | Machine    => stm_val ty.bool true
          | Supervisor => stm_val ty.bool false
          | User       => stm_val ty.bool false
          end
      end
      end in
      use lemma close_pmp_entries ;;
      if: check
      then None
      else
        match: acc in union access_type with
        |> KRead pat_unit      => stm_exp (Some E_Load_Access_Fault)
        |> KWrite pat_unit     => stm_exp (Some E_SAMO_Access_Fault)
        |> KReadWrite pat_unit => stm_exp (Some E_SAMO_Access_Fault)
        |> KExecute pat_unit   => stm_exp (Some E_Fetch_Access_Fault)
        end.

  Definition fun_pmpCheckPerms : Stm [ent ∷ ty_pmpcfg_ent; acc ∷ ty_access_type; priv ∷ ty_privilege] ty.bool :=
    match: priv in privilege with
    | Machine =>
      let: tmp := call pmpLocked ent in
      if: tmp
      then call pmpCheckRWX ent acc
      else stm_val ty.bool true
    | Supervisor =>
      call pmpCheckRWX ent acc
    | User =>
      call pmpCheckRWX ent acc
    end.

  Definition fun_pmpCheckRWX : Stm [ent ∷ ty_pmpcfg_ent; acc ∷ ty_access_type] ty.bool :=
    match: ent in rpmpcfg_ent with
      [L; A; X; W; R] =>
        match: acc in union access_type with
        |> KRead pat_unit      => if: R then stm_val ty.bool true else stm_val ty.bool false
        |> KWrite pat_unit     => if: W then stm_val ty.bool true else stm_val ty.bool false
        |> KReadWrite pat_unit => if: R && W then stm_val ty.bool true else stm_val ty.bool false
        |> KExecute pat_unit   => if: X then stm_val ty.bool true else stm_val ty.bool false
        end
    end.

  Definition fun_pmpMatchEntry : Stm [addr ∷ ty_xlenbits; width :: ty_xlenbits; acc ∷ ty_access_type; priv ∷ ty_privilege; ent ∷ ty_pmpcfg_ent; pmpaddr ∷ ty_xlenbits; prev_pmpaddr ∷ ty_xlenbits] ty_pmpmatch :=
    let: rng := call pmpAddrRange ent pmpaddr prev_pmpaddr in
    let: tmp := call pmpMatchAddr addr width rng in
    match: tmp in pmpaddrmatch with
    | PMP_NoMatch      => exp_val ty_pmpmatch PMP_Continue
    | PMP_PartialMatch => exp_val ty_pmpmatch PMP_Fail
    | PMP_Match        =>
      let: tmp := call pmpCheckPerms ent acc priv in
      if: tmp
      then exp_val ty_pmpmatch PMP_Success
      else exp_val ty_pmpmatch PMP_Fail
    end.

  Definition fun_pmpAddrRange : Stm [cfg ∷ ty_pmpcfg_ent; pmpaddr ∷ ty_xlenbits; prev_pmpaddr ∷ ty_xlenbits] ty_pmp_addr_range :=
    match: cfg in rpmpcfg_ent with
      [L; A; X; W; R] =>
        match: A in pmpaddrmatchtype with
        | OFF => None
        | TOR => Some (exp_binop bop.pair prev_pmpaddr pmpaddr)
        end
    end.

  Definition fun_pmpMatchAddr : Stm [addr ∷ ty_xlenbits; width :: ty_xlenbits; rng ∷ ty_pmp_addr_range] ty_pmpaddrmatch :=
    match: rng with
    | inl v =>
      match: v in (ty_xlenbits , ty_xlenbits) with
      | (lo , hi) =>
        if: hi <ᵘ lo
        then exp_val ty_pmpaddrmatch PMP_NoMatch
        else
          if: (exp_binop bop.bvadd addr width <=ᵘ lo) || (hi <=ᵘ addr)
          then exp_val ty_pmpaddrmatch PMP_NoMatch
          else if: (lo <=ᵘ addr) && (exp_binop bop.bvadd addr width <=ᵘ hi)
               then exp_val ty_pmpaddrmatch PMP_Match
               else exp_val ty_pmpaddrmatch PMP_PartialMatch
      end
    | inr v => exp_val ty_pmpaddrmatch PMP_NoMatch
    end.

  Definition fun_process_load (bytes : nat) {pr : IsTrue (width_constraint bytes)} : Stm [rd ∷ ty_regno; vaddr ∷ ty_xlenbits; value ∷ (ty_memory_op_result bytes); is_unsigned :: ty.bool] ty_retired :=
    let: tmp := stm_call (@extend_value _ pr) [is_unsigned; value] in
    match: tmp in union (memory_op_result xlenbytes) with
    |> KMemValue (pat_var "result") =>
        call wX rd result ;;
        stm_val ty_retired RETIRE_SUCCESS
    |> KMemException (pat_var "e")  => call handle_mem_exception vaddr e;;
                                       stm_val ty_retired RETIRE_FAIL
    end.

  Definition fun_mem_write_value (bytes : nat) {H : restrict_bytes bytes} : Stm [paddr ∷ ty_xlenbits; value ∷ ty_bytes bytes] (ty_memory_op_result 1) :=
    let: tmp1 := Write in
    let: tmp2 := stm_read_register cur_privilege in
    stm_call (@pmp_mem_write bytes H) [paddr; value; tmp1; tmp2].

  Definition fun_main : Stm ctx.nil ty.unit :=
    call init_model ;;
    call loop.

  (* NOTE: simplified init_model function, just calls init_sys which just calls
           init_pmp *)
  Definition fun_init_model : Stm ctx.nil ty.unit :=
    call init_sys.

  Definition fun_loop : Stm ctx.nil ty.unit :=
    let: "on" := stm_foreign powered_on [env] in
    if: exp_var "on"
    then call step ;; call loop
    else stm_val ty.unit tt.

  Definition fun_fetch : Stm ctx.nil ty_fetch_result :=
    let: tmp1 := Execute in
    let: tmp := stm_read_register pc in
    use lemma open_ptsto_instr [tmp];;
    let: tmp2 := stm_call (@mem_read 4%nat restrict_bytes_four) [tmp1; tmp] in
    match: tmp2 in union (memory_op_result 4) with
    |> KMemValue (pat_var "result") =>
      use lemma close_ptsto_instr [tmp; exp_var "result"];;
      stm_exp (F_Base result)
    |> KMemException (pat_var "e")  => stm_exp (F_Error e tmp)
    end.

  Definition fun_step : Stm ctx.nil ty.unit :=
    (* Allow the external world to update certain architectural state, particularly the mip (interrupts pending) CSR. *)
    stm_foreign externalWorldUpdates [env] ;;
    let: p := stm_read_register cur_privilege in
    let: "di" := call dispatchInterrupt p in
    match: exp_var "di" with
    | inl "intrpriv" =>
        match: exp_var "intrpriv" in ( ty_interruptType , ty_privilege ) with
        | ( "intr" , "priv" ) =>
            call handle_interrupt (exp_var "intr") (exp_var "priv") ;;
            stm_val ty_retired RETIRE_FAIL
        end
    | inr "unit" =>
        let: f := call fetch in
        match: f in union fetch_result with
        |> KF_Base (pat_var "w") =>  let: "ast" := foreign decode w in
                                     let: tmp := stm_read_register pc in
                                     stm_write_register nextpc (tmp +ᵇ exp_val ty_xlenbits [bv 4]) ;;
                                     call execute (exp_var "ast")
        |> KF_Error (pat_pair "e" "addr") => call handle_mem_exception addr e ;;
                                             stm_val ty_retired RETIRE_FAIL
        end
    end ;;
    call tick_pc.

  Definition fun_init_sys : Stm ctx.nil ty.unit :=
    stm_write_register cur_privilege (exp_val ty_privilege Machine) ;;
    use lemma open_pmp_entries ;;
    call init_pmp ;;
    use lemma close_pmp_entries.

  Definition fun_init_pmp : Stm ctx.nil ty.unit :=
    let: tmp := stm_read_register pmp0cfg in
    match: tmp in rpmpcfg_ent with
      ["L"; "A"; "X"; "W"; "R"] =>
        stm_write_register
          pmp0cfg (exp_record rpmpcfg_ent
                              [nenv L;
                               exp_val ty_pmpaddrmatchtype OFF;
                               X;
                               W;
                               R ]) ;;
        stm_val ty.unit tt
    end ;;
    let: tmp := stm_read_register pmp1cfg in
    match: tmp in rpmpcfg_ent with
      ["L"; "A"; "X"; "W"; "R"] =>
        stm_write_register
          pmp1cfg (exp_record rpmpcfg_ent
                              [nenv L;
                               exp_val ty_pmpaddrmatchtype OFF;
                               X;
                               W;
                               R ]) ;;
        stm_val ty.unit tt
    end.

  Definition fun_exceptionType_to_bits : Stm [e ∷ ty_exception_type] ty_exc_code :=
    match: e in union exception_type with
    |> KE_Fetch_Addr_Align pat_unit   => stm_val ty_exc_code [bv 0x00]
    |> KE_Fetch_Access_Fault pat_unit => stm_val ty_exc_code [bv 0x01]
    |> KE_Illegal_Instr pat_unit      => stm_val ty_exc_code [bv 0x02]
    |> KE_Breakpoint pat_unit         => stm_val ty_exc_code [bv 0x03]
    |> KE_Load_Addr_Align pat_unit    => stm_val ty_exc_code [bv 0x04]
    |> KE_Load_Access_Fault pat_unit  => stm_val ty_exc_code [bv 0x05]
    |> KE_SAMO_Addr_Align pat_unit    => stm_val ty_exc_code [bv 0x06]
    |> KE_SAMO_Access_Fault pat_unit  => stm_val ty_exc_code [bv 0x07]
    |> KE_U_EnvCall pat_unit          => stm_val ty_exc_code [bv 0x08]
    |> KE_S_EnvCall pat_unit          => stm_val ty_exc_code [bv 0x09]
    |> KE_Reserved_10 pat_unit        => stm_val ty_exc_code [bv 0x0a]
    |> KE_M_EnvCall pat_unit          => stm_val ty_exc_code [bv 0x0b]
    |> KE_Fetch_Page_Fault pat_unit   => stm_val ty_exc_code [bv 0x0c]
    |> KE_Load_Page_Fault pat_unit    => stm_val ty_exc_code [bv 0x0d]
    |> KE_Reserved_14 pat_unit        => stm_val ty_exc_code [bv 0x0e]
    |> KE_SAMO_Page_Fault pat_unit    => stm_val ty_exc_code [bv 0x0f]
    end.

  Definition fun_interruptType_to_bits : Stm ["i" ∷ ty_interruptType] ty_exc_code :=
    match: (exp_var "i") in interruptType with
    | I_U_Software => stm_val ty_exc_code [bv 0x00]
    | I_S_Software => stm_val ty_exc_code [bv 0x01]
    | I_M_Software => stm_val ty_exc_code [bv 0x03]
    | I_U_Timer => stm_val ty_exc_code [bv 0x04]
    | I_S_Timer => stm_val ty_exc_code [bv 0x05]
    | I_M_Timer => stm_val ty_exc_code [bv 0x07]
    | I_U_External => stm_val ty_exc_code [bv 0x08]
    | I_S_External => stm_val ty_exc_code [bv 0x09]
    | I_M_External => stm_val ty_exc_code [bv 0x0b]
    end.

  Definition fun_handle_mem_exception : Stm [addr ∷ ty_xlenbits; e ∷ ty_exception_type] ty.unit :=
    let: tmp1 := stm_read_register pc in
    let: tmp2 := stm_read_register cur_privilege in
    let: tmp3 := call exception_handler tmp2 (CTL_TRAP e) tmp1 in
    call set_next_pc tmp3.

  Definition fun_exception_handler : Stm [cur_priv ∷ ty_privilege; ctl ∷ ty_ctl_result; "pc" ∷ ty_xlenbits] ty_xlenbits :=
    match: ctl in union ctl_result with
    |> KCTL_TRAP (pat_var "e") => let: del_priv := call exception_delegatee e cur_priv in
                                  let: tmp := call exceptionType_to_bits e in
                                  call trap_handler del_priv (exp_val ty.bool false) tmp (exp_var "pc")
    |> KCTL_MRET pat_unit      =>
      (* NOTE: normally the return address is computed with:
               prepare_xret_target(Machine) & pc_alignment_mask()
               we drop the alignment mask and inline prepare_xret_target,
               which just calls get_xret_target, which returns (for M-mode)
               the value of mepc *)
      let: "tmp1" := stm_read_register mstatus in
      match: exp_var "tmp1" in rmstatus with
        ["MPP"; "SPP"; "MPIE"; "SPIE"; "MIE"; "SIE"] =>
          stm_write_register cur_privilege (exp_var "MPP") ;;
          (* if   cur_privilege != Machine *)
          (* then mstatus->MPRV() = 0b0; *)
          stm_write_register mstatus
            (exp_record rmstatus ([nenv exp_val ty_privilege User; exp_var "SPP"; exp_val ty.bool true; exp_var "SPIE"; exp_var (σ := ty.bool) "MPIE"; exp_var "SIE" ]
                                   )) ;;
          stm_read_register mepc
      end
    |> KCTL_SRET pat_unit      =>
      let: "tmp1" := stm_read_register mstatus in
      match: exp_var "tmp1" in rmstatus with
        ["MPP"; "SPP"; "MPIE"; "SPIE"; "MIE"; "SIE"] =>
          if: exp_var "SPP" = exp_val ty_privilege Machine
          then fail "Invalid SPP value" (* Sail code uses 1 bit to represent SPP, being either User or Supervisor, i.e., Machine is an impossible case so we simply fail here. *)
          else
            stm_write_register cur_privilege (exp_var "SPP") ;;
            stm_write_register mstatus
              (exp_record rmstatus ([nenv exp_var "MPP"; exp_val ty_privilege User; exp_var "MPIE"; exp_val ty.bool true; exp_var "MIE"; exp_var "SPIE" ])) ;;
            stm_read_register sepc
      end
    end.

  (* Inline function to index a medeleg bitvector based on an exception type.
     The Sail codebase handles this slightly different, by converting the
     exception_type param ee into a number first and using that to index the
     bitvector. *)
  Definition stm_idx_medeleg {Γ : PCtx} (medeleg : Exp Γ ty_xlenbits) (ee : Exp Γ ty_exception_type) : Stm Γ ty.bool :=
    match: ee in union exception_type with
    |> KE_Fetch_Addr_Align pat_unit   => stm_exp (exp_testbit medeleg 0)
    |> KE_Fetch_Access_Fault pat_unit => stm_exp (exp_testbit medeleg 1)
    |> KE_Illegal_Instr pat_unit      => stm_exp (exp_testbit medeleg 2)
    |> KE_Breakpoint pat_unit         => stm_exp (exp_testbit medeleg 3)
    |> KE_Load_Addr_Align pat_unit    => stm_exp (exp_testbit medeleg 4)
    |> KE_Load_Access_Fault pat_unit  => stm_exp (exp_testbit medeleg 5)
    |> KE_SAMO_Addr_Align pat_unit    => stm_exp (exp_testbit medeleg 6)
    |> KE_SAMO_Access_Fault pat_unit  => stm_exp (exp_testbit medeleg 7)
    |> KE_U_EnvCall pat_unit          => stm_exp (exp_testbit medeleg 8)
    |> KE_S_EnvCall pat_unit          => stm_exp (exp_testbit medeleg 9)
    |> KE_Reserved_10 pat_unit        => stm_exp (exp_testbit medeleg 10)
    |> KE_M_EnvCall pat_unit          => stm_exp (exp_testbit medeleg 11)
    |> KE_Fetch_Page_Fault pat_unit   => stm_exp (exp_testbit medeleg 12)
    |> KE_Load_Page_Fault pat_unit    => stm_exp (exp_testbit medeleg 13)
    |> KE_Reserved_14 pat_unit        => stm_exp (exp_testbit medeleg 14)
    |> KE_SAMO_Page_Fault pat_unit    => stm_exp (exp_testbit medeleg 15)
    end.

  Definition fun_idx_medeleg_record : Stm ["i" ∷ ty_Medeleg; e ∷ ty_exception_type] ty.bool :=
    match: exp_var "i" in rmedeleg with
      [ "SAMO_Page_Fault"
      ; "Load_Page_Fault"
      ; "Fetch_Page_Fault"
      ; "MEnvCall"
      ; "SEnvCall"
      ; "UEnvCall"
      ; "SAMO_Access_Fault"
      ; "SAMO_Addr_Align"
      ; "Load_Access_Fault"
      ; "Load_Addr_Align"
      ; "Breakpoint"
      ; "Illegal_Instr"
      ; "Fetch_Access_Fault"
      ; "Fetch_Addr_Align"
      ] =>
        match: exp_var "e" in union exception_type with
        |> KE_Fetch_Addr_Align pat_unit   => stm_exp (exp_var "Fetch_Addr_Align")
        |> KE_Fetch_Access_Fault pat_unit => stm_exp (exp_var "Fetch_Access_Fault")
        |> KE_Illegal_Instr pat_unit      => stm_exp (exp_var "Illegal_Instr")
        |> KE_Breakpoint pat_unit         => stm_exp (exp_var "Breakpoint")
        |> KE_Load_Addr_Align pat_unit    => stm_exp (exp_var "Load_Addr_Align")
        |> KE_Load_Access_Fault pat_unit  => stm_exp (exp_var "Load_Access_Fault")
        |> KE_SAMO_Addr_Align pat_unit    => stm_exp (exp_var "SAMO_Addr_Align")
        |> KE_SAMO_Access_Fault pat_unit  => stm_exp (exp_var "SAMO_Access_Fault")
        |> KE_U_EnvCall pat_unit          => stm_exp (exp_var "UEnvCall")
        |> KE_S_EnvCall pat_unit          => stm_exp (exp_var "SEnvCall")
        |> KE_Reserved_10 pat_unit        => stm_exp (exp_val ty.bool false)
        |> KE_M_EnvCall pat_unit          => stm_exp (exp_var "MEnvCall")
        |> KE_Fetch_Page_Fault pat_unit   => stm_exp (exp_var "Fetch_Page_Fault")
        |> KE_Load_Page_Fault pat_unit    => stm_exp (exp_var "Load_Page_Fault")
        |> KE_Reserved_14 pat_unit        => stm_exp (exp_val ty.bool false)
        |> KE_SAMO_Page_Fault pat_unit    => stm_exp (exp_var "SAMO_Page_Fault")
      end
    end.
      

  Definition fun_exception_delegatee : Stm [e ∷ ty_exception_type; p ∷ ty_privilege] ty_privilege :=
    let: "medeleg_v" := stm_read_register medeleg in
    (* Normally we need to use the bitvector representation and index that with
       the number corresponding to the exception type e. We currently just index
       the record directly using pattern matches instead. *)
    (* let: "medeleg_bits" := call Medeleg_to_bits (exp_var "medeleg_v") in *)
    (* let: "super" := stm_idx_medeleg (exp_var "medeleg_bits") (exp_var "e") in *)
    let: "super" := call idx_medeleg_record (exp_var "medeleg_v") (exp_var "e") in
    let: "deleg" := if: exp_var "super"
                    then exp_val ty_privilege Supervisor
                    else exp_val ty_privilege Machine in
    let: "deleg_bits" := call privLevel_to_bits (exp_var "deleg") in
    let: "p_bits" := call privLevel_to_bits (exp_var "p") in
    let: tmp := exp_var "deleg_bits" <=ᵘ exp_var "p_bits" in
    if: tmp
    then exp_var "p"
    else exp_var "deleg".

  Definition fun_trap_handler : Stm [del_priv ∷ ty_privilege; "intr" ∷ ty.bool; c ∷ ty_exc_code; "pc" ∷ ty_xlenbits] ty_xlenbits :=
    match: del_priv in privilege with
    | Machine =>
      let: "intrb" := call bool_to_bits (exp_var "intr") in
      (* TODO: mcause[IsInterrupt] = bool_to_bits(intr); *)
      stm_write_register mcause (exp_zext c) ;;
      let: tmp := stm_read_register cur_privilege in
      let: "tmp1" := stm_read_register mstatus in
      match: exp_var "tmp1" in rmstatus with
        ["MPP"; "SPP"; "MPIE"; "SPIE"; "MIE"; "SIE"] =>
          stm_write_register mstatus (exp_record rmstatus ([nenv tmp; exp_var "SPP"; exp_var "MIE"; exp_var "SPIE"; exp_val ty.bool false; exp_var "SIE"]
            ))
      end ;;
      (* TODO: mtval           = tval(info); *)
      stm_write_register mepc (exp_var "pc") ;;
      stm_write_register cur_privilege del_priv ;;
      (* NOTE: the following let can be dropped by just reusing c (the value we are
             writing into mcause, but this (manual) translation is more faithful to
             what I expect an automatic translation would produce, i.e. do an
             stm_read_register when a register is used as param to a function call,
             to get the value in the register

             Also keep into account that the risc-v model trap handler function handles
             more cases than represented here, i.e. we only have support for M-mode and
             do not explicitly check for this here. So we could simplify
             prepare_trap_vector to not take a cause parameter (which it won't use
             anyway because we only support direct mode for the trap vector, meaning
             that the trap handler function installed at the memory address denoted
             by mtvec will need to read the mcause register to dispatch to the
             corresponding trap handler for the cause). *)
      let: tmp := stm_read_register mcause in
      call prepare_trap_vector del_priv tmp
    | Supervisor =>
      (* TODO: S-Mode (interrupts) *)
      let: "intrb" := call bool_to_bits (exp_var "intr") in
      (* TODO: mcause[IsInterrupt] = bool_to_bits(intr); *)
      stm_write_register scause (exp_zext c) ;;
      let: tmp := stm_read_register cur_privilege in
      let: "tmp_SPP" := match: tmp in privilege with
                        | Machine => fail "invalid privilege for s-mode trap"
                        | _       => tmp
                        end in
      let: "tmp1" := stm_read_register mstatus in
      match: exp_var "tmp1" in rmstatus with
        ["MPP"; "SPP"; "MPIE"; "SPIE"; "MIE"; "SIE"] =>
          stm_write_register mstatus (exp_record rmstatus ([nenv exp_var "MPP"; exp_var "tmp_SPP"; exp_var "MPIE"; exp_var "SIE"; exp_var "MIE"; exp_val ty.bool false]))
      end ;;
      (* TODO: stval           = tval(info); *)
      stm_write_register sepc (exp_var "pc") ;;
      stm_write_register cur_privilege del_priv ;;
      (* NOTE: the following let can be dropped by just reusing c (the value we are
             writing into mcause, but this (manual) translation is more faithful to
             what I expect an automatic translation would produce, i.e. do an
             stm_read_register when a register is used as param to a function call,
             to get the value in the register

             Also keep into account that the risc-v model trap handler function handles
             more cases than represented here, i.e. we only have support for M-mode and
             do not explicitly check for this here. So we could simplify
             prepare_trap_vector to not take a cause parameter (which it won't use
             anyway because we only support direct mode for the trap vector, meaning
             that the trap handler function installed at the memory address denoted
             by mtvec will need to read the mcause register to dispatch to the
             corresponding trap handler for the cause). *)
      let: tmp := stm_read_register scause in
      call prepare_trap_vector del_priv tmp
    | User =>
      stm_fail ty_xlenbits "trap_handler: Cannot delegate traps to User mode!"
    end.

  Definition fun_prepare_trap_vector : Stm [p ∷ ty_privilege; cause ∷ ty_mcause] ty_xlenbits :=
    let: tvec := match: p in privilege with
                 | Machine    => stm_read_register mtvec
                 | Supervisor => stm_read_register stvec
                 | User       => fail "N extension (user-level interrupts) not supported"
                 end in
    let: tmp := call tvec_addr tvec cause in
    (* NOTE: tvec_addr will only ever return Some(epc), because we don't support
             the 2 mode bits and only have direct mode. The None case only arises
             for the Reserved mode of trap vectors.

             The given privilege level (p) is ignored, this only makes sense when
             supervisor mode is supported. *)
    match: tmp with
    | inl epc => epc
    | inr e   => fail "Invalid tvec mode"
    end.

  Definition fun_tvec_addr : Stm [m ∷ ty_xlenbits; c ∷ ty_mcause] (ty.option ty_xlenbits) :=
    Some m.

  Definition fun_handle_illegal : Stm ctx.nil ty.unit :=
    let: t := E_Illegal_Instr in
    let: tmp1 := stm_read_register cur_privilege in
    let: tmp2 := stm_read_register pc in
    let: tmp3 := call exception_handler tmp1 (CTL_TRAP t) tmp2 in
    call set_next_pc tmp3.

  Definition fun_lower_mstatus : Stm [m ∷ ty_mstatus] ty_sstatus :=
    match: exp_var "m" in rmstatus with
      ["MPP"; "SPP"; "MPIE"; "SPIE"; "MIE"; "SIE"] =>
        exp_record rsstatus [ exp_var "SPP"; exp_var "SPIE"; exp_var "SIE" ]
    end.

  Definition fun_lower_mip : Stm [m :: ty_Minterrupts; "d" :: ty_Minterrupts] ty_Sinterrupts :=
    (* Instead of "and'ing" individual fields, we do it once for the entire
       Minterrupts records. *)
    let: "v" := call and_Minterrupts (exp_var "m") (exp_var "d") in
    match: exp_var "v" in rminterrupts with
        ["MEI";"SEI";"UEI";"MTI";"STI";"UTI";"MSI";"SSI";"USI"] =>
          stm_exp (exp_record rsinterrupts [nenv exp_var "SEI";
                                                 exp_var "UEI";
                                                 exp_var "STI";
                                                 exp_var "UTI";
                                                 exp_var "SSI";
                                                 exp_var "USI"])
    end.

  Definition fun_lower_mie : Stm [m :: ty_Minterrupts; "d" :: ty_Minterrupts] ty_Sinterrupts :=
    (* Instead of "and'ing" individual fields, we do it once for the entire
       Minterrupts records. *)
    let: "v" := call and_Minterrupts (exp_var "m") (exp_var "d") in
    match: exp_var "v" in rminterrupts with
        ["MEI";"SEI";"UEI";"MTI";"STI";"UTI";"MSI";"SSI";"USI"] =>
          stm_exp (exp_record rsinterrupts [nenv exp_var "SEI";
                                                 exp_var "UEI";
                                                 exp_var "STI";
                                                 exp_var "UTI";
                                                 exp_var "SSI";
                                                 exp_var "USI"])
    end.

  Definition fun_lift_sip : Stm [m :: ty_Minterrupts; "d" :: ty_Minterrupts; "s" :: ty_Sinterrupts] ty_Minterrupts :=
    match: exp_var "m" in rminterrupts with
      ["MEI";"SEI";"UEI";"MTI";"STI";"UTI";"MSI";"SSI";"USI"] =>
    match: exp_var "d" in rminterrupts with
      ["D_MEI";"D_SEI";"D_UEI";"D_MTI";"D_STI";"D_UTI";"D_MSI";"D_SSI";"D_USI"] =>
    match: exp_var "s" in rsinterrupts with
      ["S_SEI";"S_UEI";"S_STI";"S_UTI";"S_SSI";"S_USI"] =>
        if: exp_var "D_SSI"
        then stm_exp (exp_record rminterrupts [nenv exp_var "MEI";
                                                    exp_var "SEI";
                                                    exp_var "UEI";
                                                    exp_var "MTI";
                                                    exp_var "STI";
                                                    exp_var "UTI";
                                                    exp_var "MSI";
                                                    exp_var "S_SSI";
                                                    exp_var "USI"])
          else exp_var "m"
        end
      end
    end.

  Definition fun_legalize_sip : Stm [m :: ty_Minterrupts; "d" :: ty_Minterrupts; v :: ty_xlenbits] ty_Minterrupts :=
    let: "v" := stm_Sinterrupts_from_bits v in
    call lift_sip (exp_var "m") (exp_var "d") (exp_var "v").

  Definition fun_lift_sie : Stm [m :: ty_Minterrupts; "d" :: ty_Minterrupts; "s" :: ty_Sinterrupts] ty_Minterrupts :=
    match: exp_var "m" in rminterrupts with
      ["MEI";"SEI";"UEI";"MTI";"STI";"UTI";"MSI";"SSI";"USI"] =>
    match: exp_var "d" in rminterrupts with
      ["D_MEI";"D_SEI";"D_UEI";"D_MTI";"D_STI";"D_UTI";"D_MSI";"D_SSI";"D_USI"] =>
    match: exp_var "s" in rsinterrupts with
      ["S_SEI";"S_UEI";"S_STI";"S_UTI";"S_SSI";"S_USI"] =>
        let: "M_SEI" := if: exp_var "D_SEI" then exp_var "S_SEI" else exp_var "SEI" in
        let: "M_STI" := if: exp_var "D_STI" then exp_var "S_STI" else exp_var "STI" in
        let: "M_SSI" := if: exp_var "D_SSI" then exp_var "S_SSI" else exp_var "SSI" in
        stm_exp (exp_record rminterrupts [nenv exp_var "MEI";
                                               exp_var "M_SEI";
                                               exp_var "UEI";
                                               exp_var "MTI";
                                               exp_var "M_STI";
                                               exp_var "UTI";
                                               exp_var "MSI";
                                               exp_var "M_SSI";
                                               exp_var "USI"])
        end
      end
    end.

  Definition fun_legalize_sie : Stm [m :: ty_Minterrupts; "d" :: ty_Minterrupts; v :: ty_xlenbits] ty_Minterrupts :=
    let: "v" := stm_Sinterrupts_from_bits v in
    call lift_sie (exp_var "m") (exp_var "d") (exp_var "v").

  Definition fun_check_CSR : Stm [csr ∷ ty_csridx; p ∷ ty_privilege] ty.bool :=
    let: tmp1 := call is_CSR_defined csr p in
    let: tmp2 := call csrAccess csr in
    let: tmp3 := call csrPriv csr in
    let: tmp := call check_CSR_access tmp2 tmp3 p in
    tmp1 && tmp.

  Definition fun_is_CSR_defined : Stm [csr ∷ ty_csridx; p ∷ ty_privilege] ty.bool :=
    match: csr in csridx with
    | MStatus   => p = exp_val ty_privilege Machine
    | Mie       => p = exp_val ty_privilege Machine
    | Mip       => p = exp_val ty_privilege Machine
    | MTvec     => p = exp_val ty_privilege Machine
    | MScratch  => p = exp_val ty_privilege Machine
    | MEpc      => p = exp_val ty_privilege Machine
    | MCause    => p = exp_val ty_privilege Machine
    | Mideleg   => p = exp_val ty_privilege Machine
    | Medeleg   => p = exp_val ty_privilege Machine
    | MPMP0CFG  => p = exp_val ty_privilege Machine
    | MPMPADDR0 => p = exp_val ty_privilege Machine
    | MPMPADDR1 => p = exp_val ty_privilege Machine
    | SStatus   => (p = exp_val ty_privilege Machine) || (p = exp_val ty_privilege Supervisor)
    | STvec     => (p = exp_val ty_privilege Machine) || (p = exp_val ty_privilege Supervisor)
    | SScratch  => (p = exp_val ty_privilege Machine) || (p = exp_val ty_privilege Supervisor)
    | SEpc      => (p = exp_val ty_privilege Machine) || (p = exp_val ty_privilege Supervisor)
    | SCause    => (p = exp_val ty_privilege Machine) || (p = exp_val ty_privilege Supervisor)
    | Sip       => (p = exp_val ty_privilege Machine) || (p = exp_val ty_privilege Supervisor)
    | Sie       => (p = exp_val ty_privilege Machine) || (p = exp_val ty_privilege Supervisor)
    end.

  (* NOTE: for csrAccess and csrPriv, the access permissions and privilege that
           are associated with a CSR are gathered from a CSR index (a 12-bit
           vector), which we currently do not have (and use an enum directly). *)
  (* NOTE: currently just assuming everything is ReadWrite and reusing our
           existing access_type (Sail code uses a different type, csrRW here *)
  Definition fun_csrAccess : Stm [csr ∷ ty_csridx] ty_access_type :=
    ReadWrite.
  Definition fun_csrPriv : Stm [csr ∷ ty_csridx] ty_privilege :=
    match: csr in csridx with
    | MStatus   => exp_val ty_privilege Machine
    | Mie       => exp_val ty_privilege Machine
    | Mip       => exp_val ty_privilege Machine
    | MTvec     => exp_val ty_privilege Machine
    | MScratch  => exp_val ty_privilege Machine
    | MEpc      => exp_val ty_privilege Machine
    | MCause    => exp_val ty_privilege Machine
    | Mideleg   => exp_val ty_privilege Machine
    | Medeleg   => exp_val ty_privilege Machine
    | MPMP0CFG  => exp_val ty_privilege Machine
    | MPMPADDR0 => exp_val ty_privilege Machine
    | MPMPADDR1 => exp_val ty_privilege Machine
    | SStatus   => exp_val ty_privilege Supervisor
    | STvec     => exp_val ty_privilege Supervisor
    | SScratch  => exp_val ty_privilege Supervisor
    | SEpc      => exp_val ty_privilege Supervisor
    | SCause    => exp_val ty_privilege Supervisor
    | Sip       => exp_val ty_privilege Supervisor
    | Sie       => exp_val ty_privilege Supervisor
    end.

  Definition fun_check_CSR_access : Stm [csrrw ∷ ty_access_type; csrpr ∷ ty_privilege; p ∷ ty_privilege] ty.bool :=
    let: tmp1 := call privLevel_to_bits csrpr in
    let: tmp2 := call privLevel_to_bits p in
    tmp1 <=ᵘ tmp2.

  Definition fun_privLevel_to_bits : Stm [p ∷ ty_privilege] ty_priv_level :=
    match: p in privilege with
    | Machine    => stm_val ty_priv_level [bits 11]
    | Supervisor => stm_val ty_priv_level [bits 01]
    | User       => stm_val ty_priv_level [bits 00]
    end.

  Definition fun_readCSR : Stm [csr ∷ ty_csridx] ty_xlenbits :=
    match: csr in csridx with
    | MStatus   => stm_mstatus_to_bits (stm_read_register mstatus)
    | Mie       => let: value := stm_read_register mie in
                   call Minterrupts_to_bits value
    | Mip       => let: value := stm_read_register mip in
                   call Minterrupts_to_bits value
    | MTvec     => stm_read_register mtvec
    | MScratch  => stm_read_register mscratch
    | MEpc      => stm_read_register mepc
    | MCause    => stm_read_register mcause
    | Mideleg   => let: value := stm_read_register mideleg in
                   call Minterrupts_to_bits value
    | Medeleg   => let: value := stm_read_register medeleg in
                   call Medeleg_to_bits value
    | MPMP0CFG  =>
        let: tmp1 := stm_pmpcfg_ent_to_bits (stm_read_register pmp0cfg) in
        let: tmp2 := stm_pmpcfg_ent_to_bits (stm_read_register pmp1cfg) in
        exp_zext (exp_binop bop.bvapp tmp1 tmp2)
    | MPMPADDR0 => stm_read_register pmpaddr0
    | MPMPADDR1 => stm_read_register pmpaddr1
    | SStatus   => let: value := stm_read_register mstatus in
                   let: value := call lower_mstatus value in
                   stm_sstatus_to_bits value
    | STvec     => stm_read_register stvec
    | SScratch  => stm_read_register sscratch
    | SEpc      => stm_read_register sepc
    | SCause    => stm_read_register scause
    | Sip       => let: value := stm_read_register mip in
                   let: "mideleg" := stm_read_register mideleg in
                   let: value := call lower_mip value (exp_var "mideleg") in
                   stm_Sinterrupts_to_bits value
    | Sie       => let: value := stm_read_register mie in
                   let: "mideleg" := stm_read_register mideleg in
                   let: value := call lower_mie value (exp_var "mideleg") in
                   stm_Sinterrupts_to_bits value
    end.

  Definition fun_writeCSR : Stm [csr ∷ ty_csridx; value ∷ ty_xlenbits] ty.unit :=
    match: csr in csridx with
    | MStatus => let: tmp := stm_mstatus_from_bits value in
                 stm_write_register mstatus tmp ;;
                 stm_val ty.unit tt
    | Mie     => let: tmp := call Minterrupts_from_bits value in
                 stm_write_register mie tmp ;;
                 stm_val ty.unit tt
    | Mip     => let: tmp := call Minterrupts_from_bits value in
                 stm_write_register mip tmp ;;
                 stm_val ty.unit tt
    | MTvec => stm_write_register mtvec value ;;
               stm_val ty.unit tt
    | MScratch => stm_write_register mscratch value ;;
                  stm_val ty.unit tt
    | MEpc => stm_write_register mepc value ;;
              stm_val ty.unit tt
    | MCause => stm_write_register mcause value ;;
                stm_val ty.unit tt
    | Mideleg => let: tmp := call Minterrupts_from_bits value in
                 stm_write_register mideleg tmp ;;
                 stm_val ty.unit tt
    | Medeleg => let: tmp := call Medeleg_from_bits value in
                 stm_write_register medeleg tmp ;;
                 stm_val ty.unit tt
    | MPMP0CFG => stm_call pmpWriteCfgReg ([exp_int 0%Z : Exp _ (type (_∷ _)); value])
    | MPMPADDR0 => let: tmp1 := stm_read_register pmp0cfg in
                   let: tmp1 := call pmpLocked tmp1 in
                   let: tmp2 := stm_read_register pmpaddr0 in
                   let: tmp  := call pmpWriteAddr tmp1 tmp2 value in
                   stm_write_register pmpaddr0 tmp ;;
                   stm_val ty.unit tt
    | MPMPADDR1 => let: tmp1 := stm_read_register pmp1cfg in
                   let: tmp1 := call pmpLocked tmp1 in
                   let: tmp2 := stm_read_register pmpaddr1 in
                   let: tmp  := call pmpWriteAddr tmp1 tmp2 value in
                   stm_write_register pmpaddr1 value ;;
                   stm_val ty.unit tt
    | SStatus   => (* TODO: adhoc impl., normally some legalize functions are used, but in essence we currently can only overwrite SPP, so we pretty much inline the relevant code here *)
                   let: tmp := stm_sstatus_from_bits value in
                   let: m   := stm_read_register mstatus in
                   match: exp_var "m" in rmstatus with
                     ["MPP"; "SPP"; "MPIE"; "SPIE"; "MIE"; "SIE"] =>
                       match: exp_var "tmp" in rsstatus with
                         ["new_SPP"; "new_SIE"; "new_SPIE"] =>
                           stm_write_register mstatus (exp_record rmstatus [exp_var "MPP"; exp_var "new_SPP"; exp_var "MPIE"; exp_var "new_SPIE"; exp_var "MIE"; exp_var "new_SIE"])
                       end
                   end ;;
                   stm_val ty.unit tt
    | STvec     => stm_write_register stvec value ;;
                   stm_val ty.unit tt
    | SScratch  => stm_write_register sscratch value ;;
                   stm_val ty.unit tt
    | SEpc      => stm_write_register sepc value ;;
                   stm_val ty.unit tt
    | SCause    => stm_write_register scause value ;;
                   stm_val ty.unit tt
    | Sip       => let: "mip" := stm_read_register mip in
                   let: "mideleg" := stm_read_register mideleg in
                   let: "v" := call legalize_sip (exp_var "mip") (exp_var "mideleg") (exp_var "value") in
                   stm_write_register mip (exp_var "v") ;;
                   stm_val ty.unit tt
    | Sie       => let: "mie" := stm_read_register mie in
                   let: "mideleg" := stm_read_register mideleg in
                   let: "v" := call legalize_sie (exp_var "mie") (exp_var "mideleg") (exp_var "value") in
                   stm_write_register mie (exp_var "v") ;;
                   stm_val ty.unit tt
    end.

  Definition fun_and_Minterrupts : Stm ["ints1" ∷ ty_Minterrupts; "ints2" ∷ ty_Minterrupts] ty_Minterrupts :=
    match: exp_var "ints1" in rminterrupts with
        ["MEI1";"SEI1";"UEI1";"MTI1";"STI1";"UTI1"; "MSI1";"SSI1";"USI1"] =>
      match: exp_var "ints2" in rminterrupts with
        ["MEI2";"SEI2";"UEI2";"MTI2";"STI2";"UTI2";"MSI2";"SSI2";"USI2"] =>
        stm_exp (exp_record rminterrupts [nenv (exp_var "MEI1" && exp_var "MEI2"); (exp_var "SEI1" && exp_var "SEI2"); (exp_var "UEI1" && exp_var "UEI2"); (exp_var "MTI1" && exp_var "MTI2"); (exp_var "STI1" && exp_var "STI2"); (exp_var "UTI1" && exp_var "UTI2"); (exp_var "MSI1" && exp_var "MSI2"); (exp_var "SSI1" && exp_var "SSI2"); (exp_var "USI1" && exp_var "USI2")])
  end
       end.

  Definition stm_not_Minterrupts {Γ} (stm_v : Stm Γ ty_Minterrupts) : Stm Γ ty_Minterrupts :=
    let: "v" := stm_v in
    match: exp_var "v" in rminterrupts with
        ["MEI";"SEI";"UEI";"MTI";"STI";"UTI"; "MSI";"SSI";"USI"] =>
          stm_exp (exp_record rminterrupts [nenv exp_not (exp_var "MEI");
                                                 exp_not (exp_var "SEI");
                                                 exp_not (exp_var "UEI");
                                                 exp_not (exp_var "MTI");
                                                 exp_not (exp_var "STI");
                                                 exp_not (exp_var "UTI");
                                                 exp_not (exp_var "MSI");
                                                 exp_not (exp_var "SSI");
                                                 exp_not (exp_var "USI")])
    end.

  Definition fun_processPending : Stm ["xip" ∷ ty_Minterrupts; "xie" ∷ ty_Minterrupts; "xideleg" ∷ ty_Minterrupts; "priv_enabled" ∷ ty.bool] ty_interrupt_set :=
    let: "not_xideleg" := stm_not_Minterrupts (exp_var "xideleg") in
    let: "tmp" := stm_call and_Minterrupts [exp_var "xip"; exp_var "xie"] in
    let: "effective_pend" := stm_call and_Minterrupts [exp_var "tmp"; exp_var "not_xideleg"] in
    let: "effective_delg" := stm_call and_Minterrupts [exp_var "xip"; exp_var "xideleg"] in
    if: exp_var "priv_enabled" && (exp_var "effective_pend" != exp_val ty_Minterrupts Minterrupts_zero)
    then
      stm_exp (exp_union interrupt_set KInts_Pending (exp_var "effective_pend"))
    else if: exp_var "effective_delg" != exp_val ty_Minterrupts Minterrupts_zero
    then 
      stm_exp (exp_union interrupt_set KInts_Delegated (exp_var "effective_delg"))
    else stm_val ty_interrupt_set Ints_Empty.

  Definition fun_findPendingInterrupt : Stm ["ip" ∷ ty_Minterrupts] (ty.option ty_interruptType) :=
    match: exp_var "ip" in rminterrupts with
      ["MEI";"SEI";"UEI";"MTI";"STI";"UTI";"MSI";"SSI";"USI"] =>
        if: exp_var "MEI" then stm_val (ty.option ty_interruptType) (inl I_M_External)
        else if: exp_var "MSI" then stm_val (ty.option ty_interruptType) (inl I_M_Software)
        else if: exp_var "MTI" then stm_val (ty.option ty_interruptType) (inl I_M_Timer)
        else if: exp_var "SEI" then stm_val (ty.option ty_interruptType) (inl I_S_External)
        else if: exp_var "SSI" then stm_val (ty.option ty_interruptType) (inl I_S_Software)
        else if: exp_var "STI" then stm_val (ty.option ty_interruptType) (inl I_S_Timer)
        else if: exp_var "UEI" then stm_val (ty.option ty_interruptType) (inl I_U_External)
        else if: exp_var "USI" then stm_val (ty.option ty_interruptType) (inl I_U_Software)
        else if: exp_var "UTI" then stm_val (ty.option ty_interruptType) (inl I_U_Timer)
        else stm_val (ty.option ty_interruptType) (inr ())
    end.

  Definition fun_getPendingSet : Stm ["priv" ∷ ty_privilege] (ty.option (ty.prod ty_Minterrupts ty_privilege)) :=
      let: "mst" := stm_read_register mstatus in
    match: exp_var "mst" in rmstatus with
      ["MPP"; "SPP"; "MPIE"; "SPIE"; "MIE"; "SIE"] =>
        let: "mIE" := (exp_var "priv" != exp_val ty_privilege Machine) ||
                        ((exp_var "priv" = exp_val ty_privilege Machine) && exp_var "MIE") in
        let: "sIE" := (exp_var "priv" = exp_val ty_privilege User) ||
                        ((exp_var "priv" = exp_val ty_privilege Supervisor) && exp_var "SIE") in
        let: "mip" := stm_read_register mip in
        let: "mie" := stm_read_register mie in
        let: "mideleg" := stm_read_register mideleg in
        match: call processPending (exp_var "mip") (exp_var "mie") (exp_var "mideleg") (exp_var "mIE") in union interrupt_set with
        |> KInts_Empty pat_unit => stm_exp None
        |> KInts_Pending (pat_var "p") =>
             stm_exp (Some (exp_binop bop.pair (exp_var "p") (exp_val ty_privilege Machine)))
        |> KInts_Delegated (pat_var "p") =>
             match: call processPending (exp_var "p") (exp_var "mie") (exp_val ty_Minterrupts Minterrupts_zero) (exp_var "sIE") in union interrupt_set with
             |> KInts_Empty pat_unit => stm_exp None
             |> KInts_Pending (pat_var "p") =>
                  stm_exp (Some (exp_binop bop.pair (exp_var "p") (exp_val ty_privilege Supervisor)))
             |> KInts_Delegated (pat_var "p") => fail "N extension not supported"
             end
        end
    end.

  Definition fun_dispatchInterrupt : Stm ["priv" ∷ ty_privilege] (ty.option (ty.prod ty_interruptType ty_privilege)) :=
    match: call getPendingSet (exp_var "priv") with
    | inl "pset" => match: exp_var "pset" in (ty_Minterrupts , ty_privilege) with
                    | ("ip" , "p") =>
                        match: call findPendingInterrupt (exp_var "ip") with
                        | inl "i" => stm_exp (Some (exp_binop bop.pair (exp_var "i") (exp_var "p")))
                        | inr "u" => stm_val (ty.option (ty.prod ty_interruptType ty_privilege)) (inr ())
                        end
                    end
    | inr "u" => stm_val (ty.option (ty.prod ty_interruptType ty_privilege)) (inr ())
    end.

  Definition fun_handle_interrupt : Stm ["i" ∷ ty_interruptType; "del_priv" ∷ ty_privilege] ty.unit :=
    let: "pc" := stm_read_register pc in
    let: "ib" := call interruptType_to_bits (exp_var "i") in
    let: "npc" := call trap_handler (exp_var "del_priv") (exp_val ty.bool true) (exp_var "ib") (exp_var "pc") in
    stm_write_register nextpc (exp_var "npc");;
    stm_val ty.unit ().

  (* NOTE: normally the definitions of execute_X are inlined and defined as
           function clauses of execute (a scattered definition) *)
  Definition fun_execute : Stm ["ast" ∷ ty_ast] ty_retired :=
    match: exp_var "ast" in union ast with
    |> KRTYPE (pat_tuple (rs2 , rs1 , rd , op))                        => call execute_RTYPE rs2 rs1 rd op
    |> KITYPE (pat_tuple (imm , rs1 , rd , op))                        => call execute_ITYPE imm rs1 rd op
    |> KSHIFTIOP (pat_tuple (shamt , rs1 , rd , op))                   => call execute_SHIFTIOP shamt rs1 rd op
    |> KUTYPE (pat_tuple (imm , rd , op))                              => call execute_UTYPE imm rd op
    |> KBTYPE (pat_tuple (imm , rs2, rs1 , op))                        => call execute_BTYPE imm rs2 rs1 op
    |> KRISCV_JAL (pat_tuple (imm , rd))                               => call execute_RISCV_JAL imm rd
    |> KRISCV_JALR (pat_tuple (imm , rs1 , rd))                        => call execute_RISCV_JALR imm rs1 rd
    |> KLOAD (pat_tuple (imm , rs1, rd , is_unsigned , w))             => call execute_LOAD imm rs1 rd is_unsigned w
    |> KSTORE (pat_tuple (imm , rs2 , rs1 , w))                        => call execute_STORE imm rs2 rs1 w
    |> KECALL pat_unit                                                 => call execute_ECALL
    |> KEBREAK pat_unit                                                => call execute_EBREAK
    |> KSRET pat_unit                                                  => call execute_SRET
    |> KMRET pat_unit                                                  => call execute_MRET
    |> KCSR (pat_tuple (csr , rs1 , rd , is_imm , op))                 => call execute_CSR csr rs1 rd is_imm op
    |> KMUL (pat_tuple (rs2 , rs1 , rd , high , signed1 , signed2))    => call execute_MUL rs2 rs1 rd high signed1 signed2
    |> KILLEGAL (pat_var w)                                            => call execute_ILLEGAL w
    end.


  Definition fun_execute_MUL : Stm [rs2 :: ty_regno; rs1 ∷ ty_regno; rd ∷ ty_regno; high ∷ ty.bool; signed1 ∷ ty.bool; signed2 :: ty.bool] ty_retired :=
    (* TODO if haveMulDiv() | haveZmmul() then *)
    let tb := to_bits (2 * xlenbits) in
    let: rs1_val := call rX rs1 in
    let: rs2_val := call rX rs2 in
    let: rs1_int := if: signed1
                    then exp_unop uop.signed rs1_val
                    else exp_unop uop.unsigned rs1_val
    in
    let: rs2_int := if: signed2
                    then exp_unop uop.signed rs2_val
                    else exp_unop uop.unsigned rs2_val
    in
    let: result_wide := call tb (rs1_int * rs2_int) in
    let: result := if: high
                   then exp_vector_subrange xlen xlen result_wide
                   else exp_vector_subrange 0 xlen result_wide
    in
    call wX rd result ;;
    stm_val ty_retired RETIRE_SUCCESS.
  
  Definition fun_execute_RTYPE : Stm [rs2 ∷ ty_regno; rs1 ∷ ty_regno; rd ∷ ty_regno; op ∷ ty_rop] ty_retired :=
    let: rs1_val := call rX rs1 in
    let: rs2_val := call rX rs2 in
    let: result :=
       match: op in rop with
       | RISCV_ADD    => rs1_val +ᵇ rs2_val
       | RISCV_SLT    => let: tmp := rs1_val <ˢ rs2_val in
                         let: tmp := call bool_to_bits tmp in
                         exp_zext tmp
       | RISCV_SLTU   => let: tmp := rs1_val <ᵘ rs2_val in
                         let: tmp := call bool_to_bits tmp in
                         exp_zext tmp
       | RISCV_AND    => exp_binop bop.bvand rs1_val rs2_val
       | RISCV_OR     => exp_binop bop.bvor  rs1_val rs2_val
       | RISCV_XOR    => exp_binop bop.bvxor rs1_val rs2_val
       | RISCV_SLL    => let: tmp := exp_vector_subrange 0 5 rs2_val in
                         exp_binop bop.shiftl rs1_val tmp
       | RISCV_SRL    => let: tmp := exp_vector_subrange 0 5 rs2_val in
                         exp_binop bop.shiftr rs1_val tmp
       | RISCV_SUB    => rs1_val -ᵇ rs2_val
       | RISCV_SRA    => let: tmp := exp_vector_subrange 0 5 rs2_val in
                         call shift_right_arith32 rs1_val tmp
     end in
     call wX rd result ;;
     stm_val ty_retired RETIRE_SUCCESS.

   Definition fun_execute_ITYPE : Stm [imm ∷ ty.bvec 12; rs1 ∷ ty_regno; rd ∷ ty_regno; op ∷ ty_iop] ty_retired :=
    let: rs1_val := call rX rs1 in
    let: immext ∷ ty_xlenbits := exp_sext imm in
    let: result :=
       match: op in iop with
       | RISCV_ADDI  => rs1_val +ᵇ immext
       | RISCV_SLTI  => let: tmp := rs1_val <ˢ immext in
                        let: tmp := call bool_to_bits tmp in
                        exp_zext tmp
       | RISCV_SLTIU => let: tmp := rs1_val <ᵘ immext in
                        let: tmp := call bool_to_bits tmp in
                        exp_zext tmp
       | RISCV_ANDI  => exp_binop bop.bvand rs1_val immext
       | RISCV_ORI   => exp_binop bop.bvor  rs1_val immext
       | RISCV_XORI  => exp_binop bop.bvxor rs1_val immext
       end in
     call wX rd result ;;
     stm_val ty_retired RETIRE_SUCCESS.

  Definition fun_execute_SHIFTIOP : Stm [shamt :: ty.bvec 6; rs1 :: ty_regno; rd :: ty_regno; op :: ty_sop] ty_retired :=
    let: rs1_val := call rX rs1 in
    let: result :=
      match: op in sop with
      | RISCV_SLLI => let: tmp := exp_vector_subrange 0 5 shamt in
                      exp_binop bop.shiftl rs1_val tmp
      | RISCV_SRLI => let: tmp := exp_vector_subrange 0 5 shamt in
                      exp_binop bop.shiftr rs1_val tmp
      | RISCV_SRAI => let: tmp := exp_vector_subrange 0 5 shamt in
                      call shift_right_arith32 rs1_val tmp
      end in
    call wX rd result ;;
    stm_val ty_retired RETIRE_SUCCESS.

  Definition fun_execute_UTYPE : Stm [imm ∷ ty.bvec 20; rd ∷ ty_regno; op ∷ ty_uop] ty_retired :=
    (* NOTE: the sign extension only makes sense to support GPRs wider than 32 bits (i.e., 64-bit risc-v needs the sign extension) *)
    let: off ∷ ty_xlenbits := exp_sext (exp_binop bop.bvapp (exp_val (ty.bvec 12) Bitvector.bv.zero) imm) in
    let: ret :=
       match: op in uop with
       | RISCV_LUI   => off
       | RISCV_AUIPC =>
         let: tmp := call get_arch_pc in
         tmp +ᵇ off
       end in
    call wX rd ret ;;
    stm_val ty_retired RETIRE_SUCCESS.

  Definition fun_execute_RISCV_JAL : Stm [imm ∷ ty.bvec 21; rd ∷ ty_regno] ty_retired :=
    let: tmp := stm_read_register pc in
    let: t := tmp +ᵇ exp_sext imm in
    let: tmp := call get_next_pc in
    call wX rd tmp ;;
    call set_next_pc t ;;
    stm_val ty_retired RETIRE_SUCCESS.

  Definition fun_execute_RISCV_JALR : Stm [imm ∷ ty.bvec 12; rs1 ∷ ty_regno; rd ∷ ty_regno] ty_retired :=
    let: tmp := call rX rs1 in
    let: t := tmp +ᵇ exp_sext imm in
    let: tmp := call get_next_pc in
    call wX rd tmp ;;
    call set_next_pc t ;;
    stm_val ty_retired RETIRE_SUCCESS.

  Definition fun_execute_BTYPE : Stm [imm ∷ ty.bvec 13; rs2 ∷ ty_regno; rs1 ∷ ty_regno; op ∷ ty_bop] ty_retired :=
    let: rs1_val := call rX rs1 in
    let: rs2_val := call rX rs2 in
    let: taken :=
       match: op in bop with
       | RISCV_BEQ  => rs1_val = rs2_val
       | RISCV_BNE  => rs1_val != rs2_val
       | RISCV_BLT  => rs1_val <ˢ rs2_val
       | RISCV_BGE  => rs1_val >=ˢ rs2_val
       | RISCV_BLTU => rs1_val <ᵘ rs2_val
       | RISCV_BGEU => rs1_val >=ᵘ rs2_val
       end in
    let: tmp := stm_read_register pc in
    let: t := tmp +ᵇ exp_sext imm in
    if: taken
    then
      call set_next_pc t ;;
      stm_val ty_retired RETIRE_SUCCESS
    else
      stm_val ty_retired RETIRE_SUCCESS.

  Definition fun_execute_LOAD : Stm [imm ∷ ty.bvec 12; rs1 ∷ ty_regno; rd ∷ ty_regno; is_unsigned :: ty.bool; width :: ty_word_width] ty_retired :=
    let: offset ∷ ty_xlenbits := exp_sext imm in
    let: tmp := call rX rs1 in
    let: paddr := tmp +ᵇ offset in
    let: tmp1 := Read in
    match: width in wordwidth with
    | BYTE =>
        let: tmp := stm_call (@mem_read 1 restrict_bytes_one) [tmp1; paddr] in
        stm_call (@process_load 1 _) [rd; paddr; tmp; is_unsigned]
    | HALF =>
        let: tmp := stm_call (@mem_read 2 restrict_bytes_two) [tmp1; paddr] in
        stm_call (@process_load 2 _) [rd; paddr; tmp; is_unsigned]
    | WORD =>
        let: tmp := stm_call (@mem_read 4 restrict_bytes_four) [tmp1; paddr] in
        stm_call (@process_load 4 _) [rd; paddr; tmp; is_unsigned]
    end.

   Definition fun_execute_STORE : Stm [imm ∷ ty.bvec 12; rs2 ∷ ty_regno; rs1 ∷ ty_regno; width :: ty_word_width] ty_retired :=
    let: offset ∷ ty_xlenbits := exp_sext imm in
    let: tmp := call rX rs1 in
    let: paddr ∷ ty_xlenbits := tmp +ᵇ offset in
    let: rs2_val :: ty.bvec xlenbits := call rX rs2 in
    let: res := match: width in wordwidth with
    | BYTE =>
        let: tmp := exp_truncate 8 rs2_val in
        stm_call (@mem_write_value 1 restrict_bytes_one) [paddr; tmp]
    | HALF =>
        let: tmp := exp_truncate 16 rs2_val in
        stm_call (@mem_write_value 2 restrict_bytes_two) [paddr; tmp]
    | WORD =>
        stm_call (@mem_write_value 4 restrict_bytes_four) [paddr; rs2_val]
    end in
    match: res in union (memory_op_result 1) with
    |> KMemValue (pat_var "v") => if: v = exp_val ty_byte [bv 1]
                                  then stm_val ty_retired RETIRE_SUCCESS
                                  else fail "store got false from write_mem_value"
    |> KMemException (pat_var "e") => call handle_mem_exception paddr e ;;
                                      stm_val ty_retired RETIRE_FAIL
    end.

  Definition fun_execute_ECALL : Stm ctx.nil ty_retired :=
    let: tmp1 := stm_read_register cur_privilege in
    let: t := match: tmp1 in privilege with
              | Machine    => E_M_EnvCall
              | Supervisor => E_S_EnvCall
              | User       => E_U_EnvCall
              end in
    let: tmp2 := stm_read_register pc in
    let: tmp3 := call exception_handler tmp1 (CTL_TRAP t) tmp2 in
    call set_next_pc tmp3 ;;
    stm_val ty_retired RETIRE_FAIL.

  (* NOTE: we implement a custom EBREAK instruction for BlockVerifier debugging purposes *)
  Definition fun_execute_EBREAK : Stm ctx.nil ty_retired :=
    stm_debugk (stm_val ty_retired RETIRE_FAIL).

  Definition fun_execute_SRET : Stm ctx.nil ty_retired :=
    let: tmp1 := stm_read_register cur_privilege in
    let: "sret_illegal" :=
      match: tmp1 in privilege with
      | User       => stm_val ty.bool true
      | Supervisor => stm_val ty.bool false
      | Machine    => stm_val ty.bool false
      end in
    if: exp_var "sret_illegal"
    then
      call handle_illegal ;;
      stm_val ty_retired RETIRE_FAIL
    else
      let: tmp2 := stm_read_register pc in
      let: tmp3 := call exception_handler tmp1 CTL_SRET tmp2 in
      call set_next_pc tmp3 ;;
      stm_val ty_retired RETIRE_SUCCESS.

  Definition fun_execute_MRET : Stm ctx.nil ty_retired :=
    let: tmp1 := stm_read_register cur_privilege in
    if: tmp1 != exp_val ty_privilege Machine
    then
      call handle_illegal ;;
      stm_val ty_retired RETIRE_FAIL
    else
      let: tmp2 := stm_read_register pc in
      let: tmp3 := call exception_handler tmp1 CTL_MRET tmp2 in
      call set_next_pc tmp3 ;;
      stm_val ty_retired RETIRE_SUCCESS.

  Definition fun_execute_ILLEGAL : Stm [w ∷ ty_word] ty_retired :=
    call handle_illegal ;;
    stm_val ty_retired RETIRE_FAIL.

  Definition fun_execute_CSR : Stm [csr :: ty_csridx; rs1 :: ty_regno; rd :: ty_regno; is_imm :: ty.bool; op :: ty_csrop] ty_retired :=
    let: rs1_val := if: is_imm
                    then exp_zext rs1
                    else call rX rs1 in
    let: isWrite := match: op in csrop with
                    | CSRRW => exp_val ty.bool true
                    | _     => if: is_imm
                               then exp_unsigned rs1_val != exp_val ty.int 0%Z
                               else exp_unsigned rs1 != exp_val ty.int 0%Z
                    end in
    let: tmp1 := stm_read_register cur_privilege in
    let: tmp2 := call check_CSR csr tmp1 in
    if: tmp2 (* then and else branch switched, Sail model uses a not here *)
    then
      (use lemma open_pmp_entries ;;
       let: csr_val := call readCSR csr in
       (if: isWrite
        then let: new_val := match: op in csrop with
                             | CSRRW => rs1_val
                             | CSRRS => exp_binop bop.bvor csr_val rs1_val
                             | CSRRC => exp_binop bop.bvand csr_val (exp_unop uop.bvnot rs1_val)
                             end in
                 call writeCSR csr new_val
        else stm_val ty.unit tt) ;;
       use lemma close_pmp_entries ;;
       call wX rd csr_val ;;
       stm_val ty_retired RETIRE_SUCCESS)
    else (call handle_illegal ;;
          stm_val ty_retired RETIRE_FAIL).

  End FunDefKit.

  Include DefaultRegStoreKit RiscvPmpBase.

  Section ForeignKit.
  Import bv.notations.

  #[derive(equations=no)]
  Equations ForeignCall {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Val σs) (res : string + Val σ) (γ γ' : RegStore) (μ μ' : Memory) : Prop :=
    ForeignCall (read_ram width) [addr] res γ γ' μ μ' :=
      (γ' , μ' , res) = (γ , μ , inr (fun_read_ram μ width addr));
    ForeignCall (write_ram width) [addr; data] res γ γ' μ μ' :=
      (γ' , μ' , res) = (γ , @fun_write_ram μ width addr data , inr true);
    ForeignCall (@mmio_read width H) [addr] res γ γ' μ μ' :=
      let (μupd,readv) := fun_read_mmio μ width addr in
      (γ' , μ' , res) = (γ , μupd , inr readv);
    ForeignCall (@mmio_write width H) [addr; data] res γ γ' μ μ' :=
      let (_, μ'') := @fun_handle_write_mmio μ width addr data in
      (γ' , μ' , res) = (γ , μ'', inr true);
    ForeignCall (@within_mmio width H) [addr] res γ γ' μ μ' :=
      (γ' , μ' , res) = (γ , μ , inr (fun_within_mmio width addr));
    ForeignCall decode [code] res γ γ' μ μ' :=
        (γ' , μ' , res) = (γ , μ , pure_decode code);
    ForeignCall externalWorldUpdates [] res γ γ' μ μ' :=
      let '(vmip' , μ'') := fun_externalWorldUpdates μ in
      (* The external world may arbitrarily change the interrupts pending register (mip)
         but will leave other state untouched. *)
      (γ' , μ' , res) = (write_register γ mip vmip' , μ'' , inr ());
    ForeignCall powered_on [] res γ γ' μ μ' :=
      (γ' , μ' , res) = (γ , μ , inr (fun_powered_on μ)).

  Local Arguments ForeignCall {_ _} f /.
  Lemma ForeignProgress {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Val σs) γ μ :
    exists γ' μ' res, ForeignCall f args res γ γ' μ μ'.
  Proof. destruct f; env.destroy args; [| | cbn; destruct fun_read_mmio | cbn; repeat case_match | ..]; repeat econstructor.
  Qed.
  End ForeignKit.

  Definition FunDef {Δ τ} (f : Fun Δ τ) : Stm Δ τ :=
    match f with
    | rX                      => fun_rX
    | wX                      => fun_wX
    | bool_to_bits            => fun_bool_to_bits
    | shift_right_arith32     => fun_shift_right_arith32
    | @extend_value _ p       => @fun_extend_value _ p
    | get_arch_pc             => fun_get_arch_pc
    | get_next_pc             => fun_get_next_pc
    | set_next_pc             => fun_set_next_pc
    | tick_pc                 => fun_tick_pc
    | (to_bits l)             => @fun_to_bits l
    (* | abs                     => fun_abs *)
    | within_phys_mem         => fun_within_phys_mem
    | @mem_read width H       => @fun_mem_read width H
    | @mem_write_value width H => @fun_mem_write_value width H
    | @checked_mem_read width H => @fun_checked_mem_read width H
    | @checked_mem_write width H => @fun_checked_mem_write width H
    | @pmp_mem_read width H   => @fun_pmp_mem_read width H
    | @pmp_mem_write width H  => @fun_pmp_mem_write width H
    | pmpLocked               => fun_pmpLocked
    | pmpWriteCfgReg          => fun_pmpWriteCfgReg
    | pmpWriteCfg             => fun_pmpWriteCfg
    | pmpWriteAddr            => fun_pmpWriteAddr
    | @pmpCheck bytes H       => @fun_pmpCheck bytes H
    | pmpCheckPerms           => fun_pmpCheckPerms
    | pmpCheckRWX             => fun_pmpCheckRWX
    | pmpMatchEntry           => fun_pmpMatchEntry
    | pmpAddrRange            => fun_pmpAddrRange
    | pmpMatchAddr            => fun_pmpMatchAddr
    | @process_load _ p       => @fun_process_load _ p
    | and_Minterrupts         => fun_and_Minterrupts
    | Minterrupts_to_bits     => fun_Minterrupts_to_bits
    | Minterrupts_from_bits   => fun_Minterrupts_from_bits
    | Medeleg_to_bits         => fun_Medeleg_to_bits
    | Medeleg_from_bits       => fun_Medeleg_from_bits
    | idx_medeleg_record      => fun_idx_medeleg_record
    | exceptionType_to_bits   => fun_exceptionType_to_bits
    | interruptType_to_bits   => fun_interruptType_to_bits
    | privLevel_to_bits       => fun_privLevel_to_bits
    | main                    => fun_main
    | init_model              => fun_init_model
    | init_sys                => fun_init_sys
    | init_pmp                => fun_init_pmp
    | loop                    => fun_loop
    | step                    => fun_step
    | fetch                   => fun_fetch
    | handle_mem_exception    => fun_handle_mem_exception
    | exception_handler       => fun_exception_handler
    | exception_delegatee     => fun_exception_delegatee
    | trap_handler            => fun_trap_handler
    | prepare_trap_vector     => fun_prepare_trap_vector
    | tvec_addr               => fun_tvec_addr
    | handle_illegal          => fun_handle_illegal
    | lower_mstatus           => fun_lower_mstatus
    | lower_mip               => fun_lower_mip
    | lower_mie               => fun_lower_mie
    | lift_sip                => fun_lift_sip
    | legalize_sip            => fun_legalize_sip
    | lift_sie                => fun_lift_sie
    | legalize_sie            => fun_legalize_sie
    | check_CSR               => fun_check_CSR
    | is_CSR_defined          => fun_is_CSR_defined
    | csrAccess               => fun_csrAccess
    | csrPriv                 => fun_csrPriv
    | check_CSR_access        => fun_check_CSR_access
    | readCSR                 => fun_readCSR
    | writeCSR                => fun_writeCSR
    | getPendingSet           => fun_getPendingSet
    | findPendingInterrupt    => fun_findPendingInterrupt
    | processPending          => fun_processPending
    | dispatchInterrupt       => fun_dispatchInterrupt
    | handle_interrupt        => fun_handle_interrupt
    | execute                 => fun_execute
    | execute_RTYPE           => fun_execute_RTYPE
    | execute_ITYPE           => fun_execute_ITYPE
    | execute_SHIFTIOP        => fun_execute_SHIFTIOP
    | execute_UTYPE           => fun_execute_UTYPE
    | execute_BTYPE           => fun_execute_BTYPE
    | execute_RISCV_JAL       => fun_execute_RISCV_JAL
    | execute_RISCV_JALR      => fun_execute_RISCV_JALR
    | execute_LOAD            => fun_execute_LOAD
    | execute_STORE           => fun_execute_STORE
    | execute_ECALL           => fun_execute_ECALL
    | execute_EBREAK          => fun_execute_EBREAK
    | execute_SRET            => fun_execute_SRET
    | execute_MRET            => fun_execute_MRET
    | execute_CSR             => fun_execute_CSR
    | execute_MUL             => fun_execute_MUL
    | execute_ILLEGAL         => fun_execute_ILLEGAL
    end.

  Lemma fundef_bindfree (Δ : PCtx) (τ : Ty) (f : Fun Δ τ) :
    stm_bindfree (FunDef f).
  Proof. destruct f; now vm_compute. Qed.

  Include ProgramMixin RiscvPmpBase.

  Import callgraph.

  Definition 𝑭_call_graph := generic_call_graph.
  Lemma 𝑭_call_graph_wellformed : CallGraphWellFormed 𝑭_call_graph.
  Proof. apply generic_call_graph_wellformed, fundef_bindfree. Qed.

  Abbreviation AccessibleFun f := (Accessible 𝑭_call_graph f).

  Module Export WithAccessibleTactics.
    Import AccessibleTactics.

    Instance accessible_rX : AccessibleFun rX.
    Proof. accessible_proof. Qed.
    Instance accessible_wX : AccessibleFun wX.
    Proof. accessible_proof. Qed.
    Instance accessible_within_phys_mem : AccessibleFun within_phys_mem.
    Proof. accessible_proof. Qed.
    Instance accessible_pmpAddrRange : AccessibleFun pmpAddrRange.
    Proof. accessible_proof. Qed.
    Instance accessible_pmpMatchAddr : AccessibleFun pmpMatchAddr.
    Proof. accessible_proof. Qed.
    Instance accessible_pmpCheckRWX : AccessibleFun pmpCheckRWX.
    Proof. accessible_proof. Qed.
    Instance accessible_pmpLocked : AccessibleFun pmpLocked.
    Proof. accessible_proof. Qed.
    Instance accessible_pmpCheckPerms : AccessibleFun pmpCheckPerms.
    Proof. accessible_proof. Qed.
    Instance accessible_pmpMatchEntry : AccessibleFun pmpMatchEntry.
    Proof. accessible_proof. Qed.
    Instance accessible_to_bits (l : nat) : AccessibleFun (to_bits l).
    Proof. accessible_proof. Qed.
    Instance accessible_pmpCheck (bytes : nat) (rest : restrict_bytes bytes) :
      AccessibleFun (@pmpCheck bytes rest).
    Proof. accessible_proof. Qed.
    Instance accessible_pmpWriteCfg : AccessibleFun pmpWriteCfg.
    Proof. accessible_proof. Qed.
    Instance accessible_pmpWriteAddr : AccessibleFun pmpWriteAddr.
    Proof. accessible_proof. Qed.
    Instance accessible_pmpWriteCfgReg : AccessibleFun pmpWriteCfgReg.
    Proof. accessible_proof. Qed.
    Instance accessible_get_next_pc : AccessibleFun get_next_pc.
    Proof. accessible_proof. Qed.
    Instance accessible_set_next_pc : AccessibleFun set_next_pc.
    Proof. accessible_proof. Qed.
    Instance accessible_exceptionType_to_bits : AccessibleFun exceptionType_to_bits.
    Proof. accessible_proof. Qed.
    Instance accessible_interruptType_to_bits : AccessibleFun interruptType_to_bits.
    Proof. accessible_proof. Qed.
    Instance accessible_tvec_addr : AccessibleFun tvec_addr.
    Proof. accessible_proof. Qed.
    Instance accessible_prepare_trap_vector : AccessibleFun prepare_trap_vector.
    Proof. accessible_proof. Qed.
    Instance accessible_bool_to_bits : AccessibleFun bool_to_bits.
    Proof. accessible_proof. Qed.
    Instance accessible_and_Minterrupts : AccessibleFun and_Minterrupts.
    Proof. accessible_proof. Qed.
    Instance accessible_Minterrupts_to_bits : AccessibleFun Minterrupts_to_bits.
    Proof. accessible_proof. Qed.
    Instance accessible_Minterrupts_from_bits : AccessibleFun Minterrupts_from_bits.
    Proof. accessible_proof. Qed.
    Instance accessible_Medeleg_to_bits : AccessibleFun Medeleg_to_bits.
    Proof. accessible_proof. Qed.
    Instance accessible_Medeleg_from_bits : AccessibleFun Medeleg_from_bits.
    Proof. accessible_proof. Qed.
    Instance accessible_idx_medeleg_record : AccessibleFun idx_medeleg_record.
    Proof. accessible_proof. Qed.
    Instance accessible_processPending : AccessibleFun processPending.
    Proof. accessible_proof. Qed.
    Instance accessible_findPendingInterrupt : AccessibleFun findPendingInterrupt.
    Proof. accessible_proof. Qed.
    Instance accessible_getPendingSet : AccessibleFun getPendingSet.
    Proof. accessible_proof. Qed.
    Instance accessible_checked_mem_read (bytes : nat) (rest : restrict_bytes bytes) :
      AccessibleFun (@checked_mem_read bytes rest).
    Proof. accessible_proof. Qed.
    Instance accessible_pmp_mem_read (bytes : nat) (rest : restrict_bytes bytes) :
      AccessibleFun (@pmp_mem_read bytes rest).
    Proof. accessible_proof. Qed.
    Instance accessible_mem_read (bytes : nat) (rest : restrict_bytes bytes) :
      AccessibleFun (@mem_read bytes rest).
    Proof. accessible_proof. Qed.
    Instance accessible_checked_mem_write (bytes : nat) (rest : restrict_bytes bytes) :
      AccessibleFun (@checked_mem_write bytes rest).
    Proof. accessible_proof. Qed.
    Instance accessible_pmp_mem_write (bytes : nat) (rest : restrict_bytes bytes) :
      AccessibleFun (@pmp_mem_write bytes rest).
    Proof. accessible_proof. Qed.
    Instance accessible_mem_write_value (bytes : nat) (rest : restrict_bytes bytes) :
      AccessibleFun (@mem_write_value bytes rest).
    Proof. accessible_proof. Qed.
    Instance accessible_shift_right_arith32 : AccessibleFun shift_right_arith32.
    Proof. accessible_proof. Qed.
    Instance accessible_privLevel_to_bits : AccessibleFun privLevel_to_bits.
    Proof. accessible_proof. Qed.
    Instance accessible_exception_delegatee : AccessibleFun exception_delegatee.
    Proof. accessible_proof. Qed.
    Instance accessible_trap_handler : AccessibleFun trap_handler.
    Proof. accessible_proof. Qed.
    Instance accessible_exception_handler : AccessibleFun exception_handler.
    Proof. accessible_proof. Qed.
    Instance accessible_handle_illegal : AccessibleFun handle_illegal.
    Proof. accessible_proof. Qed.
    Instance accessible_handle_mem_exception : AccessibleFun handle_mem_exception.
    Proof. accessible_proof. Qed.
    Instance accessible_extend_value (bytes : nat)
      {p : IsTrue (width_constraint bytes)} : AccessibleFun (extend_value bytes).
    Proof. accessible_proof. Qed.
    Instance accessible_process_load (bytes : nat)
      {p : IsTrue (width_constraint bytes)} : AccessibleFun (process_load bytes).
    Proof. accessible_proof. Qed.
    Instance accessible_init_pmp : AccessibleFun init_pmp.
    Proof. accessible_proof. Qed.
    Instance accessible_init_sys : AccessibleFun init_sys.
    Proof. accessible_proof. Qed.
    Instance accessible_fetch : AccessibleFun fetch.
    Proof. accessible_proof. Qed.
    Instance accessible_lower_mstatus : AccessibleFun lower_mstatus.
    Proof. accessible_proof. Qed.
    Instance accessible_lower_mip : AccessibleFun lower_mip.
    Proof. accessible_proof. Qed.
    Instance accessible_lower_mie : AccessibleFun lower_mie.
    Proof. accessible_proof. Qed.
    Instance accessible_lift_sip : AccessibleFun lift_sip.
    Proof. accessible_proof. Qed.
    Instance accessible_legalize_sip : AccessibleFun legalize_sip.
    Proof. accessible_proof. Qed.
    Instance accessible_lift_sie : AccessibleFun lift_sie.
    Proof. accessible_proof. Qed.
    Instance accessible_legalize_sie : AccessibleFun legalize_sie.
    Proof. accessible_proof. Qed.
    Instance accessible_is_CSR_defined : AccessibleFun is_CSR_defined.
    Proof. accessible_proof. Qed.
    Instance accessible_csrAccess : AccessibleFun csrAccess.
    Proof. accessible_proof. Qed.
    Instance accessible_csrPriv : AccessibleFun csrPriv.
    Proof. accessible_proof. Qed.
    Instance accessible_check_CSR_access : AccessibleFun check_CSR_access.
    Proof. accessible_proof. Qed.
    Instance accessible_check_CSR : AccessibleFun check_CSR.
    Proof. accessible_proof. Qed.
    Instance accessible_readCSR : AccessibleFun readCSR.
    Proof. accessible_proof. Qed.
    Instance accessible_writeCSR : AccessibleFun writeCSR.
    Proof. accessible_proof. Qed.
    Instance accessible_dispatchInterrupt : AccessibleFun dispatchInterrupt.
    Proof. accessible_proof. Qed.
    Instance accessible_handle_interrupt : AccessibleFun handle_interrupt.
    Proof. accessible_proof. Qed.
    Instance accessible_execute_RTYPE : AccessibleFun execute_RTYPE.
    Proof. accessible_proof. Qed.
    Instance accessible_execute_ITYPE : AccessibleFun execute_ITYPE.
    Proof. accessible_proof. Qed.
    Instance accessible_execute_SHIFTIOP : AccessibleFun execute_SHIFTIOP.
    Proof. accessible_proof. Qed.
    Instance accessible_get_arch_pc : AccessibleFun get_arch_pc.
    Proof. accessible_proof. Qed.
    Instance accessible_execute_UTYPE : AccessibleFun execute_UTYPE.
    Proof. accessible_proof. Qed.
    Instance accessible_execute_BTYPE : AccessibleFun execute_BTYPE.
    Proof. accessible_proof. Qed.
    Instance accessible_execute_RISCV_JAL : AccessibleFun execute_RISCV_JAL.
    Proof. accessible_proof. Qed.
    Instance accessible_execute_RISCV_JALR : AccessibleFun execute_RISCV_JALR.
    Proof. accessible_proof. Qed.
    Instance accessible_execute_LOAD : AccessibleFun execute_LOAD.
    Proof. accessible_proof. Qed.
    Instance accessible_execute_STORE : AccessibleFun execute_STORE.
    Proof. accessible_proof. Qed.
    Instance accessible_execute_ECALL : AccessibleFun execute_ECALL.
    Proof. accessible_proof. Qed.
    Instance accessible_execute_EBREAK : AccessibleFun execute_EBREAK.
    Proof. accessible_proof. Qed.
    Instance accessible_execute_SRET : AccessibleFun execute_SRET.
    Proof. accessible_proof. Qed.
    Instance accessible_execute_MRET : AccessibleFun execute_MRET.
    Proof. accessible_proof. Qed.
    Instance accessible_execute_CSR : AccessibleFun execute_CSR.
    Proof. accessible_proof. Qed.
    Instance accessible_execute_MUL : AccessibleFun execute_MUL.
    Proof. accessible_proof. Qed.
    Instance accessible_execute_ILLEGAL : AccessibleFun execute_ILLEGAL.
    Proof. accessible_proof. Qed.
    Instance accessible_execute : AccessibleFun execute.
    Proof. accessible_proof. Qed.
    Instance accessible_tick_pc : AccessibleFun tick_pc.
    Proof. accessible_proof. Qed.
    Instance accessible_init_model : AccessibleFun init_model.
    Proof. accessible_proof. Qed.
    Instance accessible_step : AccessibleFun step.
    Proof. accessible_proof. Qed.
  End WithAccessibleTactics.

  Definition 𝑭_accessible {Δ τ} (f : 𝑭 Δ τ) : option (AccessibleFun f) :=
    match f with
    | main => None
    | loop => None
    | _ => Some _
    end.

  Section BlockVerSyntax.

    (* We put this here to ensure there is only one version even if we use multiple instantiations of the Block Verifier. *)
    Inductive AnnotInstr :=
    | AnnotAST  (i : AST)
    | AnnotDebugBreak
    | AnnotLemmaInvocation {Δ} (l : 𝑳 Δ) (es : NamedEnv (Exp ([ctx] : PCtx)) Δ)
    .

    Definition extract_AST (i : AnnotInstr) : option AST :=
      match i with
      | AnnotAST a => Some a
      | _ => None
      end.

    Definition filter_AST : list AnnotInstr -> list AST :=
        base.omap extract_AST.

  End BlockVerSyntax.

End RiscvPmpProgram.

Module RiscvPmpSemantics <: Semantics RiscvPmpBase RiscvPmpProgram :=
  MakeSemantics RiscvPmpBase RiscvPmpProgram.
