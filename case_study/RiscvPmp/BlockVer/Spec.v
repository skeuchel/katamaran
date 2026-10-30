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
     Strings.String
     Lists.List.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Iris.Instance
     Iris.Base
     Notations
     Bitvector
     Sep.Hoare
     MicroSail.ShallowExecutor
     MicroSail.ShallowSoundness
     MicroSail.SymbolicExecutor
     MicroSail.RefineExecutor
     MicroSail.Soundness
     RiscvPmp.PmpCheck
     RiscvPmp.IrisModel
     RiscvPmp.IrisInstance
     RiscvPmp.Machine
     RiscvPmp.Sig
     RiscvPmp.Logic
     RiscvPmp.Contracts
     RiscvPmp.Reification.
From Katamaran Require RiscvPmp.Model.

From iris.program_logic Require Import total_lifting.

Import RiscvPmpProgram.
Import RiscvPmpProgramLogic.
(* Import RiscvPmpIrisInstancePredicates. *)
Import RiscvPmpShallowSoundness.
Import RiscvPmpSymbolicSoundness.
Import ListNotations.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.

Module Assembly.
  (* Instruction synonyms. *)
  Definition ADD (rd rs1 rs2 : RegIdx) : AST :=
    RTYPE rs2 rs1 rd RISCV_ADD.
  Definition SUB (rd rs1 rs2 : RegIdx) : AST :=
    RTYPE rs2 rs1 rd RISCV_SUB.
  Definition BEQ (rs1 rs2 : RegIdx) (imm : bv 13) : AST :=
    BTYPE imm rs2 rs1 RISCV_BEQ.
  Definition BNE (rs1 rs2 : RegIdx) (imm : bv 13) : AST :=
    BTYPE imm rs2 rs1 RISCV_BNE.
  Definition ADDI (rd rs1 : RegIdx) (imm : bv 12) : AST :=
    ITYPE imm rs1 rd RISCV_ADDI.
  Definition JALR (rd rs1 : RegIdx) (imm : bv 12) : AST :=
    RISCV_JALR imm rs1 rd.
  Definition RET : AST :=
    JALR (bv.of_N 0) (bv.of_N 1) bv.zero.
  Definition MV (rd rs1 : RegIdx) : AST :=
    ADDI rd rs1 bv.zero.
  Definition MUL (rd rs1 rs2 : RegIdx) : AST :=
    Base.MUL rs2 rs1 rd false true true.
  Definition MULH (rd rs1 rs2 : RegIdx) : AST :=
    Base.MUL rs2 rs1 rd true true true.
  Definition MULHSU (rd rs1 rs2 : RegIdx) : AST :=
    Base.MUL rs2 rs1 rd true true false.
  Definition MULHU (rd rs1 rs2 : RegIdx) : AST :=
    Base.MUL rs2 rs1 rd true false false.
End Assembly.

Module RiscvPmpBlockVerifSpec.
  Section ContractDefKit.

  Import asn.notations.
  Abbreviation asn_bool t := (asn.formula (formula_bool t)).
  Abbreviation asn_match_option T opt xl alt_inl alt_inr := (asn.match_sum T ty.unit opt xl alt_inl "_" alt_inr).
  Notation "a '↦ₘ' t" := (asn.chunk (chunk_user (@ptstomem bytes_per_word) [a; t])) (at level 70).
  Notation "a '↦ᵣ' t" := (asn.chunk (chunk_user (@ptstomem_readonly bytes_per_word) [a; t])) (at level 70).
  Notation "a '↦ᵢ' t" := (asn.chunk (chunk_user ptstoinstr [a; t])) (at level 70).
  Notation "a <ₜ b" := (term_binop bop.lt a b) (at level 60).
  Notation "a <=ₜ b" := (term_binop bop.le a b) (at level 60).
  Notation "a &&ₜ b" := (term_binop bop.and a b) (at level 80).
  Notation "a ||ₜ b" := (term_binop bop.or a b) (at level 85).
  Abbreviation asn_pmp_entries l := (asn.chunk (chunk_user pmp_entries [l])).
  Abbreviation asn_pmp_addr_access l m := (asn.chunk (chunk_user pmp_addr_access [l; m])).
  Abbreviation asn_pmp_access addr width es m p := (asn.formula (formula_user pmp_access [addr;width;es;m;p])).
  Abbreviation asn_inv_mmio bytes := (asn.chunk (chunk_user (inv_mmio bytes) [env])).
  Abbreviation asn_mmio_checked_write bytes a w := (asn.chunk (chunk_user (mmio_checked_write bytes) [a; w])).

  Definition term_eqb {Σ} (e1 e2 : Term Σ ty_regno) : Term Σ ty.bool :=
    term_binop (bop.relop bop.eq) e1 e2.

  Local Notation "e1 '=?' e2" := (term_eqb e1 e2).

  Definition z_term {Σ} : Z -> Term Σ ty.int := term_val ty.int.

  Definition sep_contract_logvars (Δ : PCtx) (Σ : LCtx) : LCtx :=
    ctx.map (fun '(x::σ) => x::σ) Δ ▻▻ Σ.

  Definition create_localstore (Δ : PCtx) (Σ : LCtx) : SStore Δ (sep_contract_logvars Δ Σ) :=
    (env.tabulate (fun '(x::σ) xIn =>
                     @term_var
                       (sep_contract_logvars Δ Σ)
                       x
                       σ
                       (ctx.in_cat_left Σ (ctx.in_map (fun '(y::τ) => y::τ) xIn)))).

  Fixpoint asn_exists {Σ} (Γ : NCtx string Ty) : Assertion (Σ ▻▻ Γ) -> Assertion Σ :=
    match Γ return Assertion (Σ ▻▻ Γ) -> Assertion Σ with
    | ctx.nil => fun asn => asn
    | ctx.snoc Γ (x :: τ) =>
      fun asn =>
        @asn_exists Σ Γ (asn.exist x τ asn)
    end.

  Definition asn_with_reg {Σ} (r : Term Σ ty_regno) (asn : Reg ty_xlenbits -> Assertion Σ) (asn_default : Assertion Σ) : Assertion Σ :=
     asn.match_bool (r =? term_val ty_regno (bv.of_N 0)) (asn_default)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 1)) (asn x1)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 2)) (asn x2)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 3)) (asn x3)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 4)) (asn x4)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 5)) (asn x5)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 6)) (asn x6)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 7)) (asn x7)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 8)) (asn x8)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 9)) (asn x9)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 10)) (asn x10)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 11)) (asn x11)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 12)) (asn x12)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 13)) (asn x13)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 14)) (asn x14)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 15)) (asn x15)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 16)) (asn x16)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 17)) (asn x17)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 18)) (asn x18)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 19)) (asn x19)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 20)) (asn x20)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 21)) (asn x21)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 22)) (asn x22)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 23)) (asn x23)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 24)) (asn x24)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 25)) (asn x25)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 26)) (asn x26)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 27)) (asn x27)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 28)) (asn x28)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 29)) (asn x29)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 30)) (asn x30)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 31)) (asn x31)
     ⊥))))))))))))))))))))))))))))))).

  Definition asn_reg_ptsto {Σ} (r : Term Σ ty_regno) (w : Term Σ ty_word) : Assertion Σ :=
    asn_with_reg r (fun r => asn.chunk (chunk_ptsreg r w)) (w = term_val ty_word bv.zero).

  Local Notation "e1 ',ₜ' e2" := (term_binop bop.pair e1 e2) (at level 100).

  (* TODO: abstract away the concrete type, look into unions for that *)
  (* TODO: length of list should be 16, no duplicates *)
  (* Definition pmp_entries {Σ} : Term Σ (ty.list (ty.prod ty_pmpcfgidx ty_pmpaddridx)) :=
    term_list
      (cons (term_val ty_pmpcfgidx PMP0CFG ,ₜ term_val ty_pmpaddridx PMPADDR0)
            (cons (term_val ty_pmpcfgidx PMP1CFG ,ₜ term_val ty_pmpaddridx PMPADDR1) nil)). *)

  End ContractDefKit.

  Import RiscvPmpSpecification.

  Import asn.notations.
  (* TODO: This notation is already defined with a different meaning in
     asn.notations. Resolve this.
   *)
  (* Notation "a '*↦ₘ[' n ']' xs" := (asn.chunk (chunk_user (@ptstomem n) [a; xs])) (at level 79). *)
  Local Notation "a '↦ₘ[' bytes ']' t" := (asn.chunk (chunk_user (@ptstomem bytes) [a; t])) (at level 70).
  Local Notation "a '↦ᵣ[' bytes ']' t" := (asn.chunk (chunk_user (@ptstomem_readonly bytes) [a; t])) (at level 70).
  #[global] Notation "r '↦ᵣ' val" := (asn_reg_ptsto r val) (at level 70) : asn_scope.
  #[global] Notation "a '↦ₘ' t" := (asn.chunk (chunk_user (@ptstomem bytes_per_word) [a; t])) (at level 70) : asn_scope.
  #[global] Notation "a '↦ᵢ' t" := (asn.chunk (chunk_user (@ptstomem_readonly bytes_per_word) [a; t])) (at level 70) : asn_scope.
  Local Notation "a '↦ᵢ' t" := (asn.chunk (chunk_user ptstoinstr [a; t])) (at level 70).
  Local Notation "a <ₜ b" := (term_binop bop.lt a b) (at level 60).
  Local Notation "a <=ₜ b" := (term_binop bop.le a b) (at level 60).
  Local Notation "a &&ₜ b" := (term_binop bop.and a b) (at level 80).
  Local Notation "a ||ₜ b" := (term_binop bop.or a b) (at level 85).
  Local Notation "x + y" := (term_binop bop.bvadd x y) : exp_scope.
  Local Abbreviation asn_match_option T opt xl alt_inl alt_inr := (asn.match_sum T ty.unit opt xl alt_inl "_" alt_inr).
  Local Abbreviation asn_pmp_entries l := (asn.chunk (chunk_user pmp_entries [l])).
  Local Abbreviation asn_pmp_addr_access l m := (asn.chunk (chunk_user pmp_addr_access [l; m])).
  Local Abbreviation asn_pmp_access addr width es m p := (asn.formula (formula_user pmp_access [addr;width;es;m;p])).
  Local Notation "e1 ',ₜ' e2" := (term_binop bop.pair e1 e2) (at level 100).
  (* TODO: clean up above notations to get rid of the following one *)
  Local Abbreviation asn_cur_privilege val := (asn.chunk (chunk_ptsreg cur_privilege val)).
  Local Abbreviation asn_bool t := (asn.formula (formula_bool t)).
  Local Abbreviation asn_in_mmio n l := (asn.formula (formula_user (in_mmio n) [l])).
  Local Abbreviation asn_inv_mmio bytes := (asn.chunk (chunk_user (inv_mmio bytes) [env])).
  Local Abbreviation asn_mmio_checked_write bytes a w := (asn.chunk (chunk_user (mmio_checked_write bytes) [a; w])).
  Import bv.notations.

  (* The ghost resources around an MMIO write. A write to the adversary-
     observable address moves this execution ahead of the other one (the
     writePending state). So does the shutdown write, which additionally
     powers off the machine. *)
  Definition asn_mmio_write_pre {Σ} (paddr : Term Σ ty_xlenbits) : Assertion Σ :=
    if: term_binop (bop.relop bop.eq) paddr (term_val ty_xlenbits write_addr_adv)
    then asn.chunk (chunk_user nothingPending env.nil)
    else if: term_binop (bop.relop bop.eq) paddr (term_val ty_xlenbits mmioShutdownAddr)
         then asn.chunk (chunk_user nothingPending env.nil) ∗
              asn.chunk (chunk_user Sig.powered [term_val ty.bool true])
         else ⊤.

  Definition asn_mmio_write_post {Σ} (bytes : nat) (paddr : Term Σ ty_xlenbits) (data : Term Σ (ty_bytes bytes)) : Assertion Σ :=
    if: term_binop (bop.relop bop.eq) paddr (term_val ty_xlenbits write_addr_adv)
    then asn.chunk (chunk_user (written bytes) [ paddr; data ])
    else if: term_binop (bop.relop bop.eq) paddr (term_val ty_xlenbits mmioShutdownAddr)
         then asn.chunk (chunk_user (Sig.written_shutdown bytes) [ paddr; data ]) ∗
              asn.chunk (chunk_user Sig.powered [term_val ty.bool false])
         else ⊤.
  Arguments asn_mmio_write_post {Σ} bytes paddr data.

  Definition sep_contract_rX : SepContractFun rX :=
    {| sep_contract_logic_variables := ["rs" :: ty_regno; "w" :: ty_word];
       sep_contract_localstore      := [term_var "rs"];
       sep_contract_precondition    := term_var "rs" ↦ᵣ term_var "w";
       sep_contract_result          := "result_rX";
       sep_contract_postcondition   := term_var "result_rX" = term_var "w" ∗
                                       term_var "rs" ↦ᵣ term_var "w";
    |}.

  Definition sep_contract_wX : SepContractFun wX :=
    {| sep_contract_logic_variables := ["rs" :: ty_regno; "v" :: ty_xlenbits; "w" :: ty_xlenbits];
       sep_contract_localstore      := [term_var "rs"; term_var "v"];
       sep_contract_precondition    := term_var "rs" ↦ᵣ term_var "w";
       sep_contract_result          := "result_wX";
       sep_contract_postcondition   := term_var "result_wX" = term_val ty.unit tt ∗
                                       if: term_eqb (term_var "rs") (term_val ty_regno [bv 0])
                                       then term_var "rs" ↦ᵣ term_val ty_word bv.zero
                                       else term_var "rs" ↦ᵣ term_var "v"
    |}.

  Definition sep_contract_fetch_instr : SepContractFun fetch :=
    {| sep_contract_logic_variables := ["a" :: ty_xlenbits; "i" :: ty_ast; "entries" :: ty.list ty_pmpentry];
       sep_contract_localstore      := [];
       sep_contract_precondition    := asn.chunk (chunk_ptsreg pc (term_var "a")) ∗
                                                 term_var "a" ↦ᵢ term_var "i" ∗
                                                 (term_val ty.int (Z.of_N minAddr) <= term_unsigned (term_var "a"))%asn ∗
                                                 (term_binop bop.plus (term_unsigned (term_var "a")) (term_val ty.int (Z.of_nat bytes_per_instr))) <= term_val ty.int (Z.of_N maxAddr) ∗
                                                 asn_cur_privilege (term_val ty_privilege Machine) ∗
                                                 asn_pmp_entries (term_var "entries") ∗
                                                 asn_pmp_access (term_var "a") (term_val ty_word bv_instrsize) (term_var "entries") (term_val ty_privilege Machine) (term_val ty_access_type Execute);
       sep_contract_result          := "result_fetch";
       sep_contract_postcondition   :=
         asn.chunk (chunk_ptsreg pc (term_var "a")) ∗ term_var "a" ↦ᵢ term_var "i" ∗
         asn.exist "w" _
           (term_var "result_fetch" = term_union fetch_result KF_Base (term_var "w") ∗
                                        asn.chunk (chunk_user encodes_instr [term_var "w"; term_var "i"])) ∗
           asn_cur_privilege (term_val ty_privilege Machine) ∗
           asn_pmp_entries (term_var "entries");
    |}.

  Definition sep_contract_checked_mem_read {bytes} {H: restrict_bytes bytes} : SepContractFun (@checked_mem_read bytes H) :=
     {| sep_contract_logic_variables := ["inv" :: ty.bool; "typ" :: ty_access_type; "paddr" :: ty_xlenbits; "w" :: ty_bytes bytes];
      sep_contract_localstore      := [term_var "typ"; term_var "paddr"];
      sep_contract_precondition    :=
        asn.match_bool (term_var "inv")
          (term_var "paddr" ↦ᵣ[ bytes ] term_var "w")
          (term_var "paddr" ↦ₘ[ bytes ] term_var "w") ∗
          (term_val ty.int (Z.of_N minAddr) <= term_unsigned (term_var "paddr"))%asn ∗
          (term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes))) <= term_val ty.int (Z.of_N maxAddr);
      sep_contract_result          := "result_mem_read";
      sep_contract_postcondition   :=
        term_var "result_mem_read" = term_union (memory_op_result bytes) KMemValue (term_var "w") ∗
         asn.match_bool (term_var "inv") (term_var "paddr" ↦ᵣ[ bytes ] term_var "w") (term_var "paddr" ↦ₘ[ bytes ] term_var "w");
    |}.

  Definition sep_contract_checked_mem_write {bytes} {H: restrict_bytes bytes} : SepContractFun (@checked_mem_write bytes H) :=
    {| sep_contract_logic_variables := ["inv" :: ty.bool; "paddr" :: ty_xlenbits; "data" :: ty_bytes bytes];
      sep_contract_localstore      := [term_var "paddr"; term_var "data"];
      sep_contract_precondition    :=
        asn.match_bool (term_var "inv")
          (asn_in_mmio bytes (term_var "paddr") ∗
           term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes)) < (term_val ty.int (Z.of_N (bv.exp2 xlenbits))) ∗
           asn_inv_mmio bytes ∗
           asn_mmio_checked_write bytes (term_var "paddr") (term_var "data") ∗
           asn_mmio_write_pre (term_var "paddr"))
          (∃ "w", term_var "paddr" ↦ₘ[ bytes ] term_var "w" ∗
           (term_val ty.int (Z.of_N minAddr) <= term_unsigned (term_var "paddr"))%asn ∗
           (term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes))) <= term_val ty.int (Z.of_N maxAddr));
      sep_contract_result          := "result_checked_mem_write";
      sep_contract_postcondition   :=
        term_var "result_checked_mem_write" = term_union (memory_op_result 1) KMemValue (term_val ty_byte [bv 1]) ∗
        asn.match_bool (term_var "inv")
        (asn_mmio_write_post bytes (term_var "paddr") (term_var "data"))
                       (term_var "paddr" ↦ₘ[ bytes ] term_var "data");
    |}.

  Definition sep_contract_pmpCheck {bytes : nat} {H : restrict_bytes bytes} : SepContractFun (@pmpCheck bytes H) :=
    {| sep_contract_logic_variables := ["addr" :: ty_xlenbits; "acc" :: ty_access_type; "priv" :: ty_privilege; "entries" :: ty.list ty_pmpentry];
       sep_contract_localstore      := [term_var "addr"; term_var "acc"; term_var "priv"];
       sep_contract_precondition    :=
        asn_pmp_entries (term_var "entries")
          ∗ term_var "priv" = term_val ty_privilege Machine
                                ∗ asn_pmp_access (term_var "addr") (term_get_slice_int (term_val ty.int (Z.of_nat bytes))) (term_var "entries") (term_var "priv") (term_var "acc");
       sep_contract_result          := "result_pmpCheck";
       sep_contract_postcondition   :=
         term_var "result_pmpCheck" = term_inr (term_val ty.unit tt)
         ∗ asn_pmp_entries (term_var "entries");
    |}.

  Definition sep_contract_pmp_mem_read {bytes} {H : restrict_bytes bytes} : SepContractFun (@pmp_mem_read bytes H) :=
    {| sep_contract_logic_variables := ["inv" :: ty.bool; "typ" :: ty_access_type; "paddr" :: ty_xlenbits; "entries" :: ty.list ty_pmpentry; "w" :: ty_bytes bytes; "m" :: ty_privilege];
      sep_contract_localstore      := [term_var "typ"; term_var "m"; term_var "paddr"];
      sep_contract_precondition    :=
        asn.match_bool (term_var "inv") (term_var "paddr" ↦ᵣ[ bytes ] term_var "w") (term_var "paddr" ↦ₘ[ bytes ] term_var "w") ∗
          term_var "m" = term_val ty_privilege Machine ∗
          (term_val ty.int (Z.of_N minAddr) <= term_unsigned (term_var "paddr"))%asn ∗
          (term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes))) <= term_val ty.int (Z.of_N maxAddr) ∗
          asn_cur_privilege (term_var "m") ∗
          asn_pmp_entries (term_var "entries") ∗
          asn_pmp_access (term_var "paddr") (term_get_slice_int (term_val ty.int (Z.of_nat bytes))) (term_var "entries") (term_var "m") (term_var "typ");
      sep_contract_result          := "result_mem_read";
      sep_contract_postcondition   :=
        term_var "result_mem_read" = term_union (memory_op_result bytes) KMemValue (term_var "w") ∗
        asn.match_bool (term_var "inv") (term_var "paddr" ↦ᵣ[ bytes ] term_var "w") (term_var "paddr" ↦ₘ[ bytes ] term_var "w") ∗
        asn_cur_privilege (term_val ty_privilege Machine) ∗
        asn_pmp_entries (term_var "entries");
    |}.


  Definition sep_contract_pmp_mem_write {bytes} {H: restrict_bytes bytes} : SepContractFun (@pmp_mem_write bytes H) :=
    {| sep_contract_logic_variables := ["inv" :: ty.bool; "paddr" :: ty_xlenbits; "data" :: ty_bytes bytes; "typ" :: ty_access_type; "m" :: ty_privilege; "entries" :: ty.list ty_pmpentry];
      sep_contract_localstore      := [term_var "paddr"; term_var "data"; term_var "typ"; term_var "m"];
      sep_contract_precondition    :=
        asn.match_bool (term_var "inv")
          (asn_in_mmio bytes (term_var "paddr") ∗
           term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes)) < (term_val ty.int (Z.of_N (bv.exp2 xlenbits))) ∗
           asn_inv_mmio bytes ∗
           asn_mmio_checked_write bytes (term_var "paddr") (term_var "data") ∗
           asn_mmio_write_pre (term_var "paddr"))
          (∃ "w", term_var "paddr" ↦ₘ[ bytes ] term_var "w" ∗
           (term_val ty.int (Z.of_N minAddr) <= term_unsigned (term_var "paddr"))%asn ∗
           (term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes))) <= term_val ty.int (Z.of_N maxAddr)) ∗
        asn_cur_privilege (term_var "m") ∗
        term_var "m" = term_val ty_privilege Machine ∗
        asn_pmp_entries (term_var "entries") ∗
        asn_pmp_access (term_var "paddr") (term_get_slice_int (term_val ty.int (Z.of_nat bytes))) (term_var "entries") (term_var "m") (term_var "typ");
      sep_contract_result          := "result_mem_write";
      sep_contract_postcondition   :=
        term_var "result_mem_write" = term_union (memory_op_result 1) KMemValue (term_val ty_byte [bv 1]) ∗
        asn.match_bool (term_var "inv")
        (asn_mmio_write_post bytes (term_var "paddr") (term_var "data"))
                       (term_var "paddr" ↦ₘ[ bytes ] term_var "data") ∗
        asn_cur_privilege (term_var "m") ∗
        asn_pmp_entries (term_var "entries");
    |}.

  Definition sep_contract_mem_read {bytes} {H : restrict_bytes bytes} : SepContractFun (@mem_read bytes H) :=
    {| sep_contract_logic_variables := ["inv" :: ty.bool; "typ" :: ty_access_type; "paddr" :: ty_xlenbits; "entries" :: ty.list ty_pmpentry; "w" :: ty_bytes bytes];
      sep_contract_localstore      := [term_var "typ"; term_var "paddr"];
      sep_contract_precondition    :=
        asn.match_bool (term_var "inv") (term_var "paddr" ↦ᵣ[ bytes ] term_var "w") (term_var "paddr" ↦ₘ[ bytes ] term_var "w") ∗
          (term_val ty.int (Z.of_N minAddr) <= term_unsigned (term_var "paddr"))%asn ∗
          (term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes))) <= term_val ty.int (Z.of_N maxAddr) ∗
          asn_cur_privilege (term_val ty_privilege Machine) ∗
          asn_pmp_entries (term_var "entries") ∗
          asn_pmp_access (term_var "paddr") (term_get_slice_int (term_val ty.int (Z.of_nat bytes))) (term_var "entries") (term_val ty_privilege Machine) (term_var "typ");
      sep_contract_result          := "result_mem_read";
      sep_contract_postcondition   :=
        term_var "result_mem_read" = term_union (memory_op_result bytes) KMemValue (term_var "w") ∗
                                       asn.match_bool (term_var "inv") (term_var "paddr" ↦ᵣ[ bytes ] term_var "w") (term_var "paddr" ↦ₘ[ bytes ] term_var "w") ∗
          asn_cur_privilege (term_val ty_privilege Machine) ∗
          asn_pmp_entries (term_var "entries");
    |}.

  (* Access type `Write` needed here, as `mem_write_value` calls `pmp_mem_write` with this access type*)
  Definition sep_contract_mem_write_value {bytes} {H: restrict_bytes bytes} : SepContractFun (@mem_write_value bytes H) :=
    {| sep_contract_logic_variables := ["inv" :: ty.bool; "paddr" :: ty_xlenbits; "data" :: ty_bytes bytes; "entries" :: ty.list ty_pmpentry];
      sep_contract_localstore      := [term_var "paddr"; term_var "data"];
      sep_contract_precondition    :=
        asn.match_bool (term_var "inv")
          (asn_in_mmio bytes (term_var "paddr") ∗
           term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes)) < (term_val ty.int (Z.of_N (bv.exp2 xlenbits))) ∗
           asn_inv_mmio bytes ∗
           asn_mmio_checked_write bytes (term_var "paddr") (term_var "data") ∗
           asn_mmio_write_pre (term_var "paddr"))
          (∃ "w", term_var "paddr" ↦ₘ[ bytes ] term_var "w" ∗
           (term_val ty.int (Z.of_N minAddr) <= term_unsigned (term_var "paddr"))%asn ∗
           (term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes))) <= term_val ty.int (Z.of_N maxAddr)) ∗
        asn_cur_privilege (term_val ty_privilege Machine) ∗
        asn_pmp_entries (term_var "entries") ∗
        asn_pmp_access (term_var "paddr") (term_get_slice_int (term_val ty.int (Z.of_nat bytes))) (term_var "entries") (term_val ty_privilege Machine) (term_val ty_access_type Write);
      sep_contract_result          := "result_mem_write";
      sep_contract_postcondition   :=
        term_var "result_mem_write" = term_union (memory_op_result 1) KMemValue (term_val ty_byte [bv 1]) ∗
        asn.match_bool (term_var "inv")
        (asn_mmio_write_post bytes (term_var "paddr") (term_var "data"))
                       (term_var "paddr" ↦ₘ[ bytes ] term_var "data") ∗
        asn_cur_privilege (term_val ty_privilege Machine) ∗
        asn_pmp_entries (term_var "entries");
    |}.

  Definition sep_contract_tick_pc : SepContractFun tick_pc :=
    {| sep_contract_logic_variables := ["ao" :: ty_xlenbits; "an" :: ty_xlenbits];
       sep_contract_localstore      := [];
       sep_contract_precondition    := asn.chunk (chunk_ptsreg pc (term_var "ao")) ∗
                                                 asn.chunk (chunk_ptsreg nextpc (term_var "an"));
       sep_contract_result          := "result_tick_pc";
       sep_contract_postcondition   := asn.chunk (chunk_ptsreg pc (term_var "an")) ∗
                                                 asn.chunk (chunk_ptsreg nextpc (term_var "an")) ∗
                                                 term_var "result_tick_pc" = term_val ty.unit tt;
    |}.

  Definition sep_contract_within_phys_mem : SepContractFun within_phys_mem :=
    {| sep_contract_logic_variables := ["paddr" :: ty_xlenbits; "width" :: ty.int];
       sep_contract_localstore      := [term_var "paddr"; term_var "width"];
       sep_contract_precondition    :=
        let paddr_int : Term _ ty.int := term_unsigned (term_var "paddr") in
        (term_val ty.int (Z.of_N minAddr) <= paddr_int) ∗
          (term_binop bop.plus paddr_int (term_var "width")) <= term_val ty.int (Z.of_N maxAddr);
       sep_contract_result          := "result_within_phys_mem";
       sep_contract_postcondition   :=
         term_var "result_within_phys_mem" = term_val ty.bool true;
    |}.

  Definition sep_contract_execute_EBREAK : SepContractFun execute_EBREAK :=
    RiscvPmpExecutor.Symbolic.Statistics.extend_postcond_with_debug
      RiscvPmpSpecification.sep_contract_execute_EBREAK.

  Definition contract_environment : SepContractEnv :=
    fun Δ τ f =>
      match f with
      | rX                         => Some sep_contract_rX
      | wX                         => Some sep_contract_wX
      | fetch                      => Some sep_contract_fetch_instr
      | @mem_read bytes H          => Some (@sep_contract_mem_read bytes H)
      | @mem_write_value bytes H   => Some (@sep_contract_mem_write_value bytes H)
      | tick_pc                    => Some sep_contract_tick_pc
      | @pmpCheck bytes H          => Some (@sep_contract_pmpCheck bytes H)
      | within_phys_mem            => Some sep_contract_within_phys_mem
      | pmpMatchAddr               => Some sep_contract_pmpMatchAddr
      | @pmp_mem_read bytes H      => Some (@sep_contract_pmp_mem_read bytes H)
      | @pmp_mem_write bytes H     => Some (@sep_contract_pmp_mem_write bytes H)
      | @checked_mem_read bytes H  => Some (@sep_contract_checked_mem_read bytes H)
      | @checked_mem_write bytes H => Some (@sep_contract_checked_mem_write bytes H)
      | execute_EBREAK            => Some sep_contract_execute_EBREAK
      | _                         => None
      end.

  Lemma linted_contract_environment :
    forall Δ τ (f : Fun Δ τ),
    match contract_environment f with
      | Some c => Linted c
      | None   => True
      end.
  Proof. intros ? ? []; try constructor. Qed.

  Definition sep_contract_read_ram {bytes} : SepContractFunX (read_ram bytes) :=
    {| sep_contract_logic_variables := ["inv" :: ty.bool; "paddr" :: ty_xlenbits; "w" :: ty_bytes bytes];
       sep_contract_localstore      := [term_var "paddr"];
       sep_contract_precondition    := asn.match_bool (term_var "inv")  (term_var "paddr" ↦ᵣ[ bytes ] term_var "w") (term_var "paddr" ↦ₘ[ bytes ] term_var "w");
       sep_contract_result          := "result_read_ram";
       sep_contract_postcondition   := asn.match_bool (term_var "inv")
                                         (term_var "paddr" ↦ᵣ[ bytes ] term_var "w") (term_var "paddr" ↦ₘ[ bytes ] term_var "w") ∗
                                            term_var "result_read_ram" = term_var "w";
    |}.

  Definition sep_contract_write_ram {bytes} : SepContractFunX (write_ram bytes) :=
    {| sep_contract_logic_variables := ["paddr" :: ty_word; "data" :: ty_bytes bytes];
       sep_contract_localstore      := [term_var "paddr"; term_var "data"];
       sep_contract_precondition    := ∃ "w", (asn.chunk (chunk_user (ptstomem bytes) [term_var "paddr"; term_var "w"]));
       sep_contract_result          := "result_write_ram";
       sep_contract_postcondition   :=  term_var "paddr" ↦ₘ[ bytes ] term_var "data";
    |}.

  (* Note; we define the contract like this, because it matches the PRE of `checked_mem_read` quite well*)
  Definition sep_contract_within_mmio `(H : restrict_bytes bytes) : SepContractFunX (within_mmio H) :=
    {| sep_contract_logic_variables := ["inv" :: ty.bool; "paddr" :: ty_xlenbits];
        sep_contract_localstore      := [term_var "paddr"];
        sep_contract_precondition    :=
        asn.match_bool (term_var "inv")
          (asn_in_mmio bytes (term_var "paddr") ∗
           term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes)) < (term_val ty.int (Z.of_N (bv.exp2 xlenbits))))
          ((term_val ty.int (Z.of_N minAddr) <= term_unsigned (term_var "paddr"))%asn ∗ (term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes))) <= term_val ty.int (Z.of_N maxAddr));
        sep_contract_result          := "result_is_within";
        sep_contract_postcondition   := term_var "result_is_within" = term_var "inv"
    |}.

  (* NOTE: No new contract for `read`, as femtokernel does not perform any reads for now *)
  (* NOTE: for now no resources in `POST`; add those once we need to reinstate local state *)
  (* NOTE: if overflow is important, a no-overflow statement can be added to the `asn_mmio_checked_write` resource *)
  Definition sep_contract_mmio_write (bytes : nat) {H: restrict_bytes bytes} : SepContractFunX (mmio_write H) :=
    {| sep_contract_logic_variables := ["paddr" :: ty_xlenbits; "data" :: ty_bytes bytes];
        sep_contract_localstore      := [term_var "paddr"; term_var "data"];
        sep_contract_precondition    :=
           asn_in_mmio bytes (term_var "paddr") ∗
           asn_inv_mmio bytes ∗
           asn_mmio_checked_write bytes (term_var "paddr") (term_var "data") ∗
           asn_mmio_write_pre (term_var "paddr");
        sep_contract_result          := "result_write_mmio";
        sep_contract_postcondition   :=
        asn_mmio_write_post bytes (term_var "paddr") (term_var "data");
    |}.

  Definition sep_contract_decode    : SepContractFunX decode :=
    {| sep_contract_logic_variables := ["code" :: ty_word; "instr" :: ty_ast];
       sep_contract_localstore      := [term_var "code"];
       sep_contract_precondition    := asn.chunk (chunk_user encodes_instr [term_var "code"; term_var "instr"]);
       sep_contract_result          := "result_decode";
       sep_contract_postcondition   := term_var "result_decode" = term_var "instr";
    |}.

  (* TODO: fix contract once we incorporate interrupts into the relational model *)
  Definition sep_contract_externalWorldUpdates    : SepContractFunX externalWorldUpdates :=
    {| sep_contract_logic_variables := ["vmip" ∷ ty_Minterrupts];
       sep_contract_localstore      := [];
       sep_contract_precondition    := mip ↦ term_var "vmip";
       sep_contract_result          := "result_externalWorldUpdates";
       sep_contract_postcondition   :=
         mip ↦ term_val ty_Minterrupts (MkMinterrupts false false false false false false false false false);
    |}.

  Definition contract_environment_foreign : SepContractEnvEx :=
    fun Δ τ f =>
      match f with
      | read_ram bytes       => sep_contract_read_ram
      | write_ram bytes      => sep_contract_write_ram
      | within_mmio res      => sep_contract_within_mmio res
      | mmio_read bytes      => sep_contract_mmio_read bytes
      | mmio_write res       => @sep_contract_mmio_write _ res
      | decode               => sep_contract_decode
      | externalWorldUpdates => sep_contract_externalWorldUpdates
      | powered_on           => RiscvPmpSpecification.sep_contract_powered_on
      end.

  Lemma linted_contract_environment_foreign :
    forall Δ τ (f : FunX Δ τ),
      Linted (contract_environment_foreign f).
  Proof.
    intros ? ? []; try constructor.
  Qed.

  Definition lemma_open_gprs : SepLemma open_gprs :=
    {| lemma_logic_variables := ctx.nil;
       lemma_patterns        := env.nil;
       lemma_precondition    := ⊤;
       lemma_postcondition   := ⊤;
    |}.

  Definition lemma_close_gprs : SepLemma close_gprs :=
    {| lemma_logic_variables := ctx.nil;
       lemma_patterns        := env.nil;
       lemma_precondition    := ⊤;
       lemma_postcondition   := ⊤;
    |}.

  Definition lemma_open_ptsto_instr : SepLemma open_ptsto_instr :=
    {| lemma_logic_variables := ["paddr" :: ty_word; "i" :: ty_ast];
       lemma_patterns        := [term_var "paddr"];
       lemma_precondition    := asn.chunk (chunk_user ptstoinstr [term_var "paddr"; term_var "i"]);
      lemma_postcondition   := ∃ "w", (asn.chunk (chunk_user (ptstomem bytes_per_word) [term_var "paddr"; term_var "w"]) ∗
                                      asn.chunk (chunk_user encodes_instr [term_var "w"; term_var "i"]))
    |}.

  Definition lemma_close_ptsto_instr : SepLemma close_ptsto_instr :=
    {| lemma_logic_variables := ["paddr" :: ty_word; "w" :: ty_word; "i" :: ty_ast];
       lemma_patterns        := [term_var "paddr"; term_var "w"];
       lemma_precondition    := asn.chunk (chunk_user (ptstomem bytes_per_word) [term_var "paddr"; term_var "w"]) ∗
                                  asn.chunk (chunk_user encodes_instr [term_var "w"; term_var "i"]);
       lemma_postcondition   := asn.chunk (chunk_user ptstoinstr [term_var "paddr"; term_var "i"]);
    |}.

  Definition lemma_extract_pmp_ptsto bytes : SepLemma (extract_pmp_ptsto bytes) :=
    {| lemma_logic_variables := ["paddr" :: ty_xlenbits];
       lemma_patterns        := [term_var "paddr"];
       lemma_precondition    := ⊤;
       lemma_postcondition   := ⊤;
    |}.

  Definition lemma_return_pmp_ptsto bytes : SepLemma (return_pmp_ptsto bytes) :=
    {| lemma_logic_variables := ["paddr" :: ty_xlenbits];
       lemma_patterns        := [term_var "paddr"];
       lemma_precondition    := ⊤;
       lemma_postcondition   := ⊤;
    |}.

  Definition map_wordwidth (w : WordWidth) : nat :=
    match w with
    | BYTE => 1
    | HALF => 2
    | WORD => 4 end.

  (* Use bounds Lemma to calculate bounds on truncation *)
  Local Lemma wordwidth_upper_bound widthh : IsTrue (map_wordwidth widthh * byte <=? bytes_per_word * byte)%nat.
  Proof. destruct widthh; now compute. Qed.
  Local Hint Resolve wordwidth_upper_bound : typeclass_instances.

  Import TermNotations.

  Definition lemma_close_mmio_write (immm : bv 12) (widthh : WordWidth): SepLemma (close_mmio_write immm widthh) :=
    {| lemma_logic_variables := ["paddr" :: ty_xlenbits; "r" :: ty_regno; "w" :: ty_word];
       lemma_patterns        := [term_var "paddr"; term_var "r"];
       lemma_precondition    :=
        (term_val ty_xlenbits write_addr) = (term_var "paddr" +ᵇ term_sext (term_val (ty.bvec 12) immm)) ∨
          ((term_val ty_xlenbits write_addr_adv) = (term_var "paddr" +ᵇ term_sext (term_val (ty.bvec 12) immm)) ∗
          (term_var "w") = (term_val ty_xlenbits (bv.of_nat 42))) ∨
          (term_val ty_xlenbits mmioShutdownAddr) = (term_var "paddr" +ᵇ term_sext (term_val (ty.bvec 12) immm));
       lemma_postcondition   :=
        asn_mmio_checked_write (map_wordwidth widthh) (term_var "paddr" +ᵇ term_sext (term_val (ty.bvec 12) immm)) (term_truncate (map_wordwidth widthh * byte) (term_var "w"));
    |}.

   Definition lemma_environment : LemmaEnv :=
     fun Δ l =>
       match l with
       | open_gprs                    => lemma_open_gprs
       | close_gprs                   => lemma_close_gprs
       | open_ptsto_instr             => lemma_open_ptsto_instr
       | close_ptsto_instr            => lemma_close_ptsto_instr
       | open_pmp_entries             => lemma_open_pmp_entries
       | close_pmp_entries            => lemma_close_pmp_entries
       | extract_pmp_ptsto bytes      => lemma_extract_pmp_ptsto bytes
       | return_pmp_ptsto bytes       => lemma_return_pmp_ptsto bytes
       | close_mmio_write immm widthh => lemma_close_mmio_write immm widthh
      end.

   #[export] Instance riscvpmp_blockverif_specification : Specification :=
     {| CEnv   := contract_environment;
        CEnvEx := contract_environment_foreign;
        LEnv   := lemma_environment;
        fail_rule_pre := false;
     |}.

End RiscvPmpBlockVerifSpec.

Module RiscvPmpSpecVerif.
  Import RiscvPmpSpecification.
  Import RiscvPmpBlockVerifSpec.
  Import RiscvPmpExecutor.
  Import RiscvPmpExecutor.Symbolic.

  Notation "r '↦' val" := (chunk_ptsreg r val) (at level 79).

  Import ModalNotations.

  Definition ValidContractDebug {Δ τ} (f : Fun Δ τ) : Prop :=
    match CEnv f with
    | Some c => ValidContract c (FunDef f)
    | None => False
    end.

  Definition ValidContractWithFuelDebug {Δ τ} (fuel : nat) (f : Fun Δ τ) : Prop :=
    match CEnv f with
    | Some c => ValidContractWithFuel fuel c (FunDef f)
    | None => False
    end.

  Definition ValidContract {Δ τ} (f : Fun Δ τ) : Prop :=
    match CEnv f with
    | Some c => ValidContractReflect c (FunDef f)
    | None => False
    end.

  Definition ValidContractWithFuel {Δ τ} (fuel : nat) (f : Fun Δ τ) : Prop :=
    match CEnv f with
    | Some c => ValidContractReflectWithFuel fuel c (FunDef f)
    | None => False
    end.

  Lemma valid_execute_rX : ValidContract rX.
  Proof. now vm_compute. Qed.

  Lemma valid_execute_wX : ValidContract wX.
  Proof. vm_reflexivity. Qed.

  (* Import SymProp.notations. *)
  (* Set Printing Depth 200. *)
  (* Eval vm_compute in (postprocess (RiscvPmpBlockVerifExecutor.SHeapSpecM.vcgen RiscvPmpBlockVerifExecutor.default_config 1 *)
  (*            sep_contract_fetch_instr (FunDef fetch))). *)
  Lemma valid_execute_fetch : ValidContract fetch.
  Proof. vm_reflexivity. Qed.

  (* Lemma valid_execute_fetch_instr : SMut.ValidContract sep_contract_fetch_instr (FunDef fetch). *)
  (* Proof. compute. Admitted. *)

  Lemma valid_execute_tick_pc : ValidContract tick_pc.
  Proof. now vm_compute. Qed.

  Ltac symbolic_simpl :=
    apply validcontract_with_erasure_sound;
    vm_compute;
    constructor;
    cbn.

  Lemma valid_checked_mem_read {bytes} {H : restrict_bytes bytes} : ValidContract (@checked_mem_read bytes H).
  Proof. destruct H; vm_reflexivity. Qed.

  Lemma valid_checked_mem_write {bytes} {H : restrict_bytes bytes} : ValidContract (@checked_mem_write bytes H).
  Proof. destruct H; vm_reflexivity. Qed.

  Lemma valid_pmp_mem_read {bytes} {H : restrict_bytes bytes} : ValidContract (@pmp_mem_read bytes H).
  Proof. destruct H; vm_reflexivity. Qed.

  Lemma valid_pmp_mem_write {bytes} {H : restrict_bytes bytes} : ValidContract (@pmp_mem_write bytes H).
  Proof. destruct H; vm_reflexivity. Qed.

  Import Bitvector.bv.notations.

  Lemma valid_pmpMatchAddr : ValidContractDebug pmpMatchAddr.
  Proof.
    symbolic_simpl.
    intros; split; intros; bv_comp; auto.
    destruct (v + v0 <=ᵘ? v1)%bv eqn:?; bv_comp; auto.
  Qed.

  Lemma valid_pmpCheck {bytes : nat} {H : restrict_bytes bytes} : ValidContractWithFuelDebug 4 (@pmpCheck bytes H).
  Proof.
    destruct H; apply verification_condition_with_erasure_sound; vm_compute;
    reify_vc; cbn;
    repeat (intros; split; intros);
    repeat match goal with
      | H: (?b1 || ?b2)%bool = true |- _ =>
          apply Bool.orb_true_iff in H
      | H: ?P /\ ?Q |- _ =>
          destruct H
      | H: ?P \/ ?Q |- _ =>
          destruct H as [H|H]
      | H: negb ?b = true |- _ =>
          apply Bool.negb_true_iff in H;
          subst
      | H1: ?a <=ᵘ ?b, H2: ?b <ᵘ ?a |- False =>
          apply bv.ule_iff_unsigned_le in H1; apply bv.ult_iff_unsigned_lt in H2; lia
      end;
    subst;
    unfold Pmp_check_perms, decide_pmp_check_perms, pmp_check_RWX in *;
    simpl in *;
    try discriminate;
    try bv_solve_Ltac.solveBvManual.
  Qed.

  Lemma valid_mem_read {bytes} {H : restrict_bytes bytes} : ValidContract (@mem_read bytes H).
  Proof. destruct H; vm_reflexivity. Qed.

  Lemma valid_mem_write_value {bytes} {H : restrict_bytes bytes} : ValidContract (@mem_write_value bytes H).
  Proof. destruct H; vm_reflexivity. Qed.

  Lemma valid_contract_within_phys_mem : ValidContractDebug within_phys_mem.
  Proof. symbolic_simpl. intros. Lia.lia. Qed.

  Lemma valid_contract_execute_EBREAK : ValidContractDebug execute_EBREAK.
  Proof. now symbolic_simpl. Qed.

  Lemma valid_contract : forall {Δ τ} (f : Fun Δ τ) (c : SepContract Δ τ),
      CEnv f = Some c ->
      ValidContract f ->
      Symbolic.ValidContract c (FunDef f).
  Proof.
    intros ? ? f c Hcenv Hvc.
    unfold ValidContract in Hvc.
    rewrite Hcenv in Hvc.
    apply Symbolic.validcontract_reflect_sound.
    apply Hvc.
  Qed.

  Lemma valid_contract_with_fuel_debug : forall {Δ τ} (fuel : nat) (f : Fun Δ τ) (c : SepContract Δ τ),
      CEnv f = Some c ->
      ValidContractWithFuelDebug fuel f ->
      Symbolic.ValidContractWithFuel fuel c (FunDef f).
  Proof.
    intros ? ? fuel f c Hcenv Hvc.
    unfold ValidContractWithFuelDebug in Hvc.
    now rewrite Hcenv in Hvc.
  Qed.

  Lemma valid_contract_debug : forall {Δ τ} (f : Fun Δ τ) (c : SepContract Δ τ),
      CEnv f = Some c ->
      ValidContractDebug f ->
      Symbolic.ValidContract c (FunDef f).
  Proof.
    intros ? ? f c Hcenv Hvc.
    unfold ValidContractDebug in Hvc.
    now rewrite Hcenv in Hvc.
  Qed.

  Lemma ValidContracts : forall {Δ τ} (f : Fun Δ τ) (c : SepContract Δ τ),
      CEnv f = Some c ->
      exists fuel, Symbolic.ValidContractWithFuel fuel c (FunDef f).
  Proof.
    intros.
    destruct f; try discriminate H; eexists.
    - refine (valid_contract _ H valid_execute_rX).
    - refine (valid_contract _ H valid_execute_wX).
    - refine (valid_contract _ H valid_execute_tick_pc).
    - refine (valid_contract_debug _ H valid_contract_within_phys_mem).
    - refine (valid_contract _ H valid_mem_read).
    - refine (valid_contract _ H valid_checked_mem_read).
    - refine (valid_contract _ H valid_checked_mem_write).
    - refine (valid_contract _ H valid_pmp_mem_read).
    - refine (valid_contract _ H valid_pmp_mem_write).
    - refine (valid_contract_with_fuel_debug _ _ H valid_pmpCheck).
    - refine (valid_contract_debug _ H valid_pmpMatchAddr).
    - refine (valid_contract _ H valid_mem_write_value).
    - refine (valid_contract _ H valid_execute_fetch).
    - refine (valid_contract_debug _ H valid_contract_execute_EBREAK).
  Qed.
End RiscvPmpSpecVerif.

Module Type RiscvPmpIrisInstanceWithContracts
  (LOR : LeftOrRight)
  (Import RVPCOM : RiscvPmpIrisBaseCommon)
  (Import RVPBASE : RiscvPmpIrisBase LOR RVPCOM)
  (Import RVPPRED : RiscvPmpIrisInstancePredicates LOR RVPCOM RVPBASE)
  (Import RVPINST : RiscvPmpIrisInstance LOR RVPCOM RVPBASE RVPPRED).

  Include IrisInstanceWithContracts RiscvPmpGlobalState RiscvPmpSignature
    RiscvPmpProgram RiscvPmpSemantics RiscvPmpProgramLogic
    RVPCOM RVPBASE RVPINST.
  Import RiscvPmpBlockVerifSpec.
  (* For the destruct_syminstance tactic. *)
  Import RiscvPmp.Model.

  Import iris.bi.interface.
  Import iris.bi.big_op.
  Import iris.base_logic.lib.iprop.
  Import iris.program_logic.weakestpre.
  Import iris.program_logic.total_weakestpre.
  Import iris.base_logic.lib.gen_heap.
  Import iris.proofmode.string_ident.
  Import iris.proofmode.proofmode.

  Lemma read_ram_sound `{sailGS Σ} {bytes} :
    TValidContractForeign RiscvPmpBlockVerifSpec.sep_contract_read_ram (read_ram bytes).
  Proof.
      intros Γ es δ ι Heq. cbn. destruct_syminstance ι.
      iIntros "H". cbn in *. iApply semTWP_foreign.
      iIntros (? ?) "(Hregs & % & Hmem & %Hmap & Htr & Hpw)".
      iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
      iIntros (res ? ? Hf). rewrite Heq in Hf. cbn in Hf. inversion Hf; subst.
      iMod "Hclose" as "_". destruct inv.
      - (* readonly case *)
        iDestruct "H" as "#H".
        iInv "H" as "Hptsto" "Hclose_ptsto".
        iDestruct (bi.later_mono _ _ (fun_read_ram_works Hmap) with "[$Hptsto $Hmem]") as "#>%eq_fun_read_ram".
        iMod ("Hclose_ptsto" with "Hptsto") as "_". iModIntro.
        iFrame "Hregs Hmem Htr Hpw". iSplitR; first auto.
        iApply semTWP_val. iModIntro.
        now iFrame "H".
      - (* old case *)
        iModIntro.
        iPoseProof (fun_read_ram_works Hmap with "[$H $Hmem]") as "%eq_fun_read_ram".
        iPoseProof (mem_state_interp_not_modified $! Hmap with "Hmem Htr Hpw") as "Hmem".
        iFrame "Hregs Hmem". iApply semTWP_val. now iFrame "H".
  Qed.

  Lemma fun_write_ram_works μ bytes paddr data memmap `{sailGS Σ} {w : bv (bytes * byte)} :
    map_Forall (λ (a : Addr) (v : Base.Byte), (memory_ram μ) a = v) memmap ->
    interp_ptstomem paddr w ∗ gen_heap.gen_heap_interp memmap ∗ trace.tr_auth (memory_trace μ) ∗ powered_auth (fun_powered_on μ) ={⊤}=∗
                                                                                                 mem_state_interp sailGS_memGS (fun_write_ram μ bytes paddr data) ∗ interp_ptstomem paddr data.
  Proof.
    iRevert (data w paddr μ memmap).
    iInduction bytes as [|bytes] "IHbytes"; cbn [fun_write_ram interp_ptstomem];
      iIntros (data w paddr μ memmap Hmap) "(Haddr & Hmem & Htr & Hpw)".
    - iModIntro. iSplitL; last done.
      now iApply (mem_state_interp_not_modified $! Hmap with "Hmem Htr Hpw").
    -  change (bv.appView _ _ data) with (bv.appView byte (bytes * byte) data).
       destruct (bv.appView byte (bytes * byte) data) as [bd data].
       destruct (bv.appView byte (bytes * byte) w) as [bw w].
       iDestruct "Haddr" as "[[H $] Haddr]".
       iMod (gen_heap.gen_heap_update _ _ _ bd with "Hmem H") as "[Hmem $]".
       iApply ("IHbytes" $! data w
                 (bv.add bv.one paddr) (memory_update_ram μ (write_byte (memory_ram μ) paddr bd))
                 (insert paddr bd memmap) with "[%] [$Haddr $Hmem $Htr $Hpw]").
       by apply map_Forall_update.
  Qed.


  Lemma write_ram_sound `{sailGS Σ} {bytes} :
    TValidContractForeign RiscvPmpBlockVerifSpec.sep_contract_write_ram (write_ram bytes).
  Proof.
    intros Γ es δ ι Heq. destruct_syminstance ι. cbn in *.
    iIntros "[%w H]". iApply semTWP_foreign.
    iIntros (? ?) "(Hregs & % & Hmem & %Hmap & Htr & Hpw)".
    iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
    iIntros (res ? ? Hf). rewrite Heq in Hf. cbn in Hf. inversion Hf; subst.
    iMod "Hclose" as "_".
    iMod (fun_write_ram_works with "[$H $Hmem $Htr $Hpw]") as "[$ H]"; auto.
    rewrite semTWP_val. now iFrame "Hregs H".
 Qed.

  (* Important sanity condition on mmio predicates - NOTE: could be in typeclass, together with the condition that reads are either all accepted, or none of them are *)
  Lemma mmio_pred_cons {bytes : nat} t e: event_pred bytes e → mmio_pred bytes t → mmio_pred bytes (cons e t).
  Proof. now apply List.Forall_cons. Qed.

  Lemma mmio_read_sound `{!sailGS Σ} `(H: restrict_bytes bytes) :
    TValidContractForeign (RiscvPmpSpecification.sep_contract_mmio_read H) (mmio_read H).
  Proof.
    intros Γ es δ ι Heq. destruct_syminstance ι. cbn.
    now iIntros "[%HFalse _]".
  Qed.

  Lemma isNotMMIOShutdownAddr {a : Addr} :
    a ≠ mmioShutdownAddr <-> ~ isShutdownAddr a.
  Proof. by unfold isShutdownAddr. Qed.

  Lemma write_addr_neq_write_addr_adv : write_addr ≠ write_addr_adv.
  Proof. by vm_compute. Qed.

  (* Writes to the M-mode only MMIO address are not observable by the adversary. *)
  Lemma filter_adv_observable_private n (v : bv (n * byte)) t :
    filter_adv_observable (mkEvent IOWrite write_addr n v :: t) = filter_adv_observable t.
  Proof.
    unfold filter_adv_observable; cbn.
    by destruct (bv.eqb_spec write_addr write_addr).
  Qed.

  Lemma write_addr_neq_shutdown : write_addr ≠ mmioShutdownAddr.
  Proof. by vm_compute. Qed.

  Lemma write_addr_adv_neq_shutdown : write_addr_adv ≠ mmioShutdownAddr.
  Proof. by vm_compute. Qed.

  (* The shutdown write is observable by the adversary. *)
  Lemma filter_adv_observable_shutdown n (v : bv (n * byte)) t :
    filter_adv_observable (mkEvent IOShutdown mmioShutdownAddr n v :: t) =
      mkEvent IOShutdown mmioShutdownAddr n v :: filter_adv_observable t.
  Proof.
    unfold filter_adv_observable; cbn.
    destruct (bv.eqb_spec mmioShutdownAddr write_addr) as [Heq|]; last done.
    by apply eq_sym, write_addr_neq_shutdown in Heq.
  Qed.

  Lemma filter_adv_observable_adv n (v : bv (n * byte)) t :
    filter_adv_observable (mkEvent IOWrite write_addr_adv n v :: t) =
      mkEvent IOWrite write_addr_adv n v :: filter_adv_observable t.
  Proof.
    unfold filter_adv_observable; cbn.
    destruct (bv.eqb_spec write_addr_adv write_addr) as [Heq|]; last done.
    by apply eq_sym, write_addr_neq_write_addr_adv in Heq.
  Qed.

  Lemma mmio_write_sound `{!sailGS Σ} `(H: restrict_bytes bytes) :
    TValidContractForeign (@RiscvPmpBlockVerifSpec.sep_contract_mmio_write _ H) (mmio_write H).
  Proof.
    intros Γ es δ ι Heq. destruct_syminstance ι. cbn in *.
    iIntros "([%Hmmio _] & #Hinv & %Hmmio_checked & Hpend)". iApply semTWP_foreign.
    iIntros (? ?) "[Hregs [% (Hmem & %Hmap & Htr & Hpw)]]".
    iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
    iIntros (res ? ? Hf). rewrite Heq in Hf. cbn in Hf.
    unfold fun_handle_write_mmio in Hf.
    destruct bytes; first (destruct Hmmio; lia).
    cbn in Hf.
    destruct Hmmio_checked as [-> | [[-> ->] | ->]];
      [ rewrite -> (decide_False _ _ (proj1 isNotMMIOShutdownAddr write_addr_neq_shutdown)) in Hf
      | rewrite -> (decide_False _ _ (proj1 isNotMMIOShutdownAddr write_addr_adv_neq_shutdown)) in Hf
      | rewrite -> (decide_True _ _ (eq_refl : isShutdownAddr mmioShutdownAddr)) in Hf ];
      inversion Hf; subst;
      iMod "Hclose" as "_"; rewrite semTWP_val;
      iFrame "Hregs Hmem %";
      (* Open the shared invariant and look at it from the perspective of this execution. *)
      iInv "Hinv" as ">(%t & Hsides)" "Hclose";
      rewrite inv_mmio_body_own_other;
      iDestruct "Hsides" as "[(%ts & Hfrag & %Hpred & Hown) Hother]";
      iDestruct (trace.trace_full_frag_eq with "Htr Hfrag") as %<-;
      iMod (trace.trace_update _ (cons _ _) with "[$Htr $Hfrag]") as "[$ Hfrag]".
    - (* M-mode only write: the observable trace does not change. *)
      destruct (eq_dec write_addr write_addr_adv) as [Hcontra|_];
        first by apply write_addr_neq_write_addr_adv in Hcontra.
      destruct (eq_dec write_addr mmioShutdownAddr) as [Hcontra|_];
        first by apply write_addr_neq_shutdown in Hcontra.
      iMod ("Hclose" with "[Hfrag Hown Hother]") as "_".
      { iExists t. rewrite inv_mmio_body_own_other. iFrame "Hother".
        iExists _. iFrame "Hfrag".
        iSplitR; first (iPureIntro; apply mmio_pred_cons; [left; by eexists | done]).
        rewrite filter_adv_observable_private.
        iExact "Hown". }
      iModIntro. by iFrame "Hpw".
    - (* Observable write: this execution moves ahead by one event. *)
      destruct (eq_dec write_addr_adv write_addr_adv) as [_|]; last done. cbn.
      iRename "Hpend" into "Hnp".
      iDestruct "Hown" as "[[%Ht Hauth] | (% & _ & Hauth)]";
        last by iDestruct (written_auth_nothingPending with "Hauth Hnp") as "[]".
      iMod (nothingPending_written with "[$Hauth $Hnp]") as "[Hauth $]".
      iMod ("Hclose" with "[Hfrag Hauth Hother]") as "_".
      { iExists t. rewrite inv_mmio_body_own_other. iFrame "Hother".
        iExists _. iFrame "Hfrag".
        iSplitR; first (iPureIntro; apply mmio_pred_cons; [by right; left | done]).
        iRight. iExists _. iFrame "Hauth".
        rewrite filter_adv_observable_adv.
        change (memory_trace (memory_update_state ?μ _)) with (memory_trace μ).
        by rewrite Ht. }
      iModIntro. by iFrame "Hpw".
    - (* Shutdown write: this execution moves ahead by one event, and is
         powered off. *)
      destruct (eq_dec mmioShutdownAddr write_addr_adv) as [Hcontra|_];
        first by apply eq_sym, write_addr_adv_neq_shutdown in Hcontra.
      destruct (eq_dec mmioShutdownAddr mmioShutdownAddr) as [_|]; last done. cbn.
      iDestruct "Hpend" as "[Hnp Hpow]". iEval (cbn) in "Hpow".
      iDestruct "Hown" as "[[%Ht Hauth] | (% & _ & Hauth)]";
        last by iDestruct (written_auth_nothingPending with "Hauth Hnp") as "[]".
      iMod (nothingPending_written with "[$Hauth $Hnp]") as "[Hauth $]".
      iDestruct (powered_agree with "Hpw Hpow") as %Hon.
      iEval (rewrite Hon) in "Hpw".
      iMod (powered_update true false with "[$Hpw $Hpow]") as "[Hpw $]".
      iMod ("Hclose" with "[Hfrag Hauth Hother]") as "_".
      { iExists t. rewrite inv_mmio_body_own_other. iFrame "Hother".
        iExists _. iFrame "Hfrag".
        iSplitR; first (iPureIntro; apply mmio_pred_cons; [by right; right; eexists | done]).
        iRight. iExists _. iFrame "Hauth".
        rewrite filter_adv_observable_shutdown.
        change (memory_trace (memory_update_state ?μ _)) with (memory_trace μ).
        by rewrite Ht. }
      iModIntro. by iFrame "Hpw".
  Qed.

  Lemma decode_sound `{sailGS Σ} :
    TValidContractForeign RiscvPmpBlockVerifSpec.sep_contract_decode RiscvPmpProgram.decode.
  Proof.
    intros Γ es δ ι Heq. destruct_syminstance ι. cbn in *.
    iIntros "%Hdecode". iApply semTWP_foreign.
    iIntros (? ?) "[Hregs [% (Hmem & %Hmap & Htr & Hpw)]]".
    iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
    iIntros (? ? ? Hf). iMod "Hclose" as "_".
    rewrite Heq in Hf. cbn in Hf. inversion Hf; subst.
    destruct (pure_decode _); inversion Hdecode.
    iPoseProof (mem_state_interp_not_modified $! Hmap with "Hmem Htr Hpw") as "Hmem".
    rewrite semTWP_val. now iFrame "Hregs Hmem".
  Qed.

  Lemma within_mmio_sound `{!sailGS Σ} `(H: restrict_bytes bytes):
    TValidContractForeign (RiscvPmpBlockVerifSpec.sep_contract_within_mmio H) (RiscvPmpProgram.within_mmio H).
  Proof.
    intros Γ es δ ι Heq. destruct_syminstance ι. cbn in *.
    iIntros "Hpre". iApply semTWP_foreign.
    iIntros (? ?) "(Hregs & Hmem)".
    iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
    iIntros (? ? ? Hf). rewrite Heq in Hf. cbn in Hf. inversion Hf; subst.
    rewrite semTWP_val. iMod "Hclose" as "_". iFrame "Hregs Hmem".
    repeat iModIntro.
    rewrite /fun_within_mmio bool_decide_and.
    destruct inv; cbn; iDestruct "Hpre" as "([%Hlft _] & [%Hrght _])".
    - iPureIntro; repeat split; auto.
      rewrite -bool_decide_and bool_decide_true //.
    - iPureIntro; repeat split; auto.
      assert (bool_decide (withinMMIO paddr bytes) = false) as ->.
      { rewrite bool_decide_eq_false.
        intros Hw. pose proof (proj1 Hw).
        eapply mmio_ram_False, withinMMIO_elem_of_base, Hw.
        apply bv.elem_of_seq_bounds; first done.
        change xlenbits with 32 in *. cbn. unfold maxAddr, minAddr in *. lia.
      }
      auto.
  Qed.

  Lemma externalWorldUpdates_sound `{sailGS Σ} :
    TValidContractForeign RiscvPmpBlockVerifSpec.sep_contract_externalWorldUpdates externalWorldUpdates.
  Proof.
    intros Γ es δ ι Heq. destruct_syminstance ι. cbn.
    iIntros "Hmip". cbn in *. iApply semTWP_foreign.
    iIntros (? ?) "(Hregs & Hmem)".
    iMod (fupd_mask_subseteq empty) as "Hclose"; auto.
    iModIntro.
    iIntros (res ? ? Hf). rewrite Heq in Hf. cbn in Hf.
    (* unfold fun_externalWorldUpdates in Hf. *)
    (* destruct state_tra_world_updates as (vmip' , s'). *)
    inversion Hf; subst.
    iMod (reg_update γ mip vmip _ with "Hregs Hmip") as "[Hregs Hmip]".
    iMod "Hclose" as "_". iModIntro. iFrame "Hregs Hmem".
    iApply semTWP_val.
    now iFrame "Hmip".
  Qed.

  Lemma powered_on_sound `{sailGS Σ} :
    TValidContractForeign RiscvPmpSpecification.sep_contract_powered_on powered_on.
  Proof.
    intros Γ es δ ι Heq. destruct_syminstance ι. cbn.
    now iIntros "[%HFalse _]".
  Qed.

  Lemma TforeignSemBlockVerif `{sailGS Σ} : TForeignSem.
    intros Δ τ f; destruct f; cbn;
      eauto using read_ram_sound, write_ram_sound, mmio_read_sound, mmio_write_sound, within_mmio_sound, decode_sound, externalWorldUpdates_sound, powered_on_sound.
  Qed.

  Lemma foreignSemBlockVerif `{sailGS Σ} : ForeignSem.
  Proof. apply (TForeignSem_ForeignSem TforeignSemBlockVerif). Qed.

  Ltac destruct_syminstance ι :=
    repeat
      match type of ι with
      | Env _ (ctx.snoc _ (MkB ?s _)) =>
          string_to_ident_cps s
            ltac:(fun id =>
                    let fr := fresh id in
                    destruct (env.view ι) as [ι fr];
                    destruct_syminstance ι)
      | Env _ ctx.nil => destruct (env.view ι)
      | _ => idtac
      end.

  Lemma open_ptsto_instr_sound `{sailGS Σ} :
    ValidLemma RiscvPmpBlockVerifSpec.lemma_open_ptsto_instr.
  Proof.
    intros ι; destruct_syminstance ι; cbn.
    iIntros "[%w (Hptsto & Henc )]".
    iExists w.
    now iFrame.
  Qed.

  Lemma close_ptsto_instr_sound `{sailGS Σ} :
    ValidLemma RiscvPmpBlockVerifSpec.lemma_close_ptsto_instr.
  Proof.
    intros ι; destruct_syminstance ι; cbn.
    iIntros "(Hptsto & Henc )".
    iExists w.
    now iFrame.
  Qed.

  Lemma close_mmio_write_sound `{sailGS Σ} (imm : bv 12) (width : WordWidth):
    ValidLemma (RiscvPmpBlockVerifSpec.lemma_close_mmio_write imm width).
  Proof.
    intros ι; destruct_syminstance ι; cbn.
    unfold interp_mmio_checked_write.
    iIntros "[[<- _] | [([<- _] & [-> _]) | [<- _]]]"; iPureIntro; intuition.
    right. left.
    split; auto.
    destruct width; now compute.
  Qed.

  Lemma open_pmp_entries_sound `{sailGS Σ} :
    ValidLemma RiscvPmpSpecification.lemma_open_pmp_entries.
  Proof.
    intros ι; destruct_syminstance ι; cbn.
    rewrite pmp_entries_ptsto.
    iIntros "(% & % & % & % & -> & e1 & e2 & e3 & e4)".
    repeat iExists _.
    now iFrame "e1 e2 e3 e4".
  Qed.

  Lemma close_pmp_entries_sound `{sailGS Σ} :
    ValidLemma RiscvPmpSpecification.lemma_close_pmp_entries.
  Proof. intros ι; destruct_syminstance ι; cbn; auto. Qed.

  Lemma lemSemBlockVerif `{sailGS Σ} : LemmaSem.
  Proof.
    intros Δ []; intros ι; destruct_syminstance ι; try now iIntros "_".
    - apply open_pmp_entries_sound.
    - apply close_pmp_entries_sound.
    - apply open_ptsto_instr_sound.
    - apply close_ptsto_instr_sound.
    - apply close_mmio_write_sound.
  Qed.

  Import RiscvPmpBlockVerifSpec.
  (* Import RiscvPmpBlockVerifExecutor.Symbolic. *)

  Lemma TcontractsSound `{sailGS Σ} : ⊢ TValidContractEnvSem CEnv.
  Proof.
    apply (tsound TforeignSemBlockVerif lemSemBlockVerif).
    intros Γ τ f c Heq.
    pose proof (RiscvPmpSpecVerif.ValidContracts f Heq) as [fuel Hvc].
    eapply shallow_vcgen_fuel_soundness, symbolic_vcgen_fuel_soundness.
    eauto.
  Qed.

  Lemma TValidContractEnvSem_ValidContractEnvSem `{sailGS Σ} :
    TValidContractEnvSem CEnv ⊢
    ValidContractEnvSem CEnv.
  Proof.
    unfold TValidContractEnvSem, TValidContractEnvN, HasValidContract, ValidContractEnvSem.
    iIntros "H" (σs σ f). iSpecialize ("H" $! (callgraph.mkNode f)). simpl.
    destruct (contract_environment f) eqn:Ef; auto.
    iApply TValidContractSem_ValidContractSem.
    iApply "H". iPureIntro.
    destruct f; try discriminate Ef; typeclasses eauto.
  Qed.

  Lemma contractsSound `{sailGS Σ} : ⊢ ValidContractEnvSem CEnv.
  Proof.
    iApply (TValidContractEnvSem_ValidContractEnvSem $! TcontractsSound).
  Qed.

End RiscvPmpIrisInstanceWithContracts.
