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
     SmallStep.Step
     RiscvPmp.BlockVer.Spec
     RiscvPmp.BlockVer.BinaryVerifier
     RiscvPmp.IrisModel
     RiscvPmp.IrisInstance
     RiscvPmp.Machine
     RiscvPmp.Sig
     RiscvPmp.Contracts
     RiscvPmp.LoopVerification
     RiscvPmp.LoopVerificationBinary
     RiscvPmp.Everything
     RiscvPmp.FemtoKernel.Kernel
     RiscvPmp.FemtoKernel.BlockVerification.
From iris.base_logic Require lib.gen_heap lib.iprop invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac big_op.
From iris.program_logic Require weakestpre adequacy.
From iris.proofmode Require string_ident proofmode.
From stdpp Require namespaces.

Import RiscvPmpProgram.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.
Import ListNotations.
Open Scope ctx_scope.

Module inv := invariants.

Import iris.program_logic.weakestpre.
Import iris.proofmode.proofmode.

Import Contracts.
Import Assembly.
Import ArchState (ArchState).

Import RVPCOM.
Import RVPV2.
Import RVPINST2.
Import RVPBASE2.
Import RVPPRED2.

Local Opaque femtokernel_init_gen.

Section RelationalVerification.

  Definition asn_interpret_left `{sailGS2 Σ} : ∀ {Γ : LCtx}, Assertion Γ -> Valuation Γ -> iProp Σ :=
    @asn.interpret _ (UnaryPredicateDefIProp__l sailGS2_sailGS_left).

  Definition asn_interpret_right `{sailGS2 Σ} : ∀ {Γ : LCtx}, Assertion Γ -> Valuation Γ -> iProp Σ :=
    @asn.interpret _ (UnaryPredicateDefIProp__r sailGS2_sailGS_right).

  Import LoopVerification.
  Import ArchState (ArchState).

  Definition interp_ptstomem2 `{mG : memGS2 Σ} {width : nat} (addr : Addr) (v__l v__r : bv (width * byte)) : iProp Σ :=
    (@RVPCOM.interp_ptstomem _ memGS_left width addr v__l
     ∗ @RVPCOM.interp_ptstomem _ memGS_right width addr v__r)%I.

  Section WithAssertionNotations.
    Import asn.notations.
    Import TermNotations.
    Import bv.notations.

    (* We define _rel analogues of the non _rel version for the secret_write pre and post.
       The difference is that we omit the data ↦ secret, since we will have two different secrets. *)
    Example femtokernel_handler_secret_write_pre_rel : Assertion (Σ__csrs ▻▻ ["x1" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits]) :=
      asn.sub_assertion (femtokernel_handler_shared_pre handler_secret_write_addr) (sub_up1 (sub_cat_left _)) ∗
      mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
      x1 ↦ term_var "x1".

    Example femtokernel_handler_dispatch_pre_rel : Assertion (Σ__csrs ▻▻ ["x1" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits]) :=
      asn.sub_assertion (femtokernel_handler_shared_pre handler_dispatch_addr) (sub_up1 (sub_cat_left _)) ∗
      mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
      x1 ↦ term_var "x1".

    Example femtokernel_handler_ack_post_rel :
      Assertion (Σ__csrs ▻▻ ["a" :: ty_xlenbits; "an" :: ty_xlenbits]) :=
      femtokernel_handler_shared_post (term_val ty_privilege Machine) ∗
      mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
      term_var "an" = term_val ty_xlenbits (bv.of_N handler_exit_addr) ∗
      x1 ↦ term_val ty_xlenbits bv.zero ∗
      x5 ↦ term_val ty_xlenbits (bv.of_N 42) ∗
      asn.chunk (chunk_user (Sig.written bytes_per_word)
                   [term_val ty_xlenbits (bv.of_N mmio_write_adv);
                    term_val (ty_bytes bytes_per_word) (bv.of_N 42)]).

    Example femtokernel_handler_secret_write_post_rel :
      Assertion (Σ__csrs ▻▻ ["x1" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits; "an"::ty_xlenbits]) :=
      asn.sub_assertion (femtokernel_handler_shared_post (term_val ty_privilege Machine)) (sub_up1 (sub_up1 (sub_cat_left _))) ∗
      mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
      term_var "an" = term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N handler_secret_write_size) ∗
      x1 ↦ term_val ty_xlenbits bv.zero.

  End WithAssertionNotations.

  #[local] Ltac destruct_seps :=
    repeat (iRename select (_ ∗ _)%I into "H'";
            iDestruct "H'" as "(? & ?)");
    repeat (iRename select (bi_exist _) into "H'";
            iDestruct "H'" as "(% & ?)");
    repeat (iRename select (_ ∗ _)%I into "H'";
            iDestruct "H'" as "(? & ?)").

  #[local] Ltac solve_split_generic :=
    iIntros; cbn - [RVPCOM.interp_ptstomem];
    unfold reg_pointsTo21, reg_pointsTo2, interp_ptstomem2, nothingPending2, written2, powered2;
    destruct_seps;
    repeat (iRename select (reg_pointsTo _ _)%I into "H'";
            iFrame "H'");
    repeat (iRename select (RVPCOM.nothingPending)%I into "H'";
            iFrame "H'");
    repeat (iRename select (RVPCOM.written _)%I into "H'";
            iFrame "H'");
    repeat (iRename select (RVPCOM.powered _)%I into "H'";
            iFrame "H'");
    repeat (iRename select (RVPCOM.interp_ptstomem _ _)%I into "H'";
            iFrame "H'");
    repeat (iRename select (⌜_⌝ ∧ emp)%I into "H'";
            iDestruct "H'" as "[#H' _]";
            try iFrame "H'"; try iDestruct "H'" as "?");
    try (iRename select (interp_inv_mmio _) into "Hmmio";
         iDestruct "Hmmio" as "#Hmmio");
    repeat (iRename select (⌜_ = _⌝)%I into "Heq";
            iDestruct "Heq" as "->");
    auto.

  Lemma sep_sep_swap {PROP : bi} (A B C D : PROP) :
    ((A ∗ C) ∗ (B ∗ D) ⊢ (A ∗ B) ∗ (C ∗ D))%I.
  Proof. iIntros "[[$ $] [$ $]]". Qed.

  #[local] Ltac solve_split_leaf :=
    first
      [ solve [ solve_split_generic ]
      | solve [ solve_split_generic; case_match; solve_split_generic ] ].

  #[local] Ltac solve_leaf :=
    first [ reflexivity | refine (bi.sep_elim_l _ _) | solve_split_leaf ].

  (* The binary assertion is a tree of pairs, while the goal is a pair of
     trees. We transpose the two trees node by node instead of framing
     each individual resource. *)
  #[local] Ltac split_tree :=
    first
      [ lazymatch goal with
        | |- ((?T1 ∗ ?T2) ⊢ (?L1 ∗ ?L2) ∗ (?R1 ∗ ?R2))%I =>
            transitivity ((L1 ∗ R1) ∗ (L2 ∗ R2))%I;
            [ apply bi.sep_mono | apply sep_sep_swap ]
        end; split_tree
      | solve_leaf ].

  #[local] Ltac combine_tree :=
    first
      [ lazymatch goal with
        | |- ((?L1 ∗ ?L2) ∗ (?R1 ∗ ?R2) ⊢ ?B1 ∗ ?B2)%I =>
            transitivity ((L1 ∗ R1) ∗ (L2 ∗ R2))%I;
            [ apply sep_sep_swap | apply bi.sep_mono ]
        end; combine_tree
      | solve_leaf ].

  #[local] Ltac extract_leaf :=
    first
      [ (etrans; [refine (bi.sep_elim_l _ _) |]; extract_leaf)
      | (etrans; [refine (bi.sep_elim_r _ _) |]; extract_leaf)
      | reflexivity
      | apply bi.and_elim_l ].

  #[local] Ltac find_eq x T :=
    lazymatch T with
    | context [(⌜x = ?X⌝ ∧ emp)%I] => X
    end.

  #[local] Ltac solve_binary_split :=
    iIntros; cbn - [RVPCOM.interp_ptstomem];
    iStopProof; split_tree.

  #[local] Ltac solve_persistent_preds :=
    iIntros; cbn - [RVPCOM.interp_ptstomem];
    unfold femto_inv_mmio; iStopProof;
    first
      [ apply bi.persistent_entails_l; [ unfold interp_inv_mmio; apply _
        | extract_leaf ]
      | solve_split_leaf ].

  #[local] Ltac combine_attempt :=
    lazymatch goal with
    | |- ((?L ∗ ?R) ⊢ ⌜?x = ?y⌝ ∗ ?B)%I =>
        let X := find_eq x L in
        let Y := find_eq y R in
        let T := type of L in
        transitivity (⌜x = y⌝ ∗ (L ∗ R))%I;
        [ apply bi.persistent_entails_l; [ apply _ |];
          transitivity ((⌜x = X⌝ ∗ ⌜y = Y⌝)%I : T);
          [ apply bi.sep_mono; extract_leaf
          | iIntros "[%E1 %E2]"; iPureIntro; congruence ]
        | iIntros "[%Heq [HL HR]]"; subst;
          iSplitL ""; [ iPureIntro; reflexivity | iStopProof; combine_tree ] ]
    end.

  #[local] Ltac solve_binary_combine :=
    intros; iIntros "HL HR"; cbn - [RVPCOM.interp_ptstomem];
    iStopProof;
    first
      [ combine_attempt
      | case_match; cbn - [RVPCOM.interp_ptstomem]; combine_attempt
      | solve_split_leaf ].

  Lemma femtokernel_handler_entry_pre_persistent_preds `{sailGS2 Σ} (x5 x10 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
    let Σ := (csrs_valuation archstate vmie).["x5" ∷ ty_xlenbits ↦ x5].["x10" ∷ ty_xlenbits ↦ x10].["a" ∷ ty_xlenbits ↦ bv.of_N handler_entry_addr] in
    asn.interpret femtokernel_handler_entry_pre Σ -∗
    femto_inv_mmio ∗ asn.interpret femtokernel_handler_entry_pre Σ.
  Proof. solve_persistent_preds. Qed.

  Lemma femtokernel_handler_secret_write_pre_persistent_preds `{sailGS2 Σ} (x1 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
    let Σ := (csrs_valuation archstate vmie).["x1" ∷ ty_xlenbits ↦ x1].["a" ∷ ty_xlenbits ↦ bv.of_N handler_secret_write_addr] in
    asn.interpret femtokernel_handler_secret_write_pre_rel Σ -∗
    femto_inv_mmio ∗ asn.interpret femtokernel_handler_secret_write_pre_rel Σ.
  Proof. solve_persistent_preds. Qed.

  Lemma femtokernel_init_pre_binary_split `{sailGS2 Σ} (archstate : ArchState) (vmie : Val ty_Minterrupts) :
    let Σ := (csrs_valuation archstate vmie).["a" ∷ ty_xlenbits ↦ bv.of_N init_addr] in
    asn.interpret femtokernel_init_pre Σ -∗
    asn_interpret_left femtokernel_init_pre Σ ∗
    asn_interpret_right femtokernel_init_pre Σ.
  Proof. solve_binary_split. Qed.

  Lemma femtokernel_handler_entry_pre_binary_split `{sailGS2 Σ} (x5 x10 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
    let Σ := (csrs_valuation archstate vmie).["x5" ∷ ty_xlenbits ↦ x5].["x10" ∷ ty_xlenbits ↦ x10].["a" ∷ ty_xlenbits ↦ bv.of_N handler_entry_addr] in
    asn.interpret femtokernel_handler_entry_pre Σ -∗
    asn_interpret_left femtokernel_handler_entry_pre Σ ∗
    asn_interpret_right femtokernel_handler_entry_pre Σ.
  Proof. solve_binary_split. Qed.

  Lemma femtokernel_handler_secret_write_pre_binary_split `{sailGS2 Σ} (x1 secret1 secret2 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
    let Σ__csrs := (csrs_valuation archstate vmie) in
    let Σ__x1   := [env].["x1" ∷ ty_xlenbits ↦ x1] in
    let Σ__a    := [env].["a" ∷ ty_xlenbits ↦ bv.of_N handler_secret_write_addr] in
    let Σ__secret secret := Σ__csrs ►► Σ__x1 ►► [env].["secret" ∷ ty_xlenbits ↦ secret] ►► Σ__a in
    asn.interpret femtokernel_handler_secret_write_pre_rel (Σ__csrs ►► Σ__x1 ►► Σ__a) ∗
    interp_ptstomem2 (bv.of_N data_addr) secret1 secret2 -∗
    asn_interpret_left femtokernel_handler_secret_write_pre (Σ__secret secret1) ∗
    asn_interpret_right femtokernel_handler_secret_write_pre (Σ__secret secret2).
  Proof. solve_split_leaf. Qed.

  Lemma femtokernel_handler_exit_pre_binary_split `{sailGS2 Σ} (archstate : ArchState) (vmie : Val ty_Minterrupts) :
    let Σ := (csrs_valuation archstate vmie).["a" ∷ ty_xlenbits ↦ bv.of_N handler_exit_addr] in
    asn.interpret femtokernel_handler_exit_pre Σ -∗
    asn_interpret_left femtokernel_handler_exit_pre Σ ∗
    asn_interpret_right femtokernel_handler_exit_pre Σ.
  Proof. solve_binary_split. Qed.

  Lemma femtokernel_init_post_binary_combine `{sailGS2 Σ} (na1 na2 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
    let ι__csrs := csrs_valuation archstate vmie in
    let Σ na := ι__csrs.["a"∷ty_xlenbits ↦ bv.of_N init_addr].["an"∷ty_xlenbits ↦ na] in
    asn_interpret_left femtokernel_init_post (Σ na1) -∗
    asn_interpret_right femtokernel_init_post (Σ na2) -∗
    ⌜na1 = na2⌝ ∗ asn.interpret femtokernel_init_post (Σ na1).
  Proof. solve_binary_combine. Qed.

  Lemma femtokernel_handler_entry_post_binary_combine `{sailGS2 Σ} (x5 x10 na1 na2 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
    let ι__csrs := csrs_valuation archstate vmie in
    let Σ na := ι__csrs.["x5"∷ty_xlenbits ↦ x5].["x10" ∷ ty_xlenbits ↦ x10].["a"∷ty_xlenbits ↦ bv.of_N handler_entry_addr].["an"∷ty_xlenbits ↦ na] in
    asn_interpret_left femtokernel_handler_entry_post (Σ na1) -∗
    asn_interpret_right femtokernel_handler_entry_post (Σ na2) -∗
    ⌜na1 = na2⌝ ∗ asn.interpret femtokernel_handler_entry_post (Σ na1).
  Proof. solve_binary_combine. Qed.

  Lemma femtokernel_handler_secret_write_post_binary_combine `{sailGS2 Σ} (x1 secret1 secret2 na1 na2 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
    let ι__csrs := csrs_valuation archstate vmie in
    let Σ__rel na := ι__csrs.["x1"∷ty_xlenbits ↦ x1].["a"∷ty_xlenbits ↦ bv.of_N handler_secret_write_addr].["an"∷ty_xlenbits ↦ na] in
    let Σ secret na := ι__csrs.["x1"∷ty_xlenbits ↦ x1].["secret" ∷ ty_xlenbits ↦ secret].["a"∷ty_xlenbits ↦ bv.of_N handler_secret_write_addr].["an"∷ty_xlenbits ↦ na] in
    asn_interpret_left femtokernel_handler_secret_write_post (Σ secret1 na1) -∗
    asn_interpret_right femtokernel_handler_secret_write_post (Σ secret2 na2) -∗
    ⌜na1 = na2⌝ ∗ asn.interpret femtokernel_handler_secret_write_post_rel (Σ__rel na1)
    ∗ interp_ptstomem2 (bv.of_N data_addr) secret1 secret2.
  Proof. solve_split_leaf. Qed.

  Lemma femtokernel_handler_shutdown_check_pre_binary_split `{sailGS2 Σ} (x1 x5 x10 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
    let Σ := (csrs_valuation archstate vmie).["x1" ∷ ty_xlenbits ↦ x1].["x5" ∷ ty_xlenbits ↦ x5].["x10" ∷ ty_xlenbits ↦ x10].["a" ∷ ty_xlenbits ↦ bv.of_N handler_shutdown_check_addr] in
    asn.interpret femtokernel_handler_shutdown_check_pre Σ -∗
    asn_interpret_left femtokernel_handler_shutdown_check_pre Σ ∗
    asn_interpret_right femtokernel_handler_shutdown_check_pre Σ.
  Proof. solve_binary_split. Qed.

  Lemma femtokernel_handler_shutdown_check_post_binary_combine `{sailGS2 Σ} (x1 x5 x10 na1 na2 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
    let ι__csrs := csrs_valuation archstate vmie in
    let Σ na := ι__csrs.["x1"∷ty_xlenbits ↦ x1].["x5"∷ty_xlenbits ↦ x5].["x10" ∷ ty_xlenbits ↦ x10].["a"∷ty_xlenbits ↦ bv.of_N handler_shutdown_check_addr].["an"∷ty_xlenbits ↦ na] in
    asn_interpret_left femtokernel_handler_shutdown_check_post (Σ na1) -∗
    asn_interpret_right femtokernel_handler_shutdown_check_post (Σ na2) -∗
    ⌜na1 = na2⌝ ∗ asn.interpret femtokernel_handler_shutdown_check_post (Σ na1).
  Proof. solve_binary_combine. Qed.

  Lemma femtokernel_handler_shutdown_pre_binary_split `{sailGS2 Σ} (archstate : ArchState) (vmie : Val ty_Minterrupts) :
    let Σ := (csrs_valuation archstate vmie).["a" ∷ ty_xlenbits ↦ bv.of_N handler_shutdown_addr] in
    asn.interpret femtokernel_handler_shutdown_pre Σ -∗
    asn_interpret_left femtokernel_handler_shutdown_pre Σ ∗
    asn_interpret_right femtokernel_handler_shutdown_pre Σ.
  Proof. solve_binary_split. Qed.

  Lemma femtokernel_handler_shutdown_post_binary_combine `{sailGS2 Σ} (na1 na2 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
    let ι__csrs := csrs_valuation archstate vmie in
    let Σ na := ι__csrs.["a"∷ty_xlenbits ↦ bv.of_N handler_shutdown_addr].["an"∷ty_xlenbits ↦ na] in
    asn_interpret_left femtokernel_handler_shutdown_post (Σ na1) -∗
    asn_interpret_right femtokernel_handler_shutdown_post (Σ na2) -∗
    ⌜na1 = na2⌝ ∗ asn.interpret femtokernel_handler_shutdown_post (Σ na1).
  Proof. solve_binary_combine. Qed.

  Lemma femtokernel_handler_exit_post_binary_combine `{sailGS2 Σ} (na1 na2 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
    let ι__csrs := csrs_valuation archstate vmie in
    let Σ na := ι__csrs.["a"∷ty_xlenbits ↦ bv.of_N handler_exit_addr].["an"∷ty_xlenbits ↦ na] in
    asn_interpret_left femtokernel_handler_exit_post (Σ na1) -∗
    asn_interpret_right femtokernel_handler_exit_post (Σ na2) -∗
    ⌜na1 = na2⌝ ∗ asn.interpret femtokernel_handler_exit_post (Σ na1).
  Proof. solve_binary_combine. Qed.

  Definition ptsto_instrs_handler2 `{sailGS2 Σ} : iProp Σ :=
    @ptsto_instrs_handler _ memGS_left
    ∗ @ptsto_instrs_handler _ memGS_right.

  Lemma ptsto_instrs_handler2_equiv `{sailGS2 Σ} :
    ptsto_instrs_handler2 ⊣⊢
      ptsto_instrs (bv.of_N handler_entry_addr) (filter_AST femtokernel_handler_entry) ∗
      ptsto_instrs (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) ∗
      ptsto_instrs (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) ∗
      ptsto_instrs (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) ∗
      ptsto_instrs (bv.of_N handler_shutdown_check_addr) (filter_AST femtokernel_handler_shutdown_check) ∗
      ptsto_instrs (bv.of_N handler_shutdown_addr) (filter_AST femtokernel_handler_shutdown) ∗
      ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) ∗
      ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit).
  Proof.
    unfold ptsto_instrs_handler2, ptsto_instrs_handler.
    rewrite !ptsto_instrs_equiv.
    iSplit.
    - iIntros "((Hhentry1 & Hhdispatch1 & Hhnotzero1 & Hhiszero1 & Hhcheck1 & Hhshutdown1 & Hhsecret1 & Hhexit1) & (Hhentry2 & Hhdispatch2 & Hhnotzero2 & Hhiszero2 & Hhcheck2 & Hhshutdown2 & Hhsecret2 & Hhexit2))".
      iFrame "Hhentry1 Hhentry2 Hhdispatch1 Hhdispatch2 Hhnotzero1 Hhnotzero2 Hhiszero1 Hhiszero2 Hhcheck1 Hhcheck2 Hhshutdown1 Hhshutdown2 Hhsecret1 Hhsecret2 Hhexit1 Hhexit2".
    - iIntros "((Hhentry1 & Hhentry2) & (Hhdispatch1 & Hhdispatch2) & (Hhnotzero1 & Hhnotzero2) & (Hhiszero1 & Hhiszero2) & (Hhcheck1 & Hhcheck2) & (Hhshutdown1 & Hhshutdown2) & (Hhsecret1 & Hhsecret2) & (Hhexit1 & Hhexit2))".
      iFrame "Hhentry1 Hhdispatch1 Hhnotzero1 Hhiszero1 Hhcheck1 Hhshutdown1 Hhsecret1 Hhexit1 Hhentry2 Hhdispatch2 Hhnotzero2 Hhiszero2 Hhcheck2 Hhshutdown2 Hhsecret2 Hhexit2".
  Qed.

  (* TODO: shouldn't be needed, probably defined elsewhere already? *)
  #[local] Notation "a '↦ᵣ' t" := (reg_pointsTo2 a t t).

  Definition femtokernel_safe_shared_pre2 `{sailGS2 Σ} (addr : N) (b : Block) : iProp Σ :=
    exec_instructions_prologue (bv.of_N addr) (filter_AST b) ∗
      (∃ v, mscratch ↦ᵣ v) ∗
      @interp_pmp_addr_access _ sailGS2_memGS liveAddrs mmioAddrs femto_pmpentries User. (* Not needed for handler, but required for the rest of execution *)

  Lemma femtokernel_handler_exit_safe_rel `{sailGS2 Σ} (archstate : ArchState) (vmie : Val ty_Minterrupts) (Hmpp : ArchState.mpp (ArchState.mstate archstate) ≠ Machine) :
    ⊢ femtokernel_safe_shared_pre2 handler_exit_addr femtokernel_handler_exit ∗
      asn.interpret femtokernel_handler_exit_pre (csrs_valuation archstate vmie).["a" ∷ ty_xlenbits ↦ bv.of_N handler_exit_addr] ∗
      interp_gprs ∅ ∗
      nothingPending2 ∗
      powered2 true ∗
      ▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
           ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
           LoopVerificationBinary.M_Trap (femto_archstate priv ms ss pc) -∗ nothingPending2 -∗ powered2 true -∗ WP2_loop nothingPending2)
      -∗
      WP2_loop nothingPending2.
  Proof.
    iIntros "((Hpro & [%vmscratch Hmscratch] & HaccU) & Hpre & Hgprs & Hnp & Hpow & Htrap)".
    iApply (WP2_loop_semTripleBlock (λ a, asn.interpret femtokernel_handler_exit_pre _) _ _
              (λ a na, asn.interpret femtokernel_handler_exit_post _)
             with "Hpow Hpro Hpre []").
    - iIntros "Hpre".
      iPoseProof (femtokernel_handler_exit_pre_binary_split with "Hpre")
        as "(Hpre1 & Hpre2)".
      iPoseProof (contract_femtohandler_exit_verified__l (bv.of_N handler_exit_addr) archstate vmie with "Hpre1") as "H1".
      iPoseProof (contract_femtohandler_exit_verified__r (bv.of_N handler_exit_addr) archstate vmie with "Hpre2") as "H2".
      iApply (step_n_focus with "H1 H2").
      iIntros (na1 na2) "(H1 & H2)".
      iApply (femtokernel_handler_exit_post_binary_combine with "H1 H2").
    - iIntros (an) "(Hpost & Hepi & Hpow)".
      iDestruct "Hepi" as "(Hpc & Hinstrs & Hnpc)".
      iDestruct "Hpost" as "((Hcurpriv & Hmtvec & Hmcause & Hmip & Hmie & Hmepc & Hsepc & Hscause & Hsscratch & Hstvec & Hmideleg & Hmedeleg & Hpmp) & Hmstatus & [%Han _])"; cbn - [interp_ptstomem] in *.
      iAssert (interp_pmp_addr_access liveAddrs mmioAddrs femto_pmpentries (ArchState.mpp (ArchState.mstate archstate))) with "[HaccU]" as "Hacc".
      { assert (Hmpp' : ArchState.mpp (ArchState.mstate archstate) = User ∨ ArchState.mpp (ArchState.mstate archstate) = Supervisor)
          by (destruct (ArchState.mpp (ArchState.mstate archstate)); auto; congruence).
        destruct Hmpp' as [Heq|Heq]; rewrite Heq; first iExact "HaccU".
        by iApply interp_pmp_addr_access_s_u_eq. }
      iApply (LoopVerificationBinary.valid_semTriple_loop $! nothingPending2 (femto_return_archstate archstate vmscratch an)).
      unfold LoopVerificationBinary.loop_pre.
      iSplitR "Hnp Hpow Htrap Hinstrs".
      { unfold LoopVerificationBinary.Step_pre; cbn.
        iFrame "Hacc Hgprs Hpmp Hmie Hmip Hcurpriv Hpc Hnpc Hmtvec Hstvec Hmstatus Hmepc Hsepc Hmideleg Hmedeleg Hmscratch Hmcause Hsscratch Hscause".
        auto. }
      iFrame "Hnp Hpow".
      iSplitR.
      { iIntros "!> [H' _]". iDestruct (LoopVerificationBinary.M_CSRMod_machine with "H'") as %Heq.
        cbn in Heq. contradiction. }
      iSplitL "Htrap Hinstrs".
      { iIntros "!> (H' & Hnp & Hpow)". iApply ("Htrap" $! (ArchState.mpp (ArchState.mstate archstate)) with "[//] Hinstrs H' Hnp Hpow"). }
      iSplitR.
      { iIntros "!> [H' _]". iDestruct (LoopVerificationBinary.MRET_machine with "H'") as %Heq.
        cbn in Heq. contradiction. }
      iIntros "!> [H' _]". iDestruct (LoopVerificationBinary.SRET_machine with "H'") as %Heq.
      cbn in Heq. contradiction.
  Qed.

  Lemma femtokernel_handler_dispatch_pre_persistent_preds `{sailGS2 Σ} (x1 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
    let Σ := (csrs_valuation archstate vmie).["x1" ∷ ty_xlenbits ↦ x1].["a" ∷ ty_xlenbits ↦ bv.of_N handler_dispatch_addr] in
    asn.interpret femtokernel_handler_dispatch_pre_rel Σ -∗
    femto_inv_mmio ∗ asn.interpret femtokernel_handler_dispatch_pre_rel Σ.
  Proof. solve_persistent_preds. Qed.

  Lemma femtokernel_handler_dispatch_pre_binary_split `{sailGS2 Σ} (x1 secret1 secret2 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
    let Σ__csrs := (csrs_valuation archstate vmie) in
    let Σ__x1   := [env].["x1" ∷ ty_xlenbits ↦ x1] in
    let Σ__a    := [env].["a" ∷ ty_xlenbits ↦ bv.of_N handler_dispatch_addr] in
    let Σ__secret secret := Σ__csrs ►► [env].["x1" ∷ ty_xlenbits ↦ x1].["secret" ∷ ty_xlenbits ↦ secret] ►► Σ__a in
    asn.interpret femtokernel_handler_dispatch_pre_rel (Σ__csrs ►► Σ__x1 ►► Σ__a) ∗
    interp_ptstomem2 (bv.of_N data_addr) secret1 secret2 -∗
    asn_interpret_left femtokernel_handler_dispatch_pre (Σ__secret secret1) ∗
    asn_interpret_right femtokernel_handler_dispatch_pre (Σ__secret secret2).
  Proof. solve_split_leaf. Qed.

  (* The not_zero and is_zero blocks have the same postcondition, so both
     executions can be recombined at the exit block, independently of the
     path they took. *)
  Lemma femtokernel_handler_ack_post_binary_combine `{sailGS2 Σ}
    (x1l x5l x1r x5r al ar an1 an2 secret1 secret2 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
    let ι__csrs := csrs_valuation archstate vmie in
    let Σ x1 x5 secret a an := ι__csrs ►► [env].["x1" ∷ ty_xlenbits ↦ x1].["x5" ∷ ty_xlenbits ↦ x5].["secret" ∷ ty_xlenbits ↦ secret]
                                       ►► [env].["a" ∷ ty_xlenbits ↦ a].["an" ∷ ty_xlenbits ↦ an] in
    asn_interpret_left femtokernel_handler_ack_post (Σ x1l x5l secret1 al an1) -∗
    asn_interpret_right femtokernel_handler_ack_post (Σ x1r x5r secret2 ar an2) -∗
    ⌜an1 = an2⌝ ∗ asn.interpret femtokernel_handler_ack_post_rel ι__csrs.["a" ∷ ty_xlenbits ↦ al].["an" ∷ ty_xlenbits ↦ an1]
    ∗ interp_ptstomem2 (bv.of_N data_addr) secret1 secret2.
  Proof. solve_binary_combine. Qed.

  Lemma femtokernel_handler_dispatch_nonempty : filter_AST femtokernel_handler_dispatch ≠ []%list.
  Proof. vm_compute. discriminate. Qed.

  Lemma femtokernel_handler_is_zero_nonempty : filter_AST femtokernel_handler_is_zero ≠ []%list.
  Proof. vm_compute. discriminate. Qed.

  Lemma femtokernel_handler_not_zero_nonempty : filter_AST femtokernel_handler_not_zero ≠ []%list.
  Proof. vm_compute. discriminate. Qed.

  (* A lemma that reasons on the path taken for the left execution, keeping the right execution untouched.
     We also have a _right variant of it. Bit annoying to have this duplication, should probably improve
     this at some point. The difference between the left and right lemmas is which modules (left or right)
     we need to prove it. *)
  Lemma femtokernel_dispatch_path_left `{sailGS2 Σ} (vx1 vx5 secret : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
    let ι__csrs := csrs_valuation archstate vmie in
    ⊢ femto_inv_mmio -∗
      @RVPTVl.exec_instructions_prologue _ sailGS2_sailGS_left (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) -∗
      asn_interpret_left femtokernel_handler_dispatch_pre
        (ι__csrs ►► [env].["x1" ∷ ty_xlenbits ↦ vx1].["secret" ∷ ty_xlenbits ↦ secret]
                 ►► [env].["a" ∷ ty_xlenbits ↦ bv.of_N handler_dispatch_addr]) -∗
      @RVPCOM.nothingPending _ (@mc_wpGS _ (@mc_ghGS2_left _ sailGS2_memGS)) -∗
      powered_left true -∗
      @reg_pointsTo _ sailRegGS2_sailRegGS_left _ x5 vx5 -∗
      @RVPCOM.ptsto_instrs _ memGS_left (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) -∗
      @RVPCOM.ptsto_instrs _ memGS_left (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) -∗
      (∀ x1 x5 a an,
         asn_interpret_left femtokernel_handler_ack_post
           (ι__csrs ►► [env].["x1" ∷ ty_xlenbits ↦ x1].["x5" ∷ ty_xlenbits ↦ x5].["secret" ∷ ty_xlenbits ↦ secret]
                    ►► [env].["a" ∷ ty_xlenbits ↦ a].["an" ∷ ty_xlenbits ↦ an]) -∗
         @reg_pointsTo _ sailRegGS2_sailRegGS_left _ pc an -∗
         @reg_pointsTo _ sailRegGS2_sailRegGS_left _ nextpc an -∗
         @RVPCOM.ptsto_instrs _ memGS_left (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) -∗
         @RVPCOM.ptsto_instrs _ memGS_left (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) -∗
         @RVPCOM.ptsto_instrs _ memGS_left (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) -∗
         powered_left true -∗
         WP2_loop nothingPending2) -∗
      WP2_loop nothingPending2.
  Proof.
    iIntros (ι__csrs) "#Hinv Hpro Hpre Hnp Hp Hx5 Hnz Hiz Hk".
    iPoseProof (contract_femtohandler_dispatch_verified__l vx1 secret (bv.of_N handler_dispatch_addr) archstate vmie) as "Htrip".
    iApply (@WP2_loop_semTripleBlock_left _ _ _ _ (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) _
              femtokernel_handler_dispatch_nonempty with "Hp Hpro [Hpre] Htrip [Hnp Hx5 Hnz Hiz Hk]");
      first iExact "Hpre".
    iIntros (an) "(Hpost & (Hpc & Hcode & Hnpc) & Hp)".
    iEval (cbn - [RVPCOM.interp_ptstomem]) in "Hpost".
    iDestruct "Hpost" as "(Hshared & Hmstatus & Han & Hx1 & Hdata)".
    case_match; iDestruct "Han" as "[%Han _]"; cbn in Han; subst an.
    - (* The secret is zero: is_zero block. *)
      iPoseProof (contract_femtohandler_is_zero_verified__l secret vx5 secret (bv.of_N handler_is_zero_addr) archstate vmie) as "Htrip'".
      iApply (@WP2_loop_semTripleBlock_left _ _ _ _ (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) _
                femtokernel_handler_is_zero_nonempty with "Hp [Hpc Hiz Hnpc] [Hshared Hmstatus Hnp Hx1 Hx5 Hdata] Htrip' [Hk Hcode Hnz]").
      + iFrame "Hpc Hiz". by iExists _.
      + cbn - [RVPCOM.interp_ptstomem].
        iFrame "Hinv Hmstatus Hnp Hx1 Hx5 Hdata".
        repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
        repeat iSplit; try iPureIntro; try done; by vm_compute.
      + iIntros (an') "(Hpost & (Hpc & Hcode' & Hnpc) & Hp)".
        iApply ("Hk" with "Hpost Hpc Hnpc Hcode Hnz Hcode' Hp").
    - (* The secret is not zero: not_zero block. *)
      iPoseProof (contract_femtohandler_not_zero_verified__l secret vx5 secret (bv.of_N handler_not_zero_addr) archstate vmie) as "Htrip'".
      iApply (@WP2_loop_semTripleBlock_left _ _ _ _ (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) _
                femtokernel_handler_not_zero_nonempty with "Hp [Hpc Hnz Hnpc] [Hshared Hmstatus Hnp Hx1 Hx5 Hdata] Htrip' [Hk Hcode Hiz]").
      + iFrame "Hpc Hnz". by iExists _.
      + cbn - [RVPCOM.interp_ptstomem].
        iFrame "Hinv Hmstatus Hnp Hx1 Hx5 Hdata".
        repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
        repeat iSplit; try iPureIntro; try done; by vm_compute.
      + iIntros (an') "(Hpost & (Hpc & Hcode' & Hnpc) & Hp)".
        iApply ("Hk" with "Hpost Hpc Hnpc Hcode Hcode' Hiz Hp").
  Qed.

  (* Analogues to femtokernel_dispatch_path_left, see comment there. *)
  Lemma femtokernel_dispatch_path_right `{sailGS2 Σ} (vx1 vx5 secret : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
    let ι__csrs := csrs_valuation archstate vmie in
    ⊢ femto_inv_mmio -∗
      @RVPTVr.exec_instructions_prologue _ sailGS2_sailGS_right (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) -∗
      asn_interpret_right femtokernel_handler_dispatch_pre
        (ι__csrs ►► [env].["x1" ∷ ty_xlenbits ↦ vx1].["secret" ∷ ty_xlenbits ↦ secret]
                 ►► [env].["a" ∷ ty_xlenbits ↦ bv.of_N handler_dispatch_addr]) -∗
      @RVPCOM.nothingPending _ (@mc_wpGS _ (@mc_ghGS2_right _ sailGS2_memGS)) -∗
      powered_right true -∗
      @reg_pointsTo _ sailRegGS2_sailRegGS_right _ x5 vx5 -∗
      @RVPCOM.ptsto_instrs _ memGS_right (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) -∗
      @RVPCOM.ptsto_instrs _ memGS_right (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) -∗
      (∀ x1 x5 a an,
         asn_interpret_right femtokernel_handler_ack_post
           (ι__csrs ►► [env].["x1" ∷ ty_xlenbits ↦ x1].["x5" ∷ ty_xlenbits ↦ x5].["secret" ∷ ty_xlenbits ↦ secret]
                    ►► [env].["a" ∷ ty_xlenbits ↦ a].["an" ∷ ty_xlenbits ↦ an]) -∗
         @reg_pointsTo _ sailRegGS2_sailRegGS_right _ pc an -∗
         @reg_pointsTo _ sailRegGS2_sailRegGS_right _ nextpc an -∗
         @RVPCOM.ptsto_instrs _ memGS_right (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) -∗
         @RVPCOM.ptsto_instrs _ memGS_right (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) -∗
         @RVPCOM.ptsto_instrs _ memGS_right (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) -∗
         powered_right true -∗
         WP2_loop nothingPending2) -∗
      WP2_loop nothingPending2.
  Proof.
    iIntros (ι__csrs) "#Hinv Hpro Hpre Hnp Hp Hx5 Hnz Hiz Hk".
    iPoseProof (contract_femtohandler_dispatch_verified__r vx1 secret (bv.of_N handler_dispatch_addr) archstate vmie) as "Htrip".
    iApply (@WP2_loop_semTripleBlock_right _ _ _ _ (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) _
              femtokernel_handler_dispatch_nonempty with "Hp Hpro [Hpre] Htrip [Hnp Hx5 Hnz Hiz Hk]");
      first iExact "Hpre".
    iIntros (an) "(Hpost & (Hpc & Hcode & Hnpc) & Hp)".
    iEval (cbn - [RVPCOM.interp_ptstomem]) in "Hpost".
    iDestruct "Hpost" as "(Hshared & Hmstatus & Han & Hx1 & Hdata)".
    case_match; iDestruct "Han" as "[%Han _]"; cbn in Han; subst an.
    - (* The secret is zero: is_zero block. *)
      iPoseProof (contract_femtohandler_is_zero_verified__r secret vx5 secret (bv.of_N handler_is_zero_addr) archstate vmie) as "Htrip'".
      iApply (@WP2_loop_semTripleBlock_right _ _ _ _ (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) _
                femtokernel_handler_is_zero_nonempty with "Hp [Hpc Hiz Hnpc] [Hshared Hmstatus Hnp Hx1 Hx5 Hdata] Htrip' [Hk Hcode Hnz]").
      + iFrame "Hpc Hiz". by iExists _.
      + cbn - [RVPCOM.interp_ptstomem].
        iFrame "Hinv Hmstatus Hnp Hx1 Hx5 Hdata".
        repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
        repeat iSplit; try iPureIntro; try done; by vm_compute.
      + iIntros (an') "(Hpost & (Hpc & Hcode' & Hnpc) & Hp)".
        iApply ("Hk" with "Hpost Hpc Hnpc Hcode Hnz Hcode' Hp").
    - (* The secret is not zero: not_zero block. *)
      iPoseProof (contract_femtohandler_not_zero_verified__r secret vx5 secret (bv.of_N handler_not_zero_addr) archstate vmie) as "Htrip'".
      iApply (@WP2_loop_semTripleBlock_right _ _ _ _ (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) _
                femtokernel_handler_not_zero_nonempty with "Hp [Hpc Hnz Hnpc] [Hshared Hmstatus Hnp Hx1 Hx5 Hdata] Htrip' [Hk Hcode Hiz]").
      + iFrame "Hpc Hnz". by iExists _.
      + cbn - [RVPCOM.interp_ptstomem].
        iFrame "Hinv Hmstatus Hnp Hx1 Hx5 Hdata".
        repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
        repeat iSplit; try iPureIntro; try done; by vm_compute.
      + iIntros (an') "(Hpost & (Hpc & Hcode' & Hnpc) & Hp)".
        iApply ("Hk" with "Hpost Hpc Hnpc Hcode Hcode' Hiz Hp").
  Qed.

  Lemma femtokernel_handler_dispatch_safe_rel `{sailGS2 Σ} (vx1 secret1 secret2 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) (Hmpp : ArchState.mpp (ArchState.mstate archstate) ≠ Machine) :
    ⊢ femtokernel_safe_shared_pre2 handler_dispatch_addr femtokernel_handler_dispatch ∗
      asn.interpret femtokernel_handler_dispatch_pre_rel (csrs_valuation archstate vmie).["x1" ∷ ty_xlenbits ↦ vx1].["a" ∷ ty_xlenbits ↦ bv.of_N handler_dispatch_addr] ∗
      interp_gprs {[x1]} ∗
      interp_ptstomem2 (bv.of_N data_addr) secret1 secret2 ∗
      nothingPending2 ∗
      powered2 true ∗
      ptsto_instrs (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) ∗
      ptsto_instrs (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) ∗
      ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) ∗
      ▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
         ptsto_instrs (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) -∗
         ptsto_instrs (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) -∗
         ptsto_instrs (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) -∗
         interp_ptstomem2 (bv.of_N data_addr) secret1 secret2 -∗
         ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
         LoopVerificationBinary.M_Trap (femto_archstate priv ms ss pc) -∗ nothingPending2 -∗ powered2 true -∗ WP2_loop nothingPending2)
      -∗
      WP2_loop nothingPending2.
  Proof.
    iIntros "((Hpro & Hmscratch & HaccU) & Hpre & Hgprs & Hdata & Hnp & [Hpl Hpr] & Hhnz & Hhiz & Hhexit & Hk)".
    iPoseProof (femtokernel_handler_dispatch_pre_persistent_preds with "Hpre") as "(#Hinv & Hpre)".
    iPoseProof (femtokernel_handler_dispatch_pre_binary_split with "[$Hpre $Hdata]") as "(Hpre1 & Hpre2)".
    iPoseProof (interp_gprs_with_excluded_gen {[x1]} (exclude2 := {[x5]}) with "Hgprs") as "(Hregs & Hgprs)";
      try solve_subseteq.
    reduce_big_sepS_big_sepL.
    iDestruct "Hregs" as "([%vx5 Hx5] & _)".
    subst l; clear Hl Hdup.
    unfold reg_pointsTo21, reg_pointsTo2. iDestruct "Hx5" as "[Hx5l Hx5r]".
    unfold exec_instructions_prologue, reg_pointsTo21, reg_pointsTo2.
    iDestruct "Hpro" as "([Hpcl Hpcr] & Hcode & [%npc [Hnpcl Hnpcr]])".
    iDestruct (ptsto_instrs_equiv with "Hcode") as "[Hcodel Hcoder]".
    iDestruct (ptsto_instrs_equiv with "Hhnz") as "[Hnzl Hnzr]".
    iDestruct (ptsto_instrs_equiv with "Hhiz") as "[Hizl Hizr]".
    iDestruct "Hnp" as "[Hnpl Hnpr]".
    (* Run the left execution until the exit block. *)
    iApply (femtokernel_dispatch_path_left vx1 vx5 secret1 archstate vmie
              with "Hinv [Hpcl Hcodel Hnpcl] Hpre1 Hnpl Hpl Hx5l Hnzl Hizl").
    { iFrame "Hpcl Hcodel". by iExists _. }
    iIntros (x1l x5l al anl) "Hpostl Hpcl Hnpcl Hcodel Hnzl Hizl Hpl".
    (* Run the right execution until the exit block. *)
    iApply (femtokernel_dispatch_path_right vx1 vx5 secret2 archstate vmie
              with "Hinv [Hpcr Hcoder Hnpcr] Hpre2 Hnpr Hpr Hx5r Hnzr Hizr").
    { iFrame "Hpcr Hcoder". by iExists _. }
    iIntros (x1r x5r ar anr) "Hpostr Hpcr Hnpcr Hcoder Hnzr Hizr Hpr".
    iDestruct (femtokernel_handler_ack_post_binary_combine with "Hpostl Hpostr") as "(<- & Hpost & Hdata)".
    iEval (cbn) in "Hpost".
    iDestruct "Hpost" as "(Hshared & Hmstatus & [%Han _] & Hx1 & Hx5 & [Hwl Hwr])"; subst anl.
    iApply (fupd_semWP2 ⊤).
    iMod (written_nothingPending2 bytes_per_word with "Hinv Hwl Hwr") as "Hnp"; first solve_ndisj.
    iModIntro.
    iAssert (∃ v, reg_pointsTo21 x1 v)%I with "[Hx1]" as "Hx1"; first by iExists _.
    iAssert (∃ v, reg_pointsTo21 x5 v)%I with "[Hx5]" as "Hx5"; first by iExists _.
    iAssert (interp_gprs ∅) with "[Hgprs Hx1 Hx5]" as "Hgprs".
    { iApply (interp_gprs_with_excluded (exclude := {[x1; x5]})); try solve_subseteq.
      iFrame "Hgprs".
      reduce_big_sepS_big_sepL.
      iFrame "Hx1 Hx5". by cbn. }
    iPoseProof (ptsto_instrs_equiv with "[$Hcodel $Hcoder]") as "Hhdispatch".
    iPoseProof (ptsto_instrs_equiv with "[$Hnzl $Hnzr]") as "Hhnz".
    iPoseProof (ptsto_instrs_equiv with "[$Hizl $Hizr]") as "Hhiz".
    iAssert (pc ↦ᵣ bv.of_N handler_exit_addr)%I with "[Hpcl Hpcr]" as "Hpc".
    { unfold reg_pointsTo2. iFrame "Hpcl Hpcr". }
    iAssert (nextpc ↦ᵣ bv.of_N handler_exit_addr)%I with "[Hnpcl Hnpcr]" as "Hnpc".
    { unfold reg_pointsTo2. iFrame "Hnpcl Hnpcr". }
    iAssert (▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
               ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
               LoopVerificationBinary.M_Trap (femto_archstate priv ms ss pc) -∗ nothingPending2 -∗ powered2 true -∗ WP2_loop nothingPending2))%I
      with "[Hk Hhdispatch Hhnz Hhiz Hdata]" as "Hk".
    { iIntros "!>" (priv ms ss pc Hpriv) "Hhexit Htrap Hnp Hpow".
      iApply ("Hk" with "[//] Hhdispatch Hhnz Hhiz Hdata Hhexit Htrap Hnp Hpow"). }
    iApply (femtokernel_handler_exit_safe_rel _ _ Hmpp).
    iFrame "Hpc Hhexit Hmscratch HaccU Hmstatus Hgprs Hk Hinv Hnp Hpl Hpr"; cbn.
    iSplitL "Hnpc"; first by iExists _.
    repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
    now iPureIntro.
  Qed.

  Lemma femtokernel_handler_secret_write_safe_rel `{sailGS2 Σ} (vx1 secret1 secret2 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) (Hmpp : ArchState.mpp (ArchState.mstate archstate) ≠ Machine) :
    ⊢ femtokernel_safe_shared_pre2 handler_secret_write_addr femtokernel_handler_secret_write ∗
      asn.interpret femtokernel_handler_secret_write_pre_rel (csrs_valuation archstate vmie).["x1" ∷ ty_xlenbits ↦ vx1].["a" ∷ ty_xlenbits ↦ bv.of_N handler_secret_write_addr] ∗
      interp_gprs {[x1]} ∗
      interp_ptstomem2 (bv.of_N data_addr) secret1 secret2 ∗
      nothingPending2 ∗
      powered2 true ∗
      ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) ∗
      ▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
         ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) -∗
         interp_ptstomem2 (bv.of_N data_addr) secret1 secret2 -∗
         ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
         LoopVerificationBinary.M_Trap (femto_archstate priv ms ss pc) -∗ nothingPending2 -∗ powered2 true -∗ WP2_loop nothingPending2)
      -∗
      WP2_loop nothingPending2.
  Proof.
    iIntros "((Hpro & Hmscratch & HaccU) & Hpre & Hgprs & Hdata & Hnp & Hpow & Hhexit & Htrap)".
    iPoseProof (femtokernel_handler_secret_write_pre_persistent_preds with "Hpre")
                 as "(#Hinv & Hpre)".
    iApply (WP2_loop_semTripleBlock (λ a, asn.interpret femtokernel_handler_secret_write_pre_rel _) _ _
              (λ a na, asn.interpret femtokernel_handler_secret_write_post_rel _
                       ∗ interp_ptstomem2 (bv.of_N data_addr) secret1 secret2)%I
             with "Hpow Hpro Hpre [Hdata]").
    - iIntros "Hpre".
      iPoseProof (femtokernel_handler_secret_write_pre_binary_split with "[$Hpre $Hdata]")
        as "(Hpre1 & Hpre2)".
      iPoseProof (contract_femtohandler_secret_write_verified__l vx1 secret1 (bv.of_N handler_secret_write_addr) archstate vmie with "Hpre1") as "H1".
      iPoseProof (contract_femtohandler_secret_write_verified__r vx1 secret2 (bv.of_N handler_secret_write_addr) archstate vmie with "Hpre2") as "H2".
      iApply (step_n_focus with "H1 H2").
      iIntros (na1 na2) "(H1 & H2)".
      iApply (femtokernel_handler_secret_write_post_binary_combine with "H1 H2").
    - iIntros (an) "(Hpost & Hepi & Hpow)".
      iDestruct "Hepi" as "(Hpc & Hinstrs & Hnpc)".
      iDestruct "Hpost" as "((Hshared & Hmstatus & [%Han _] & Hx1) & Hdata)"; cbn - [interp_ptstomem] in *.
      iAssert (interp_gprs ∅) with "[Hgprs Hx1]" as "Hgprs".
      { iApply (interp_gprs_with_excluded (exclude := {[x1]}));
          try solve_subseteq.
        iFrame "Hgprs".
        reduce_big_sepS_big_sepL.
        now iFrame "Hx1". }
      iAssert (▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
                 ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
                 LoopVerificationBinary.M_Trap (femto_archstate priv ms ss pc) -∗ nothingPending2 -∗ powered2 true -∗ WP2_loop nothingPending2))%I
        with "[Htrap Hinstrs Hdata]" as "Htrap".
      { iIntros "!>" (priv ms ss pc Hpriv) "Hhexit' Htrap' Hnp Hpow".
        iApply ("Htrap" with "[//] Hinstrs Hdata Hhexit' Htrap' Hnp Hpow"). }
      iApply (femtokernel_handler_exit_safe_rel _ _ Hmpp).
      rewrite Han.
      iFrame "Hpc Hhexit Hnpc Hmscratch HaccU Hmstatus Hgprs Htrap Hinv Hnp Hpow"; cbn - [interp_ptstomem].
      repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
      now iPureIntro.
  Qed.

  (* The shutdown check, followed by either powering off both machines, or by
     the secret write. The shutdown request is public, so both executions
     take the same branch. *)
  Lemma femtokernel_handler_shutdown_check_safe_rel `{sailGS2 Σ} (vx1 vx5 vx10 secret1 secret2 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) (Hmpp : ArchState.mpp (ArchState.mstate archstate) ≠ Machine) :
    ⊢ femto_inv_mmio -∗
      femtokernel_safe_shared_pre2 handler_shutdown_check_addr femtokernel_handler_shutdown_check ∗
      asn.interpret femtokernel_handler_shutdown_check_pre (csrs_valuation archstate vmie).["x1" ∷ ty_xlenbits ↦ vx1].["x5" ∷ ty_xlenbits ↦ vx5].["x10" ∷ ty_xlenbits ↦ vx10].["a" ∷ ty_xlenbits ↦ bv.of_N handler_shutdown_check_addr] ∗
      interp_gprs {[x1; x5; x10]} ∗
      interp_ptstomem2 (bv.of_N data_addr) secret1 secret2 ∗
      nothingPending2 ∗
      powered2 true ∗
      ptsto_instrs (bv.of_N handler_shutdown_addr) (filter_AST femtokernel_handler_shutdown) ∗
      ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) ∗
      ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) ∗
      ▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
         ptsto_instrs (bv.of_N handler_shutdown_check_addr) (filter_AST femtokernel_handler_shutdown_check) -∗
         ptsto_instrs (bv.of_N handler_shutdown_addr) (filter_AST femtokernel_handler_shutdown) -∗
         ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) -∗
         interp_ptstomem2 (bv.of_N data_addr) secret1 secret2 -∗
         ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
         LoopVerificationBinary.M_Trap (femto_archstate priv ms ss pc) -∗ nothingPending2 -∗ powered2 true -∗ WP2_loop nothingPending2)
      -∗
      WP2_loop nothingPending2.
  Proof.
    iIntros "#Hinv ((Hpro & Hmscratch & HaccU) & Hpre & Hgprs & Hdata & Hnp & Hpow & Hhshutdown & Hhsecret & Hhexit & Hk)".
    iApply (WP2_loop_semTripleBlock (λ a, asn.interpret femtokernel_handler_shutdown_check_pre _) _ _
              (λ a na, asn.interpret femtokernel_handler_shutdown_check_post _)
             with "Hpow Hpro Hpre []").
    - iIntros "Hpre".
      iPoseProof (femtokernel_handler_shutdown_check_pre_binary_split with "Hpre") as "(Hpre1 & Hpre2)".
      iPoseProof (contract_femtohandler_shutdown_check_verified__l vx1 vx5 vx10 (bv.of_N handler_shutdown_check_addr) archstate vmie with "Hpre1") as "H1".
      iPoseProof (contract_femtohandler_shutdown_check_verified__r vx1 vx5 vx10 (bv.of_N handler_shutdown_check_addr) archstate vmie with "Hpre2") as "H2".
      iApply (step_n_focus with "H1 H2").
      iIntros (na1 na2) "(H1 & H2)".
      iApply (femtokernel_handler_shutdown_check_post_binary_combine with "H1 H2").
    - iIntros (an) "(Hpost & Hepi & Hpow)".
      iDestruct "Hepi" as "(Hpc & Hinstrs & Hnpc)".
      iEval (cbn - [interp_ptstomem]) in "Hpost".
      iDestruct "Hpost" as "(Hshared & Hmstatus & Han & Hx1 & Hx5 & Hx10)".
      case_match; iDestruct "Han" as "[-> _]".
      + (* Power off both machines. *)
        iAssert (semTripleBlock
                   (λ a, asn.interpret femtokernel_handler_shutdown_pre (csrs_valuation archstate vmie).["a" ∷ ty_xlenbits ↦ a])
                   (bv.of_N handler_shutdown_addr) (filter_AST femtokernel_handler_shutdown)
                   (λ a na, asn.interpret femtokernel_handler_shutdown_post (csrs_valuation archstate vmie).["a" ∷ ty_xlenbits ↦ a].["an" ∷ ty_xlenbits ↦ na]))%I
          as "Htrip'".
        { iIntros "Hpre".
          iPoseProof (femtokernel_handler_shutdown_pre_binary_split with "Hpre") as "(Hpre1 & Hpre2)".
          iPoseProof (contract_femtohandler_shutdown_verified__l (bv.of_N handler_shutdown_addr) archstate vmie with "Hpre1") as "H1".
          iPoseProof (contract_femtohandler_shutdown_verified__r (bv.of_N handler_shutdown_addr) archstate vmie with "Hpre2") as "H2".
          iApply (step_n_focus with "H1 H2").
          iIntros (na1 na2) "(H1 & H2)".
          iApply (femtokernel_handler_shutdown_post_binary_combine with "H1 H2"). }
        iApply (WP2_loop_semTripleBlock_power_off with "Hpow [Hpc Hhshutdown Hnpc] [Hshared Hmstatus Hx5 Hnp] Htrip'").
        * iFrame "Hpc Hhshutdown Hnpc".
        * cbn - [interp_ptstomem].
          iFrame "Hinv Hmstatus Hx5 Hnp".
          repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
          repeat iSplit; try iPureIntro; try done; by vm_compute.
        * iIntros "!>" (an') "(Hpost & _ & [Hoffl Hoffr])".
          iEval (cbn) in "Hpost". iDestruct "Hpost" as "(_ & [Hwl Hwr])".
          iApply (fupd_semWP2 ⊤).
          iMod (written_nothingPending2 bytes_per_word with "Hinv Hwl Hwr") as "Hnp"; first solve_ndisj.
          iModIntro. unfold WP2_loop.
          iApply (semWP2_fun_loop_off with "Hoffl Hoffr").
          iIntros "_ _". iFrame "Hnp". done.
      + (* Perform the secret write. *)
        iAssert (interp_gprs {[x1]}) with "[Hgprs Hx5 Hx10]" as "Hgprs".
        { iApply (interp_gprs_with_excluded_gen {[x1]} (exclude2 := {[x5; x10]})); try solve_subseteq.
          iFrame "Hgprs".
          reduce_big_sepS_big_sepL.
          iFrame "Hx5 Hx10". by cbn. }
        iAssert (▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
                   ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) -∗
                   interp_ptstomem2 (bv.of_N data_addr) (secret1 : Val ty_xlenbits) secret2 -∗
                   ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
                   LoopVerificationBinary.M_Trap (femto_archstate priv ms ss pc) -∗ nothingPending2 -∗ powered2 true -∗ WP2_loop nothingPending2))%I
          with "[Hk Hinstrs Hhshutdown]" as "Hksecret".
        { iIntros "!>" (priv ms ss pc Hpriv) "Hhsecret Hdata Hhexit Htrap Hnp Hpow".
          iApply ("Hk" with "[//] Hinstrs Hhshutdown Hhsecret Hdata Hhexit Htrap Hnp Hpow"). }
        iApply (femtokernel_handler_secret_write_safe_rel _ _ _ _ _ Hmpp); cbn - [interp_ptstomem].
        iFrame "Hhsecret Hpc Hnpc Hmscratch HaccU Hmstatus Hgprs Hhexit Hx1 Hdata Hnp Hpow Hksecret Hinv".
        repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
        repeat iSplit; try iPureIntro; try done; by vm_compute.
  Qed.

  Lemma femtokernel_handler_entry_safe_rel `{sailGS2 Σ} (x5_val x10_val : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) (Hmpp : ArchState.mpp (ArchState.mstate archstate) ≠ Machine) :
    ⊢ femtokernel_safe_shared_pre2 handler_entry_addr femtokernel_handler_entry ∗
      asn.interpret femtokernel_handler_entry_pre (csrs_valuation archstate vmie).["x5" ∷ ty_xlenbits ↦ x5_val].["x10" ∷ ty_xlenbits ↦ x10_val].["a" ∷ ty_xlenbits ↦ bv.of_N handler_entry_addr] ∗
      interp_gprs {[ x1; x5; x10 ]} ∗
      (∃ v, x1 ↦ᵣ v) ∗
      (∃ (v1 v2 : Val ty_xlenbits), interp_ptstomem2 (bv.of_N data_addr) v1 v2) ∗
      nothingPending2 ∗
      powered2 true ∗
      ptsto_instrs (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) ∗
      ptsto_instrs (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) ∗
      ptsto_instrs (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) ∗
      ptsto_instrs (bv.of_N handler_shutdown_check_addr) (filter_AST femtokernel_handler_shutdown_check) ∗
      ptsto_instrs (bv.of_N handler_shutdown_addr) (filter_AST femtokernel_handler_shutdown) ∗
      ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) ∗
      ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit)
      -∗
      WP2_loop nothingPending2.
  Proof.
    iLöb as "IH" forall (x5_val x10_val archstate vmie Hmpp).
    iIntros "((Hpro & Hmscratch & HaccU) & Hpre & Hgprs & Hx1 & Hdata & Hnp & Hpow & Hhdispatch & Hhnotzero & Hhiszero & Hhcheck & Hhshutdown & Hhsecret & Hhexit)".
    iPoseProof (femtokernel_handler_entry_pre_persistent_preds with "Hpre")
                 as "(#Hinv & Hpre)".
    (* When the adversary traps back into the handler, we are back at the
       start of this lemma (with possibly different CSR values). *)
    iAssert (▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
               ptsto_instrs_handler2 ∗ (∃ (v1 v2 : Val ty_xlenbits), interp_ptstomem2 (bv.of_N data_addr) v1 v2) -∗
               LoopVerificationBinary.M_Trap (femto_archstate priv ms ss pc) -∗ nothingPending2 -∗ powered2 true -∗ WP2_loop nothingPending2))%I with "[]" as "#Hk".
    { iIntros "!>" (priv ms ss pc Hpriv) "(Hhandler & Hdata) Htrap Hnp Hpow".
      iDestruct (ptsto_instrs_handler2_equiv with "Hhandler") as "(Hhentry & Hhdispatch & Hhnotzero & Hhiszero & Hhcheck & Hhshutdown & Hhsecret & Hhexit)".
      assert (HU : User ≠ Machine) by auto.
      iPoseProof (LoopVerificationBinary.M_Trap_SU_irrelevant (femto_archstate priv ms ss pc) (femto_archstate User ms ss pc)
                    Hpriv HU eq_refl with "Htrap") as "Htrap".
      unfold LoopVerificationBinary.M_Trap, LoopVerificationBinary.transition; cbn.
      iDestruct "Htrap" as "(HaccU & Hgprs & Hpmp & [%vmie' Hmie] & Hmip & Hcurpriv & Hpc & Hnpc & Hmtvec & [%vstvec Hstvec] & [%vspp [%vmpie [%vspie [%vsie [%vmpp (Hmstatus & [%Hmpp' _])]]]]] & [%vmepc Hmepc] & [%vsepc Hsepc] & Hmideleg & Hmedeleg & [%vmscratch Hmscratch] & [%vmcause Hmcause] & [%vsscratch Hsscratch] & [%vscause Hscause])".
      iPoseProof (interp_gprs_with_excluded (exclude := {[x1;x5;x10]}) with "Hgprs") as "(Hregs & Hgprs)";
        try solve_subseteq.
      reduce_big_sepS_big_sepL.
      iDestruct "Hregs" as "([% Hx5] & Hx1 & [% Hx10] & _)".
      iApply ("IH" $! _ _
                (femto_handler_archstate vmpp vmpie vmcause vmscratch vmepc (ArchState.mkSState vstvec (MkSstatus vspp vspie vsie) vscause vsscratch vsepc)) vmie' with "[//]").
      cbn - [interp_ptstomem].
      iFrame "Hhentry Hpc Hnpc Hmscratch HaccU Hcurpriv Hmtvec Hmcause Hmip Hmie Hmepc Hsepc Hscause Hsscratch Hstvec Hmideleg Hmedeleg Hpmp Hinv Hmstatus Hgprs Hx5 Hx10 Hx1 Hdata Hnp Hpow Hhdispatch Hhnotzero Hhiszero Hhcheck Hhshutdown Hhsecret Hhexit".
      auto. }
    iApply (WP2_loop_semTripleBlock (λ a, asn.interpret femtokernel_handler_entry_pre _) _ _
              (λ a na, asn.interpret femtokernel_handler_entry_post _)
             with "Hpow Hpro Hpre []").
    - iIntros "Hpre".
      iPoseProof (femtokernel_handler_entry_pre_binary_split with "Hpre")
        as "(Hpre1 & Hpre2)".
      iPoseProof (contract_femtohandler_entry_verified__l x5_val x10_val (bv.of_N handler_entry_addr) archstate vmie with "Hpre1") as "H1".
      iPoseProof (contract_femtohandler_entry_verified__r x5_val x10_val (bv.of_N handler_entry_addr) archstate vmie with "Hpre2") as "H2".
      iApply (step_n_focus with "H1 H2").
      iIntros (na1 na2) "(H1 & H2)".
      iApply (femtokernel_handler_entry_post_binary_combine with "H1 H2").
    - iIntros (an) "(Hpost & Hepi & Hpow)".
      iDestruct "Hepi" as "(Hpc & Hinstrs & Hnpc)".
      iDestruct "Hpost" as "((Hcurpriv & Hmtvec & Hmcause & Hmip & Hmie & Hmepc & Hsepc & Hscause & Hsscratch & Hstvec & Hmideleg & Hmedeleg & Hpmp) & Hmstatus & Han & Hx5 & Hx10)"; cbn - [interp_ptstomem].
      iDestruct "Hx1" as "[% Hx1]".
      case_match; cbn - [interp_ptstomem];
        iDestruct "Han" as "[-> _]".
      + (* Dispatch on the secret. *)
        iAssert (interp_gprs {[ x1; x5 ]}) with "[Hgprs Hx10]" as "Hgprs".
        { iApply (interp_gprs_with_excluded_gen {[x1; x5]} (exclude2 := {[x10]}));
            try solve_subseteq.
          iFrame "Hgprs".
          reduce_big_sepS_big_sepL.
          now iFrame "Hx10". }
        iAssert (interp_gprs {[ x1 ]}) with "[Hgprs Hx5]" as "Hgprs".
        { iApply (interp_gprs_with_excluded_gen {[x1]} (exclude2 := {[x5]}));
            try solve_subseteq.
          iFrame "Hgprs".
          reduce_big_sepS_big_sepL.
          now iFrame "Hx5". }
        iDestruct "Hdata" as "(%secret1 & %secret2 & Hdata)".
        iAssert (▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
                   ptsto_instrs (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) -∗
                   ptsto_instrs (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) -∗
                   ptsto_instrs (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) -∗
                   interp_ptstomem2 (bv.of_N data_addr) (secret1 : Val ty_xlenbits) secret2 -∗
                   ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
                   LoopVerificationBinary.M_Trap (femto_archstate priv ms ss pc) -∗ nothingPending2 -∗ powered2 true -∗ WP2_loop nothingPending2))%I
          with "[Hinstrs Hhcheck Hhshutdown Hhsecret]" as "Hkdispatch".
        { iIntros "!>" (priv ms ss pc Hpriv) "Hhdispatch Hhnotzero Hhiszero Hdata Hhexit Htrap Hnp Hpow".
          iApply ("Hk" with "[//] [Hinstrs Hhdispatch Hhnotzero Hhiszero Hhcheck Hhshutdown Hhsecret Hhexit Hdata] Htrap Hnp Hpow").
          iSplitR "Hdata"; last by iExists _, _.
          iApply ptsto_instrs_handler2_equiv.
          iFrame "Hinstrs Hhdispatch Hhnotzero Hhiszero Hhcheck Hhshutdown Hhsecret Hhexit". }
        iApply (femtokernel_handler_dispatch_safe_rel _ _ _ _ _ Hmpp).
        iFrame "Hkdispatch"; cbn - [interp_ptstomem].
        iFrame "Hhdispatch Hpc Hnpc Hmscratch HaccU Hcurpriv Hmtvec Hmcause Hmip Hmie Hmepc Hsepc Hscause Hsscratch Hstvec Hmideleg Hmedeleg Hpmp Hinv Hmstatus Hgprs Hhnotzero Hhiszero Hhexit Hx1 Hdata Hnp Hpow";
          repeat iSplitR; auto.
      + (* Check for a shutdown request. *)
        iDestruct "Hdata" as "(%secret1 & %secret2 & Hdata)".
        iAssert (▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
                   ptsto_instrs (bv.of_N handler_shutdown_check_addr) (filter_AST femtokernel_handler_shutdown_check) -∗
                   ptsto_instrs (bv.of_N handler_shutdown_addr) (filter_AST femtokernel_handler_shutdown) -∗
                   ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) -∗
                   interp_ptstomem2 (bv.of_N data_addr) (secret1 : Val ty_xlenbits) secret2 -∗
                   ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
                   LoopVerificationBinary.M_Trap (femto_archstate priv ms ss pc) -∗ nothingPending2 -∗ powered2 true -∗ WP2_loop nothingPending2))%I
          with "[Hinstrs Hhdispatch Hhnotzero Hhiszero]" as "Hkcheck".
        { iIntros "!>" (priv ms ss pc Hpriv) "Hhcheck Hhshutdown Hhsecret Hdata Hhexit Htrap Hnp Hpow".
          iApply ("Hk" with "[//] [Hinstrs Hhdispatch Hhnotzero Hhiszero Hhcheck Hhshutdown Hhsecret Hhexit Hdata] Htrap Hnp Hpow").
          iSplitR "Hdata"; last by iExists _, _.
          iApply ptsto_instrs_handler2_equiv.
          iFrame "Hinstrs Hhdispatch Hhnotzero Hhiszero Hhcheck Hhshutdown Hhsecret Hhexit". }
        iApply (femtokernel_handler_shutdown_check_safe_rel _ _ _ _ _ _ _ Hmpp with "Hinv").
        iFrame "Hkcheck"; cbn - [interp_ptstomem].
        iFrame "Hhcheck Hpc Hnpc Hmscratch HaccU Hcurpriv Hmtvec Hmcause Hmip Hmie Hmepc Hsepc Hscause Hsscratch Hstvec Hmideleg Hmedeleg Hpmp Hinv Hmstatus Hgprs Hx1 Hx5 Hx10 Hdata Hnp Hpow Hhshutdown Hhsecret Hhexit";
          repeat iSplitR; auto.
  Qed.

  Lemma memAdv_pmpPolicy_binary `{sailGS2 Σ} :
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

  Lemma femtokernel_handler_safe_rel `{sailGS2 Σ} :
    ⊢ femto_inv_mmio -∗
      ∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
        ptsto_instrs_handler2 ∗ (∃ (v1 v2 : Val ty_xlenbits), interp_ptstomem2 (bv.of_N data_addr) v1 v2) -∗
        LoopVerificationBinary.M_Trap (femto_archstate priv ms ss pc) -∗ nothingPending2 -∗ powered2 true -∗ WP2_loop nothingPending2.
  Proof.
    iIntros "#Hinv" (priv ms ss pc Hpriv) "(Hhandler & Hdata) Htrap Hnp Hpow".
    iDestruct (ptsto_instrs_handler2_equiv with "Hhandler") as "(Hhentry & Hhdispatch & Hhnotzero & Hhiszero & Hhcheck & Hhshutdown & Hhsecret & Hhexit)".
    (* Traps from S-mode look the same as traps from U-mode *)
    assert (HU : User ≠ Machine) by auto.
    iPoseProof (LoopVerificationBinary.M_Trap_SU_irrelevant (femto_archstate priv ms ss pc) (femto_archstate User ms ss pc)
                  Hpriv HU eq_refl with "Htrap") as "Htrap".
    unfold LoopVerificationBinary.M_Trap, LoopVerificationBinary.transition; cbn.
    iDestruct "Htrap" as "(HaccU & Hgprs & Hpmp & [%vmie Hmie] & Hmip & Hcurpriv & Hpc & Hnpc & Hmtvec & [%vstvec Hstvec] & [%vspp [%vmpie [%vspie [%vsie [%vmpp (Hmstatus & [%Hmpp _])]]]]] & [%vmepc Hmepc] & [%vsepc Hsepc] & Hmideleg & Hmedeleg & [%vmscratch Hmscratch] & [%vmcause Hmcause] & [%vsscratch Hsscratch] & [%vscause Hscause])".
    iPoseProof (interp_gprs_with_excluded (exclude := {[x1;x5;x10]}) with "Hgprs") as "(Hregs & Hgprs)";
      try solve_subseteq.
    reduce_big_sepS_big_sepL.
    iDestruct "Hregs" as "([% Hx5] & Hx1 & [% Hx10] & _)".
    iApply (femtokernel_handler_entry_safe_rel _ _
              (femto_handler_archstate vmpp vmpie vmcause vmscratch vmepc (ArchState.mkSState vstvec (MkSstatus vspp vspie vsie) vscause vsscratch vsepc)) vmie Hmpp).
    cbn - [interp_ptstomem].
    iFrame "Hhentry Hpc Hnpc Hmscratch HaccU Hcurpriv Hmtvec Hmcause Hmip Hmie Hmepc Hsepc Hscause Hsscratch Hstvec Hmideleg Hmedeleg Hpmp Hinv Hmstatus Hgprs Hx5 Hx10 Hx1 Hdata Hnp Hpow Hhdispatch Hhnotzero Hhiszero Hhcheck Hhshutdown Hhsecret Hhexit".
    auto.
  Qed.

  Lemma femtokernel_manualStep2_rel `{sailGS2 Σ} :
    ⊢ (∃ mpp mpie mie, mstatus ↦ᵣ {| MPP := mpp; SPP := User; MPIE := mpie; SPIE := false; MIE := mie; SIE := false |}) ∗
      (mtvec ↦ᵣ (bv.of_N handler_entry_addr)) ∗
      (∃ v, mcause ↦ᵣ v) ∗
      (∃ v, mip ↦ᵣ v) ∗ (∃ v, mie ↦ᵣ v) ∗
      (∃ v, mscratch ↦ᵣ v) ∗
      (∃ v, mepc ↦ᵣ v) ∗
      (∃ v, scause ↦ᵣ v) ∗
      (∃ v, sscratch ↦ᵣ v) ∗
      (∃ v, sepc ↦ᵣ v) ∗
      (∃ v, stvec ↦ᵣ v) ∗
      mideleg ↦ᵣ Minterrupts_zero ∗
      medeleg ↦ᵣ Medeleg_zero ∗
      cur_privilege ↦ᵣ User ∗
      interp_gprs ∅ ∗
      interp_pmp_entries femto_pmpentries ∗
      femto_inv_mmio ∗
      (pc ↦ᵣ (bv.of_N adv_addr)) ∗
      (∃ v, nextpc ↦ᵣ v) ∗
      ptsto_instrs_handler2 ∗
      (∃ (v1 v2 : Val ty_xlenbits), interp_ptstomem2 (bv.of_N data_addr) v1 v2) ∗
      ptstoSthL advAddrs ∗
      nothingPending2 ∗
      powered2 true
      ={⊤}=∗
      ∃ mpp mcause mscratch mepc scause sscratch sepc stvec mpie mie, LoopVerificationBinary.loop_pre nothingPending2
             (femto_adv_archstate mpp mpie mie mcause mscratch mepc stvec scause sscratch sepc).
  Proof.
    iIntros "((%mpp & %mpie & %mie & Hmst) & Hmtvec & [%vmcause Hmcause] & Hmip & Hmie & [%vmscratch Hmscratch] & [%vmepc Hmepc] & [%vscause Hscause] & [%vsscratch Hsscratch] & [%vsepc Hsepc] & [%vstvec Hstvec] & Hmideleg & Hmedeleg & Hcurpriv & Hgprs & Hpmpcfg & #Hmmio & Hpc & Hnpc & Hhandler & Hdata & Hmemadv & Hnp & Hpow)".
    cbn - [ptstoSthL interp_ptstomem LoopVerificationBinary.loop_pre femto_archstate ptsto_instrs_handler2].
    iExists mpp, vmcause, vmscratch, vmepc, vscause, vsscratch, vsepc, vstvec, mpie, mie.
    iModIntro.
    unfold LoopVerificationBinary.loop_pre.
    iSplitR "Hhandler Hdata Hnp Hpow".
    - unfold LoopVerificationBinary.Step_pre.
      cbn - [ptstoSthL interp_ptstomem].
      iFrame "Hgprs Hpmpcfg Hmie Hmip Hcurpriv Hpc Hnpc Hmtvec Hstvec Hmst Hmepc Hsepc Hmideleg Hmedeleg Hmscratch Hsscratch Hmcause Hscause".
      iSplitR; first auto.
      by iApply memAdv_pmpPolicy_binary.
    - iFrame "Hnp Hpow".
      iSplitR.
      { iIntros "!> [H' _]". iDestruct (LoopVerificationBinary.M_CSRMod_machine with "H'") as %Heq.
        cbn in Heq; discriminate Heq. }
      iSplitL "Hhandler Hdata".
      { iIntros "!> (H' & Hnp & Hpow)".
        iApply (femtokernel_handler_safe_rel with "Hmmio [] [$Hhandler $Hdata] H' Hnp Hpow").
        iPureIntro; discriminate. }
      iSplitR.
      { iIntros "!> [H' _]". iDestruct (LoopVerificationBinary.MRET_machine with "H'") as %Heq.
        cbn in Heq; discriminate Heq. }
      iIntros "!> [H' _]". iDestruct (LoopVerificationBinary.SRET_machine with "H'") as %Heq.
      cbn in Heq; discriminate Heq.
  Qed.

  Lemma femtokernel_init_safe_rel `{sailGS2 Σ} (archstate : ArchState) (vmie : Val ty_Minterrupts) :
    ⊢ exec_instructions_prologue (bv.of_N init_addr) (filter_AST femtokernel_init_gen)
      ∗ ptsto_instrs_handler2
      ∗ ptstoSthL advAddrs
      ∗ asn.interpret femtokernel_init_pre (csrs_valuation archstate vmie).["a" ∷ ty_xlenbits ↦ bv.of_N init_addr]
      ∗ interp_gprs {[x1]}
      ∗ (∃ (v1 v2 : Val ty_xlenbits), interp_ptstomem2 (bv.of_N data_addr) v1 v2)
      ∗ (∃ v, mscratch ↦ᵣ v)
      ∗ (∃ v : Val ty_scause, scause ↦ᵣ v)
      ∗ (∃ v : Val ty_xlenbits, sscratch ↦ᵣ v)
      ∗ (∃ v : Val ty_xlenbits, sepc ↦ᵣ v)
      ∗ (∃ v : Val ty_xlenbits, stvec ↦ᵣ v)
      ∗ femto_inv_mmio
      ∗ nothingPending2
      ∗ powered2 true
        -∗
        WP2_loop nothingPending2.
  Proof.
    iIntros "(Hpro & Hhandler & Hadv & Hpre & Hgprs & Hdata & Hmscratch & Hscause & Hsscratch & Hsepc & Hstvec & #Hmem & Hnp & Hpow)".
    iApply (WP2_loop_semTripleBlock (λ a, asn.interpret femtokernel_init_pre _) _ _
                                    (λ a na, asn.interpret femtokernel_init_post (csrs_valuation archstate vmie).["a"∷ty_xlenbits ↦ a].["an"∷ty_xlenbits ↦ na])
             with "Hpow Hpro Hpre []").
    iIntros "Hpre".
    iPoseProof (femtokernel_init_pre_binary_split archstate vmie with "Hpre") as "(Hpre1 & Hpre2)".
    iPoseProof (contract_femtoinit_verified__l (bv.of_N init_addr) archstate vmie with "Hpre1") as "H1".
    iPoseProof (contract_femtoinit_verified__r (bv.of_N init_addr) archstate vmie with "Hpre2") as "H2".
    iApply (step_n_focus with "H1 H2").
    iIntros (na1 na2) "(H1 & H2)".
    now iPoseProof (femtokernel_init_post_binary_combine with "H1 H2") as "(<- & $)".
    iIntros (an) "(Hpost & Hepi & Hpow)".
    cbn - [asn_regs_ptsto interp_pmp_entries].
    iDestruct "Hpost" as "([-> _] & Hmtvec & Hmcause & Hmip & Hmie & Hmepc & Hmstatus & Hmideleg & Hmedeleg & Hcurpriv & Hx1 & Hpmpentries)".
    iAssert (interp_gprs ∅) with "[Hgprs Hx1]" as "Hgprs".
    { iApply (interp_gprs_with_excluded (exclude := {[x1]}));
        try solve_subseteq.
      reduce_big_sepS_big_sepL.
      now iFrame "Hx1 Hgprs". }
    iDestruct "Hepi" as "(Hpc & Hinstrs & Hnpc)".
    rewrite ?bv.add_zero_l.
    iApply (fupd_semWP2 ⊤).
    iMod (femtokernel_manualStep2_rel with "[$Hmstatus $Hmtvec $Hmcause $Hmip $Hmie $Hmscratch $Hmepc $Hscause $Hsscratch $Hsepc $Hstvec $Hmideleg $Hmedeleg $Hcurpriv $Hgprs $Hpmpentries $Hmem $Hpc $Hnpc $Hhandler $Hdata $Hadv $Hnp $Hpow]") as "(%mpp & %mcause & %mscratch & %mepc & %scause & %sscratch & %sepc & %stvec & %mpie & %mie & Hlooppre)".
    iModIntro.
    iApply (LoopVerificationBinary.valid_semTriple_loop with "Hlooppre").
  Qed.

  Lemma intro_ptstoSthL_binary `{sailGS2 Σ} (μ : Memory) (addrs : list Xlenbits)  :
    ([∗ list] a' ∈ addrs, @RVPCOM.interp_ptsto _ memGS_left a' ((memory_ram μ) a'))
    ∗ ([∗ list] a' ∈ addrs, @RVPCOM.interp_ptsto _ memGS_right a' ((memory_ram μ) a'))
    ⊢ ptstoSthL addrs.
  Proof.
    induction addrs as [|a l]; cbn; auto.
    iIntros "[[Hmemal Hmeml] [Hmemar Hmemr]]".
    iSplitL "Hmemal Hmemar".
    - iExists ((memory_ram μ) a). iFrame "Hmemal Hmemar".
    - iApply IHl. iFrame "Hmeml Hmemr".
  Qed.

  Definition obs_equiv (t1 t2 : Trace) : Prop :=
    filter_adv_observable t1 = filter_adv_observable t2.

  Lemma femtokernel_splitMemory_rel `{sailGS2 Σ} {μ1 μ2 : Memory} (secret1 secret2 : Val ty_xlenbits) :
    mem_has_femtokernel μ1 secret1 ->
    mem_has_femtokernel μ2 secret2 ->
    mmio_pred bytes_per_word (memory_trace μ1) -> (* Either demand sensible data in memory, or a sensible history of trace events. Note that the extra handler instruction in the case of mmio is already captured by the previous conjunct *)
    mmio_pred bytes_per_word (memory_trace μ2) -> (* Either demand sensible data in memory, or a sensible history of trace events. Note that the extra handler instruction in the case of mmio is already captured by the previous conjunct *)
    obs_equiv (memory_trace μ1) (memory_trace μ2) -> (* Both executions start with the same adversary-observable history *)
    fun_powered_on μ1 = true -> fun_powered_on μ2 = true -> (* Both machines start powered on *)
    List.Forall (λ a, memory_ram μ1 a = memory_ram μ2 a) advAddrs -> (* We require that the memory the adversary can access is indistinguishable in the left and right memory *)
    RVPADEQ2.mem_res2 μ1 μ2 ⊢ |={⊤}=>
      ptsto_instrs (bv.of_N init_addr) (filter_AST femtokernel_init_gen) ∗
      ptsto_instrs_handler2 ∗
      interp_ptstomem2 (bv.of_N data_addr) secret1 secret2 ∗
      femto_inv_mmio ∗
      nothingPending2 ∗
      powered2 true ∗
      ptstoSthL advAddrs.
  Proof.
    iIntros (Hfk1 Hfk2 Hpred1 Hpred2 Hobs Hon1 Hon2 Hadv) "Hmem".
    iDestruct "Hmem" as "((Hmem1 & Htr1 & Hauth1 & Hnp1 & Hpw1) & (Hmem2 & Htr2 & Hauth2 & Hnp2 & Hpw2))".
    iDestruct (femtokernel_splitMemory (mG := memGS_left) Hfk1 with "Hmem1")
      as "(Hinit1 & Hhandler1 & Hdata1 & Hadv1)".
    iDestruct (femtokernel_splitMemory (mG := memGS_right) Hfk2 with "Hmem2")
      as "(Hinit2 & Hhandler2 & Hdata2 & Hadv2)".
    (* Both executions start in sync, with the same observable history. *)
    iMod (inv.inv_alloc RVPCOM.femto_inv_mmio_ns ⊤
            (∃ t, side_inv bytes_per_word mc_ghGS2_left t ∗ side_inv bytes_per_word mc_ghGS2_right t)
           with "[Htr1 Htr2 Hauth1 Hauth2]") as "#Hinv".
    { iNext. iExists (filter_adv_observable (memory_trace μ1)).
      iSplitL "Htr1 Hauth1".
      - iExists _. iFrame "Htr1". iSplitR; first done. iLeft. by iFrame "Hauth1".
      - iExists _. iFrame "Htr2". iSplitR; first done. iLeft. iFrame "Hauth2". rewrite /obs_equiv in Hobs. by rewrite Hobs. }
    iModIntro.
    rewrite ptsto_instrs_equiv.
    unfold ptsto_instrs_handler2, interp_ptstomem2, nothingPending2, femto_inv_mmio, interp_inv_mmio.
    iEval (rewrite Hon1) in "Hpw1". iEval (rewrite Hon2) in "Hpw2".
    iFrame "Hinit1 Hinit2 Hhandler1 Hhandler2 Hdata1 Hdata2 Hnp1 Hnp2 Hpw1 Hpw2 Hinv".
    iApply (intro_ptstoSthL_binary μ1 with "[$Hadv1 Hadv2]").
    iApply (big_sepL_impl with "Hadv2").
    iIntros "!>" (k a HIn) "H".
    pose proof (Forall_lookup_1 _ _ _ _ Hadv HIn) as Heq.
    cbn in Heq. by rewrite Heq.
  Qed.

  Import RiscvPmpSemantics.SmallStepNotations.

  Lemma femtokernel_rel_endToEnd {γ1 γ2 γ1' : RegStore} {μ1 μ1' μ2 : Memory}
    {δ1 δ1' δ2 : CStore [ctx]} {s1' : Stm [ctx] ty.unit} {v1 : IVal ty.unit} {secret1 secret2 : Val ty_xlenbits} :
    mem_has_femtokernel μ1 secret1 ->
    mem_has_femtokernel μ2 secret2 ->
    Forall (λ a : Addr, memory_ram μ1 a = memory_ram μ2 a) advAddrs -> (* We assume that the memory the adv has access to, before executing the kernel, contains the same values *)
    mmio_pred bytes_per_word (memory_trace μ1) -> (* Either demand sensible data in memory, or a sensible history of trace events. Note that the extra handler instruction in the case of mmio is already captured by the previous conjunct *)
    mmio_pred bytes_per_word (memory_trace μ2) -> (* Either demand sensible data in memory, or a sensible history of trace events. Note that the extra handler instruction in the case of mmio is already captured by the previous conjunct *)
    obs_equiv (memory_trace μ1) (memory_trace μ2) -> (* Both executions start with the same adversary-observable history *)
    fun_powered_on μ1 = true -> fun_powered_on μ2 = true -> (* Both machines start powered on *)
    (∀ {σ : Ty} (r : Reg σ), read_register γ1 r = read_register γ2 r) -> (* We require that the initial values of all registers are the same, as we consider these to be public. The secrets in our verification are part of MMIO. *)
    femto_init_regs γ1 ->
    (* For every terminating execution of the left machine, the right machine
       also terminates, with the same result (a value or a failure). *)
    ⟨ γ1, μ1, δ1, fun_loop ⟩ --->* ⟨ γ1', μ1', δ1', s1' ⟩ ->
    stm_to_val s1' = Some v1 ->
    ∃ γ2' μ2' δ2' s2',
      ⟨ γ2, μ2, δ2, fun_loop ⟩ --->* ⟨ γ2', μ2', δ2', s2' ⟩
      ∧ stm_to_val s2' = Some v1
      (* Confidentiality: adversary cannot distinguish both executions *)
      ∧ obs_equiv (memory_trace μ1') (memory_trace μ2')
      (* Integrity: both executions only performed allowed MMIO events *)
      ∧ mmio_pred bytes_per_word (memory_trace μ1')
      ∧ mmio_pred bytes_per_word (memory_trace μ2').
  Proof.
    intros μfk1 μfk2 μadv μft1 μft2 μobs μon1 μon2 γeq
      (γmstatus & γcurpriv & γpmp0cfg & γpmpaddr0 & γpmp1cfg & γpmpaddr1 & γpc & γmideleg & γmedeleg) steps1 Hval1.
    eapply (wp2_strong_adequacy fun_loop γ2 μ2 δ2 steps1 Hval1
              (Q := fun _ _ v1 δ1' v2 δ2' => ⌜v1 = v2⌝ ∗ ⌜δ1' = δ2'⌝ ∗ femto_inv_mmio ∗ nothingPending2)%I).
    iIntros (Σ sg).
    iSplitL.
    - iIntros "(Hmem & Hregs)".
      iMod (femtokernel_splitMemory_rel μfk1 μfk2 μft1 μft2 μobs μon1 μon2 μadv with "Hmem")
        as "(Hinit & Hhandler & Hdata & #Hmmio & Hnp & Hpow & Hadv)".
      destruct (nenv.view δ1), (nenv.view δ2).
      iPoseProof (femtokernel_init_safe_rel (femto_init_archstate γ1)
                   (read_register γ1 mie)
                   with "[-]") as "H".
      { #[local] Opaque ptsto_instrs. (* Avoid spinning because code is unfolded *)
        iFrame "Hinit Hhandler Hadv Hdata Hmmio Hnp Hpow". cbn - [interp_gprs].
        rewrite <- ?γeq.
        rewrite γmstatus γcurpriv γpmp0cfg γpmpaddr0 γpmp1cfg γpmpaddr1 γpc γmideleg γmedeleg.
        iDestruct "Hregs" as "($ & $ & Hregs)".
        rewrite <- ?bi.sep_assoc.
        iSplitR; first auto.
        rewrite <- ?bi.sep_assoc.
        repeat first [iDestruct "Hregs" as "($ & Hregs)"
                     | iDestruct "Hregs" as "(? & Hregs)"].
        unfold interp_gprs; reduce_big_sepS_big_sepL; cbn.
        iAssert (□ ∀ r v, (reg_pointsTo2 r v v -∗ ∃ v, reg_pointsTo21 r v))%I as "#Heq".
        { iModIntro. iIntros (? v) "H". iExists v. iFrame "H". }
        repeat try (iRename select (reg_pointsTo2 _ _ _) into "Hpts";
                    iPoseProof ("Heq" with "Hpts") as "Hpts";
                    iFrame "Hpts"). }
      iModIntro.
      iApply (semWP2_mono with "H").
      iIntros (? ? ? ?) "($ & $ & $)". iFrame "Hmmio".
    - iIntros (γ2' μ2' δ2' s2' v2 steps2 Hval) "(%Hv & _ & #Hmmio & [Hnpl Hnpr]) Hmem".
      iDestruct "Hmem" as "[(%memmap1 & Hinv1 & %link1 & Htr1 & _)
                            (%memmap2 & Hinv2 & %link2 & Htr2 & _)]".
      iInv "Hmmio" as ">(%t & (%t1 & Hf1 & %Hpred1 & H1) & (%t2 & Hf2 & %Hpred2 & H2))" "_".
      iDestruct (trace.trace_full_frag_eq with "Htr1 Hf1") as %<-.
      iDestruct (trace.trace_full_frag_eq with "Htr2 Hf2") as %<-.
      iAssert (⌜filter_adv_observable (memory_trace μ1') = t⌝)%I with "[H1 Hnpl]" as %Hobs1.
      { iDestruct "H1" as "[[%Heq _] | (%e & _ & Hauth)]"; first done.
        iDestruct (RVPCOM.written_auth_nothingPending with "Hauth Hnpl") as "[]". }
      iAssert (⌜filter_adv_observable (memory_trace μ2') = t⌝)%I with "[H2 Hnpr]" as %Hobs2.
      { iDestruct "H2" as "[[%Heq _] | (%e & _ & Hauth)]"; first done.
        iDestruct (RVPCOM.written_auth_nothingPending with "Hauth Hnpr") as "[]". }
      iApply fupd_mask_intro; first set_solver. iIntros "_".
      iPureIntro. exists γ2', μ2', δ2', s2'.
      split; first done. split; first by rewrite Hval Hv.
      split; first by rewrite /obs_equiv Hobs1 Hobs2.
      done.
  Qed.

End RelationalVerification.
