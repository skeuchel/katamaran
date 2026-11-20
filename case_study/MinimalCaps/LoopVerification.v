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
     Lists.List.
From Katamaran Require Import
     Bitvector
     Environment
     MicroSail.ShallowVCGen
     MicroSail.ShallowSoundness
     MicroSail.RefineVCGen
     MicroSail.Soundness
     Iris.Instance
     Iris.Base
     Program
     Semantics
     Sep.Hoare
     Sep.Logic
     MinimalCaps.Machine
     MinimalCaps.Sig
     MinimalCaps.Model
     MinimalCaps.Contracts.Definitions
     MinimalCaps.Contracts.Verification.

From iris.base_logic Require lib.gen_heap lib.iprop.
From iris.base_logic Require Export invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac.
From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import string_ident proofmode.

Set Implicit Arguments.
Import ListNotations.
Import MinCapsSpecification.
Import MinCapsProgram.
Import MinCapsIrisPrelims.
Import MinCapsIrisBase.
Import MinCapsIrisInstance.
Import MinCapsIrisInstanceWithContracts.
Import MinCapsValidContracts.

Import MinCapsSignature.

Section Loop.
  Context `{sg : sailGS Σ}.
  Import env.notations.

  Definition semWP' {Γ τ} (δ : CStore Γ) (s : Stm Γ τ)
    (Q : Val τ -> CStore Γ -> iProp Σ) : iProp Σ :=
    semWP δ s (λ v δ, match v with
                    | inl v => Q v δ
                    | inr m => True%I
                    end).

  Lemma semWP'_semWP {Γ τ} {s : Stm Γ τ} {Q POST} {δ} :
    (∀ v δ, match v with
            | inl v => Q v δ
            | inr m => True
            end -∗ POST v δ) -∗
    semWP' δ s Q -∗
    semWP δ s POST.
  Proof.
    iIntros "H Hwp". unfold semWP'. iApply (semWP_mono with "Hwp"). auto.
  Qed.

  Local Notation "r '↦' val" := (reg_pointsTo r val) (at level 70).

  Definition Step_pre : iProp Σ :=
    interp_gprs interp ∗
    (∃ c, pc ↦ c ∗ interp (inr c) ∗ ⌜CorrectPC c⌝).

  Definition Step_post : iProp Σ :=
    interp_gprs interp ∗
    ((∃ c, pc ↦ c ∗ interp (inr c))
     ∨
     (∃ c, pc ↦ c ∗ interp_expression interp c)).

  Definition semTriple_step : iProp Σ :=
    IH -∗ semTriple [env] Step_pre (FunDef step) (fun _ _ => Step_post).

  Lemma valid_step_contract : ⊢ ValidContractSem fun_step sep_contract_step.
  Proof.
     iApply (contracts_sound $! _ _ step).
  Qed.

  Lemma valid_semTriple_step : ⊢ semTriple_step.
  Proof.
    iIntros "IH (Hregs & [%c (Hpc & Hsafe & Hcorrect)])".
    iApply (valid_step_contract $! [env]).
    cbn - [interp_gprs interp].
    iFrame "Hregs IH".
    iExists c; iFrame.
  Qed.

  Definition semTriple_loop : iProp Σ :=
    IH -∗ semTriple [env] Step_pre (FunDef loop) (fun _ _ => True)%I.

  Lemma valid_semContract_loop : ⊢ semTriple_loop.
  Proof.
    iIntros "#IH Hpre".
    unfold FunDef, fun_loop.
    iApply (semWP_seq (call step) (call loop)).
    iApply semWP_call_inline.
    iPoseProof (valid_semTriple_step with "IH Hpre") as "trip_step".
    iApply (semWP_mono with "trip_step").
    iIntros ([v|m] ?) "Hpost"; auto.
    iApply (semWP_call_inline_later loop).
    iDestruct "Hpost" as "(Hgprs & [[%c [Hpc' #Hsafe']] | [%c [Hpc' Hexpr]]])".
    - iModIntro.
      destruct c as [p b e a].
      iSpecialize ("IH" $! p b e a with "Hgprs Hpc' Hsafe'").
      unfold interp_loop. rewrite /semWP. cbn.
      iApply (wp_mono with "IH"). iIntros ([[|] ?] _); auto.
    - destruct c as [p b e a].
      cbn - [interp_gprs interp].
      iDestruct "Hexpr" as "[%Hp #Hexpr]". iModIntro. subst.
      iSpecialize ("Hexpr" with "[$Hpc' $Hgprs]").
      unfold interp_loop. rewrite /semWP.
      iApply (wp_mono with "Hexpr"). iIntros ([[|] ?] _); auto.
    - now rewrite semWP_fail.
  Qed.

  Import ctx.notations.
  Import env.notations.
  Import wptactics.

  Lemma semWP_is_perm {Γ} (e1 e2 : Exp Γ ty.perm) Q δ :
    ⊢ ((⌜eval e1 δ = eval e2 δ⌝ -∗ Q true δ) ∧
      (⌜Base.is_perm (eval e1 δ) (eval e2 δ) = false⌝ -∗ Q false δ)) -∗
      semWP' δ (call MinCapsProgram.is_perm e1 e2) Q.
  Proof.
    iIntros "HYP".
    iApply (semWP_call_inline MinCapsProgram.is_perm).
    iPoseProof (contracts_sound $! _ _ MinCapsProgram.is_perm) as "-#His_perm".
    rewrite valid_contract_curry.
    unfold ValidContractSemCurried, sep_contract_is_perm; cbn.
    iPoseProof ("His_perm" $! (eval e1 δ) (eval e2 δ) with "[%]") as "His_perm"; [by auto|].
    iApply (semWP_mono with "His_perm").
    iIntros ([[]|m] _) "H"; auto; cbn; iApply "HYP".
    - iDestruct "H" as "($ & _)".
    - iDestruct "H" as "(%H & _)". iPureIntro.
      by apply is_perm_Not_is_perm_false.
  Qed.

  Lemma is_correct_pc_false {c cpc} : decide_correct_pc c = cpc ->
    ⊢ semWP' [env].[ "c" ∷ ty.cap ↦ c ] (FunDef is_correct_pc) (fun x y => ⌜ x = cpc ⌝ ).
  Proof.
    destruct c as [p b e a]. cbn.
    intros Heq. iIntros. rewrite /semWP'.
    kEval. kStep. kStep. cbn. kStep. iApply semWP'_semWP.
    { iIntros ([v|m] δ) "HQ". iExact "HQ". simpl.
      iApply semWP_fail. auto. }
    iApply semWP_is_perm; cbn. iSplit.
    - iIntros "%H1". subst p. cbn in *. kStep.
      iApply semWP'_semWP.
      { iIntros ([|] ?) "HQ"; [iExact "HQ"|now iApply semWP_fail]. }
      iApply semWP_is_perm; cbn. iSplit.
      iIntros "%H1". discriminate.
      iIntros "_". kStep. kStep. cbn.
      kStep; rewrite semWP_val; auto.
    - iIntros "%H1". kStep.
      iApply semWP'_semWP.
      { iIntros ([|] ?) "HQ"; [iExact "HQ"|now iApply semWP_fail]. }
      iApply semWP_is_perm; cbn. iSplit.
      iIntros "%H2". subst p. cbn in *. kStep.
      cbn. kStep. cbn.
      kStep; rewrite semWP_val; auto.
      iIntros "%H2". kStep. kStep. cbn.
      rewrite andb_false_r.
      rewrite semWP_val.
      iPureIntro. subst.
      rewrite H1 H2.
      now rewrite ?andb_false_r.
  Qed.

  Lemma wrongPC_crashes_step {c Q} : decide_correct_pc c = false ->
                              ⊢ semTriple [env] (pc ↦ c) (FunDef step) Q.
  Proof.
    iIntros (wrongPC) "Hpc".
    unfold FunDef, fun_step.
    iApply semWP_let.
    iApply semWP_read_register.
    iExists c; iFrame.
    iIntros "Hpc".
    iApply semWP_let.
    iApply semWP_call_inline.
    cbn.
    iApply (semWP_mono $! (is_correct_pc_false wrongPC)).
    iIntros ([?|?] _ Heq).
    - subst.
      unfold stm_if.
      kStep. kStep. kEval.
      now rewrite semWP_fail.
    - now rewrite semWP_fail.
  Qed.

  Lemma wrongPC_crashes {c Q} : decide_correct_pc c = false ->
                              ⊢ semTriple [env] (pc ↦ c) (FunDef loop) Q.
  Proof.
    iIntros (wrongPc) "Hpc".
    unfold FunDef, fun_loop.
    iApply semWP_seq.
    iApply semWP_call_inline.
    iPoseProof (wrongPC_crashes_step wrongPc with "Hpc") as "H".
    iApply (semWP_mono with "H"). iIntros ([v|?] δ) "HQ".
    iExact "HQ".
    now rewrite semWP_fail.
  Qed.

  (* and now without the IH. *)
  Definition semContract_loop :=
    semTriple [env] Step_pre (FunDef loop) (fun _ _ => True)%I.

  Lemma valid_semContract_loop2 : ⊢ semContract_loop.
  Proof.
    iIntros.
    iLöb as "IH".
    iApply valid_semContract_loop.
    do 2 iModIntro.
    iIntros (p b e a) "Hgprs Hpc #Hpcvalid".
    destruct (decide_correct_pc {| cap_permission := p; cap_begin := b; cap_end := e; cap_cursor := a |}) eqn:Heqdpc.
    - iSpecialize ("IH" with "[$Hgprs Hpc]").
      { iExists _. now iFrame "Hpc Hpcvalid %". }
      unfold interp_loop. iApply (wp_mono with "IH").
      now iIntros ([[|] ?]).
    - unfold interp_loop.
      iPoseProof (wrongPC_crashes Heqdpc (Q := fun _ _ => True)%I with "[$]") as "H".
      iApply (wp_mono with "H").
      now iIntros ([[|] ?]).
  Qed.

End Loop.
