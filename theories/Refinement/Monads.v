(******************************************************************************)
(* Copyright (c) 2020 Dominique Devriese, Georgy Lukyanov,                    *)
(*   Sander Huyghebaert, Steven Keuchel                                       *)
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
     Classes.Morphisms
     Classes.Morphisms_Prop.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Prelude
     Base
     Shallow.Monads
     Symbolic.Monads
     Symbolic.Propositions
     Symbolic.Solver
     Symbolic.UnifLogic
     Symbolic.Worlds
     Syntax.Assertions
     Syntax.Chunks
     Syntax.Formulas
     Syntax.Predicates.

Import ctx.notations.
Import env.notations.

Set Implicit Arguments.

Module Type RefinementMonadsOn
  (Import B : Base)
  (Import PK : PredicateKit B)
  (Import WR : WorldsMixin B PK)
  (Import SK : SolverKit B PK WR)
  (Import SP : SymPropOn B PK WR)
  (Import UL : UnifLogicOn B PK WR)
  (Import LSP : LogSymPropOn B PK WR SP UL)
  (Import GS : GenericSolverOn B PK WR SK SP UL LSP)
  (Import AS : AssertionsOn B PK WR)
  (Import SHAL : ShallowMonadsOn B PK WR SP AS)
  (Import SYMB : SymbolicMonadsOn B PK WR SK SP UL LSP GS AS).

  Import ModalNotations.
  Import LogicalSoundness.
  Import SymProp.

  Import logicalrelation logicalrelation.notations proofmode.
  Import iris.bi.interface iris.proofmode.proofmode.

  Definition RPureSpec [SA CA] (RA : Rel SA CA) :
    Rel (SPureSpec SA) (CPureSpec CA) := □ᵣ(RA -> ℙ) -> ℙ.

  #[export] Instance refine_compat_block_finish {w} :
    Related RProp FINISH w SymProp.block | 0.
  Proof. now iIntros "_". Qed.

  Module PureSpec.
    Import SPureSpec.notations.

    (* Instance search does not unfold the concrete operations, so their
       instances are indexed, and tried, by their head. *)
    #[export] Typeclasses Opaque CPureSpec.angelic CPureSpec.angelic_binary
      CPureSpec.angelic_ctx CPureSpec.angelic_list' CPureSpec.assert_eq_chunk
      CPureSpec.assert_eq_nenv CPureSpec.assert_formula
      CPureSpec.assert_pathcondition CPureSpec.assume_formula
      CPureSpec.assume_pathcondition CPureSpec.bind CPureSpec.block
      CPureSpec.consume_chunk CPureSpec.debug CPureSpec.demonic
      CPureSpec.demonic_binary CPureSpec.demonic_ctx CPureSpec.demonic_list
      CPureSpec.demonic_list' CPureSpec.produce_chunk CPureSpec.pure
      CPureSpec.read_register CPureSpec.run CPureSpec.write_register.

    Definition RPureSpec [SA CA] (RA : Rel SA CA) :
      Rel (SPureSpec SA) (CPureSpec CA) := □ᵣ(RA -> RProp) -> RProp.

    #[export] Instance refine_run {w} :
      Related (RPureSpec RUnit -> RProp) CPureSpec.run w (SPureSpec.run (w := w)).
    Proof. unfold Related. unfold CPureSpec.run, SPureSpec.run; solve_related. Qed.

    #[export] Instance refine_pure `{RA : Rel SA CA} {w} :
      Related (RA -> RPureSpec RA) CPureSpec.pure w (SPureSpec.pure (w := w)).
    Proof. unfold CPureSpec.pure, SPureSpec.pure, RPureSpec; solve_related. Qed.

    #[export] Instance refine_bind `{RA : Rel SA CA, RB : Rel SB CB} {w} :
      Related (RPureSpec RA -> □ᵣ(RA -> RPureSpec RB) -> RPureSpec RB)
        CPureSpec.bind w (SPureSpec.bind (w := w)).
    Proof. unfold CPureSpec.bind, SPureSpec.bind, RPureSpec; solve_related. Qed.

    #[export] Instance refine_block `{R : Rel AT A} {w} :
      Related (RPureSpec R) CPureSpec.block w (@SPureSpec.block AT w).
    Proof. done. Qed.

    #[export] Instance refine_error `{RA : Rel AT A} {w} m msg :
      Related (RPureSpec RA) m w (@SPureSpec.error _ w msg).
    Proof.
      unfold Related, RPureSpec, RProp; cbn.
      iIntros (k K) "Hk".
      now cbn.
    Qed.

    #[export] Instance refine_angelic (x : option LVar) σ {w} :
      Related (RPureSpec (RVal σ)) (CPureSpec.angelic σ) w (SPureSpec.angelic (w := w) x σ).
    Proof.
      unfold Related, CPureSpec.angelic, SPureSpec.angelic; simpl.
      iIntros (k K) "HKk HK".
      rewrite knowing_acc_snoc_right2.
      iDestruct "HK" as "[%v HSP]".
      iSpecialize ("HKk" $! _ (acc_snoc_right (b := fresh_lvar w x∷σ)) v term_var_zero).
      iDestruct (knowing_assuming with "[$HKk $HSP]") as "H".
      iApply (knowing_pure2 _ with "H").
      iIntros "((Hv & HK) & HKk)".
      iExists v.
      now iApply ("HKk" with "Hv").
    Qed.

    #[export] Instance refine_demonic (x : option LVar) σ {w} :
      Related (RPureSpec (RVal σ)) (CPureSpec.demonic σ) w (SPureSpec.demonic (w := w) x σ).
    Proof.
      unfold Related, CPureSpec.demonic, SPureSpec.demonic.
      iIntros (k K) "HK HSP %v".
      iSpecialize ("HK" $! _ (acc_snoc_right (b := fresh_lvar w x∷σ)) v term_var_zero).
      cbn.
      rewrite assuming_acc_snoc_right2.
      iDestruct (knowing_assuming with "[$HK $HSP]") as "H".
      iApply (knowing_pure2 _ with "H").
      iIntros "[HKk HSP]".
      now iApply "HKk".
    Qed.

    #[export] Instance refine_angelic_ctx {N : Set} {n : N -> LVar} Δ {w} :
      Related (RPureSpec (RNEnv N Δ))
        (CPureSpec.angelic_ctx Δ) w (SPureSpec.angelic_ctx (w := w) n Δ).
    Proof.
      RefineSolver.rentry.
      induction Δ; cbn [SPureSpec.angelic_ctx CPureSpec.angelic_ctx]; solve_related.
    Qed.

    #[export] Instance refine_demonic_ctx {N : Set} {n : N -> LVar} Δ {w} :
      Related (RPureSpec (RNEnv N Δ))
        (CPureSpec.demonic_ctx Δ) w (SPureSpec.demonic_ctx (w := w) n Δ).
    Proof.
      RefineSolver.rentry.
      induction Δ; cbn [SPureSpec.demonic_ctx CPureSpec.demonic_ctx]; solve_related.
    Qed.

    Lemma obligation_equiv {w : World} (msg : AMessage w) (fml : Formula w) :
      (Obligation msg fml : Pred w) ⊣⊢ instprop fml.
    Proof. crushPredEntails3.
           - now destruct H0. 
           - now constructor.
    Qed.

    Lemma obligation_equiv_pred {w : World} (msg : AMessage w) (fml : Formula w) :
      (Obligation msg fml : Pred w) ⊣⊢ instpred fml.
    Proof. crushPredEntails3.
           - rewrite ?instpred_prop. now destruct H0.
           - rewrite instpred_prop in H0. now constructor.
    Qed.

    Lemma safe_assume_triangular {w0 w1} (ζ : Tri w0 w1) (o : 𝕊 w1) :
      (psafe (assume_triangular ζ o) ⊣⊢ (assuming (acc_triangular ζ) (psafe o))).
    Proof.
      induction ζ; first by rewrite assuming_id.
      cbn [sub_triangular].
      rewrite (assuming_trans (ω23 := acc_triangular ζ)).
      cbn.
      now rewrite IHζ.
    Qed.

    Lemma safe_assume_pathcondition_without_solver {w : World}
      (C : PathCondition w) (p : 𝕊 w) :
      psafe (assume_pathcondition_without_solver C p) ⊣⊢
        (instpred C -∗ psafe (w := wpathcondition w C) p).
    Proof.
      revert p. induction C; cbn; intros p.
      - destruct w. (* needed to make coq see that wpathcondition w0 [ctx] is the same as w0 *)
        now rewrite bi.emp_wand.
      - rewrite IHC.
        cbn.
        change (instpred_ctx C) with (instpred C).
        rewrite <-bi.wand_curry.
        (* Coq doesn't see that instpred is parametric in the world. Fortunately,
         * instpred_prop happens to imply this.
         *)
        enough (instpred (w := w) b ⊣⊢ instpred (w := wpathcondition w C) b) as H by now rewrite H.
        constructor; intros.
        now rewrite !instpred_prop.
    Qed.

    (* TODO: more logical inst_triangular *)
    Lemma safe_assert_triangular {w0 w1} msg (ζ : Tri w0 w1)
      (o : AMessage w1 -> 𝕊 w1) :
      (psafe (assert_triangular msg ζ o) ⊣⊢
         (knowing (acc_triangular ζ) (psafe (o (subst msg (sub_triangular ζ)))))).
    Proof.
      revert o. induction ζ; intros o.
      - now rewrite knowing_id subst_sub_id.
      - cbn [psafe assert_triangular acc_triangular].
        rewrite obligation_equiv.
        cbn [sub_triangular].
        rewrite (knowing_trans (w2 := wsubst _ _ _)).
        rewrite subst_sub_comp.
        rewrite (IHζ (subst msg (sub_single xIn t)) o).
        now rewrite knowing_acc_subst_right.
    Qed.

    Lemma safe_assert_pathcondition_without_solver {w0 : World}
      (msg : AMessage w0) (C : PathCondition w0) (p : 𝕊 w0) :
      psafe (assert_pathcondition_without_solver msg C p) ⊣⊢
        (instpred C ∗ psafe (w := wpathcondition w0 C) p).
    Proof.
      unfold assert_pathcondition_without_solver. revert p.
      induction C; cbn; intros p.
      - rewrite bi.True_sep.
        now destruct w0.
      - rewrite IHC; cbn.
        rewrite bi.sep_assoc.
        now rewrite <-obligation_equiv_pred.
    Qed.

    Lemma refine_assert_pathcondition {w} :
      ⊢ ℛ⟦RMsg _ (RPathCondition -> RPureSpec RUnit)⟧
        CPureSpec.assert_pathcondition (SPureSpec.assert_pathcondition (w := w)).
    Proof.
      unfold SPureSpec.assert_pathcondition, CPureSpec.assert_pathcondition.
      iIntros (msg cC sC) "HC %cΦ %sΦ rΦ HΦ".
      destruct (combined_solver_spec w sC) as [[w1 [ζ sc1]] Hsolver|Hsolver].
      - rewrite safe_assert_triangular.
        rewrite safe_assert_pathcondition_without_solver.
        iSplit.
        + iDestruct (knowing_sepₚ with "HΦ") as "[Hsc1 _]".
          rewrite Hsolver.
          iApply ("HC" with "Hsc1").
        + iSpecialize ("rΦ" $! (wpathcondition w1 sc1) (acc_trans (acc_triangular ζ) (acc_pathcondition_right w1 sc1))).
          rewrite assuming_trans.
          iPoseProof (knowing_assuming (acc_triangular ζ) with "[$HΦ $rΦ]") as "H".
          iApply knowing_pure.
          iApply (knowing_proper with "H").
          iIntros "((Hsc1 & HsΦ) & HΦ)".
          iPoseProof (assuming_acc_pathcondition_right with "[$HΦ $Hsc1]") as "HΦ".
          unfold RImpl, RProp; cbn.
          repeat change (@bi_forall (@bi_pred (wpathcondition w1 sc1)) ?A ?P) with (@bi_forall (@bi_pred w1) A P).
          repeat change (@bi_wand (@bi_pred (wpathcondition w1 sc1)) ?P ?Q) with (@bi_wand (@bi_pred w1) P Q).
          repeat change (@repₚ ?T  ?A ?instTA ?t1 (wpathcondition w1 sc1) ?t2) with (@repₚ T A instTA t1 w1 t2).
          iApply ("HΦ" with "[] HsΦ").
          now iApply refine_unit.
      - cbn.
        by iDestruct "HΦ" as %[].
    Qed.

    #[export] Instance refine_compat_assert_pathcondition {w msg} :
      Related (RPathCondition -> RPureSpec RUnit)
        CPureSpec.assert_pathcondition w (SPureSpec.assert_pathcondition (w := w) msg).
    Proof. now iApply (refine_assert_pathcondition $! msg). Qed.

    #[export] Instance refine_assume_pathcondition {w} :
      Related (RPathCondition -> RPureSpec RUnit)
        CPureSpec.assume_pathcondition w (SPureSpec.assume_pathcondition (w := w)).
    Proof. unfold Related.
      unfold SPureSpec.assume_pathcondition, CPureSpec.assume_pathcondition.
      iIntros "%C %Cs HC %Φ %Φs HΦ Hsp %HC".
      destruct (combined_solver_spec _ Cs) as [[w1 [ζ sc1]] Hsolver|Hsolver].
      - rewrite safe_assume_triangular.
        rewrite safe_assume_pathcondition_without_solver.
        iDestruct "HC" as "[_ HC2]".
        iSpecialize ("HC2" $! HC).
        rewrite <-Hsolver.
        iSpecialize ("HΦ" $! _ (acc_trans (acc_triangular ζ) (acc_pathcondition_right w1 sc1))).
        rewrite assuming_trans.
        iDestruct (assuming_sepₚ with "[HΦ Hsp]") as "H".
        { now iSplitL "HΦ". }
        iDestruct (knowing_assuming with "[$HC2 $H]") as "H".
        iApply knowing_pure.
        iApply (knowing_proper with "H").
        iIntros "(#Hsc1 & H & HΦ)".
        iDestruct (@assuming_acc_pathcondition_right w1 with "[$Hsc1 $H]") as "H".
        iSpecialize ("HΦ" with "Hsc1").
        unfold RImpl, RProp; cbn.
        repeat change (@bi_forall (@bi_pred (wpathcondition w1 sc1)) ?A ?P) with (@bi_forall (@bi_pred w1) A P).
        repeat change (@bi_wand (@bi_pred (wpathcondition w1 sc1)) ?P ?Q) with (@bi_wand (@bi_pred w1) P Q).
        repeat change (@repₚ ?T  ?A ?instTA ?t1 (wpathcondition w1 sc1) ?t2) with (@repₚ T A instTA t1 w1 t2).
        iApply ("H" with "[] HΦ").
        now iApply refine_unit.
      - iExFalso.
        iApply Hsolver.
        iDestruct "HC" as "[_ HC2]".
        now iApply "HC2".
    Qed.

    #[export] Instance refine_assert_formula {w msg} :
      Related (RFormula -> RPureSpec RUnit)
        CPureSpec.assert_formula w (SPureSpec.assert_formula (w := w) msg).
    Proof.
      unfold Related, RPureSpec, SPureSpec.assert_formula, CPureSpec.assert_formula.
      iIntros "%fml %fmls Hfml".
      iApply refine_assert_pathcondition.
      iApply (proprepₚ_cong (T2 := PathCondition) with "Hfml").
      intros. cbn. now apply bi.emp_sep.
    Qed.

    #[export] Instance refine_assume_formula {w} :
      Related (RFormula -> RPureSpec RUnit)
        CPureSpec.assume_formula w (SPureSpec.assume_formula (w := w)).
    Proof.
      unfold RPureSpec, SPureSpec.assume_formula, CPureSpec.assume_formula.
      iIntros "%fml %fmls Hfml".
      iApply refine_assume_pathcondition.
      iApply (proprepₚ_cong (T2 := PathCondition) with "Hfml").
      intros. cbn. now apply bi.emp_sep.
    Qed.

    #[export] Instance refine_angelic_binary `{RA : Rel SA CA} {w} :
      Related (RPureSpec RA -> RPureSpec RA -> RPureSpec RA)
        CPureSpec.angelic_binary w (SPureSpec.angelic_binary (w := w)).
    Proof. unfold CPureSpec.angelic_binary, SPureSpec.angelic_binary, RPureSpec; solve_related. Qed.

    #[export] Instance refine_demonic_binary `{RA : Rel SA CA} {w} :
      Related (RPureSpec RA -> RPureSpec RA -> RPureSpec RA)
        CPureSpec.demonic_binary w (SPureSpec.demonic_binary (w := w)).
    Proof. unfold CPureSpec.demonic_binary, SPureSpec.demonic_binary, RPureSpec; solve_related. Qed.

    #[export] Instance refine_angelic_list' `{RA : Rel SA CA} {w} :
      Related (RA -> RList RA -> RPureSpec RA)
        CPureSpec.angelic_list' w (SPureSpec.angelic_list' (w := w)).
    Proof. unfold Related.
      iIntros "%v %sv Hv %vs %svs Hvs".
      iRevert (v sv) "Hv".
      iApply (RList_ind (R := RA) (MkRel (fun vs w svs => ∀ (v : CA) (sv : SA w), ℛ⟦RA⟧ v sv -∗ ℛ⟦RPureSpec RA⟧ (CPureSpec.angelic_list' v vs) (SPureSpec.angelic_list' (w := w) sv svs))%I) w with "[] Hvs"); cbn.
      iSplit.
      - iApply refine_pure.
      - clear. iIntros (v sv vs svs) "Hv Hvs IHvs %v2 %sv2 Hv2".
        iApply (refine_angelic_binary with "[Hv2]").
        + now iApply refine_pure.
        + now iApply "IHvs".
    Qed.

    Lemma refine_angelic_list `{RA : Rel SA CA} {w} :
      ⊢ ℛ⟦RMsg _ (RList RA -> RPureSpec RA)⟧
        CPureSpec.angelic_list (SPureSpec.angelic_list (w := w)).
    Proof.
      iIntros (msg vs svs) "Hvs".
      iApply (RList_ind (R := RA) (MkRel (fun vs w svs => ∀ msg, ℛ⟦RPureSpec RA⟧ (CPureSpec.angelic_list vs) (SPureSpec.angelic_list (w := w) msg svs))%I) w with "[] Hvs"); cbn.
      clear.
      iSplit.
      - iIntros (msg). now iApply refine_error.
      - iIntros (v svs vs sv) "Hv Hvs _ %msg".
        cbn -[RSat].
        now iApply (refine_angelic_list' with "Hv Hvs").
    Qed.

    #[export] Instance refine_demonic_list' `{RA : Rel SA CA} {w} :
      Related (RA -> RList RA -> RPureSpec RA)
        CPureSpec.demonic_list' w (SPureSpec.demonic_list' (w := w)).
    Proof. unfold Related.
      iIntros "%v %sv Hv %vs %svs Hvs".
      iRevert (v sv) "Hv".
      iApply (RList_ind (R := RA) (MkRel (fun vs w svs => ∀ (v : CA) (sv : SA w), ℛ⟦RA⟧ v sv -∗ ℛ⟦RPureSpec RA⟧ (CPureSpec.demonic_list' v vs) (SPureSpec.demonic_list' (w := w) sv svs))%I) w with "[] Hvs"); cbn.
      iSplit.
      - iApply refine_pure.
      - clear. iIntros (v sv vs svs) "Hv Hvs IHvs %v2 %sv2 Hv2".
        iApply (refine_demonic_binary with "[Hv2]").
        + now iApply refine_pure.
        + now iApply "IHvs".
    Qed.

    #[export] Instance refine_demonic_list `{RA : Rel SA CA} {w} :
      Related (RList RA -> RPureSpec RA)
        CPureSpec.demonic_list w (SPureSpec.demonic_list (w := w)).
    Proof. unfold Related.
      iIntros (vs svs) "Hvs".
      iApply (RList_ind (R := RA) (MkRel (fun vs w svs => ℛ⟦RPureSpec RA⟧ (CPureSpec.demonic_list vs) (SPureSpec.demonic_list (w := w) svs))%I) w with "[] Hvs"); cbn.
      clear.
      iSplit.
      - now iApply refine_block.
      - iIntros (v svs vs sv) "Hv Hvs _".
        now iApply (refine_demonic_list' with "Hv Hvs").
    Qed.

    Lemma refine_angelic_finite {F} `{finite.Finite F} {w} :
      ⊢ ℛ⟦RMsg _ (RPureSpec (RConst F))⟧
        (CPureSpec.angelic_finite F) (@SPureSpec.angelic_finite F _ _ w).
    Proof.
      iIntros (msg).
      unfold CPureSpec.angelic_finite, SPureSpec.angelic_finite.
      iApply (refine_angelic_list (RA := RConst F)).
      iStopProof.
      crushPredEntails3.
      induction (finite.enum F); now constructor.
    Qed.

    #[export] Instance refine_demonic_finite {F} `{finite.Finite F} {w} :
      Related (RPureSpec (RConst F))
        (CPureSpec.demonic_finite F) w (@SPureSpec.demonic_finite F _ _ w).
    Proof. unfold Related.
      unfold CPureSpec.demonic_finite, SPureSpec.demonic_finite.
      iApply (refine_demonic_list (RA := RConst F)).
      iStopProof.
      crushPredEntails3.
      induction (finite.enum F); now constructor.
    Qed.

    Lemma refine_angelic_pattern_match' {N : Set} (n : N -> LVar)
      {σ} (pat : Pattern (N:=N) σ) {w} :
      ⊢ ℛ⟦RMsg _ (RVal σ -> RPureSpec (RMatchResult pat))⟧
        (CPureSpec.angelic_pattern_match pat)
        (SPureSpec.angelic_pattern_match' (w := w) n pat).
    Proof.
      iIntros (msg v t) "Hv".
      unfold SPureSpec.angelic_pattern_match'.
      unfold CPureSpec.angelic_pattern_match.
      iApply (refine_bind (RA := RConst _) (RB := RMatchResult _)).
      { now iApply refine_angelic_finite. }
      iIntros (w1 r01) "!> %ι1 %sι1 Hι1".
      unfold RConst, RInst; cbn.
      rewrite repₚ_const.
      iDestruct "Hι1" as "<-"; solve_related.
    Qed.
    #[global] Arguments refine_angelic_pattern_match' {N} n {σ} pat.

    Lemma refine_demonic_pattern_match' {N : Set} (n : N -> LVar)
      {σ} (pat : Pattern (N:=N) σ) {w} :
      ⊢ ℛ⟦RVal σ -> RPureSpec (RMatchResult pat)⟧
        (CPureSpec.demonic_pattern_match pat)
        (SPureSpec.demonic_pattern_match' (w := w) n pat).
    Proof.
      iIntros (v t) "Hv".
      unfold SPureSpec.demonic_pattern_match'.
      unfold CPureSpec.demonic_pattern_match.
      iApply (refine_bind (RA := RConst _) (RB := RMatchResult _)).
      { now iApply refine_demonic_finite. }
      iIntros (w1 r01) "!> %ι1 %sι1 Hι1".
      unfold RConst, RInst; cbn.
      rewrite repₚ_const.
      iDestruct "Hι1" as "<-"; solve_related.
    Qed.
    #[global] Arguments refine_demonic_pattern_match' {N} n {σ} pat.

    #[export] Instance refine_angelic_pattern_match {N : Set} (n : N -> LVar)
      {σ} (pat : Pattern (N:=N) σ) {w} :
      Related (RMsg _ (RVal σ -> RPureSpec (RMatchResult pat)))
        (CPureSpec.angelic_pattern_match pat) w
        (SPureSpec.angelic_pattern_match (w := w) n pat).
    Proof.
      induction pat; cbn - [RSat].
      - iIntros (msg v sv) "Hv %Φ %sΦ rΦ HSP". 
        rewrite CPureSpec.wp_angelic_pattern_match.
        iApply ("rΦ" with "[Hv] HSP"); solve_related.
      - iIntros (msg v sv) "Hv".
        destruct (term_get_val_spec sv); subst.
        + iIntros (Φ sΦ) "rΦ HSP".
          rewrite CPureSpec.wp_angelic_pattern_match; cbn.
          iDestruct (refine_term_val2 with "Hv") as "<-".
          iApply ("rΦ" with "[Hv] HSP"); solve_related.
        + now iApply (refine_angelic_pattern_match' n pat_bool).
      - iApply (refine_angelic_pattern_match' n (pat_list σ x y)).
      - iIntros (msg v sv) "Hv".
        destruct (term_get_pair_spec sv) as [[svl svr] Heq|]; subst.
        + iIntros (Φ sΦ) "rΦ HSP".
          rewrite CPureSpec.wp_angelic_pattern_match.
          iApply ("rΦ" with "[Hv] HSP").
          destruct v as (v1 & v2); cbn.
          iExists eq_refl; cbn.
          iPoseProof (eqₚ_triv (vt2 := term_binop bop.pair svl svr : STerm (ty.prod σ τ) w) Heq) as "Heq".
          iDestruct (repₚ_eqₚ (T := STerm (ty.prod σ τ)) with "[$Heq $Hv]") as "Hv12".
          iDestruct (repₚ_term_prod with "Hv12") as "(Hv1 & Hv2)".
          solve_related.
        + now iApply (refine_angelic_pattern_match' n (pat_pair _ _)).
      - iIntros (msg v sv) "Hv".
        destruct (term_get_sum_spec sv) as [[svl|svr] Heq|]; subst.
        + iPoseProof (eqₚ_triv (vt2 := term_inl svl : STerm (ty.sum σ τ) w) Heq) as "Heq".
          iDestruct (repₚ_eqₚ (T := STerm (ty.sum _ _)) with "[$Heq $Hv]") as "Hv'".
          iIntros (Φ sΦ) "rΦ HSP".
          rewrite CPureSpec.wp_angelic_pattern_match.
          iApply ("rΦ" with "[Hv'] HSP").
          iDestruct (repₚ_inversion_term_inl with "Hv'") as "(%vl & -> & Hvl)".
          solve_related.
        + iPoseProof (eqₚ_triv (vt2 := term_inr svr : STerm (ty.sum σ τ) w) Heq) as "Heq".
          iDestruct (repₚ_eqₚ (T := STerm (ty.sum _ _)) with "[$Heq $Hv]") as "Hv'".
          iIntros (Φ sΦ) "rΦ HSP".
          rewrite CPureSpec.wp_angelic_pattern_match.
          iApply ("rΦ" with "[Hv'] HSP").
          iDestruct (repₚ_inversion_term_inr with "Hv'") as "(%vr & -> & Hvr)".
          solve_related.
        + now iApply (refine_angelic_pattern_match' n (pat_sum _ _ _ _)).
      - iIntros (msg v sv) "Hv %Φ %sΦ rΦ HSP".
        rewrite CPureSpec.wp_angelic_pattern_match.
        iApply ("rΦ" with "[Hv] HSP").
        destruct v; solve_related.
      - iIntros (msg v sv) "Hv".
        destruct (term_get_val_spec sv); subst.
        + iIntros (Φ sΦ) "rΦ HSP".
          rewrite CPureSpec.wp_angelic_pattern_match.
          iDestruct (refine_term_val2 with "Hv") as "->".
          iApply ("rΦ" with "[Hv] HSP"); solve_related.
        + now iApply (refine_angelic_pattern_match' n (pat_enum E)).
      - iApply (refine_angelic_pattern_match' n (pat_bvec_split _ _ x y)).
      - iIntros (msg v sv) "Hv".
        destruct (term_get_val_spec sv); subst.
        + iIntros (Φ sΦ) "rΦ HSP".
          rewrite CPureSpec.wp_angelic_pattern_match.
          iDestruct (refine_term_val2 with "Hv") as "->".
          iApply ("rΦ" with "[Hv] HSP"); solve_related.
        + now iApply (refine_angelic_pattern_match' n (pat_bvec_exhaustive m)).
      - iApply (refine_angelic_pattern_match' n (pat_tuple p)).
      - iIntros (msg v sv) "Hv".
        destruct (term_get_record_spec sv) as [svs Heq|]; subst.
        + iPoseProof (eqₚ_triv (vt2 := term_record R svs : STerm (ty.record R) w) Heq) as "Heq".
          iDestruct (repₚ_eqₚ (T := STerm (ty.record _)) with "[$Heq $Hv]") as "Hv".
          iIntros (Φ sΦ) "rΦ HSP".
          rewrite CPureSpec.wp_angelic_pattern_match.
          iApply ("rΦ" with "[Hv] HSP").
          iDestruct (repₚ_inversion_record with "Hv") as "(%vs & -> & Hvs)".
          iExists eq_refl.
          unfold record_pattern_match_val.
          rewrite recordv_unfold_fold.
          iApply (repₚ_cong (T1 := fun w => NamedEnv (Term w) _) (T2 := fun w => NamedEnv (Term w) _) with "Hvs").
          intros.
          now rewrite inst_record_pattern_match.
        + now iApply (refine_angelic_pattern_match' n (pat_record _ _ _)).
      - iIntros (msg v sv) "Hv".
        destruct (term_get_union_spec sv) as [[K scr'] Heq|]; subst.
        + iIntros (Φ sΦ) "rΦ".
          iPoseProof (eqₚ_triv (vt2 := term_union U K scr' : STerm (ty.union U) w) Heq) as "Heq".
          iDestruct (repₚ_eqₚ (T := STerm (ty.union _)) with "[$Heq $Hv]") as "Hv".
          iDestruct (repₚ_inversion_union with "Hv") as "(%t & -> & Hv)".
          iIntros "HSP".
          rewrite CPureSpec.wp_angelic_pattern_match.
          cbn -[RSat].
          rewrite unionv_unfold_fold.
          rewrite -(CPureSpec.wp_angelic_pattern_match _ (fun v => Φ (let (pc, δpc) := v in _))).
          iApply (H with "Hv [rΦ] HSP").
          iIntros (w2 ω2) "!> %mr %smr Hmr".
          destruct mr, smr.
          iDestruct "Hmr" as "(%e & Hmr)".
          subst x0.
          rewrite forgetting_unconditionally.
          iApply ("rΦ" with "[Hmr]"); solve_related.
        + now iApply (refine_angelic_pattern_match' n (pat_union _ _)).
    Qed.
    #[global] Arguments refine_angelic_pattern_match' {N} n {σ} pat.

    #[export] Instance refine_demonic_pattern_match {N : Set} (n : N -> LVar)
      {σ} (pat : Pattern (N:=N) σ) {w} :
      Related (RVal σ -> RPureSpec (RMatchResult pat))
        (CPureSpec.demonic_pattern_match pat) w
        (SPureSpec.demonic_pattern_match n pat (w := w)).
    Proof.
      induction pat; cbn - [RSat].
      - iIntros (v sv) "Hv %Φ %sΦ rΦ HSP". 
        rewrite CPureSpec.wp_demonic_pattern_match.
        iApply ("rΦ" with "[Hv] HSP").
        solve_related.
      - iIntros (v sv) "Hv".
        destruct (term_get_val_spec sv); subst.
        + iIntros (Φ sΦ) "rΦ HSP".
          rewrite CPureSpec.wp_demonic_pattern_match; cbn.
          iApply ("rΦ" with "[Hv] HSP").
          iDestruct (refine_term_val2 with "Hv") as "->"; solve_related.
        + now iApply (refine_demonic_pattern_match' n pat_bool).
      - iApply (refine_demonic_pattern_match' n (pat_list σ x y)).
      - iIntros (v sv) "Hv".
        destruct (term_get_pair_spec sv) as [[svl svr] Heq|]; subst.
        + iIntros (Φ sΦ) "rΦ HSP".
          rewrite CPureSpec.wp_demonic_pattern_match.
          iApply ("rΦ" with "[Hv] HSP").
          destruct v as (v1 & v2); cbn.
          iExists eq_refl; cbn.
          iPoseProof (eqₚ_triv (vt2 := term_binop bop.pair svl svr : STerm (ty.prod σ τ) w) Heq) as "Heq".
          iDestruct (repₚ_eqₚ (T := STerm (ty.prod σ τ)) with "[$Heq $Hv]") as "Hv12".
          iDestruct (repₚ_term_prod with "Hv12") as "(Hv1 & Hv2)".
          solve_related.
        + now iApply (refine_demonic_pattern_match' n (pat_pair _ _)).
      - iIntros (v sv) "Hv".
        destruct (term_get_sum_spec sv) as [[svl|svr] Heq|]; subst.
        + iPoseProof (eqₚ_triv (vt2 := term_inl svl : STerm (ty.sum σ τ) w) Heq) as "Heq".
          iDestruct (repₚ_eqₚ (T := STerm (ty.sum _ _)) with "[$Heq $Hv]") as "Hv'".
          iIntros (Φ sΦ) "rΦ HSP".
          rewrite CPureSpec.wp_demonic_pattern_match.
          iApply ("rΦ" with "[Hv'] HSP").
          iDestruct (repₚ_inversion_term_inl with "Hv'") as "(%vl & -> & Hvl)".
          solve_related.
        + iPoseProof (eqₚ_triv (vt2 := term_inr svr : STerm (ty.sum σ τ) w) Heq) as "Heq".
          iDestruct (repₚ_eqₚ (T := STerm (ty.sum _ _)) with "[$Heq $Hv]") as "Hv'".
          iIntros (Φ sΦ) "rΦ HSP".
          rewrite CPureSpec.wp_demonic_pattern_match.
          iApply ("rΦ" with "[Hv'] HSP").
          iDestruct (repₚ_inversion_term_inr with "Hv'") as "(%vr & -> & Hvr)".
          solve_related.
        + now iApply (refine_demonic_pattern_match' n (pat_sum _ _ _ _)).
      - iIntros (v sv) "Hv %Φ %sΦ rΦ HSP".
        rewrite CPureSpec.wp_demonic_pattern_match.
        iApply ("rΦ" with "[Hv] HSP").
        destruct v.
        iExists eq_refl.
        iApply (repₚ_triv (T := fun w => NamedEnv (Term w) _)).
        now intros.
      - iIntros (v sv) "Hv".
        destruct (term_get_val_spec sv); subst.
        + iIntros (Φ sΦ) "rΦ HSP".
          rewrite CPureSpec.wp_demonic_pattern_match.
          iApply ("rΦ" with "[Hv] HSP").
          iDestruct (refine_term_val2 with "Hv") as "->".
          solve_related.
        + now iApply (refine_demonic_pattern_match' n (pat_enum E)).
      - iApply (refine_demonic_pattern_match' n (pat_bvec_split _ _ x y)).
      - iIntros (v sv) "Hv".
        destruct (term_get_val_spec sv); subst.
        + iIntros (Φ sΦ) "rΦ HSP".
          rewrite CPureSpec.wp_demonic_pattern_match.
          iApply ("rΦ" with "[Hv] HSP").
          iDestruct (refine_term_val2 with "Hv") as "->".
          solve_related.
        + now iApply (refine_demonic_pattern_match' n (pat_bvec_exhaustive m)).
      - iApply (refine_demonic_pattern_match' n (pat_tuple p)).
      - iIntros (v sv) "Hv".
        destruct (term_get_record_spec sv) as [svs Heq|]; subst.
        + iPoseProof (eqₚ_triv (vt2 := term_record R svs : STerm (ty.record R) w) Heq) as "Heq".
          iDestruct (repₚ_eqₚ (T := STerm (ty.record _)) with "[$Heq $Hv]") as "Hv".
          iIntros (Φ sΦ) "rΦ HSP".
          rewrite CPureSpec.wp_demonic_pattern_match.
          iApply ("rΦ" with "[Hv] HSP").
          iDestruct (repₚ_inversion_record with "Hv") as "(%vs & -> & Hvs)".
          iExists eq_refl.
          unfold record_pattern_match_val.
          rewrite recordv_unfold_fold.
          iApply (repₚ_cong (T1 := fun w => NamedEnv (Term w) _) (T2 := fun w => NamedEnv (Term w) _) with "Hvs").
          intros.
          now rewrite inst_record_pattern_match.
        + now iApply (refine_demonic_pattern_match' n (pat_record _ _ _)).
      - iIntros (v sv) "Hv".
        destruct (term_get_union_spec sv) as [[K scr'] Heq|]; subst.
        + iIntros (Φ sΦ) "rΦ".
          iPoseProof (eqₚ_triv (vt2 := term_union U K scr' : STerm (ty.union U) w) Heq) as "Heq".
          iDestruct (repₚ_eqₚ (T := STerm (ty.union _)) with "[$Heq $Hv]") as "Hv".
          iDestruct (repₚ_inversion_union with "Hv") as "(%t & -> & Hv)".
          iIntros "HSP".
          rewrite CPureSpec.wp_demonic_pattern_match.
          cbn -[RSat].
          rewrite unionv_unfold_fold.
          rewrite -(CPureSpec.wp_demonic_pattern_match _ (fun v => Φ (let (pc, δpc) := v in _))).
          iApply (H with "Hv [rΦ] HSP").
          iIntros (w2 ω2) "!> %mr %smr Hmr".
          destruct mr, smr.
          iDestruct "Hmr" as "(%e & Hmr)".
          subst x0.
          rewrite forgetting_unconditionally.
          iApply ("rΦ" with "[Hmr]").
          now iExists eq_refl.
        + now iApply (refine_demonic_pattern_match' n (pat_union _ _)).
    Qed.
    #[global] Arguments refine_demonic_pattern_match' {N} n {σ} pat.

    Lemma refine_new_pattern_match_regular {N : Set} n σ (pat : Pattern (N:=N) σ) {w} :
      ⊢ ℛ⟦RVal σ -> RPureSpec (RMatchResult pat)⟧
        (CPureSpec.new_pattern_match pat)
        (SPureSpec.new_pattern_match_regular (w := w) n pat).
    Proof.
      unfold SPureSpec.new_pattern_match_regular.
      iIntros (v sv) "rv %post %spost rpost Hsp".
      unfold CPureSpec.new_pattern_match.
      rewrite <- (pattern_match_val_freshen n pat (Σ := w)).
      iPoseProof (refine_pattern_match (p := freshen_pattern n w pat) with "rv") as "Hpm".
      destruct pattern_match_val as [pc vs]. cbn - [acc_trans RSat].
      unfold CPureSpec.pure; cbn -[RSat].
      iSpecialize ("Hsp" $! pc).
      iSpecialize ("rpost" $! _ (acc_match_right pc)).
      iDestruct (knowing_assuming with "[$Hpm $Hsp]") as "H".
      iDestruct (knowing_assuming with "[$H $rpost]") as "H".
      iApply (knowing_pure (acc_match_right pc)).
      iApply (knowing_proper (ω := acc_match_right pc) _ _ with "H").
      iIntros "[[Hargs Hsp] rpost]".
      iApply ("rpost" with "[Hargs] Hsp").
      iExists eq_refl.
      now iApply (refine_unfreshen_patterncaseenv with "Hargs").
    Qed.

    Lemma refine_pattern_match_var {N : Set} n {x σ} (pat : Pattern (N:=N) σ) {w} :
      ⊢ ℛ⟦RIn (x∷σ) -> RPureSpec (RMatchResult pat)⟧
        (CPureSpec.new_pattern_match pat)
        (SPureSpec.new_pattern_match_var (w := w) n pat).
    Proof.
      iIntros "%v %sv Hv %post %spost Hpost".
      unfold SPureSpec.new_pattern_match_var, CPureSpec.new_pattern_match, CPureSpec.pure.
      iIntros "Hsp".
      iPoseProof (refine_pattern_match_var (p := freshen_pattern n w pat) with "Hv") as "Hpm".
      rewrite <- (pattern_match_val_freshen n pat (Σ := w)).
      destruct pattern_match_val as [pc vs]. cbn - [acc_trans RSat].
      iSpecialize ("Hsp" $! pc).
      iSpecialize ("Hpost" $! _ (acc_matchvar_right pc)).
      iDestruct (knowing_assuming with "[$Hpm $Hsp]") as "H".
      iDestruct (knowing_assuming with "[$H $Hpost]") as "H".
      iApply (knowing_pure (acc_matchvar_right pc)).
      iApply (knowing_proper (ω := acc_matchvar_right pc) _ _ with "H").
      iIntros "[[Hargs Hsp] Hpost]".
      iApply ("Hpost" with "[Hargs] Hsp").
      iExists eq_refl; cbn.
      now iApply (refine_unfreshen_patterncaseenv with "Hargs").
    Qed.

    Lemma refine_new_pattern_match' {N : Set} n σ (pat : Pattern (N:=N) σ) {w} :
      ⊢ ℛ⟦RVal σ -> RPureSpec (RMatchResult pat)⟧
        (CPureSpec.new_pattern_match pat)
        (SPureSpec.new_pattern_match' (w := w) n pat).
    Proof.
      unfold SPureSpec.new_pattern_match'.
      iIntros "%v %sv rv".
      destruct sv.
      now iApply refine_pattern_match_var.
      all: now iApply refine_new_pattern_match_regular.
    Qed.

    #[export] Instance refine_new_pattern_match {N : Set} n σ (pat : Pattern (N:=N) σ) {w} :
      Related (RVal σ -> RPureSpec (RMatchResult pat))
        (CPureSpec.new_pattern_match pat) w
        (SPureSpec.new_pattern_match (w := w) n pat).
    Proof. unfold Related.
      induction pat; iIntros "%v %sv Hv";
        cbn [SPureSpec.new_pattern_match];
        solve_related.
      - cbn; solve_related.
      - destruct (term_get_val_spec sv) as [cv ?|]; cbn.
        + subst. iDestruct (refine_term_val2  with "Hv") as "<-"; cbn.
          solve_related.
        + iApply (refine_new_pattern_match' with "Hv").
      - now iApply (refine_new_pattern_match' with "Hv").
      - destruct (term_get_pair_spec sv) as [[? ?] eq|].
        + iApply (refine_pure (RA := RMatchResult _) with "[Hv]").
          destruct v as [v1 v2].
          iPoseProof (eqₚ_triv (vt2 := term_binop bop.pair t t0) eq) as "Heq".
          iDestruct (RVal_eqₚ with "[$Hv $Heq]") as "Hv".
          iDestruct (RVal_pair with "Hv") as "[Hv1 Hv2]".
          solve_related.
        + now iApply (refine_new_pattern_match' with "Hv").
      - destruct (term_get_sum_spec sv) as [[] eq|].
        + iDestruct (RVal_eqₚ with "[$Hv]") as "Hv".
          { iApply (eqₚ_triv (vt2 := term_inl t) eq). }
          iDestruct (RVal_invert_inl with "Hv") as "[%vl [-> Hv]]".
          cbn; solve_related.
        + iDestruct (RVal_eqₚ with "[$Hv]") as "Hv".
          { iApply (eqₚ_triv (vt2 := term_inr t) eq). }
          iDestruct (RVal_invert_inr with "Hv") as "[%vl [-> Hv]]".
          cbn; solve_related.
        + now iApply (refine_new_pattern_match' with "Hv").
      - cbn; solve_related.
      - destruct (term_get_val_spec sv) as [? ->|].
        + iDestruct (refine_term_val2 with "Hv") as "->".
          cbn; solve_related.
        + now iApply (refine_new_pattern_match' with "Hv").
      - now iApply (refine_new_pattern_match').
      - destruct (term_get_val_spec sv) as [? ->|].
        + iDestruct (refine_term_val2 with "Hv") as "->".
          cbn; solve_related.
        + now iApply (refine_new_pattern_match' with "Hv").
      - destruct (term_get_tuple_spec sv) as [? eq|].
        + iDestruct (RVal_eqₚ with "[$Hv]") as "Hv".
          { iApply (eqₚ_triv (vt2 := term_tuple a) eq).  }
          cbn; solve_related.
          refine (RefineSolver.rimpl_elim (RefineSolver.rvalid refine_tuple_pattern_match_env) _).
          now rewrite <-RVal_tuple.
        + now iApply refine_new_pattern_match'.
      - destruct (term_get_record_spec sv) as [? eq|].
        + iDestruct (RVal_eqₚ with "[$Hv]") as "Hv".
          { iApply (eqₚ_triv (vt2 := term_record R a) eq).  }
          cbn; solve_related.
          unfold record_pattern_match_val.
          rewrite <-refine_record_pattern_match_env.
          now rewrite RVal_record recordv_fold_unfold.
        + now iApply refine_new_pattern_match'.
      - destruct (term_get_union_spec sv) as [[K tf] Heq|].
        + iIntros (post spost) "rpost"; cbn.
          iPoseProof (RVal_eqₚ with "[$Hv]") as "Hv".
          { iApply (eqₚ_triv (vt2 := term_union U K tf) Heq). }
          rewrite <-(unionv_fold_unfold U v).
          destruct (unionv_unfold U v) as [K' vf].
          iDestruct (RVal_union_invertK with "Hv") as "->".
          rewrite RVal_union.
          iPoseProof (H K with "Hv") as "H".
          unfold CPureSpec.new_pattern_match; cbn.
          rewrite unionv_unfold_fold; cbn.
          destruct (pattern_match_val (p K) vf) as [pc δpc] eqn:?.
          iApply ("H" $! (fun '(existT pc δpc) => post (existT (existT K pc) δpc)) with "[rpost]").
          clear.
          iIntros (w2 ω2) "!> %mr %smr Hmr".
          destruct mr as [pc' δargs].
          destruct smr as [spc' sδargs].
          iDestruct "Hmr" as "[%eq H2]"; subst; cbn.
          rewrite forgetting_unconditionally.
          iApply "rpost".
          now iExists eq_refl.
        + now iApply refine_new_pattern_match'.
    Qed.

    #[export] Instance refine_debug `{RA : Rel SA CA} {w msg} :
      Related (RPureSpec RA -> RPureSpec RA)
        CPureSpec.debug w (SPureSpec.debug (w := w) msg).
    Proof.
      iIntros (m ms) "Hm %k %ks Hk HSP".
      iApply ("Hm" with "Hk [HSP]").
      now iApply elim_debugPred.
    Qed.

    #[export] Instance refine_compat_debug `{R : Rel AT A} {w0 : World} {f} {mc ms} :
      RelatedFrom (RPureSpec R) (CPureSpec.debug mc) w0 (@SPureSpec.debug AT w0 f ms) (ℛ⟦RPureSpec R⟧ mc ms).
    Proof. unfold RelatedFrom. iApply refine_debug. Qed.

    Lemma refine_assert_eq_nenv {N : Set} {w} :
      ⊢ ℛ⟦∀ᵣ Δ : NCtx N Ty, RMsg _ (RNEnv _ Δ -> RNEnv _ Δ -> RPureSpec RUnit)⟧
        CPureSpec.assert_eq_nenv (SPureSpec.assert_eq_nenv (w := w)).
    Proof.
      iIntros (Δ msg E1 Es1) "HE1 %E2 %Es2 HE2".
      iInduction Es1 as [|Es1] "IHEs1";
        env.destroy Es2; env.destroy E1; env.destroy E2; cbn -[RSat].
      - now iApply (refine_pure (RA := RUnit)).
      - iDestruct (repₚ_invert_snoc with "HE1") as "(HE1 & Hv0db)".
        iDestruct (repₚ_invert_snoc with "HE2") as "(HE2 & Hv1v)".
        iSpecialize ("IHEs1" with "HE1 HE2").
        iApply (refine_bind (RA := RUnit) (RB := RUnit) with "IHEs1"); solve_related.
    Qed.

    #[export] Instance refine_compat_assert_eq_nenv {N : Set} {w} {Δ : NCtx N Ty} {msg} :
      Related (RNEnv _ Δ -> RNEnv _ Δ -> RPureSpec RUnit) (CPureSpec.assert_eq_nenv (Δ := Δ)) w (SPureSpec.assert_eq_nenv (w := w) msg).
    Proof. iIntros. iApply refine_assert_eq_nenv. Qed.

    Lemma refine_assert_eq_env {w} :
      ⊢ ℛ⟦∀ᵣ Δ, RMsg _ (REnv Δ -> REnv Δ -> RPureSpec RUnit)⟧
        CPureSpec.assert_eq_env (SPureSpec.assert_eq_env (w := w)).
    Proof.
      iIntros (Δ msg E1 Es1) "HE1 %E2 %Es2 HE2".
      iInduction Es1 as [] "IHE"; env.destroy E1; env.destroy E2; env.destroy Es2; cbn - [RSat].
      - now iApply (refine_pure (RA := RUnit)).
      - iDestruct (repₚ_invert_snoc with "HE1") as "(HE1 & Hvdb)".
        iDestruct (repₚ_invert_snoc with "HE2") as "(HE2 & Hv0v1)".
        iSpecialize ("IHE" with "HE1 HE2").
        iApply (refine_bind (RA := RUnit) (RB := RUnit) with "IHE"); solve_related.
    Qed.
    
    Lemma RChunk_ind (P : Rel Chunk SCChunk) {w : World} :
      (∀ p args sargs, ℛ⟦ REnv (𝑯_Ty p) ⟧ args sargs -∗ ℛ⟦ P ⟧ (chunk_user p args) (chunk_user p sargs)) ∗
        (∀ σ r v sv, ℛ⟦ RVal σ ⟧ v sv -∗ ℛ⟦ P ⟧ (chunk_ptsreg r v) (chunk_ptsreg r sv)) ∗
        (∀ c1 sc1 c2 sc2, ℛ⟦ RChunk ⟧ c1 sc1 -∗ ℛ⟦ RChunk ⟧ c2 sc2 -∗ ℛ⟦ P ⟧ c1 sc1 -∗ ℛ⟦ P ⟧ c2 sc2 -∗ ℛ⟦ P ⟧ (chunk_conj c1 c2) (chunk_conj sc1 sc2)) ∗
        (∀ c1 sc1 c2 sc2, ℛ⟦ RChunk ⟧ c1 sc1 -∗ ℛ⟦ RChunk ⟧ c2 sc2 -∗ ℛ⟦ P ⟧ c1 sc1 -∗ ℛ⟦ P ⟧ c2 sc2 -∗ ℛ⟦ P ⟧ (chunk_wand c1 c2) (chunk_wand sc1 sc2))
        ⊢
        ∀ c (sc : Chunk w), ℛ⟦ RChunk ⟧ c sc → ℛ⟦ P ⟧ c sc.
    Proof.
      constructor. intros ι Hpc (Huser & Hptsreg & Hconj & Hwand) c sc Hsc.
      revert c Hsc; induction sc; intros c Hsc; inversion Hsc.
      - now eapply Huser.
      - now eapply Hptsreg.
      - eapply Hconj; try now cbn.
        + now eapply IHsc1.
        + now eapply IHsc2.
      - eapply Hwand; try now cbn.
        + now eapply IHsc1.
        + now eapply IHsc2.
    Qed.

    Lemma RChunk_case (P : Rel Chunk SCChunk) {w : World} :
      (∀ p args sargs, ℛ⟦ REnv (𝑯_Ty p) ⟧ args sargs -∗ ℛ⟦ P ⟧ (chunk_user p args) (chunk_user p sargs)) ∗
        (∀ σ r v sv, ℛ⟦ RVal σ ⟧ v sv -∗ ℛ⟦ P ⟧ (chunk_ptsreg r v) (chunk_ptsreg r sv)) ∗
        (∀ c1 sc1 c2 sc2, ℛ⟦ RChunk ⟧ c1 sc1 -∗ ℛ⟦ RChunk ⟧ c2 sc2 -∗ ℛ⟦ P ⟧ (chunk_conj c1 c2) (chunk_conj sc1 sc2)) ∗
        (∀ c1 sc1 c2 sc2, ℛ⟦ RChunk ⟧ c1 sc1 -∗ ℛ⟦ RChunk ⟧ c2 sc2 -∗ ℛ⟦ P ⟧ (chunk_wand c1 c2) (chunk_wand sc1 sc2))
        ⊢
        ∀ c (sc : Chunk w), ℛ⟦ RChunk ⟧ c sc → ℛ⟦ P ⟧ c sc.
    Proof.
      iIntros "(Huser & Hptsreg & Hconj & Hwand) %c %sc #Hsc".
      iApply (RChunk_ind P with "[Huser Hptsreg Hconj Hwand] Hsc").
      iFrame "Huser Hptsreg".
      iSplitL "Hconj".
      - iIntros (c1 sc1 c2 sc2) "Hc1 Hc2 _ _". 
        now iApply ("Hconj" with "Hc1 Hc2").
      - iIntros (c1 sc1 c2 sc2) "Hc1 Hc2 _ _". 
        now iApply ("Hwand" with "Hc1 Hc2").
    Qed.

    Lemma refine_assert_eq_chunk {w} :
      ⊢ ℛ⟦RMsg _ (RChunk -> RChunk -> □ᵣ(RPureSpec RUnit))⟧
        CPureSpec.assert_eq_chunk (SPureSpec.assert_eq_chunk (w := w)).
    Proof.
      iIntros (msg c1 sc1) "Hc1".
      iApply (RChunk_ind (MkRel (fun c w sc => ∀ (msg : AMessage w), ℛ⟦RChunk -> □ᵣ (RPureSpec RUnit)⟧ (CPureSpec.assert_eq_chunk c) (SPureSpec.assert_eq_chunk (w := w) msg sc))%I) with "[] Hc1").
      clear.
      repeat iSplit.
      - iIntros (p args sargs) "Hargs %msg %c2 %sc2 Hc2".
        iApply (RChunk_case (MkRel (fun c2 w sc2 => ∀ msg p args sargs, ℛ⟦REnv (𝑯_Ty p)⟧ args sargs -∗ ℛ⟦□ᵣ (RPureSpec RUnit)⟧ (CPureSpec.assert_eq_chunk (chunk_user p args) c2) (SPureSpec.assert_eq_chunk msg (chunk_user p sargs) sc2))%I) with "[] Hc2 Hargs").
        clear.
        repeat iSplit.
        + iIntros (p args sargs) "Hargs %msg %p2 %args2 %sargs2 Hargs2 %w1 %ω1 !>".
          cbn -[RSat].
          destruct (eq_dec p2 p); last by iApply (refine_error (RA := RUnit)).
          subst; unfold REnv, RInst; cbn.
          rewrite <- !forgetting_repₚ.
          now iApply (refine_assert_eq_env with "Hargs2 Hargs").
        + iIntros (σ r v sv) "Hv %msg %p %args %sargs Hargs %w1 %ω1 !>"; solve_related.
        + iIntros (c1 sc1 c2 sc2) "_ _ %msg %p %args %sargs Hargs %w1 %ω1 !>"; solve_related.
        + iIntros (c1 sc1 c2 sc2) "_ _ %msg %p %args %sargs Hargs %w1 %ω1 !>"; solve_related.
      - iIntros (σ r v sv) "Hv %msg %c2 %sc2 Hc2".
        iApply (RChunk_case (MkRel (fun c2 w sc2 => ∀ msg σ r v sv, ℛ⟦RVal σ⟧ v sv -∗ ℛ⟦□ᵣ (RPureSpec RUnit)⟧ (CPureSpec.assert_eq_chunk (chunk_ptsreg r v) c2) (SPureSpec.assert_eq_chunk msg (chunk_ptsreg r sv) sc2))%I) with "[] Hc2 Hv").
        clear.
        repeat iSplit.
        + iIntros (p args sargs) "Hargs %msg %σ %r %v %sv Hv %w1 %ω1 !>".
          iApply (refine_error (RA := RUnit)).
        + iIntros (σ2 r2 v2 sv2) "Hv2 %msg %σ %r %v %sv Hv %w1 %ω1 !>".
          cbn -[RSat].
          destruct (eq_dec_het r r2); last solve_related.
          dependent elimination e; cbn -[RSat].
          iApply refine_assert_formula; solve_related.
        + iIntros (c1 sc1 c2 sc2) "Hc1 Hc2 %msg %σ %r %v %sv Hv %w1 %ω1 !>"; solve_related.
        + iIntros (c1 sc1 c2 sc2) "Hc1 Hc2 %msg %σ %r %v %sv Hv %w1 %ω1 !>"; solve_related.
      - iIntros (c1 sc1 c2 sc2) "Hc1 Hc2 IHc1 IHc2 %msg %c3 %sc3 Hc3".
        iApply (RChunk_case (MkRel (fun c3 w sc3 => ∀ msg c1 sc1 c2 sc2,
                                        ℛ⟦RChunk⟧ c1 sc1 -∗
                                                            ℛ⟦RChunk -> □ᵣ (RPureSpec RUnit)⟧ (CPureSpec.assert_eq_chunk c1) (SPureSpec.assert_eq_chunk msg sc1) -∗
                                                                                                                                                                    ℛ⟦RChunk⟧ c2 sc2 -∗
                                                                                                                                                                                        ℛ⟦RChunk -> □ᵣ (RPureSpec RUnit)⟧ (CPureSpec.assert_eq_chunk c2) (SPureSpec.assert_eq_chunk msg sc2) -∗
                                                                                                                                                                                                                                                                                                ℛ⟦□ᵣ (RPureSpec RUnit)⟧ (CPureSpec.assert_eq_chunk (chunk_conj c1 c2) c3) (SPureSpec.assert_eq_chunk msg (chunk_conj sc1 sc2) sc3))%I) with "[] Hc3 Hc1 IHc1 Hc2 IHc2").
        clear. repeat iSplitL.
        + iIntros (p args sargs) "Hargs %msg %c1 %sc1 %c2 %sc2 Hc1 IHc1 Hc2 IHc2 %w1 %ω1 !>"; solve_related.
        + iIntros (σ r v sv) "Hv %msg %c1 %sc1 %c2 %sc2 Hc1 IHc1 Hc2 IHc2 %w1 %ω1 !>"; solve_related.
        + iIntros (c3 sc3 c4 sc4) "Hc3 Hc4 %msg %c1 %sc1 %c2 %sc2 Hc1 IHc1 Hc2 IHc2 %w1 %ω1 !>".
          iApply (refine_bind (RA := RUnit) (RB := RUnit) with "[Hc1 IHc1 Hc3] [Hc2 IHc2 Hc4]").
          * iSpecialize ("IHc1" with "Hc3").
            now rewrite forgetting_unconditionally_drastic.
          * iIntros (w2 ω2) "!> %u %su _".
            iSpecialize ("IHc2" with "Hc4").
            now rewrite forgetting_unconditionally_drastic.
        + iIntros (c3 sc3 c4 sc4) "Hc3 Hc4 %msg %c1 %sc1 %c2 %sc2 Hc1 IHc1 Hc2 IHc2 %w1 %ω1 !>"; solve_related.
      - iIntros (c1 sc1 c2 sc2) "Hc1 Hc2 IHc1 IHc2 %msg %c3 %sc3 Hc3".
        iApply (RChunk_case (MkRel (fun c3 w sc3 => ∀ msg c1 sc1 c2 sc2,
                                        ℛ⟦RChunk⟧ c1 sc1 -∗
                                                            ℛ⟦RChunk -> □ᵣ (RPureSpec RUnit)⟧ (CPureSpec.assert_eq_chunk c1) (SPureSpec.assert_eq_chunk msg sc1) -∗
                                                                                                                                                                    ℛ⟦RChunk⟧ c2 sc2 -∗
                                                                                                                                                                                        ℛ⟦RChunk -> □ᵣ (RPureSpec RUnit)⟧ (CPureSpec.assert_eq_chunk c2) (SPureSpec.assert_eq_chunk msg sc2) -∗
                                                                                                                                                                                                                                                                                                ℛ⟦□ᵣ (RPureSpec RUnit)⟧ (CPureSpec.assert_eq_chunk (chunk_wand c1 c2) c3) (SPureSpec.assert_eq_chunk msg (chunk_wand sc1 sc2) sc3))%I) with "[] Hc3 Hc1 IHc1 Hc2 IHc2").
        clear. repeat iSplitL.
        + iIntros (p args sargs) "Hargs %msg %c1 %sc1 %c2 %sc2 Hc1 IHc1 Hc2 IHc2 %w1 %ω1 !>".
          iApply (refine_error (RA := RUnit)).
        + iIntros (σ r v sv) "Hv %msg %c1 %sc1 %c2 %sc2 Hc1 IHc1 Hc2 IHc2 %w1 %ω1 !>".
          iApply (refine_error (RA := RUnit)).
        + iIntros (c3 sc3 c4 sc4) "Hc3 Hc4 %msg %c1 %sc1 %c2 %sc2 Hc1 IHc1 Hc2 IHc2 %w1 %ω1 !>".
          iApply (refine_error (RA := RUnit)).
        + iIntros (c3 sc3 c4 sc4) "Hc3 Hc4 %msg %c1 %sc1 %c2 %sc2 Hc1 IHc1 Hc2 IHc2 %w1 %ω1 !>".
          iApply (refine_bind (RA := RUnit) (RB := RUnit) with "[Hc1 IHc1 Hc3] [Hc2 IHc2 Hc4]").
          * iSpecialize ("IHc1" with "Hc3").
            now rewrite forgetting_unconditionally_drastic.
          * iIntros (w2 ω2) "!> %u %su _".
            iSpecialize ("IHc2" with "Hc4").
            now rewrite forgetting_unconditionally_drastic.
    Qed.

    #[export] Instance refine_compat_assert_eq_chunk {w msg} :
      Related (RChunk -> RChunk -> □ᵣ(RPureSpec RUnit))
        CPureSpec.assert_eq_chunk w (SPureSpec.assert_eq_chunk (w := w) msg).
    Proof. iIntros. iApply refine_assert_eq_chunk. Qed.

    #[export] Instance refine_compat_env_lookup {Σ : LCtx} {x : LVar} {σ} {xIn : ctx.In (x∷σ) Σ} {w : World}
      {a : Valuation Σ} {sa : Sub Σ w} :
      RelatedFrom (RVal σ) (env.lookup a (b := x∷σ) xIn) w (env.lookup sa (b := x∷σ) xIn) (ℛ⟦RNEnv LVar Σ⟧ a sa).
    Proof.
      unfold RelatedFrom. iIntros "H".
      iApply (repₚ_cong (T1 := Sub Σ) (T2 := STerm σ) (fun ι => env.lookup ι xIn) (fun ιs => env.lookup ιs xIn) with "H").
      intros. now rewrite inst_lookup.
    Qed.

    #[export] Instance refine_compat_env_remove {Σ : LCtx} {x : LVar} {σ} {xIn : ctx.In (x∷σ) Σ} {w : World}
      {a : Valuation Σ} {sa : Sub Σ w} :
      RelatedFrom (RNEnv LVar (Σ - x∷σ)) (env.remove (x∷σ) a xIn) w (env.remove (x∷σ) sa xIn)
        (ℛ⟦RNEnv LVar Σ⟧ a sa).
    Proof.
      unfold RelatedFrom. iIntros "H".
      iApply (repₚ_cong (T1 := Sub Σ) (T2 := Sub (Σ - (x∷σ))) (fun vs => env.remove (x∷σ) vs xIn) (fun vs => env.remove (x∷σ) vs xIn) with "H").
      intros. now rewrite <- inst_sub_shift, <- inst_subst, sub_comp_shift.
    Qed.

    Lemma refine_replay_aux {Σ} (s : 𝕊 Σ) {w} :
      Related (RNEnv LVar Σ -> RPureSpec RUnit)
        (CPureSpec.replay_aux s) w (SPureSpec.replay_aux (w := w) s).
    Proof.
      revert w; induction s; intros w; cbn -[RSat]; solve_related.
      all: rewrite <-inst_sub_shift, <-inst_subst; solve_related.
    Qed.

    Lemma refine_replay (s : 𝕊 wnil) :
      ⊢ (ℛ⟦ RProp ⟧ (CPureSpec.replay s [env]) (SPureSpec.replay s)).
    Proof.
      unfold CPureSpec.replay, SPureSpec.replay.
      iApply refine_run.
      iApply (refine_replay_aux s).
      now iApply (refine_lift (AT := Sub [ctx])).
    Qed.

    #[export] Instance refine_peval_chunk {w} :
      Related (RChunk -> RChunk) id w (peval_chunk : Impl _ _ w).
    Proof. unfold Related.
      unfold RImpl, RChunk, RInst. crushPredEntails3.
      now rewrite peval_chunk_sound.
    Qed.

    #[export] Instance refine_produce_chunk {w} :
      Related (RChunk -> RHeap -> RPureSpec RHeap)
        CPureSpec.produce_chunk w  (SPureSpec.produce_chunk (w := w)).
    Proof. unfold Related.
      iIntros (c sc) "Hc %h %sh Hh".
      unfold SPureSpec.produce_chunk, CPureSpec.produce_chunk.
      iApply (refine_pure (RA := RHeap)).
      iApply (refine_RHeap_cons with "[Hc] Hh").
      now iApply refine_peval_chunk.
    Qed.

    #[export] Instance refine_is_duplicable {w} :
      Related (RChunk -> RConst bool) is_duplicable w (@is_duplicable (Chunk w) _ : Impl Chunk (Const bool) w).
    Proof. unfold Related.
      unfold RImpl, RChunk, RConst, RInst; crushPredEntails3; subst.
      now destruct a0.
    Qed.

    #[export] Instance refine_heap_extractions {w} :
      Related (RHeap -> RList (RProd RChunk RHeap))
        (heap_extractions) w
        (heap_extractions : Impl SHeap (fun w => list (Chunk w * SHeap w)) w).
    Proof. unfold Related.
      iIntros (h sh) "Hh".
      unfold RHeap, SHeap, SCHeap, inst_heap.
      rewrite <-(RList_RInst (AT := Chunk)).
      iApply (RList_ind (MkRel (fun h w sh => ℛ⟦RList (RProd RChunk RHeap)⟧ (heap_extractions h) (heap_extractions sh))) with "[] Hh").
      clear.
      iSplit.
      - iApply (refine_nil (R := RProd RChunk RHeap)).
      - iIntros (v svs vs sv) "#Hv #Hvs IHvs".
        iApply (refine_cons (R := RProd RChunk RHeap) with "[Hv Hvs] [Hvs IHvs]").
        + iSplitL; first done.
          iApply (refine_if (R := RHeap)).
          * now iApply refine_is_duplicable.
          * rewrite (RList_RInst (AT := Chunk)).
            now iApply refine_RHeap_cons.
          * now rewrite (RList_RInst (AT := Chunk)).
        + iApply (refine_map (R1 := RProd RChunk RHeap) (R2 := RProd RChunk RHeap) with "[] IHvs").
          iIntros ([c1 h1] [sc1 sh1]) "[Hc1 Hh1]".
          iFrame "Hc1".
          now iApply refine_RHeap_cons.
    Qed.

    Lemma refine_In `{R : Rel AT A} {w} {sv : AT w} {sl l} :
      ⊢ ℛ⟦ RList R ⟧ l sl -∗ ⌜ In sv sl ⌝ -∗ ∃ v, ⌜ In v l ⌝ ∗ ℛ⟦ R ⟧ v sv.
    Proof.
      iIntros "Hl %Hin".
      iApply (RList_ind (R := R) (MkRel (fun l w sl => ∀ sv, ⌜ In sv sl ⌝ -∗ ∃ v, ⌜ In v l ⌝ ∗ ℛ⟦ R ⟧ v sv))%I with "[] Hl [%//]").
      clear.
      iSplit.
      - iIntros "%sv %Hin".
        now inversion Hin.
      - iIntros (v sv vs svs) "Hv Hvs IHvs %sv2 %Hin".
        destruct Hin as [<- | Hin].
        + iExists v.
          iFrame.
          now iLeft.
        + iDestruct ("IHvs" with "[% //]") as "(%v2 & Hin & Hv2)".
          iExists v2. iFrame.
          now iRight.
    Qed.

    Lemma refine_consume_chunk_exact {w : World} {c h} {sc : Chunk w} {sh sh' : SHeap w} :
      try_consume_chunk_exact sh sc = Some sh' →
      ℛ⟦RChunk⟧ c sc ∗ ℛ⟦RHeap⟧ h sh ⊢
      ℛ⟦RPureSpec RHeap⟧ (CPureSpec.consume_chunk c h) (SPureSpec.pure sh').
    Proof.
      intros Hexact.
      pose proof (try_consume_chunk_exact_spec sh sc) as HsIn.
      rewrite Hexact in HsIn; rewrite option.wlp_some in HsIn.
      iIntros "[Hc Hh] %K %sK HK HSP".
      iDestruct (refine_heap_extractions with "Hh") as "Hexts".
      iDestruct (refine_In with "Hexts [//]") as "(%v & %HIn & HH)".
      destruct v as (c1 & h').
      iDestruct "HH" as "(Hc1 & Hh')".
      iDestruct (repₚ_antisym_left with "Hc Hc1") as "<-".
      unfold CPureSpec.consume_chunk, CPureSpec.bind.
      rewrite CPureSpec.wp_angelic_list.
      iExists (c, h').
      iSplit; first done.
      rewrite CPureSpec.wp_assert_eq_chunk.
      iSplit; first done.
      now iApply (refine_T with "HK Hh' HSP").
    Qed.

    Lemma refine_consume_chunk_precise {w : World} {c h} {sc : Chunk w} {sh sh' : SHeap w}
      {eqs : PathCondition w} (msg : AMessage w) :
      try_consume_chunk_precise sh sc = Some (sh', eqs) →
      ℛ⟦RChunk⟧ c sc ∗ ℛ⟦RHeap⟧ h sh ⊢
      ℛ⟦RPureSpec RHeap⟧ (CPureSpec.consume_chunk c h)
        (⟨ θ ⟩ _ <- SPureSpec.assert_pathcondition msg eqs ;; SPureSpec.pure sh'⟨θ⟩).
    Proof.
      intros Hprecise.
      pose proof (try_consume_chunk_precise_spec sh sc) as HIn.
      rewrite Hprecise in HIn; rewrite option.wlp_some in HIn.
      iIntros "[Hc Hh]".
      iDestruct (eval_prop eqs) as "(%eq & Heq)".
      iDestruct (eval_ex sh') as "(%h' & Hh')".
      iIntros (K sK) "HK HSP".
      iAssert (⌜eq /\ K h'⌝)%I with "[HK HSP]" as "%HeqKh'".
      { iPoseProof (refine_assert_pathcondition $! msg eq eqs with "Heq") as "Hapc".
        iApply ("Hapc" $! (fun _ => K h') with "[HK] HSP").
        iIntros (w2 ω2) "!> %u %su _".
        rewrite forgetting_unconditionally.
        iApply (refine_T with "HK"); solve_related.
      }
      destruct HeqKh' as (Heq & HKh').
      iAssert ⌜In (c, h') (heap_extractions h)⌝%I with "[Hc Hh]" as "%HInch'".
      { iStopProof. unfold RChunk, RHeap, RInst; cbn - [repₚ].
        clear -HIn Heq. crushPredEntails3. subst. apply HIn.
        now rewrite instpred_prop in H5.
      }
      unfold CPureSpec.consume_chunk, CPureSpec.bind.
      rewrite CPureSpec.wp_angelic_list.
      iExists (c, h').
      iSplit; first done.
      rewrite CPureSpec.wp_assert_eq_chunk.
      now iSplit.
    Qed.

    #[export] Instance refine_consume_chunk {w} :
      Related (RChunk -> RHeap -> RPureSpec RHeap)
        CPureSpec.consume_chunk w (SPureSpec.consume_chunk (w := w)).
    Proof. unfold Related.
      iIntros (c sc) "#Hc %h %sh #Hh".
      unfold SPureSpec.consume_chunk.
      iPoseProof (refine_peval_chunk with "Hc") as "Hcp"; cbn -[RSat].
      set (sc1 := peval_chunk sc).
      destruct (try_consume_chunk_exact sh sc1) as [sh'|] eqn:Hexact.
      { iApply (refine_consume_chunk_exact Hexact with "[$Hcp $Hh]"). }
      destruct (try_consume_chunk_precise sh sc1) as [[sh' eqs]|] eqn:Hprecise.
      { iApply (refine_consume_chunk_precise _ Hprecise with "[$Hcp $Hh]"). }
      now iApply (refine_error (RA := RHeap)).
    Qed.

    #[export] Instance refine_consume_chunk_angelic {w} :
      Related (RChunk -> RHeap -> RPureSpec RHeap)
        CPureSpec.consume_chunk w (SPureSpec.consume_chunk_angelic (w := w)).
    Proof. unfold Related.
      iIntros (c sc) "Hc %h %sh Hh".
      unfold SPureSpec.consume_chunk_angelic.
      iDestruct (refine_peval_chunk with "Hc") as "Hc1".
      set (sc1 := peval_chunk sc).
      destruct (try_consume_chunk_exact sh sc1) as [sh'|] eqn:Hexact; solve_related.
      { iApply (refine_consume_chunk_exact Hexact with "[$Hc1 $Hh]"). }
      destruct (try_consume_chunk_precise sh sc1) as [[sh' eqs]|] eqn:Hprecise.
      { iApply (refine_consume_chunk_precise _ Hprecise with "[$Hc1 $Hh]"). }
      { iApply (refine_bind (RA := RProd RChunk RHeap) (RB := RHeap) with "[Hh] [Hc1]").
        { iApply (refine_angelic_list (RA := RProd RChunk RHeap)).
          now iApply refine_heap_extractions.
        }
        iIntros (w2 ω2) "!> %ch %sch Hch".
        destruct ch as (c', h').
        destruct sch as (sc', sh').
        iDestruct "Hch" as "(Hc' & Hh')".
        iApply (refine_bind (RA := RUnit) (RB := RHeap) with "[Hc1 Hc'] [Hh']"); solve_related.
        rewrite refine_inst_persist.
        iPoseProof (refine_assert_eq_chunk with "Hc1 Hc'") as "Haec".
        iApply (refine_T with "Haec").
      } 
    Qed.

    #[export] Instance refine_read_register {τ} (reg : 𝑹𝑬𝑮 τ) {w} :
      Related (RHeap -> RPureSpec (RProd (RVal τ) RHeap))
        (CPureSpec.read_register reg) w (SPureSpec.read_register (w := w) reg).
    Proof. unfold Related.
      unfold SPureSpec.read_register, SPureSpec.pure, T.
      iIntros (h sh) "#Hh".
      destruct (find_chunk_ptsreg_precise_spec reg sh) as [[st sh'] HIn|]; last solve_related.
      cbv [CPureSpec.read_register CPureSpec.consume_chunk CPureSpec.pure
             CPureSpec.produce_chunk CPureSpec.bind CPureSpec.angelic].
      iDestruct (eval_ex (AT := STerm τ) st) as "(%v & Hv)".
      iDestruct (eval_ex (AT := SHeap) sh') as "(%h' & Hh')".
      iIntros "%K %sK HK HSP".
      iExists v.
      rewrite CPureSpec.wp_angelic_list.
      iExists (chunk_ptsreg reg v, h').
      iSplitR.
      - iStopProof.
        unfold RHeap, RInst.
        crushPredEntails3. now subst. 
      - rewrite CPureSpec.wp_assert_eq_chunk.
        iSplit; first done.
        iApply (refine_T with "HK [Hv Hh'] HSP").
        iSplitL "Hv"; first done.
        iApply (refine_RHeap_cons with "[Hv] Hh'").
        solve_related.
    Qed.

    #[export] Instance refine_write_register {τ} (reg : 𝑹𝑬𝑮 τ) {w} :
      Related (RVal τ -> RHeap -> RPureSpec (RProd (RVal τ) RHeap))
        (CPureSpec.write_register reg) w (SPureSpec.write_register (w := w) reg).
    Proof. unfold Related.
      unfold SPureSpec.write_register, SPureSpec.pure, T.
      iIntros (v sv) "#Hv %h %sh #Hh".
      destruct (find_chunk_ptsreg_precise_spec reg sh) as [[st sh'] HIn|]; last solve_related.
      cbv [CPureSpec.write_register CPureSpec.consume_chunk CPureSpec.pure
             CPureSpec.produce_chunk CPureSpec.bind CPureSpec.angelic].
      iDestruct (eval_ex (AT := STerm τ) st) as "(%v' & Hv')".
      iDestruct (eval_ex (AT := SHeap) sh') as "(%h' & Hh')".
      iIntros "%K %sK HK HS".
      iExists v'.
      rewrite CPureSpec.wp_angelic_list.
      iExists (chunk_ptsreg reg v', h').
      iSplitR.
      - iStopProof. unfold RHeap, RInst.
        crushPredEntails3. now subst.
      - rewrite CPureSpec.wp_assert_eq_chunk.
        iSplit; first done.
        iApply (refine_T with "HK [Hv Hh'] HS").
        iFrame "Hv".
        iApply (refine_RHeap_cons with "[Hv] Hh'"); solve_related.
    Qed.

  End PureSpec.

  Definition RHeapSpec [SA CA] (RA : Rel SA CA) :
    Rel (SHeapSpec SA) (CHeapSpec CA) :=
    □ᵣ(RA -> RHeap -> ℙ) -> RHeap -> ℙ.

  Module HeapSpec.
    Import PureSpec.

    (* Instance search does not unfold the concrete operations, so their
       instances are indexed, and tried, by their head. *)
    #[export] Typeclasses Opaque CHeapSpec.angelic CHeapSpec.angelic_binary
      CHeapSpec.angelic_ctx CHeapSpec.assert_formula CHeapSpec.assume_formula
      CHeapSpec.bind CHeapSpec.call_contract CHeapSpec.call_lemma
      CHeapSpec.consume CHeapSpec.consume_chunk CHeapSpec.debug
      CHeapSpec.demonic CHeapSpec.demonic_binary CHeapSpec.demonic_ctx
      CHeapSpec.lift_purespec CHeapSpec.produce CHeapSpec.produce_chunk
      CHeapSpec.pure CHeapSpec.read_register CHeapSpec.run
      CHeapSpec.write_register.

    #[export] Instance refine_run {w} :
      Related (RHeapSpec RUnit -> ℙ) CHeapSpec.run w (SHeapSpec.run (w := w)).
    Proof. unfold Related.
      unfold CHeapSpec.run, SHeapSpec.run. solve_related.
    Qed.

    #[export] Instance refine_lift_purespec `{RA : Rel SA CA} {w} :
      Related (RPureSpec RA -> RHeapSpec RA)
        CHeapSpec.lift_purespec w (SHeapSpec.lift_purespec (w := w)).
    Proof.
      unfold SHeapSpec.lift_purespec, CHeapSpec.lift_purespec, RHeapSpec. solve_related.
    Qed.

    #[export] Instance refine_pure `{RA : Rel SA CA} {w} :
      Related (RA -> RHeapSpec RA) CHeapSpec.pure w (SHeapSpec.pure (w := w)).
    Proof.
      iIntros (v sv) "rv %Φ %sΦ rΦ %h %sh rh".
      iApply (refine_T with "rΦ rv rh").
    Qed.

    Lemma refine_bind `{RA : Rel SA CA, RB : Rel SB CB} {w} :
      ⊢ ℛ⟦RHeapSpec RA -> □ᵣ(RA -> RHeapSpec RB) -> RHeapSpec RB⟧
        CHeapSpec.bind (SHeapSpec.bind (w := w)).
    Proof. unfold CHeapSpec.bind, SHeapSpec.bind, RPureSpec, RHeapSpec; solve_related. Qed.

    #[export] Instance refine_compat_heapspec_bind `{RA : Rel AT A} `{RB : Rel BT B} {w} :
      Related (RHeapSpec RA -> (□ᵣ (RA -> RHeapSpec RB)) -> RHeapSpec RB)
        CHeapSpec.bind w (SHeapSpec.bind (w := w)) | (Related _ _ _ SHeapSpec.bind) :=
      HeapSpec.refine_bind.

    #[export] Instance refine_error `{RA : Rel SA CA} cm {w} msg :
      Related (RHeapSpec RA) cm w (SHeapSpec.error (w := w) msg).
    Proof.
      iIntros (cΦ sΦ) "_ %ch %sh rh".
      unfold RProp; now cbn.
    Qed.

    #[export] Instance refine_angelic x σ {w} :
      Related (RHeapSpec (RVal σ))
        (CHeapSpec.angelic σ) w (SHeapSpec.angelic (w := w) x σ).
    Proof. unfold CHeapSpec.angelic, SHeapSpec.angelic; solve_related. Qed.

    #[export] Instance refine_demonic x σ {w} :
      Related (RHeapSpec (RVal σ))
        (CHeapSpec.demonic σ) w (SHeapSpec.demonic (w := w) x σ).
    Proof. unfold CHeapSpec.demonic, SHeapSpec.demonic; solve_related. Qed.

    #[export] Instance refine_angelic_ctx {N : Set} {n : N -> LVar} Δ {w} :
      Related (RHeapSpec (RNEnv N Δ))
          (CHeapSpec.angelic_ctx Δ) w (SHeapSpec.angelic_ctx (w := w) n Δ).
    Proof. unfold CHeapSpec.angelic_ctx, SHeapSpec.angelic_ctx; solve_related. Qed.

    #[export] Instance refine_demonic_ctx {N : Set} {n : N -> LVar} Δ {w} :
      Related (RHeapSpec (RNEnv N Δ))
          (CHeapSpec.demonic_ctx Δ) w (SHeapSpec.demonic_ctx (w := w) n Δ).
    Proof. unfold CHeapSpec.demonic_ctx, SHeapSpec.demonic_ctx; solve_related. Qed.

    #[export] Instance refine_angelic_binary `{RA : Rel SA CA} {w} :
      Related (RHeapSpec RA -> RHeapSpec RA -> RHeapSpec RA)
        CHeapSpec.angelic_binary w (SHeapSpec.angelic_binary (w := w)).
    Proof. unfold CHeapSpec.angelic_binary, SHeapSpec.angelic_binary, RPureSpec, RHeapSpec; solve_related. Qed.

    
    #[export] Instance refine_demonic_binary `{RA : Rel SA CA} {w} :
      Related (RHeapSpec RA -> RHeapSpec RA -> RHeapSpec RA)
        CHeapSpec.demonic_binary w (SHeapSpec.demonic_binary (w := w)).
    Proof. unfold CHeapSpec.demonic_binary, SHeapSpec.demonic_binary, RPureSpec, RHeapSpec; solve_related. Qed.

    
    #[export] Instance refine_debug `{RA : Rel SA CA} {w msg} :
      Related (RHeapSpec RA -> RHeapSpec RA)
        CHeapSpec.debug w (SHeapSpec.debug (w := w) msg).
    Proof.
      unfold Related, CHeapSpec.debug, SHeapSpec.debug.
      iIntros (cm sm) "rm %cΦ %sΦ #rΦ %ch %sh rh".
      iApply refine_symprop_debug.
      iApply "rm"; auto.
    Qed.

    (* [CHeapSpec.debug m] reduces to [m]. *)
    #[export] Instance refine_compat_debug_reduced `{RA : Rel SA CA} {w msg} {mc ms} :
      RelatedFrom (RHeapSpec RA) mc w (SHeapSpec.debug (w := w) msg ms) (ℛ⟦RHeapSpec RA⟧ mc ms) | 10.
    Proof. unfold RelatedFrom. iIntros "H". iApply (refine_debug (RA := RA) (msg := msg) $! mc ms with "H"). Qed.

    (* A [debug] only on the concrete side. *)
    #[export] Instance refine_compat_debug_concrete `{RA : Rel SA CA} {w} {mc ms} :
      RelatedFrom (RHeapSpec RA) (CHeapSpec.debug mc) w ms (ℛ⟦RHeapSpec RA⟧ mc ms) | 10.
    Proof. unfold RelatedFrom. now iIntros "H". Qed.

    #[export] Instance refine_assert_formula {w msg} :
      Related (RFormula -> RHeapSpec RUnit)
        CHeapSpec.assert_formula w (SHeapSpec.assert_formula (w := w) msg).
    Proof.
      unfold Related, CHeapSpec.assert_formula, SHeapSpec.assert_formula,
               CHeapSpec.lift_purespec.
      iIntros (cF sF) "rF %cΦ %sΦ rΦ %ch %sh rh".
      iApply (PureSpec.refine_assert_formula with "rF").
      iIntros (w1 θ1) "!> %cu %su ru".
      iApply ("rΦ" with "ru"); solve_related.
    Qed.

    #[export] Instance refine_assume_formula {w} :
      Related (RFormula -> RHeapSpec RUnit)
        CHeapSpec.assume_formula w (SHeapSpec.assume_formula (w := w)).
    Proof. unfold CHeapSpec.assume_formula, SHeapSpec.assume_formula; solve_related. Qed.

    #[export] Instance refine_produce_chunk {w} :
      Related (RChunk -> RHeapSpec RUnit)
        CHeapSpec.produce_chunk w (SHeapSpec.produce_chunk (w := w)).
    Proof. unfold CHeapSpec.produce_chunk, SHeapSpec.produce_chunk, RPureSpec, RHeapSpec; solve_related. Qed.

    #[export] Instance refine_consume_chunk {w} :
      Related (RChunk -> RHeapSpec RUnit)
        CHeapSpec.consume_chunk w (SHeapSpec.consume_chunk (w := w)).
    Proof. unfold CHeapSpec.consume_chunk, SHeapSpec.consume_chunk, RPureSpec, RHeapSpec; solve_related. Qed.

    #[export] Instance refine_consume_chunk_angelic {w} :
      Related (RChunk -> RHeapSpec RUnit)
        CHeapSpec.consume_chunk w (SHeapSpec.consume_chunk_angelic (w := w)).
    Proof. unfold CHeapSpec.consume_chunk, SHeapSpec.consume_chunk_angelic, RPureSpec, RHeapSpec; solve_related. Qed.

    #[export] Instance refine_produce {Σ} (asn : Assertion Σ) :
      ∀ w, Related (RInst (Sub Σ) (Valuation Σ) -> RHeapSpec RUnit)
             (CHeapSpec.produce asn) w (SHeapSpec.produce (w := w) asn).
    Proof.
      induction asn; cbn - [RSat]; intros w; solve_related.
    Qed.

    #[export] Instance refine_consume {Σ} (asn : Assertion Σ) :
      ∀ w, Related (RInst (Sub Σ) (Valuation Σ) -> RHeapSpec RUnit)
             (CHeapSpec.consume asn) w (SHeapSpec.consume asn (w := w)).
    Proof.
      induction asn; cbn - [RSat]; intros w; solve_related.
    Qed.

    #[export] Instance refine_read_register {τ} (reg : 𝑹𝑬𝑮 τ) {w} :
      Related (RHeapSpec (RVal τ)) (CHeapSpec.read_register reg) w (SHeapSpec.read_register reg (w := w)).
    Proof. unfold Related.
      iIntros (Φ sΦ) "rΦ %ch %sh rh".
      unfold CHeapSpec.read_register, SHeapSpec.read_register.
      iApply (PureSpec.refine_read_register with "rh").
      iIntros (w1 θ1) "!> %vh %svh  Hvh".
      destruct vh as [v h2].
      destruct svh as [sv sh2].
      iDestruct "Hvh" as "[Hv Hh2]".
      now iApply ("rΦ" with "Hv").
    Qed.

    #[export] Instance refine_write_register {τ} (reg : 𝑹𝑬𝑮 τ) {w} :
      Related (RVal τ -> RHeapSpec (RVal τ)) (CHeapSpec.write_register reg) w (SHeapSpec.write_register reg (w := w)).
    Proof. unfold Related.
      iIntros (v sv) "rv %Φ %sΦ rΦ %h %sh rh".
      unfold CHeapSpec.write_register, SHeapSpec.write_register.
      iApply (PureSpec.refine_write_register with "rv rh").
      iIntros (w1 θ1) "!> %vh %svh Hvh".
      destruct vh as [v2 h2].
      destruct svh as [sv2 sh2].
      iDestruct "Hvh" as "[Hv2 Hh2]".
      now iApply ("rΦ" with "Hv2").
    Qed.

    Import PureSpec.
    #[export] Instance refine_call_contract {Δ τ} (c : SepContract Δ τ) {w} :
      Related (RInst (SStore Δ) (CStore Δ) -> RHeapSpec (RVal τ))
        (CHeapSpec.call_contract c) w (SHeapSpec.call_contract c (w := w)).
    Proof. unfold CHeapSpec.call_contract, SHeapSpec.call_contract; solve_related. Qed.

    #[export] Instance refine_call_lemma {Δ} (lem : Lemma Δ) w :
      Related (RInst (SStore Δ) (CStore Δ) -> RHeapSpec RUnit)
          (CHeapSpec.call_lemma lem) w (SHeapSpec.call_lemma lem (w := w)).
    Proof. unfold CHeapSpec.call_lemma, SHeapSpec.call_lemma; solve_related. Qed.

  End HeapSpec.

End RefinementMonadsOn.

(* Local Variables: *)
(* proof-omit-proofs-option: t *)
(* End: *)
