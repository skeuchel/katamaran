(******************************************************************************)
(* Copyright (c) 2023 Steven Keuchel, Dominique Devriese                      *)
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

(* Strongly based on https://github.com/decrn/em *)

From Stdlib Require Import
     Classes.Morphisms
     Classes.Morphisms_Prop
     Classes.RelationClasses
     Relations.Relation_Definitions
.
From Equations Require Import
     Equations.
From stdpp Require Import base.
From Katamaran Require Import
     Prelude
     Bitvector
     Base
     Environment
     Symbolic.Worlds
     Syntax.Predicates
.
From iris Require bi.derived_connectives bi.interface proofmode.proofmode.

Declare Scope pred_scope.
Delimit Scope pred_scope with P.

Create Rewrite HintDb obligation.
Create Rewrite HintDb punfold.
Create Rewrite HintDb uniflogic.

Module Type UnifLogicOn
  (Import B : Base)
  (Import P : PredicateKit B)
  (Import W : WorldsMixin B P).

  Ltac punfold_connectives :=
    change (@interface.bi_and (@bi_pred ?w) ?P ?Q ?ι) with (P ι /\ Q ι) in * ||
    change (@interface.bi_sep (@bi_pred ?w) ?P ?Q ?ι) with (sepₚ (w := w) P Q ι) in * ||
    change (@eqₚ ?T ?A ?instTA ?w ?t1 ?t2 ?ι) with (inst t1 ι = inst t2 ι) in * ||
    change (@repₚ ?T ?A ?instTA ?t2 ?w ?t1 ?ι) with (inst t1 ι = t2) in *||
    change (@wandₚ ?w ?P ?Q ?ι) with (P ι -> Q ι)%type in *||
    change (@proprepₚ ?T ?instTP ?t2 ?w ?t1 ?ι) with (instprop t1 ι <-> t2)%type in *||
    change (@interface.bi_emp (@bi_pred _) ?ι) with (empₚ ι) in *||
    change (@interface.bi_wand (@bi_pred ?w) ?P ?Q ?ι) with (@wandₚ w P Q ι) in *||
    change (@interface.bi_entails (@bi_pred _) ?P ?Q) with (entails P Q) in *||
    change (@interface.bi_persistently (@bi_pred _) ?P ?ι) with (persistently P ι) in *||
    change (@interface.bi_or (@bi_pred ?w) ?P ?Q ?ι) with (P ι \/ Q ι) in *||
    change (@interface.bi_impl (@bi_pred ?w) ?P ?Q ?ι) with (P ι -> Q ι) in *||
    change (@derived_connectives.bi_iff (@bi_pred ?w) ?P ?Q ?ι) with (iff (P ι) (Q ι)) in *||
    change (@interface.bi_pure (@bi_pred _) ?P _) with P in *||
    change (@interface.bi_forall (@bi_pred ?w) ?A ?f ?ι) with (forall a, f a ι) ||
    (* the change seems to trigger some coq binding bug, so I removed the "in *" for now... *)
    change (@interface.bi_exist (@bi_pred ?w) ?A ?P) with (fun ι => exists a : A, P a ι) in *||
    unfold derived_connectives.bi_wand_iff, derived_connectives.bi_intuitionistically, derived_connectives.bi_affinely, interface.bi_emp_valid, proprepₚ in *;
    (* change (@subst Pred subst_pred _ _ ?P _ ?θ ?ι) with (P (inst θ ι)) in *; *)
    try progress (cbn beta).
  (* Ltac crushPredEntailsMatch3 := *)
  (*   match goal with *)
  (*   | [ H: interface.bi_entails ?x ?y, ι : Valuation ?w, Hpc : instprop ?pc ?ι |- _ ] => (pose proof (fromEntails x y H ι Hpc); clear H) *)
  (*   | [ |- interface.bi_entails ?x ?y ] => constructor *)
  (*   | [ H: interface.bi_sep _ _ _ |- _ ] => destruct H *)
  (*   | [ |- interface.bi_sep _ _ _ ] => split *)
  (*   | [ H: interface.bi_and _ _ _ |- _ ] => destruct H *)
  (*   | [ |- interface.bi_and _ _ _ ] => split *)
  (*   | [ H: interface.bi_persistently ?P ?ι |- _ ] => destruct H *)
  (*   | [ |- interface.bi_persistently ?P ?ι ] => constructor *)
  (*   | [ |- interface.bi_wand _ _ _ ] => constructor; intros *)
  (*   | [ H : interface.bi_wand _ _ _ |- _ ] => destruct H; cbn in H *)
  (*   | [ |- interface.bi_emp _ ] => constructor *)
  (*   end. *)
  Ltac crushPredEntails3 := cbn; intros;
                            repeat punfold_connectives;
                            repeat (repeat punfold_connectives; crushPredEntailsMatch1 || crushPredEntailsMatch2);
                            repeat punfold_connectives;
                            intuition.
                                 
  Module Import notations.

    Import iris.bi.interface iris.bi.derived_connectives.

    Notation "P ⊣⊢ₚ Q" := (@equiv (bi_car (@bi_pred _)) (@pred_equiv _) P%P Q%P)
      (at level 95).
    Notation "(⊣⊢ₚ)" := (@equiv (bi_car (@bi_pred _)) (@pred_equiv _))
      (only parsing).

    Notation "P ⊢ₚ Q" := (@bi_entails (@bi_pred _) P%P Q%P) (at level 95).
    Notation "(⊢ₚ)" := (@bi_entails (@bi_pred _)) (only parsing).

    Notation "⊤ₚ" := (@bi_pure (@bi_pred _) True) : pred_scope.
    Notation "⊥ₚ" := (@bi_pure (@bi_pred _) False) : pred_scope.
    Notation "P <->ₚ Q" := (@bi_iff (@bi_pred _) P%P Q%P) (at level 94) : pred_scope.
    Notation "P ->ₚ Q"  := (@bi_impl (@bi_pred _) P%P Q%P) (at level 94, right associativity) : pred_scope.
    Notation "P /\ₚ Q"  := (@bi_and (@bi_pred _) P%P Q%P) (at level 80, right associativity) : pred_scope.
    Notation "P \/ₚ Q"  := (@bi_or (@bi_pred _) P%P Q%P) (at level 85, right associativity) : pred_scope.

    Infix "=ₚ" := eqₚ (at level 70, no associativity) : pred_scope.

    Notation "∀ₚ x .. y , P" :=
      (@bi_forall (@bi_pred _) _ (fun x => .. (@bi_forall (@bi_pred _) _ (fun y => P%P)) ..))
      (at level 200, x binder, y binder, right associativity,
        format "'[ ' '[ ' ∀ₚ  x .. y ']' ,  '/' P ']'") : pred_scope.
    Notation "∃ₚ x .. y , P" :=
      (@bi_exist (@bi_pred _) _ (fun x => .. (@bi_exist (@bi_pred _) _ (fun y => P%P)) ..))
      (at level 200, x binder, y binder, right associativity,
        format "'[ ' '[ ' ∃ₚ  x .. y ']' ,  '/' P ']'") : pred_scope.

  End notations.

  #[export] Instance pred_absorbing {w} {P : Pred w} : derived_connectives.Absorbing P.
  Proof.
    unfold derived_connectives.Absorbing, derived_connectives.bi_absorbingly.
    crushPredEntails3.
  Qed.

  Lemma bientails_unfold [w] (P Q : Pred w) :
    (P ⊣⊢ₚ Q) <-> forall ι, instprop (wco w) ι -> P ι <-> Q ι.
  Proof. crushPredEntails3. Qed.
  Lemma entails_unfold [w] (P Q : Pred w) :
    (P ⊢ₚ Q) <-> forall ι, instprop (wco w) ι -> P ι -> Q ι.
  Proof. crushPredEntails3. Qed.
  Lemma sep_unfold w (P Q : Pred w) :
    ∀ ι, interface.bi_sep P Q ι ↔ (P ι /\ Q ι).
  Proof. crushPredEntails3. Qed.
  Lemma wand_unfold w (P Q : Pred w) :
    ∀ ι, interface.bi_wand P Q ι ↔ (P ι → Q ι).
  Proof. crushPredEntails3. Qed.
  Lemma intuitionistically_unfold w (P : Pred w) :
    ∀ ι, @derived_connectives.bi_intuitionistically _ P ι <-> P ι.
  Proof. crushPredEntails3. Qed.

  Create HintDb punfold.
  #[export] Hint Rewrite bientails_unfold entails_unfold sep_unfold wand_unfold
    intuitionistically_unfold (* (@inst_subst OEnv Env _ _ _) *)
    (* (@inst_subst OExp Exp _ _ _) (@inst_subst OTy Ty _ _ _) *)
    (* (@inst_lift OEnv Env _ _ _) (@inst_lift OExp Exp _ _ _) *)
    (* (@inst_lift OTy Ty _ _ _) (@inst_thin Par _ Par.lk_thin_par) *)
    (* @inst_refl @inst_trans @inst_insert @Open.inst_pure *)
    (* @oexp.inst_var @oexp.inst_true @oexp.inst_false @oexp.inst_ifte *)
    (* @oexp.inst_absu @oexp.inst_abst @oexp.inst_app *) : punfold.

  Ltac pred_unfold :=
    repeat
      (punfold_connectives;
       try rewrite_db punfold; auto 1 with typeclass_instances;
       cbn [eqₚ inst] in *;
       (* repeat rewrite ?inst_subst, ?inst_lift, ?inst_refl, ?inst_trans, *)
       (*   ?inst_insert, ?oexp.inst_var, ?oexp.inst_true, ?oexp.inst_false, *)
       (*   ?oexp.inst_absu, ?oexp.inst_abst, ?oexp.inst_app, ?oexp.inst_ifte in *; *)
       try
         match goal with
         | |- forall ι : Valuation _, _ =>
             let ι := fresh "ι" in
             intro ι; pred_unfold;
             first [clear ι | revert ι]
         | |- @interface.bi_emp_valid (@bi_pred _) _ => constructor; intros ι _; cbn
         | |- @interface.bi_entails (@bi_pred _) _ _ => constructor; intros ι; cbn
         (* | H: context[@inst ?AT ?A ?I ?w ?x ?ι] |- _ => *)
         (*     is_var x; generalize (@inst AT A I w x ι); *)
         (*     clear x; intro x; subst *)
         | |- context[@inst ?AT ?A ?I ?w ?x ?ι] =>
             is_var x; generalize (@inst AT A I w x ι);
             clear x; intro x; subst
         end).

  Section Lemmas.

    Import iris.bi.interface iris.bi.derived_laws.bi.
    Create HintDb obligation.
    (* #[local] Hint Rewrite @inst_refl @inst_trans : obligation. *)

    #[local] Ltac obligation :=
      cbv [Proper flip respectful pointwise_relation forall_relation];
      repeat (autorewrite with obligation in *; cbn in *; intros; subst; pred_unfold);
      repeat
        (match goal with
         | H: _ ⊢ₚ _ |- _ => destruct H as [H]
         | H: _ ⊣⊢ₚ _ |- _ => destruct H as [H]
         | H: forall (H : ?A), _, a : ?A |- _ =>
           specialize (H a); autorewrite with obligation in H; cbn in H
         | |- (forall _ : ?A, _) <-> (forall _ : ?A, _) =>
             apply all_iff_morphism; intro; autorewrite with obligation; cbn
         | |- (exists _ : ?A, _) <-> (exists _ : ?A, _) =>
             apply ex_iff_morphism; intro; autorewrite with obligation; cbn
         (* | |- _ ⊣⊢ₚ _ => constructor; cbn; intros *)
         (* | |- _ ⊢ₚ _ => constructor; cbn; intros *)
         end);
      try easy; try (intuition; fail); try (intuition congruence; fail).
    #[local] Obligation Tactic := obligation.

    #[local] Hint Rewrite <- @tactics.forall_and_distr : obligation.

    (* #[export] Instance proper_subst_bientails {Θ w} : *)
    (*   Proper ((⊣⊢ₚ) ==> forall_relation (fun _ => eq ==> (⊣⊢ₚ))) *)
    (*   (@subst Pred Pred.subst_pred Θ w). *)
    (* Proof. obligation. Qed. *)

    Lemma split_bientails {w} (P Q : Pred w) : (P ⊣⊢ₚ Q) <-> (P ⊢ₚ Q) /\ (Q ⊢ₚ P).
    Proof. crushPredEntails3. Qed.
    Lemma impl_and_adjoint {w} (P Q R : Pred w) : (P /\ₚ Q ⊢ₚ R) <-> (P ⊢ₚ Q ->ₚ R).
    Proof. crushPredEntails3. Qed.
    Lemma and_true_l {w} (P : Pred w) : ⊤ₚ /\ₚ P ⊣⊢ₚ P.
    Proof. crushPredEntails3. Qed.
    Lemma and_true_r {w} (P : Pred w) : P /\ₚ ⊤ₚ ⊣⊢ₚ P.
    Proof. crushPredEntails3. Qed.
    Lemma and_false_l {w} (P : Pred w) : ⊥ₚ /\ₚ P ⊣⊢ₚ ⊥ₚ.
    Proof. crushPredEntails3. Qed.
    Lemma and_false_r {w} (P : Pred w) : P /\ₚ ⊥ₚ ⊣⊢ₚ ⊥ₚ.
    Proof. crushPredEntails3. Qed.
    Lemma impl_true_l {w} (P : Pred w) : ⊤ₚ ->ₚ P ⊣⊢ₚ P.
    Proof. crushPredEntails3. Qed.
    Lemma impl_true_r {w} (P : Pred w) : P ->ₚ ⊤ₚ ⊣⊢ₚ ⊤ₚ.
    Proof. crushPredEntails3. Qed.
    Lemma impl_false_l {w} (P : Pred w) : ⊥ₚ ->ₚ P ⊣⊢ₚ ⊤ₚ.
    Proof. crushPredEntails3. Qed.
    (* Lemma false_l {w} (P : Pred w) : ⊥ₚ ⊢ₚ P. *)
    (* Proof. crushPredEntails3. Qed. *)
    (* Lemma true_r {w} (P : Pred w) : P ⊢ₚ ⊤ₚ. *)
    (* Proof. crushPredEntails3. Qed. *)
    (* Lemma impl_forget {w} (P Q R : Pred w) : P ⊢ₚ R -> P ⊢ₚ (Q ->ₚ R). *)
    (* Proof. crushPredEntails3. Qed. *)
    Lemma impl_and [w] (P Q R : Pred w) : ((P /\ₚ Q) ->ₚ R) ⊣⊢ₚ (P ->ₚ Q ->ₚ R).
    Proof. crushPredEntails3. Qed.

    Lemma forall_l {I : Type} {w} (P : I -> Pred w) Q :
      (exists x : I, P x ⊢ₚ Q) -> (∀ x : I, P x)%I ⊢ₚ Q.
    Proof. crushPredEntails3. Qed.
    Lemma forall_r {I : Type} {w} P (Q : I -> Pred w) :
      (P ⊢ₚ (∀ₚ x : I, Q x)) <-> (forall x : I, P ⊢ₚ Q x).
    Proof. crushPredEntails3. Qed.

    Lemma exists_l {I : Type} {w} (P : I -> Pred w) (Q : Pred w) :
      (forall x : I, P x ⊢ₚ Q) -> (∃ₚ x : I, P x) ⊢ₚ Q.
    Proof. crushPredEntails3. Qed.
    Lemma exists_r {I : Type} {w} P (Q : I -> Pred w) :
      (exists x : I, P ⊢ₚ Q x) -> P ⊢ₚ (∃ₚ x : I, Q x).
    Proof. crushPredEntails3. Qed.
    #[global] Arguments exists_r {I w P Q} _.

    Lemma wand_is_impl [w] (P Q : Pred w) : (P -∗ Q)%I ⊣⊢ₚ (P ->ₚ Q).
    Proof. crushPredEntails3. Qed.

    Lemma sep_is_and [w] (P Q : Pred w) : (P ∗ Q)%I ⊣⊢ₚ (P ∧ Q)%I.
    Proof. crushPredEntails3. Qed.

    Lemma pApply {w} {P Q R : Pred w} : P ⊢ₚ Q -> Q ⊢ₚ R -> P ⊢ₚ R.
    Proof. now transitivity Q. Qed.

    Lemma pApply_r {w} {P Q R : Pred w} : Q ⊢ₚ R -> P ⊢ₚ Q -> P ⊢ₚ R.
    Proof. now transitivity Q. Qed.

    Lemma elim_debugPred {B : LCtx → Type} {w : World} {b : B w} {P : Pred w} :
      DebugPred B b P ⊢ P.
    Proof.
      crushPredEntails3.
      now destruct H0.
    Qed.

    Section Eq.

      Context {T A} {instTA : Inst T A}.

      Lemma eqₚ_intro {w : World} (t : T w) : ⊢ (t =ₚ t)%P.
      Proof. crushPredEntails3. Qed.

      Lemma eqₚ_refl {w : World} (t : T w) : t =ₚ t ⊣⊢ₚ ⊤ₚ.
      Proof. crushPredEntails3. Qed.

      Lemma eqₚ_sym {w : World} (s t : T w) : s =ₚ t ⊣⊢ₚ t =ₚ s.
      Proof. crushPredEntails3. Qed.

      Lemma eqₚ_trans {w : World} (s t u : T w) : s =ₚ t /\ₚ t =ₚ u ⊢ₚ s =ₚ u.
      Proof. crushPredEntails3. now transitivity (inst t ι). Qed.

    End Eq.
    #[global] Arguments eqₚ_trans {T A _ w} s t u.

  End Lemmas.

  Section SubstMod.
    Import ModalNotations.
    Import ctx.notations.
    Import classes.

    Lemma acc_pathcond {w1 w2} (ω : w2 ⊒ w1) :
      forall ι,  instprop (wco w1) ι -> instprop (wco w2) (inst (sub_acc ω) ι).
    Proof.
      intros.
      rewrite <-instprop_subst.
      now apply (ent_acc_sub ω ι H).
    Qed.

    Import iris.bi.interface.

    (* #[export] Instance knowing_params : *)
    (*   Params (@knowing) 3. Qed. *)

    #[export] Instance knowing_proper {w1 w2 : World} {ω : w1 ⊒ w2} :
      Proper (entails ==> entails) (knowing ω).
    Proof.
      unfold knowing.
      crushPredEntails3.
    Qed.

    #[export] Instance knowing_proper_bientails {w1 w2 : World} {ω : w1 ⊒ w2} :
      Proper (bientails ==> bientails) (knowing ω).
    Proof.
      unfold knowing.
      crushPredEntails3.
    Qed.


    Lemma knowing_exists {w1 w2 : World} {ω : w1 ⊒ w2} {A} (P : A -> Pred w2) :
      (∃ v, knowing ω (P v)) ⊣⊢ knowing ω (∃ v, P v).
    Proof.
      unfold knowing.
      crushPredEntails3.
    Qed.

    Lemma knowing_sepₚ {w1 w2 : World} {ω : w1 ⊒ w2} (P1 P2 : Pred w2) :
      (knowing ω (P1 ∗ P2)) ⊢ knowing ω P1 ∗ knowing ω P2.
    Proof.
      unfold knowing.
      crushPredEntails3.
    Qed.

    Lemma assuming_sepₚ {w1 w2 : World} {ω : w1 ⊒ w2} (P1 P2 : Pred w2) :
      (assuming ω (P1 ∗ P2)) ⊣⊢ assuming ω P1 ∗ assuming ω P2.
    Proof.
      unfold assuming.
      crushPredEntails3.
    Qed.

    Lemma assuming_True {w1 w2 : World} {ω : w1 ⊒ w2}  :
      assuming ω True ⊣⊢ True.
    Proof.
      unfold assuming.
      crushPredEntails3.
    Qed.

    Lemma assuming_forall {w1 w2 : World} {ω : w1 ⊒ w2} {A} {P : A -> Pred w2} :
      (∀ v : A, assuming ω (P v)) ⊣⊢ assuming ω (∀ v : A, P v).
    Proof.
      unfold assuming.
      crushPredEntails3.
    Qed.

    #[export] Instance assuming_proper {w1 w2 : World} {ω : w1 ⊒ w2} :
      Proper (entails ==> entails) (assuming ω).
    Proof.
      unfold assuming.
      crushPredEntails3.
    Qed.

    #[export] Instance assuming_proper_bientails {w1 w2 : World} {ω : w1 ⊒ w2} :
      Proper (bientails ==> bientails) (assuming ω).
    Proof.
      unfold assuming.
      crushPredEntails3.
    Qed.
    
    #[export] Instance forgetting_proper {w1 w2 : World} {ω : w1 ⊒ w2} :
      Proper (entails ==> entails) (forgetting ω).
    Proof.
      unfold forgetting.
      crushPredEntails3.
      apply (fromEntails H); last done.
      now apply acc_pathcond.
    Qed.

    #[export] Instance forgetting_proper_bientails {w1 w2 : World} {ω : w1 ⊒ w2} :
      Proper (equiv ==> equiv) (forgetting ω).
    Proof.
      unfold forgetting.
      crushPredEntails3;
        (apply (fromBientails H); last done;
         now apply acc_pathcond).
    Qed.
    
    Lemma forgetting_forall {w1 w2 : World} {ω : w1 ⊒ w2} {A} {P : A -> Pred w1} :
      (∀ v : A, forgetting ω (P v)) ⊣⊢ forgetting ω (∀ v : A, P v).
    Proof.
      unfold forgetting.
      crushPredEntails3.
    Qed.

    Lemma forgetting_wand {w1 w2 : World} {ω : w1 ⊒ w2} {P1 P2 : Pred w1} :
      (forgetting ω P1 -∗ forgetting ω P2) ⊣⊢ forgetting ω (P1 -∗ P2).
    Proof.
      unfold forgetting.
      crushPredEntails3.
    Qed.

    Lemma forgetting_wand_iff {w1 w2 : World} {ω : w1 ⊒ w2} {P1 P2 : Pred w1} :
      (forgetting ω P1 ∗-∗ forgetting ω P2) ⊣⊢ forgetting ω (P1 ∗-∗ P2).
    Proof.
      unfold forgetting, bi_wand_iff.
      crushPredEntails3.
    Qed.


    Lemma knowing_assuming {w1 w2 : World} (ω : w2 ⊒ w1) {P Q} :
      knowing ω P ∗ assuming ω Q ⊢ knowing ω (P ∗ Q).
    Proof.
      unfold knowing, assuming.
      crushPredEntails3.
    Qed.

    Lemma knowing_absorb_forgetting {w1 w2 : World} (ω : w2 ⊒ w1) {P Q} :
      knowing ω P ∗ Q ⊣⊢ knowing ω (P ∗ forgetting ω Q).
    Proof.
      unfold knowing, forgetting.
      crushPredEntails3; now subst.
    Qed.

    Import iris.proofmode.modalities.
    Import iris.proofmode.classes.
    Import iris.proofmode.proofmode.

    Lemma knowing_pure {w1 w2 : World} (ω : w2 ⊒ w1) {P} :
      knowing ω (bi_pure P) ⊢ bi_pure P.
    Proof.
      unfold knowing.
      crushPredEntails3.
    Qed.

    Lemma knowing_pure2 {w1 w2 : World} (ω : w2 ⊒ w1) {P} {Q : Prop} :
      (P ⊢ ⌜ Q ⌝)%I -> (knowing ω P ⊢ ⌜ Q ⌝)%I.
    Proof.
      iIntros (HPQ) "HP".
      rewrite -knowing_pure.
      now iApply (knowing_proper with "HP").
    Qed.

    Lemma knowing_forall {w1 w2 : World} {ω : w1 ⊒ w2} {A} {P : A -> Pred w2} :
      knowing ω (∀ v : A, P v) ⊢ (∀ v : A, knowing ω (P v)).
    Proof.
      unfold knowing.
      crushPredEntails3.
    Qed.

    Lemma forgetting_assuming_adjoint {w1 w2 : World} {ω : Acc w1 w2} {P Q} :
      (forgetting ω P ⊢ Q) <-> (P ⊢ assuming ω Q).
    Proof.
      rewrite /forgetting /assuming.
      split; crushPredEntails3.
      - subst; now apply H4.
      - apply (fromEntails H) with (inst (sub_acc ω) ι);
          auto using acc_pathcond.
    Qed.

    Lemma knowing_forgetting_adjoint {w1 w2 : World} {ω : Acc w1 w2} {P Q} :
      (knowing ω P ⊢ Q) <-> (P ⊢ forgetting ω Q).
    Proof.
      rewrite /forgetting /assuming /knowing.
      split; crushPredEntails3.
      - apply (fromEntails H); auto using acc_pathcond.
        now exists ι.
      - now subst.
    Qed.

    Lemma forgetting_pure {w1 w2 : World} (ω : w2 ⊒ w1) {P} :
      forgetting ω (bi_pure P) ⊣⊢ bi_pure P.
    Proof.
      unfold forgetting.
      crushPredEntails3.
    Qed.

    Lemma forgetting_emp {w1 w2 : World} (ω : w2 ⊒ w1) :
      forgetting ω emp ⊣⊢ emp.
    Proof.
      unfold forgetting.
      crushPredEntails3.
    Qed.

    Lemma forgetting_sep {w1 w2 : World} (ω : w2 ⊒ w1) {P Q}:
      forgetting ω (P ∗ Q) ⊣⊢ forgetting ω P ∗ forgetting ω Q.
    Proof.
      unfold forgetting.
      crushPredEntails3.
    Qed.

    Lemma forgetting_or {w1 w2 : World} {ω : w1 ⊒ w2} {P1 P2 : Pred w1} :
      (forgetting ω P1 ∨ forgetting ω P2) ⊣⊢ forgetting ω (P1 ∨ P2).
    Proof.
      unfold forgetting.
      crushPredEntails3.
    Qed.

    Lemma assuming_pure {w1 w2 : World} (ω : w2 ⊒ w1) {P} :
      bi_pure P ⊢ assuming ω (bi_pure P).
    Proof.
      unfold assuming.
      crushPredEntails3.
    Qed.

    Lemma forgetting_unconditionally {w1 w2 : World} {ω : w2 ⊒ w1} (P : (□ Pred) w2) :
      forgetting ω (unconditionally P) ⊢ unconditionally (four P ω).
    Proof.
      unfold forgetting, unconditionally, assuming.
      crushPredEntails3.
      eapply H0; eauto using acc_pathcond.
      now rewrite <-H1, <-inst_subst, <-sub_acc_trans.
    Qed.

    Lemma forgetting_unconditionally_drastic {w1 w2 : World} {ω : w1 ⊒ w2} {P} :
      forgetting ω (unconditionally P) ⊢ P _ ω.
    Proof.
      unfold forgetting, unconditionally, assuming.
      constructor.
      intros.
      now apply (H0 w2 ω ι).
    Qed.

    Lemma unconditionally_T {w} (P : (□ Pred) w) :
      unconditionally P ⊢ T P.
    Proof.
      unfold T, unconditionally, assuming.
      crushPredEntails3.
      eapply H0; try assumption.
      eapply inst_sub_id.
    Qed.

    Lemma eval_ex `{Inst AT A} {w : World} (t : AT w) :
      ⊢ ∃ v, repₚ v (w := w) t.
    Proof. crushPredEntails3. now eexists. Qed.

    Lemma eval_prop `{InstPred AT} {w : World} (t : AT w) :
      ⊢ ∃ P, proprepₚ P (w := w) t.
    Proof. crushPredEntails3. now exists (instpred t ι). Qed.

    Lemma forgetting_valuation_repₚ {w : World} (ι : Valuation w) {T : LCtx -> Type} `{Inst T A} ( t : T w) :
      ⊢ forgetting (acc_wlctx_valuation ι) (repₚ (inst t ι) t).
    Proof.
      unfold forgetting.
      crushPredEntails3.
      now rewrite inst_lift.
    Qed.

    Lemma lift_repₚ `{InstLift AT A} (v : A) {w : World} :
      ⊢ repₚ v (lift v : AT w).
    Proof.
      crushPredEntails3.
    Qed.

    Lemma repₚ_triv {T : LCtx -> Type} `{Inst T A} {a : A} {w : World} {vt : T w}:
      (∀ ι : Valuation w, inst vt ι = a) ->
      ⊢ repₚ a vt.
    Proof.
      crushPredEntails3.
    Qed.

    Lemma repₚ_eqₚ {T : LCtx -> Type} `{Inst T A} {a : A} {w : World} {vt1 vt2 : T w}:
      repₚ a vt1 ∗ eqₚ vt1 vt2 ⊢ repₚ a vt2.
    Proof.
      crushPredEntails3. now rewrite <-H1.
    Qed.


    Lemma eqₚ_triv {T : LCtx -> Type} `{Inst T A} {w : World} {vt1 vt2 : T w}:
      (∀ ι : Valuation w, inst vt1 ι = inst vt2 ι) ->
      ⊢ eqₚ vt1 vt2.
    Proof.
      crushPredEntails3.
    Qed.


    Lemma repₚ_antisym_left {T : LCtx -> Type} `{Inst T A} {a1 a2 : A} {w : World} {sa : T w} :
      ⊢ repₚ a1 sa -∗ repₚ a2 sa -∗ ⌜ a1 = a2 ⌝.
    Proof.
      crushPredEntails3. now subst.
    Qed.

    Lemma proprepₚ_triv {T : LCtx -> Type} `{InstPred T} {a : Prop} {w : World} {vt : T w}:
      (∀ ι : Valuation w, instprop vt ι <-> a) ->
      ⊢ proprepₚ a vt.
    Proof.
      unfold proprepₚ.
      crushPredEntails3.
      - now rewrite instpred_prop in H3.
      - now rewrite instpred_prop.
    Qed.

    Lemma repₚ_cong {T1 : LCtx -> Type} `{Inst T1 A1}
      {T2 : LCtx -> Type} `{Inst T2 A2}
      (f : A1 -> A2) {w : World} (fs : T1 w -> T2 w)
      {v1 : A1} {vs1 : T1 w} :
      (∀ (ι : Valuation w) vs1, inst (fs vs1) ι = f (inst vs1 ι)) ->
      repₚ v1 vs1 ⊢ repₚ (f v1) (fs vs1).
    Proof.
      crushPredEntails3.
      now rewrite H1 H3.
    Qed.

    Lemma repₚ_cong₂ {T1 : LCtx -> Type} `{Inst T1 A1}
      {T2 : LCtx -> Type} `{Inst T2 A2}
      {T3 : LCtx -> Type} `{Inst T3 A3}
      (f : A1 -> A2 -> A3) {w : World} (fs : T1 w -> T2 w -> T3 w)
      {v1 : A1} {vs1 : T1 w} {v2 : A2} {vs2 : T2 w} :
      (∀ (ι : Valuation w) vs1 vs2, inst (fs vs1 vs2) ι = f (inst vs1 ι) (inst vs2 ι)) ->
      repₚ v1 vs1 ∗ repₚ v2 vs2 ⊢ repₚ (f v1 v2) (fs vs1 vs2).
    Proof.
      crushPredEntails3.
      now rewrite H2 H4 H5.
    Qed.

    Lemma eqₚ_term_prod {σ1 σ2} {w : World} {sva1 svb1 : STerm σ1 w} {sva2 svb2 : STerm σ2 w} :
      eqₚ (T := STerm (ty.prod σ1 σ2)) (term_binop bop.pair sva1 sva2) (term_binop bop.pair svb1 svb2) ⊣⊢ eqₚ sva1 svb1 ∗ eqₚ sva2 svb2.
    Proof. crushPredEntails3; try (now inversion H0); now cbn; f_equal. Qed.


    Lemma repₚ_term_prod {σ1 σ2} {v1 : Val σ1} {v2 : Val σ2} {w : World} {sv1 : STerm σ1 w} {sv2 : STerm σ2 w} :
      repₚ (T := STerm (ty.prod σ1 σ2)) (v1,v2) (term_binop bop.pair sv1 sv2) ⊣⊢ repₚ v1 sv1 ∗ repₚ v2 sv2.
    Proof.
      unfold repₚ.
      crushPredEntails3.
      - now inversion H0.
      - now inversion H0.
      - now f_equal.
    Qed.

    Lemma rep_term_val {w : World} {σ : Ty} {v : Val σ} :
      repₚ (w := w) v (term_val σ v) ⊣⊢ True.
    Proof. unfold repₚ. crushPredEntails3. Qed.

    Lemma eq_term_val {w : World} {σ : Ty} {v : Val σ} :
      eqₚ (w := w) (term_val σ v) (term_val σ v) ⊣⊢ True.
    Proof. unfold eqₚ. crushPredEntails3. Qed.

    Lemma rep_term_cons {w : World} {σ : Ty} {t : STerm σ w} {ts : STerm (ty.list σ) w} {v vs} :
      repₚ v t ∗ repₚ (T := STerm (ty.list σ)) vs ts ⊣⊢ repₚ (T := STerm (ty.list σ)) (v :: vs) (term_binop bop.cons t ts).
    Proof. unfold repₚ. crushPredEntails3; try (now subst); now inversion H0. Qed.

    Lemma eq_term_cons {w : World} {σ : Ty} {t1 t2 : STerm σ w} {ts1 ts2 : STerm (ty.list σ) w} :
      eqₚ (T := STerm (ty.list σ)) (term_binop bop.cons t1 ts1) (term_binop bop.cons t2 ts2) ⊣⊢
        eqₚ t1 t2 ∗ eqₚ (T := STerm (ty.list σ)) ts1 ts2.
    Proof. crushPredEntails3; try (now inversion H0); now cbn; f_equal. Qed.

    Set Equations With UIP.
    Lemma repₚ_unionv_fold {w : World} {U} {K : unionk U} {t : STerm (unionk_ty U K) w} {v : Val (unionk_ty U K)} :
      repₚ (T := STerm _) (unionv_fold U (existT K v)) (term_union U K t) ⊣⊢ repₚ (T := STerm _) v t.
    Proof.
      unfold repₚ; crushPredEntails3; try (now subst).
      apply (f_equal (unionv_unfold U)) in H0.
      rewrite !unionv_unfold_fold in H0.
      now dependent elimination H0.
    Qed.

    Lemma eqₚ_unionv_fold {w : World} {U} {K : unionk U} {t1 t2 : STerm (unionk_ty U K) w} :
      eqₚ (T := STerm _) (term_union U K t1) (term_union U K t2) ⊣⊢ eqₚ (T := STerm _) t1 t2.
    Proof.
      unfold eqₚ; crushPredEntails3.
      - apply (f_equal (unionv_unfold U)) in H0.
        rewrite !unionv_unfold_fold in H0.
        (* avoid axiom K *)
        refine (Eqdep_dec.inj_pair2_eq_dec _ _ _ _ _ _ H0).
        apply unionk_eqdec.
      - now do 2 f_equal.
    Qed.

    Lemma repₚ_unionv_neq {w : World} {U} {K1 K2 : unionk U} {t : STerm (unionk_ty U K1) w} {v : Val (unionk_ty U K2)} : 
      K1 ≠ K2 ->
      repₚ (T := STerm _) (unionv_fold U (existT K2 v)) (term_union U K1 t) ⊣⊢ False.
    Proof.
      intros HKneq.
      unfold repₚ; crushPredEntails3; try (now subst).
      apply (f_equal (unionv_unfold U)) in H0.
      rewrite !unionv_unfold_fold in H0.
      dependent elimination H0.
      now apply HKneq.
    Qed.

    Lemma eqₚ_term_union_neq {w : World} {U} {K1 K2 : unionk U} {t1 : STerm (unionk_ty U K1) w} {t2 : STerm (unionk_ty U K2) w} : 
      K1 ≠ K2 ->
      eqₚ (T := STerm _) (term_union U K1 t1) (term_union U K2 t2) ⊣⊢ False.
    Proof.
      intros HKneq.
      unfold repₚ; crushPredEntails3; try (now subst).
      apply HKneq.
      apply (f_equal (unionv_unfold U)) in H0.
      rewrite !unionv_unfold_fold in H0.
      apply (eq_sigT_fst H0).
    Qed.


    Lemma proprepₚ_cong {T1 : LCtx -> Type} `{InstPred T1}
      {T2 : LCtx -> Type} `{InstPred T2}
      {w : World} (fs : T1 w -> T2 w)
      {v1 : Prop} {vs1 : T1 w} :
      (forall vs1, instpred (fs vs1) ⊣⊢ instpred vs1) ->
      proprepₚ v1 vs1 ⊢ proprepₚ v1 (fs vs1).
    Proof.
      crushPredEntails3.
    Qed.

    Lemma proprepₚ_cong₂ {T1 : LCtx -> Type} `{Inst T1 A1}
      {T2 : LCtx -> Type} `{Inst T2 A2}
      {T3 : LCtx -> Type} `{InstPred T3}
      (f : A1 -> A2 -> Prop) {w : World} (fs : T1 w -> T2 w -> T3 w)
      {v1 : A1} {vs1 : T1 w} {v2 : A2} {vs2 : T2 w} :
      (∀ (ι : Valuation w) vs1 vs2, instpred (fs vs1 vs2) ι <-> f (inst vs1 ι) (inst vs2 ι)) ->
      repₚ v1 vs1 ∗ repₚ v2 vs2 ⊢ proprepₚ (f v1 v2) (fs vs1 vs2).
    Proof.
      crushPredEntails3; now subst.
    Qed.

    Lemma repₚ_elim {T : LCtx -> Type} `{Inst T A} {a b : A} {w : World} {vt : T w}:
      (∀ ι : Valuation w, inst vt ι = a) ->
      repₚ b vt ⊣⊢ ⌜ b = a ⌝.
    Proof.
      crushPredEntails3; now subst.
    Qed.

    Lemma repₚ_const {A} {v sv} {w} : repₚ (w := w) (T := Const A) sv v ⊣⊢  ⌜ v = sv ⌝.
    Proof. crushPredEntails3. Qed.

    Lemma repₚ_val {σ} {v sv} {w} : repₚ (w := w) (T := STerm σ) v (term_val _ sv) ⊣⊢  ⌜ v = sv ⌝.
    Proof. crushPredEntails3. Qed.

    Lemma repₚ_elim_repₚ {T : LCtx -> Type} `{Inst T A} {a1 : A} (a2 : A) {w : World} {vt1 : T w} (vt2 : T w):
      (∀ ι : Valuation w, inst vt1 ι = a1 -> inst vt2 ι = a2) ->
      repₚ a1 vt1 ⊢ repₚ a2 vt2.
    Proof. now crushPredEntails3. Qed.

    Lemma repₚ_inversion_term_inl {σ τ} (v : Val (ty.sum σ τ)) {w : World} (svl : STerm σ w) :
      (repₚ v (term_inl svl) : Pred w) ⊢ ∃ (vl : Val σ), ⌜ v = inl vl ⌝ ∗ repₚ vl svl.
    Proof.
      unfold repₚ.
      destruct v; crushPredEntails3; now inversion H0.
    Qed.

    Lemma repₚ_inversion_term_inr {σ τ} (v : Val (ty.sum σ τ)) {w : World} (svr : STerm τ w) :
      (repₚ v (term_inr svr) : Pred w) ⊢ ∃ vr, ⌜ v = inr vr ⌝ ∗ repₚ vr svr.
    Proof.
      unfold repₚ.
      destruct v; crushPredEntails3; now inversion H0.
    Qed.

    Lemma repₚ_inversion_term_unsigned {n} (v : Val ty.int) {w : World} (sbv : STerm (ty.bvec n) w) :
      (repₚ v (term_unsigned sbv) : Pred w)
      ⊢ ∃ bv : Val (ty.bvec n), ⌜ v = bv.unsigned bv ⌝ ∗ repₚ bv sbv.
    Proof.
      unfold repₚ. crushPredEntails3.
      now exists (inst_term sbv ι).
    Qed.

    Lemma repₚ_inversion_term_signed {n} (v : Val ty.int) {w : World} (sbv : STerm (ty.bvec n) w) :
      (repₚ v (term_signed sbv) : Pred w)
      ⊢ ∃ bv : Val (ty.bvec n), ⌜ v = bv.signed bv ⌝ ∗ repₚ bv sbv.
    Proof.
      unfold repₚ. crushPredEntails3.
      now exists (inst_term sbv ι).
    Qed.

    Lemma repₚ_inversion_record {R} {w : World} {v : recordt R} {svs : NamedEnv (λ τ : Ty, Term w τ) (recordf_ty R)} :
      repₚ (T := STerm (ty.record R)) v (term_record R svs) ⊣⊢
        ∃ (vs : NamedEnv Val (recordf_ty R)), ⌜ v = recordv_fold R vs ⌝ ∗ repₚ vs svs.
    Proof.
      unfold repₚ. crushPredEntails3.
      - exists (recordv_unfold R v).
        rewrite recordv_fold_unfold.
        crushPredEntails3.
        now rewrite <-H0, recordv_unfold_fold.
      - now subst.
    Qed.

    Lemma repₚ_inversion_union {U} (K : unionk U) {v : Val (ty.union U)}
      {w : World} {st : STerm (unionk_ty U K) w} :
      repₚ (T := STerm (ty.union U)) v (term_union U K st) ⊢
        ∃ (t : Val (unionk_ty U K)), ⌜ v = unionv_fold U (existT K t) ⌝ ∗ repₚ t st.
    Proof.
      unfold repₚ. crushPredEntails3.
      destruct (unionv_unfold U v) as [K' t] eqn:Heqv .
      rewrite <-H0 in Heqv.
      rewrite unionv_unfold_fold in Heqv.
      dependent elimination Heqv.
      exists (inst (st : STerm _ w) ι).
      now crushPredEntails3.
    Qed.

    Section WithEnvironments.
      Import ctx.notations.
      Import env.notations.
      
      Lemma repₚ_invert_snoc
        (T : Set) {S : LCtx → T → Set} {A : T → Set} {Σ : Ctx T}
        {w : World} {b : T} {E1 : Env A Σ} {Es1 : Env (S w) Σ} {v : A b} {db : S w b} 
        (instSA : ∀ τ : T, Inst (λ Σ : LCtx, S Σ τ) (A τ)) :
        @repₚ _ _ inst_env (env.snoc E1 b v) w (env.snoc Es1 b db) ⊢  repₚ E1 Es1 ∗ repₚ v db.
      Proof.
        crushPredEntails3;
        now apply env.inversion_eq_snoc in H0.
      Qed.
    End WithEnvironments.
        
    Lemma forgetting_repₚ `{InstSubst AT, @SubstLaws AT _} {v w1 w2}  {ω : w1 ⊒ w2} (t : AT w1) :
      (repₚ v (persist t ω) ⊣⊢ forgetting ω (repₚ v t))%I.
    Proof.
      rewrite persist_subst.
      unfold forgetting, repₚ.
      constructor. split; rewrite inst_subst; auto using acc_pathcond.
    Qed.

    Lemma instpred_persist {T : LCtx -> Type} `{InstPredSubst T} {_ : SubstLaws T} {w1 w2} {ω : w1 ⊒ w2} (t : T w1) :
      instpred (persist t ω) ⊣⊢ forgetting ω (instpred t).
    Proof.
      now rewrite instpred_subst.
    Qed.

    Lemma forgetting_proprepₚ `{InstPredSubst AT, @SubstLaws AT _} {v w1 w2} {ω : w1 ⊒ w2}  (t : AT w1) :
      (proprepₚ v (persist t ω) ⊣⊢ forgetting ω (proprepₚ v t))%I.
    Proof.
      unfold proprepₚ.
      now rewrite instpred_persist -forgetting_wand_iff forgetting_pure.
    Qed.

    Lemma assuming_id {w} {P : Pred w} : assuming acc_refl P ⊣⊢ P.
    Proof.
      rewrite /assuming.
      crushPredEntails3.
      - apply H0; [apply inst_sub_id|done].
      - rewrite inst_sub_id in H1; now subst.
    Qed.

    Lemma knowing_trans {w1 w2 w3 : World} {ω12 : w1 ⊒ w2} `{ω23 : w2 ⊒ w3} {P : Pred w3} :
      knowing (acc_trans ω12 ω23) P ⊣⊢ knowing ω12 (knowing ω23 P).
    Proof.
      rewrite /knowing.
      crushPredEntails3.
      - rewrite sub_acc_trans inst_subst in H0.
        exists (inst (sub_acc ω23) x).
        repeat split; try done.
        { now apply acc_pathcond. }
        now exists x.
      - rewrite sub_acc_trans inst_subst.
        now subst.
    Qed.

    Lemma assuming_trans {w1 w2 w3 : World} {sub12 : w1 ⊒ w2} `{ω23 : w2 ⊒ w3} {P : Pred w3} :
      assuming (acc_trans sub12 ω23) P ⊣⊢ assuming sub12 (assuming ω23 P).
    Proof.
      rewrite /assuming.
      crushPredEntails3.
      - rewrite sub_acc_trans inst_subst in H0.
        apply H0; last done.
        now rewrite H3.
      - rewrite sub_acc_trans inst_subst in H1.
        apply (H0 (inst (sub_acc ω23) ιpast)); try done.
        now apply acc_pathcond.
    Qed.

    Lemma forgetting_trans {w1 w2 w3 : World} {ω12 : w1 ⊒ w2} {ω23 : w2 ⊒ w3} {P : Pred w1} :
      forgetting (acc_trans ω12 ω23) P ⊣⊢ forgetting ω23 (forgetting ω12 P).
    Proof.
      rewrite /forgetting.
      crushPredEntails3.
      - now rewrite sub_acc_trans inst_subst in H0.
      - now rewrite sub_acc_trans inst_subst.
    Qed.

    Lemma forgetting_id {w} {P : Pred w} : forgetting acc_refl P ⊣⊢ P.
    Proof.
      rewrite /forgetting.
      crushPredEntails3.
      - now rewrite <-inst_sub_id.
      - now rewrite inst_sub_id.
    Qed.

    Lemma forgetting_assuming {w1 w2 : World} {ω : w1 ⊒ w2} {P : Pred w2} :
      forgetting ω (assuming ω P) ⊢ P.
    Proof.
      now apply forgetting_assuming_adjoint.
    Qed.

    Lemma assuming_forgetting {w1 w2 : World} {ω : w1 ⊒ w2} {P : Pred w1} :
      P ⊢ assuming ω (forgetting ω P).
    Proof.
      now apply (proj1 forgetting_assuming_adjoint).
    Qed.

    Lemma knowing_forgetting {w1 w2 : World} {ω : w1 ⊒ w2} {P : Pred w1} :
      knowing ω (forgetting ω P) ⊢ P.
    Proof.
      now apply knowing_forgetting_adjoint.
    Qed.

    Lemma forgetting_knowing {w1 w2 : World} {ω : w1 ⊒ w2} {P : Pred w2} :
      P ⊢ forgetting ω (knowing ω P).
    Proof.
      now apply (proj1 knowing_forgetting_adjoint).
    Qed.

    #[export] Instance intowand_forgetting_unconditionally {p q} {w1 w2 : World} {ω : w1 ⊒ w2} {P : ((□ Pred) w1)%modal} {Q R} :
      IntoWand p q (P w2 ω) Q R -> IntoWand p q (forgetting ω (unconditionally P)) Q R | 0.
    Proof.
      unfold IntoWand; cbn.
      now rewrite forgetting_unconditionally_drastic.
    Qed.

    #[export] Instance intowand_forgetting {w1 w2 : World} {ω : w1 ⊒ w2} {P : Pred w1} {Q R}:
      IntoWand false false P Q R -> IntoWand false false (forgetting ω P) (forgetting ω Q) (forgetting ω R) | 1.
    Proof.
      iIntros (Hiw).
      unfold IntoWand; cbn.
      rewrite forgetting_wand.
      pose proof (into_wand false false P Q R) as Hwand.
      cbn in Hwand.
      now rewrite Hwand.
    Qed.

    #[export] Instance intowand_unconditionally {p q} {w} {P : ((□ Pred) w)%modal} {Q R}:
      IntoWand p q (P w acc_refl) Q R -> IntoWand p q (unconditionally P) Q R.
    Proof.
      unfold IntoWand; cbn.
      now rewrite unconditionally_T.
    Qed.

    #[export] Instance intoforall_forgetting {w1 w2 : World} {ω : w1 ⊒ w2} {P : Pred w1} {A} {Φ}:
      IntoForall (A := A) P Φ -> IntoForall (forgetting ω P) (fun a => forgetting ω (Φ a)).
    Proof.
      iIntros (Hiw).
      unfold IntoForall; cbn.
      rewrite forgetting_forall.
      now rewrite (into_forall P).
    Qed.

    #[export] Instance intoforall_assuming {w1 w2 : World} {ω : w1 ⊒ w2} {P : Pred w2} {A} {Φ}:
      IntoForall (A := A) P Φ -> IntoForall (assuming ω P) (fun a => assuming ω (Φ a)).
    Proof.
      iIntros (Hiw).
      unfold IntoForall; cbn.
      rewrite assuming_forall.
      now rewrite (into_forall P).
    Qed.

    #[export] Instance intoforall_unconditionally {w} {P : (□ Pred) w} {A} {Φ}:
      IntoForall (A := A) (P w acc_refl) Φ -> IntoForall (unconditionally P) Φ.
    Proof.
      unfold IntoForall; cbn.
      now rewrite unconditionally_T.
    Qed.

    Class IntoAssuming {w1 w2 : World} (ω : w1 ⊒ w2) (P : Pred w1) (Q : Pred w2) :=
      into_assuming : P ⊢ assuming ω Q.

    #[export] Instance into_assuming_default {w1 w2 : World} {ω : w1 ⊒ w2} (P : Pred w1) :
      IntoAssuming ω P (forgetting ω P) | 10.
    Proof. unfold IntoAssuming. now apply assuming_forgetting. Qed.

    #[export] Instance into_assuming_assuming {w1 w2 : World} {ω : w1 ⊒ w2} (P : Pred w2) :
      IntoAssuming ω (assuming ω P) P | 0.
    Proof. now unfold IntoAssuming. Qed.

    #[export] Instance into_assuming_forgetting {w1 w2 w3 : World} {ω12 : w1 ⊒ w2} {ω23 : w2 ⊒ w3 }(P : Pred w1) :
      IntoAssuming ω23 (forgetting ω12 P) (forgetting (acc_trans ω12 ω23) P) | 0.
    Proof. unfold IntoAssuming. rewrite forgetting_trans. now apply assuming_forgetting. Qed.

    Lemma modality_mixin_assuming {w1 w2 : World} {ω : w1 ⊒ w2} : modality_mixin (assuming ω) (MIEnvTransform (IntoAssuming ω)) (MIEnvTransform (IntoAssuming ω)).
    Proof.
      constructor; cbn; try done; rewrite /assuming; crushPredEntails3.
      destruct into_assuming as [HPQ].
      crushPredEntails3.
    Qed.

    Definition modality_assuming {w1 w2 : World} (ω : w1 ⊒ w2) : modality (Pred w2) (Pred w1) :=
      Modality (assuming ω) modality_mixin_assuming.

    #[export] Instance fromModal_assuming {w1 w2 : World} {ω : w1 ⊒ w2} {P} :
      FromModal True (modality_assuming ω) tt (assuming ω P) P.
    Proof.
      constructor; crushPredEntails3.
    Qed.

    Class RemoveSub {w1 w2 w3 : World} (ω : w2 ⊒ w3) (ω2 : w1 ⊒ w3) (ωr : w1 ⊒ w2) :=
      removeSub : forall P, forgetting (acc_trans ωr ω) P ⊣⊢ forgetting ω2 P.

    #[export] Instance removesub_base {w1 w2 w3 : World} (ω : w2 ⊒ w3) (ωr : w1 ⊒ w2) :
      RemoveSub ω (acc_trans ωr ω) ωr | 0.
    Proof. now unfold RemoveSub. Qed.

    #[export] Instance removesub_step {w1 w2 w3 w0 : World} (ω : w2 ⊒ w3) (ω2 : w1 ⊒ w3) (ωr : w1 ⊒ w2) (ωf : w0 ⊒ w1):
      RemoveSub ω ω2 ωr -> RemoveSub ω (acc_trans ωf ω2) (acc_trans ωf ωr) | 1.
    Proof. unfold RemoveSub. intros H P. iSplit; iIntros "H";
             specialize (H (forgetting ωf P));
             rewrite !forgetting_trans in H;
             now rewrite !forgetting_trans H.
    Qed.

    #[export] Instance removesub_step' {w1 w2 w3 w4 : World} (ω1 : w2 ⊒ w3) (ω2 : w3 ⊒ w4) (ω : w1 ⊒ w4) (ωr1 : w1 ⊒ w3) (ωr2 : w1 ⊒ w2) :
      RemoveSub ω2 ω ωr1 -> RemoveSub ω1 ωr1 ωr2 -> RemoveSub (acc_trans ω1 ω2) ω ωr2 | 0.
    Proof. unfold RemoveSub. intros H1 H2 P.
           now rewrite <-(H1 P), !forgetting_trans, <-(H2 P), !forgetting_trans.
    Qed.

    Class IntoForgetting {w1 w2 : World} (ω : w1 ⊒ w2) (P : Pred w2) (Q : Pred w1) :=
      into_forgetting : P ⊢ forgetting ω Q.

    #[export] Instance into_forgetting_default {w1 w2 : World} {ω : w1 ⊒ w2} (P : Pred w2) :
      IntoForgetting ω P (knowing ω P) | 10.
    Proof. unfold IntoForgetting. now apply forgetting_knowing. Qed.

    #[export] Instance into_forgetting_knowing {w1 w2 w3 : World} {ω12 : w1 ⊒ w2} {ω23 : w2 ⊒ w3} (P : Pred w3) :
      IntoForgetting ω12 (knowing ω23 P) (knowing (acc_trans ω12 ω23) P) | 0.
    Proof. unfold IntoForgetting. rewrite knowing_trans. now apply forgetting_knowing. Qed.

    #[export] Instance into_forgetting_forgetting {w1 w2 : World} {ω : w1 ⊒ w2} (P : Pred w1) :
      IntoForgetting ω (forgetting ω P) P | 0.
    Proof. now unfold IntoForgetting. Qed.

    #[export] Instance into_forgetting_forgetting_trans {w1 w2 w3 : World} {ω : w1 ⊒ w3} {ω' : w2 ⊒ w3} {ωr : w1 ⊒ w2}(P : Pred w1) :
      RemoveSub ω' ω ωr ->
      IntoForgetting ω' (forgetting ω P) (forgetting ωr P) | 1.
    Proof.
      unfold RemoveSub, IntoForgetting.
      iIntros (H) "HωP".
      now rewrite <-(H P), forgetting_trans.
    Qed.

    (* TODO: define typeclass FromForgetting to preserve other forgetting assumptions *)
    Lemma modality_mixin_forgetting {w1 w2 : World} `{ω : w1 ⊒ w2} : modality_mixin (forgetting ω) (MIEnvTransform (IntoForgetting ω)) (MIEnvTransform (IntoForgetting ω)).
    Proof.
      constructor; cbn; try done; rewrite /forgetting; crushPredEntails3.
      - destruct H as [H]. apply H; done.
      - apply H; last done. now apply acc_pathcond.
    Qed.

    Definition modality_forgetting {w1 w2 : World} {ω : w1 ⊒ w2} : modality (Pred w1) (Pred w2) :=
      Modality (forgetting ω) modality_mixin_forgetting.

    #[export] Instance fromModal_forgetting {w1 w2 : World} {ω : w1 ⊒ w2} {P} :
      FromModal True (modality_forgetting (ω := ω)) tt (forgetting ω P) P.
    Proof.
      constructor; crushPredEntails3.
    Qed.


    #[export] Instance fromExist_knowing {w1 w2 : World} {A} {ω : w1 ⊒ w2} {P} {Φ : A -> Pred _}:
      FromExist P Φ -> FromExist (knowing ω P) (fun v => knowing ω (Φ v)).
    Proof.
      unfold FromExist.
      iIntros (H) "[%v H]".
      (* doesn't work for some reason *)
      (* rewrite <-H. *)
      iApply (knowing_proper _ _ H).
      iApply (knowing_proper with "H").
      iIntros "H".
      now iExists v.
    Qed.

    #[export] Instance fromExist_assuming {w1 w2 : World} {A} {ω : w1 ⊒ w2} {P} {Φ : A -> Pred _}:
      FromExist P Φ -> FromExist (assuming ω P) (fun v => assuming ω (Φ v)).
    Proof.
      unfold FromExist.
      iIntros (H) "[%v H]".
      (* doesn't work for some reason *)
      (* rewrite <-H. *)
      iModIntro.
      iApply H.
      now iExists v.
    Qed.

    Global Instance elim_modal_unconditionally {w} {P : Box Pred w} {Q : Pred w} :
      ElimModal True false false (unconditionally P) (P w acc_refl) Q Q.
    Proof.
      iIntros (_) "[#HP Hk]".
      iApply "Hk".
      iSpecialize ("HP" $! w acc_refl).
      now rewrite /ElimModal /unconditionally assuming_id.
    Qed.
    Lemma knowing_acc_pathcondition_right {w pc} {P} :
      knowing (acc_pathcondition_right w pc) P ⊣⊢ instpred pc ∗ P.
    Proof.
      unfold knowing, acc_pathcondition_right.
      crushPredEntails3.
      - rewrite instprop_cat in H1.
        rewrite inst_sub_id in H0; subst.
        now rewrite instpred_prop.
      - now rewrite inst_sub_id in H0; subst.
      - apply inst_sub_id.
      - rewrite instprop_cat.
        now rewrite instpred_prop in H0.
    Qed.

    Lemma knowing_acc_snoc_right {w b P} :
      knowing (w1 := wsnoc w b) acc_snoc_right P ⊣⊢ ∃ v, forgetting (w1 := wsnoc w b) (acc_snoc_left acc_refl b (term_val _ v)) P.
    Proof.
      unfold knowing, forgetting.
      crushPredEntails3.
      - destruct (env.view x) as [ιp v].
        exists v.
        change (env.snoc _ _ _) with (env.snoc (inst (sub_id w) ι) b v).
        now rewrite inst_sub_id -H0 inst_sub_wk1.
      - exists (env.snoc ι b x).
        change (env.snoc _ _ _) with (env.snoc (inst (sub_id w) ι) b x) in H0.
        rewrite inst_sub_id in H0.
        repeat split; eauto using inst_sub_wk1.
        now rewrite instprop_subst inst_sub_wk1.
    Qed.

    Lemma forgetting_acc_snoc_left_repₚ {w1 w2 : World} {b} {ω : w1 ⊒ w2} {v} :
      ⊢ forgetting (w1 := wsnoc w1 b) (acc_snoc_left ω b (term_val _ v)) (repₚ v term_var_zero).
    Proof.
      unfold forgetting.
      now crushPredEntails3.
    Qed.

    Lemma knowing_acc_snoc_right2 {w b P} :
      knowing (w1 := wsnoc w b) acc_snoc_right P ⊣⊢ ∃ v, knowing (w1 := wsnoc w b) acc_snoc_right (repₚ v term_var_zero ∗ P).
    Proof.
      unfold knowing.
      crushPredEntails3.
      destruct (env.view x) as [ι' v].
      now exists v, (env.snoc ι' b v).
    Qed.


    Lemma knowing_acc_subst_right {w : World} {x σ} `{xIn : (x∷σ ∈ w)%katamaran}
      {t : Term (w - x∷σ) σ} {P} :
      (knowing (w1 := wsubst w x t) (acc_subst_right t) P : Pred w) ⊣⊢ 
        (eqₚ (term_var_in xIn) (subst t (sub_shift xIn)) ∗
           assuming (w1 := wsubst w x t) (acc_subst_right t) P)%I.
    Proof.
      unfold knowing, assuming.
      crushPredEntails3.
      - subst; cbn.
        rewrite <-inst_lookup, <-inst_subst.
        now rewrite lookup_sub_single_eq subst_shift_single.
      - rewrite !inst_sub_single2 in H3 H0.
        apply (f_equal (fun ι => env.remove (x∷σ) ι xIn)) in H0, H3.
        rewrite !env.remove_insert in H3, H0.
        assert (ιpast = x0) by (now transitivity (env.remove (x∷σ) ι xIn)).
        now subst.
      - exists (inst (sub_shift xIn) ι).
        assert (instprop (wco w) (inst (sub_single xIn t) (inst (sub_shift xIn) ι))) as Hpc2.
        { rewrite inst_sub_single_shift; first done.
          now rewrite <-inst_subst.
        }
        assert (inst t (inst (sub_shift xIn) ι) = env.lookup ι xIn) as Hinst.
        { now rewrite <-inst_subst. }
        assert (inst (sub_single xIn t) (inst (sub_shift xIn) ι) = ι) as Hinst2.
        { now rewrite inst_sub_single_shift. }
        repeat split; try done.
        + now rewrite instprop_subst.
        + apply H1; try done.
          now rewrite instprop_subst.
    Qed.

    Lemma assuming_acc_snoc_right {w b P} :
      assuming (w1 := wsnoc w b) (acc_snoc_right) P ⊣⊢ ∀ v, forgetting (w1 := wsnoc w b) (acc_snoc_left acc_refl b (term_val _ v)) P.
    Proof.
      unfold assuming, forgetting.
      crushPredEntails3.
      - change (P (env.snoc (inst (sub_id w) ι) b a)).
        rewrite inst_sub_id.
        apply H0.
        + eapply inst_sub_wk1.
        + now rewrite instprop_subst inst_sub_wk1.
      - destruct (env.view ιpast) as [ι' v].
        rewrite inst_sub_wk1 in H1; subst.
        specialize (H0 v).
        change (env.snoc _ _ _) with (env.snoc (inst (sub_id w) ι) b v) in H0.
        rewrite inst_sub_id in H0.
        now apply H0.
    Qed.

    Lemma assuming_acc_snoc_right2 {w b P v} :
      assuming (w1 := wsnoc w b) acc_snoc_right (repₚ v term_var_zero -∗ P) ⊢ knowing acc_snoc_right P.
    Proof.
      iIntros "HP".
      rewrite knowing_acc_snoc_right.
      iExists v.
      rewrite assuming_acc_snoc_right.
      iApply "HP".
      iApply forgetting_acc_snoc_left_repₚ.
    Qed.


    Lemma forgetting_acc_pathcondition_right {w : World}
      {C : PathCondition w}
      {P : Pred (wpathcondition w C)} :
      (forgetting (w2 := wpathcondition w C) acc_refl P : Pred w) ⊣⊢ P.
    Proof.
      unfold forgetting, acc_pathcondition_right, wpathcondition; cbn.
      crushPredEntails3.
      - now rewrite inst_sub_id in H0.
      - now rewrite inst_sub_id.
    Qed.

    Lemma assuming_acc_pathcondition_right
      {w : World} {sc : PathCondition w} {P : Pred w} :
      instpred sc ∗ assuming (w2 := wpathcondition w sc) acc_refl P ⊢ P.
    Proof.
      unfold assuming.
      crushPredEntails3.
      apply H1.
      - apply inst_sub_id.
      - rewrite instpred_prop in H0.
        now apply instprop_cat.
    Qed.

    Lemma forgetting_acc_pathcondition_right_sep {w : World} {P : Pred w} {C : PathCondition w}
      {Q : Pred (wpathcondition w C)} :
      (forgetting (w1 := wpathcondition w C) acc_refl (P ∗ Q) : Pred w) ⊣⊢
        P ∗ forgetting (w2 := wpathcondition w C) acc_refl Q.
    Proof.
      unfold forgetting, acc_pathcondition_right, wpathcondition; cbn.
      crushPredEntails3.
      - now rewrite inst_sub_id in H0.
      - now rewrite inst_sub_id.
    Qed.

    (* Lemma assuming_acc_subst_right_left  {w : World} x {σ} {xIn : x∷σ ∈ w} *)
    (*   (t : Term (w - x∷σ) σ) {P} : *)
    (*   assuming (acc_subst_right x t) P ⊣⊢ *)
    (*     eqₚ (term_var xIn) (subst (sub_wk1 xIn) t) ∗ *)
    (*     forgetting (acc_subst_left x) P. *)

    Definition assuming_acc_match_right {w : World} {σ} {s : Term w σ}
      {p : Pattern (N:=LVar) σ} (pc : PatternCase p) :
      ⊢ assuming (w1 := wmatch w s p pc) (acc_match_right pc)
        (eqₚ (persist s (acc_match_right pc)) (pattern_match_term_reverse p pc (sub_wmatch_patctx pc))).
    Proof.
      unfold assuming.
      crushPredEntails3.
    Qed.

  End SubstMod.

  Module logicalrelation.
    Import ModalNotations.
    Import iris.bi.interface.
    Import iris.proofmode.classes.
    Import iris.proofmode.proofmode.
    Record Rel (AT : TYPE) (A : Type) : Type :=
      MkRel { RSat : A -> (⊢ AT -> Pred)%modal }.
    Bind Scope rel_scope with Rel.

    #[global] Arguments MkRel [AT A] &.
    #[global] Arguments RSat {_ _} !Rel _ {w} _ : rename.
    (* We use the same script ℛ as in the paper. This encodes (ι,x,y) ∈ ℛ[_,_]
       from the paper as (ℛ ι x y), i.e. the types of the relation are
       implicit. *)
    #[local] Notation "ℛ⟦ R ⟧" := (RSat R%R) (format "ℛ⟦ R ⟧").

    
    (* This instance can be used for any (first-class) symbolic data that can be
       instantiated with a valuation, i.e. symbolic terms, stores, heaps etc. *)
    Definition RInst AT A {instA : Inst AT A} : Rel AT A :=
      MkRel repₚ.
    Arguments RInst _ _ {_} : simpl never.

    Definition RInstPropIff AT {instA : InstPred AT} : Rel AT Prop :=
      MkRel proprepₚ.
    Arguments RInstPropIff _ {_}.

    Definition RBox {AT A} (RA : Rel AT A) : Rel (Box AT) A :=
      MkRel 
        (fun v w t => unconditionally (fun w2 ω => ℛ⟦ RA ⟧ v (t w2 ω))).
    Arguments RBox {AT A} RA : simpl never.

    Definition RImpl {AT A BT B} (RA : Rel AT A) (RB : Rel BT B) :
      Rel (Impl AT BT) (A -> B) :=
      MkRel (fun fc w fs => ∀ a ta, ℛ⟦ RA ⟧ a ta -∗ ℛ⟦ RB ⟧ (fc a) (fs ta))%I.
    Arguments RImpl {_ _ _ _} RA RB : simpl never.

    Definition intowand_rimpl {A AT B BT} {RA : Rel AT A} {RB : Rel BT B}  {w} {a sa f} {sf} :
      IntoWand false false (RSat (RImpl RA RB) f sf) (RSat RA a sa) (RSat RB (f a) (w := w) (sf sa)).
    Proof.
      unfold IntoWand, RImpl; cbn.
      iIntros "H".
      now iApply "H".
    Qed.

    Definition RForall {𝑲}
      {AT : forall K : 𝑲, TYPE} {A : forall K : 𝑲, Type}
      (RA : forall K, Rel (AT K) (A K)) :
      Rel (@W.Forall 𝑲 AT) (forall K : 𝑲, A K) :=
      MkRel (fun fc w fs => ∀ₚ K : 𝑲, ℛ⟦ RA K ⟧ (fc K) (fs K))%P.
    Arguments RForall {_ _ _} RA : simpl never.
    #[export] Instance intoforall_rforall {𝑲}
      {AT : forall K : 𝑲, TYPE} {A : forall K : 𝑲, Type}
      {RA : forall K, Rel (AT K) (A K)} {f w} {sf : forall K, AT K w} :
      IntoForall (RSat (RForall RA) f sf) (fun K => RSat (RA K) (f K) (sf K)).
    Proof.
      unfold IntoForall, RForall.
      now cbn.
    Qed.

    Definition RVal (σ : Ty) : Rel (fun Σ => Term Σ σ) (Val σ) :=
      RInst (fun Σ => Term Σ σ) (Val σ).
    Arguments RVal σ : simpl never.

    Definition RNEnv (N : Set) (Δ : NCtx N Ty) : Rel _ _ :=
      RInst (fun Σ => NamedEnv (Term Σ) Δ) (NamedEnv Val Δ).
    Definition REnv (Δ : Ctx Ty) : Rel _ _ :=
      RInst (fun Σ : LCtx => Env (Term Σ) Δ) (Env Val Δ).
    Definition RUnit : Rel B.Unit unit := RInst B.Unit unit.

    Definition RPathCondition : Rel PathCondition Prop := RInstPropIff PathCondition.
    Arguments RPathCondition : simpl never.
    Definition RFormula : Rel Formula Prop := RInstPropIff Formula.
    Arguments RFormula : simpl never.

    Definition RChunk : Rel Chunk SCChunk := RInst Chunk SCChunk.

    (* Give the [RMsg] instance a lower priority (3) than [RImpl]. *)
    Definition RMsg M {AT A} (RA : Rel AT A) : Rel (M -> AT) A :=
      MkRel (fun v w t => ∀ₚ m, RSat RA v (t m))%P.
    #[global] Arguments RMsg M%_modal {AT A} RA%_R.

    Inductive RList' {AT A} (R : Rel AT A) :
      list A -> ∀ [w : World], WList AT w -> Pred w :=
    | rlist_nil : ∀ w ι, @RList' _ _ R nil w nil ι
    | rlist_cons {w v ts vs} {t : AT w}: ∀ ι,
      RSat R v t ι -> RList' R vs ts ι ->
      RList' R (cons v vs) (cons t ts) ι.

    Definition RList {AT A} (R : Rel AT A) : Rel (WList AT) (list A) :=
      MkRel (RList' R).

    Definition RHeap : Rel SHeap SCHeap := RInst SHeap SCHeap.
    Definition RConst A : Rel (Const A) A := RInst (Const A) A.

    Definition RProd `(RA : Rel AT A, RB : Rel BT B) :
      Rel (WProd AT BT) (A * B)%type :=
      MkRel (fun '(va,vb) w '(ta,tb) => ℛ⟦RA⟧ va ta ∗ ℛ⟦RB⟧ vb tb)%I.

    Definition RMatchResult {N σ} (p : Pattern (N:=N) σ) :
      Rel (SMatchResult p) (MatchResult p) :=
      MkRel
        (fun '(existT pc2 vs) w '(existT pc1 ts) =>
           ∃ₚ e : pc1 = pc2,
             ℛ⟦RNEnv _ (PatternCaseCtx pc2)⟧
               vs
               (eq_rect pc1 (fun pc => NamedEnv (Term w) (PatternCaseCtx pc))
                  ts pc2 e)
               )%P.

    Definition RIn b : Rel (ctx.In b) (Val (type b)) :=
      MkRel (fun v w bIn ι => env.lookup ι bIn = v).

    Module Import notations.
      Open Scope rel_scope.
      Notation "ℛ⟦ R ⟧" := (RSat R%R) (format "ℛ⟦ R ⟧").
      Notation "A -> B" := (RImpl A%R B%R) : rel_scope.
      Notation "□ᵣ A"    := (RBox A%R) (at level 9) : rel_scope.
      Notation "'∀ᵣ' x .. y , R " :=
        (RForall (fun x => .. (RForall (fun y => R)) ..))
          (at level 200, x binder, y binder, right associativity,
            format "'[  ' '[  ' ∀ᵣ  x  ..  y ']' ,  '/' R ']'")
          : rel_scope.
    End notations.
  End logicalrelation.

  Section ModalRel.
    Import logicalrelation logicalrelation.notations iris.bi.interface notations ModalNotations.
    Lemma forgetting_RImpl {AT A BT B} {RA : Rel AT A} {RB : Rel BT B} {w1 w2 : World} {ω : w1 ⊒ w2} {f sf} :
      forgetting ω (ℛ⟦ RImpl RA RB ⟧ f sf) ⊣⊢ (∀ a sa, forgetting ω (ℛ⟦ RA ⟧ a sa) -∗ forgetting ω (ℛ⟦ RB ⟧ (f a) (sf sa))).
    Proof.
      unfold RImpl at 1. cbn.
      rewrite <-forgetting_forall.
      apply derived_laws.bi.forall_proper; intros a.
      rewrite <-forgetting_forall.
      apply derived_laws.bi.forall_proper; intros sa.
      rewrite <-forgetting_wand.
      now apply derived_laws.bi.wand_proper.
    Qed.
  End ModalRel.


  Module RSolve.
    Import logicalrelation logicalrelation.notations iris.bi.interface notations ModalNotations iris.proofmode.proofmode iris.proofmode.environments.

    Class RefineCompat `(R : Rel AT A) (v : A)  w (vs : AT w) (Ob : Pred w) :=
      MkRefineCompat {
          refine_compat_lemma : Ob ⊢ ℛ⟦ R ⟧ v vs
        }.
    #[export] Hint Mode RefineCompat - + - + + + - : typeclass_instances.
    #[global] Arguments refine_compat_lemma {AT A R v w vs Ob} rci : rename.
    #[global] Arguments RefineCompat {AT A} R v w vs Ob%_I.
    #[global] Arguments MkRefineCompat {AT A R v w vs Ob%_I} rci : rename.

    Program Definition refine_compat_impl `{RA : Rel AT A} `{RB : Rel BT B} {f v w fs vs} {Pf}
      (compatf : RefineCompat (RA -> RB) f w fs Pf) : RefineCompat RB (f v) w (fs vs) (Pf ∗ RSat RA v vs) :=
      MkRefineCompat _.
    Next Obligation.
      iIntros (AT A RA BT B RB f v w fs vs Pf compatf) "[Hcf Hv]".
      now iApply (refine_compat_lemma compatf with "Hcf").
    Qed.

    (* Outside section because Coq doesn't allow to put it inside (?) *)
    (* The Hint Resolve used "simple apply", which wasn't instantiating evars sufficiently strongly. Hint Extern with eapply works better. *)
    #[export] Hint Extern 1 (RefineCompat ?RB (?f ?v) ?w (?fs ?vs) _) => eapply (refine_compat_impl (RB := RB) (fs := fs) (vs := vs) (f := f) (v := v) (w := w)) : typeclass_instances.

    #[export] Program Instance refine_compat_forall {𝑲} {AT : forall K : 𝑲, TYPE} {A : forall K : 𝑲, Type} (RA : forall K, Rel (AT K) (A K)) {f w fs k P}
      (compatf : RefineCompat (RForall RA) f w fs P) : RefineCompat (RA k) (f k) w (fs k) P :=
      MkRefineCompat _.
    Next Obligation.
      iIntros (𝑲 AT A RA f w fs k P compatf) "Hcf".
      now iApply (refine_compat_lemma compatf with "Hcf").
    Qed.

    (* Proof mode steps for [rsolve_step]. *)
    Lemma tac_refine_compat `{R : Rel AT A} {v w vs Ob} {Δ : envs (Pred w)} :
      RefineCompat R v w vs Ob → envs_entails Δ Ob → envs_entails Δ (ℛ⟦R⟧ v vs).
    Proof. rewrite envs_entails_unseal. intros [H] HΔ. now rewrite HΔ. Qed.

    Lemma tac_sep_split_pred {w} {Δ : envs (Pred w)} {P Q} :
      envs_entails Δ P → envs_entails Δ Q → envs_entails Δ (P ∗ Q).
    Proof.
      rewrite envs_entails_unseal => HP HQ.
      rewrite -bi.persistent_and_sep_1. now apply bi.and_intro.
    Qed.

    Lemma tac_rbox_intro `{R : Rel AT A} {v w} {vs : Box AT w} {Δ : envs (Pred w)} :
      (∀ w2 (ω : w ⊒ w2), envs_entails Δ (assuming ω (ℛ⟦R⟧ v (vs w2 ω)))) →
      envs_entails Δ (ℛ⟦□ᵣ R⟧ v vs).
    Proof.
      rewrite envs_entails_unseal => H.
      apply bi.forall_intro => w2. apply bi.forall_intro => ω. apply H.
    Qed.

    Lemma tac_unconditionally_intro {w} {P : Box Pred w} {Δ : envs (Pred w)} :
      (∀ w2 (ω : w ⊒ w2), envs_entails Δ (assuming ω (P w2 ω))) →
      envs_entails Δ (unconditionally P).
    Proof.
      rewrite envs_entails_unseal => H.
      apply bi.forall_intro => w2. apply bi.forall_intro => ω. apply H.
    Qed.

    Lemma tac_rimpl_intro `{RA : Rel AT A} `{RB : Rel BT B} {f w} {fs : Impl AT BT w}
      {Δ : envs (Pred w)} :
      (∀ a ta, envs_entails Δ (ℛ⟦RA⟧ a ta -∗ ℛ⟦RB⟧ (f a) (fs ta))) →
      envs_entails Δ (ℛ⟦RA -> RB⟧ f fs).
    Proof.
      rewrite envs_entails_unseal => H.
      apply bi.forall_intro => a. apply bi.forall_intro => ta. apply H.
    Qed.

    Ltac rsolve_step :=
      first [
          (lazymatch goal with
           | |- envs_entails _ (ℛ⟦□ᵣ _⟧ _ _) =>
               notypeclasses refine (tac_rbox_intro _); intros ? ?; iModIntro
           | |- envs_entails _ (forgetting _ _) => iModIntro
           | |- envs_entails _ (ℛ⟦_ -> _⟧ _ _) =>
               notypeclasses refine (tac_rimpl_intro _); intros ? ?; iIntros "#?"
           end)
        | lazymatch goal with
          | |- envs_entails _ (ℛ⟦ ?R ⟧ ?v ?vs) =>
              notypeclasses refine (tac_refine_compat (R := R) (v := v) (vs := vs) _ _);
              [tc_solve|]
          | |- envs_entails _ (_ ∗ _) => notypeclasses refine (tac_sep_split_pred _ _)
          | |- envs_entails _ (unconditionally _) =>
              notypeclasses refine (tac_unconditionally_intro _); intros ? ?; iModIntro
          end
        ].

    Ltac rsolve :=
      iStartProof;
      repeat rsolve_step;
      (* [RSat] goals left by [rsolve_step] have no [RefineCompat] instance. *)
      try lazymatch goal with
        | |- envs_entails _ (ℛ⟦_⟧ _ _) => iAssumption
        | |- _ => done
        end;
      (* After walking through the symbolic computation using the above lemmas,
       * we try to apply induction hypotheses.
       * To do this, we determine the right world to apply the IH in by looking at the current goal.
       *)
      repeat match goal with
        | H : (forall (w : World), _) |- @envs_entails (@bi_pred ?w) _ _ => specialize (H w)
        | H : (forall (w : World), _) |- @envs_entails _ _ (@logicalrelation.RSat _ _ _ _ ?w _) => specialize (H w)
        | H : ⊢ ?P |- envs_entails _ ?P => (try iApply H); clear H
        end.

    Class RefineCompatGen (w : World) (P : Pred w) (Ob : Pred w) (withbase : bool):=
      MkRefineCompatGen {
          refine_compat_gen_lemma : Ob ⊢ P
        }.
    #[global] Arguments RefineCompatGen [w] P%_I Ob%_I withbase.
    #[global] Arguments MkRefineCompatGen {w} {P} _%_I _ {_}.
    #[global] Arguments refine_compat_gen_lemma {w} P%_I {Ob} withbase rcg : rename.

    #[export] Program Instance refine_compat_gen_step `(R : Rel AT A) (v : A) (w : World) (vs : AT w) Ob1 Ob2 b
      (rc : RefineCompat R v w vs Ob1)
      (iter : RefineCompatGen Ob1 Ob2 b) :
      RefineCompatGen (ℛ⟦ R ⟧ v vs) Ob2 b := MkRefineCompatGen Ob2 _.
    Next Obligation.
      iIntros (AT A R v w vs Ob1 Ob2 b rc iter) "H".
      iApply (refine_compat_lemma with "[H]").
      now iApply (refine_compat_gen_lemma with "[H]").
    Qed.

    #[export] Program Instance refine_compat_gen_base_true {w} {b} :
      RefineCompatGen (w := w) True emp b := MkRefineCompatGen emp _.
    Next Obligation.
      now iIntros.
    Qed.

    #[export] Program Instance refine_compat_gen_base_emp {w} {b} :
      RefineCompatGen (w := w) emp emp b := MkRefineCompatGen emp _.
    Next Obligation.
      now iIntros.
    Qed.

    #[export] Program Instance refine_compat_gen_base {w} (P : Pred w):
      RefineCompatGen (w := w) P P true | 10 := MkRefineCompatGen P _.
    Next Obligation.
      now iIntros.
    Qed.

    Class ObSep {w} (P1 P2 P3 : Pred w) : Prop :=
      obsep_equiv : P1 ∗ P2 ⊣⊢ P3.
    #[export] Instance obsep_empL {w} {P : Pred w} : ObSep emp%I P P.
    Proof. apply bi.emp_sep. Qed.
    #[export] Instance obsep_empR {w} {P : Pred w} : ObSep P emp%I P.
    Proof. apply bi.sep_emp. Qed.
    #[export] Instance obsep_sep {w} {P1 P2 : Pred w} : ObSep P1 P2 (P1 ∗ P2)%I | 1.
    Proof. done. Qed.

    #[export] Program Instance refine_compat_gen_split {w} {P1 P2 : Pred w} {Ob1 Ob2 Ob} {b}
      (rcg1 : RefineCompatGen P1 Ob1 b) (rcg2 : RefineCompatGen P2 Ob2 b) {_ : ObSep Ob1 Ob2 Ob} :
      RefineCompatGen (w := w) (P1 ∗ P2) Ob b | 1 := MkRefineCompatGen Ob _.
    Next Obligation.
      iIntros (w P1 P2 Ob1 Ob2 Ob b rcg1 rcg2 obsep) "H".
      rewrite -(obsep_equiv (ObSep := obsep)).
      iDestruct "H" as "(H1 & H2)".
      iSplitL "H1".
      - iApply (refine_compat_gen_lemma with "H1").
      - iApply (refine_compat_gen_lemma with "H2").
    Qed.

    Ltac rsolve2_step :=
      first [
          (lazymatch goal with
           | |- envs_entails _ (ℛ⟦□ᵣ _⟧ _ _) => iIntros (? ?) "!>"
           | |- envs_entails _ (ℛ⟦_ -> _⟧ _ _) => iIntros (? ?) "#?"
           end)
        | lazymatch goal with
          | |- envs_entails _ ?P => iApply (refine_compat_gen_lemma P true)
          | |- envs_entails _ (unconditionally _) => iIntros (? ?) "!>"
          end
        ].

    Ltac rsolve2 :=
      iStartProof;
      progress rsolve2_step; try done;
      (* After walking through the symbolic computation using the above lemmas,
       * we try to apply induction hypotheses.
       * To do this, we determine the right world to apply the IH in by looking at the current goal.
       *)
      repeat match goal with
        | H : (forall (w : World), _) |- @envs_entails (@bi_pred ?w) _ _ => specialize (H w)
        | H : (forall (w : World), _) |- @envs_entails _ _ (@logicalrelation.RSat _ _ _ _ ?w _) => specialize (H w)
        | H : ⊢ ?P |- envs_entails _ ?P => (try iApply H); clear H
        end.
  End RSolve.


  Section LRCompat.
    Import notations.
    Import logicalrelation.
    Import logicalrelation.notations.
    (* Import ModalNotations. *)
    Import iris.proofmode.proofmode.
    Import RSolve.
    
    Lemma refine_RMatchResult_existT_eq {N σ} {p : Pattern (N:=N) σ} {w} {pc args1 args2}:
      ℛ⟦RNEnv _ (PatternCaseCtx pc)⟧ args1 args2 ⊢
        RSat (w := w) (RMatchResult p) (existT pc args1) (existT pc args2).
    Proof. iIntros "Hargs". now iExists eq_refl. Qed.

    #[export] Instance refine_compat_RMatchResult_existT_eq {N σ} {p : Pattern (N:=N) σ} {w} {pc args1 args2} :
      RefineCompat (RMatchResult p) (existT pc args1) w (existT pc args2) _ :=
      MkRefineCompat refine_RMatchResult_existT_eq.

    Lemma refine_term_val {w τ v} : ⊢ (ℛ⟦RVal τ⟧ v (term_val τ v) : Pred w).
    Proof. unfold RVal, RInst. crushPredEntails3. Qed.

    Lemma refine_term_val2 {w τ v1 v2} : bi_pure (v1 = v2) ⊣⊢ (ℛ⟦RVal τ⟧ v1 (term_val τ v2) : Pred w).
    Proof. unfold RVal, RInst. crushPredEntails3. Qed.

    Lemma refine_term_binop {w τ1 τ2 τ3} {op : BinOp τ1 τ2 τ3} {a1 sa1 a2 sa2}:
      ℛ⟦RVal τ1⟧ a1 sa1 ∗ ℛ⟦RVal τ2⟧ a2 sa2 ⊢
        ℛ⟦RVal τ3⟧ (bop.eval op a1 a2) (w := w) (term_binop op sa1 sa2).
    Proof.
      unfold RVal, RInst; crushPredEntails3; now subst.
    Qed.
    
    Lemma refine_unit {w} {u su} :
      ⊢ ℛ⟦ RUnit ⟧ u su : Pred w.
    Proof. destruct u, su. now crushPredEntails3. Qed.
    Hint Resolve refine_unit : core.

    #[export] Instance refine_compat_unit {w} {u su} :
      RefineCompat RUnit u w su emp :=
      MkRefineCompat refine_unit.

    Lemma RProd_pair {AT A} {RA : Rel AT A} {BT B} {RB : Rel BT B} {w} {v1 v2 sv1} {sv2 : BT w}:
      ℛ⟦ RProd RA RB ⟧ (v1, v2) (sv1 , sv2) ⊣⊢ ℛ⟦ RA ⟧ v1 sv1 ∗ ℛ⟦ RB ⟧ v2 sv2.
    Proof. now crushPredEntails3. Qed.

    Lemma refine_pair {AT A} {RA : Rel AT A} {BT B} {RB : Rel BT B} {w} :
      ⊢ ℛ⟦ RA -> RB -> RProd RA RB ⟧ pair (@pair (AT w) (BT w)).
    Proof.
      crushPredEntails3.
      now constructor.
    Qed.

    #[export] Instance refine_compat_pair {AT A} {RA : Rel AT A} {BT B} {RB : Rel BT B} {w} :
      RefineCompat (RA -> RB -> RProd RA RB) pair w (@pair (AT w) (BT w)) emp :=
      MkRefineCompat refine_pair.

    Lemma refine_RHeap_nil {w} :
      ⊢ ℛ⟦ RHeap ⟧ nil (nil : SHeap (wctx w)).
    Proof.
      iApply repₚ_triv.
      now intros.
    Qed.
    Hint Resolve refine_RHeap_nil : core.

    #[export] Instance refine_compat_RHeap_nil {w} :
      RefineCompat RHeap nil w (nil : SHeap (wctx w)) emp :=
      MkRefineCompat refine_RHeap_nil.

    Lemma refine_RHeap_cons {w} :
      ⊢ ℛ⟦ RChunk -> RHeap -> RHeap ⟧ cons (@cons (Chunk (wctx w))).
    Proof.
      iIntros (c1 c2) "Rc %h1 %h2 Rh".
      iApply ((repₚ_cong₂ (T2 := fun Σ => list (Chunk Σ)) (T3 := fun Σ => list (Chunk Σ)) cons cons) with "[$Rc $Rh]").
      now intros.
    Qed.

    #[export] Instance refine_compat_RHeap_cons {w} :
      RefineCompat (RChunk -> RHeap -> RHeap) cons w (@cons (Chunk (wctx w))) emp :=
      MkRefineCompat refine_RHeap_cons.

    Lemma refine_nil {AT A} {R : Rel AT A} {w} :
      ⊢ ℛ⟦ RList R ⟧ nil (nil : list (AT w)).
    Proof.
      crushPredEntails3.
      constructor.
    Qed.
    Hint Resolve refine_nil : core.

    Definition refine_compat_nil {AT A} {R : Rel AT A} {w} :
      RefineCompat (RList R) nil w (nil : list (AT w)) emp :=
      MkRefineCompat refine_nil.

    Lemma refine_cons {AT A} {R : Rel AT A} {w} :
      ⊢ ℛ⟦ R -> RList R -> RList R ⟧ cons (@cons (AT w)).
    Proof.
      crushPredEntails3.
      now constructor.
    Qed.

    #[export] Instance refine_compat_cons {AT A} {R : Rel AT A} {w} :
      RefineCompat (R -> RList R -> RList R) cons w (@cons (AT w)) emp :=
      MkRefineCompat refine_cons.

    Lemma refine_if {AT A} {R : Rel AT A} {w} {v1 sv1 v2 sv2 c sc}:
      ⊢ ℛ⟦ RConst bool ⟧ c sc -∗ ℛ⟦ R ⟧ v1 sv1 -∗ ℛ⟦ R ⟧ v2 sv2 -∗
        ℛ⟦ R ⟧ (if c then v1 else v2) (if sc then sv1 else sv2 : AT w).
    Proof.
      unfold RConst, RInst; cbn.
      crushPredEntails3; subst.
      now destruct sc.
    Qed.

    Lemma RList_ind {AT : TYPE} {A : Type} {R : Rel AT A}
      (P : Rel (WList AT) (list A)) :
      ∀ (w : World),
        (ℛ⟦P⟧ [] ([] : WList AT w) ∗
           (∀ (v : A) (t : AT w) (vs : list A) (ts : WList AT w),
               ℛ⟦R⟧ v t -∗ ℛ⟦ RList R ⟧ vs ts -∗ ℛ⟦P⟧ vs ts -∗ ℛ⟦P⟧ (v :: vs) (t :: ts)) ⊢
           ∀ (l : list A) (l0 : WList AT w), ℛ⟦ RList R ⟧ l l0 -∗ ℛ⟦P⟧ l l0)%I.
    Proof.
      intros w. constructor.
      intros ι Hpc (Hnil & Hcons) l l0 HRList.
      induction HRList.
      - now apply Hnil.
      - apply Hcons; try done.
        now apply IHHRList.
    Qed.

    Lemma refine_map {AT1 A1} {R1 : Rel AT1 A1} {AT2 A2} {R2 : Rel AT2 A2} {w} :
      ⊢ ℛ⟦ (R1 -> R2) -> RList R1 -> RList R2 ⟧ (@map _ _) (@map _ _ : Impl _ _ w).
    Proof.
      iIntros (f sf) "Hf %l %sl Hl".
      iApply (RList_ind (R := R1) (MkRel (fun l w sl => ℛ⟦ (R1 -> R2) -> RList R2 ⟧ (fun f => map f l) (fun sf => map sf sl : list (AT2 w)))) with "[] Hl Hf").
      clear; iIntros; iSplit.
      - iIntros (f sf) "Hf".
        iApply (refine_nil (R := R2)).
      - iIntros (v sv vs svs) "Hv Hvs IHvs %f %sf #Hf".
        iApply (refine_cons (R := R2) with "[Hf Hv]").
        + now iApply ("Hf" $! v sv with "Hv").
        + now iApply ("IHvs" $! f sf with "Hf").
    Qed.

    Lemma RList_RInst {AT A} `{InstSubst AT A, @SubstLaws AT _} :
      forall (v : list A) (w : World) (t : list (AT w)),
        ℛ⟦RList (RInst AT A)⟧ v t ⊣⊢ ℛ⟦RInst (fun w => list (AT w)) (list A)⟧ v t.
    Proof.
      unfold RInst. crushPredEntails3.
      - induction H4; first done.
        now rewrite <-H4, <-IHRList'.
      - revert v H4. induction t; intros v H4; subst; repeat constructor.
        now apply IHt.
    Qed.

    Lemma refine_four {w1 w2} {ω : Acc w2 w1} {AT A} (RA : Rel AT A) :
      (⊢ ∀ (v__s : Box AT w2) v, (forgetting ω (ℛ⟦□ᵣ RA⟧ v v__s) → ℛ⟦□ᵣ RA⟧ v (four v__s ω)))%I.
    Proof.
      iIntros (v__s v) "Hbox".
      now iApply (forgetting_unconditionally (λ (w0 : World) (ω0 : Acc w2 w0), ℛ⟦RA⟧ v (v__s w0 ω0))).
    Qed.

    Lemma refine_T {AT A} (R : Rel AT A) :
      forall v (w : World), (⊢ ∀ (t : Box AT w), (ℛ⟦ □ᵣ R ⟧ v t) → ℛ⟦R⟧ v (T t))%I.
    Proof.
      iIntros (v w t) "Hvt".
      unfold RBox; cbn.
      now iMod "Hvt".
    Qed.

    Lemma refine_apply {AT A BT B} (RA : Rel AT A) (RB : Rel BT B) :
      forall v f (w : World),
        (⊢ ∀ F (t : AT w), ℛ⟦RA -> RB⟧ f F → ℛ⟦RA⟧ v t → ℛ⟦RB⟧ (f v) (F t))%I.
    Proof. iIntros (v f w F t) "#Hf #Hv". now iApply "Hf". Qed.

    Lemma refine_inst_persist {AT A} `{InstSubst AT A, @SubstLaws AT _}
      {v : A} {w1 w2 : World} {ω : Acc w1 w2} (t : AT w1) :
        forgetting ω (ℛ⟦RInst AT A⟧ v t) ⊢ ℛ⟦RInst AT A⟧ v (persist t ω).
    Proof. 
      iIntros "Hvt".
      now iApply forgetting_repₚ.
    Qed.

    Lemma refine_formula_bool {w : World} {v} {sv : Term w ty.bool} :
      ℛ⟦RVal ty.bool⟧ v sv ⊢ ℛ⟦RFormula⟧ (v = true) (formula_bool sv).
    Proof. unfold RVal, RInst. crushPredEntails3; cbn in *; now subst. Qed.

    Lemma refine_formula_true {w : World} :
      ⊢ ℛ⟦RFormula⟧ True%type (formula_true : Formula w).
    Proof. unfold RFormula. crushPredEntails3. Qed.

    Lemma refine_formula_relop {w : World} {σ v1 v2} {sv1 sv2 : Term w σ}  {relop : RelOp σ}:
      ℛ⟦ RVal σ ⟧ v1 sv1 ∗ ℛ⟦ RVal σ ⟧ v2 sv2 ⊢
        ℛ⟦RFormula⟧ (bop.eval_relop_prop relop v1 v2) (formula_relop relop sv1 sv2).
    Proof.
      unfold RFormula, RVal, RInst. crushPredEntails3; now subst.
    Qed.

    Lemma refine_formula_persist :
      forall (w1 w2 : World) {ω : Acc w1 w2} (f : Formula w1) (p : Prop),
        ⊢ forgetting ω (ℛ⟦RFormula⟧ p f) -∗ ℛ⟦RFormula⟧ p (persist f ω).
    Proof.
      iIntros (w1 w2 ω f p) "Hvt".
      now iApply forgetting_proprepₚ.
    Qed.

    Lemma refine_inst_subst {Σ} {T : LCtx -> Type} `{InstSubst T A} (vs : T Σ) {w : World} :
      ⊢ ℛ⟦ RInst (Sub Σ) (Valuation Σ) -> RInst T A ⟧ (inst vs) (subst vs : Sub Σ w -> T w)%I.
    Proof.
      unfold RImpl, RInst. cbn.
      crushPredEntails3.
      now rewrite inst_subst H4.
    Qed.

    Definition refine_compat_inst_subst {Σ} {T : LCtx -> Type} `{InstSubst T A} (vs : T Σ) {w : World} :
      RefineCompat (RInst (Sub Σ) (Valuation Σ) -> RInst T A) (inst vs) w (subst vs) _ :=
      MkRefineCompat (refine_inst_subst vs).

    Lemma refine_instprop_subst {Σ} {T : LCtx -> Type} `{InstPredSubst T}
      (vs : T Σ) {w : World} :
      ⊢ ℛ⟦ (RInst (Sub Σ) (Valuation Σ) -> RInstPropIff T) ⟧ (instprop vs) (subst vs : Sub Σ w -> T w)%I.
    Proof.
      unfold RImpl, RInst. cbn.
      unfold proprepₚ; cbn.
      crushPredEntails3; subst.
      - rewrite instpred_prop in H5.
        now rewrite <-instprop_subst.
      - now rewrite instpred_prop instprop_subst.
    Qed.

    #[export] Instance refine_compat_instprop_subst {Σ} {T : LCtx -> Type} `{InstPredSubst T}
      {vs : T Σ} {w : World} :
      RefineCompat ((RInst (Sub Σ) (Valuation Σ) -> RInstPropIff T)) (instprop vs) w (subst vs : Sub Σ w -> T w)%I emp :=
      MkRefineCompat (refine_instprop_subst _).

    Lemma refine_lift {AT A} `{InstLift AT A} {w : World} (a : A) :
      ⊢ ℛ⟦RInst AT A⟧ a (lift a : AT w).
    Proof. iApply lift_repₚ. Qed.

    #[export] Instance refine_compat_lift `{InstLift AT A} {w : World} (a : A) :
      RefineCompat (RInst AT A) a w (lift a) _ :=
      MkRefineCompat (refine_lift a).

    Import ModalNotations. 
    Section WithNotations.
      Import env.notations.
      Import ctx.notations.
      Lemma refine_namedenv_snoc {N} {Δ : NCtx N Ty} {b} {w : World} {vs : NamedEnv Val Δ} {svs : NamedEnv (Term w) Δ} {v : Val (type b)} {sv : Term w (type b)} :
        ℛ⟦RNEnv N Δ⟧ vs svs ∗ ℛ⟦RVal (type b)⟧ v sv ⊢ ℛ⟦RNEnv N (Δ ▻ b)⟧ (vs.[b ↦ v])%env (svs.[b ↦ sv])%env.
      Proof.
        iIntros "[Hvs Hv]".
        iApply (repₚ_cong₂ (T1 := fun w => NamedEnv (Term w) Δ) (T2 := STerm (type b)) (T3 := fun w => NamedEnv (Term w) (Δ ▻ b)) (fun vs v => vs.[b ↦ v]) (fun vs (v : Term w (type b)) => vs.[b ↦ v]) with "[$Hvs $Hv]").
        now intros.
      Qed.

      #[export] Instance refine_compat_namedenv_snoc {N} {Δ : NCtx N Ty} {b} {w : World} {vs : NamedEnv Val Δ} {svs : NamedEnv (Term w) Δ} {v : Val (type b)} {sv : Term w (type b)} :
        RefineCompat (RNEnv N (Δ ▻ b)) (vs.[b ↦ v])%env w (svs.[b ↦ sv])%env _ :=
        MkRefineCompat refine_namedenv_snoc.

      Lemma refine_sub_snoc {τ : Ty} {Γ : LCtx} {x : LVar}
        {w : World} {vs : NamedEnv Val Γ} {svs : NamedEnv (Term w) Γ}
        {v : Val τ} {sv : Term w τ} :
        (ℛ⟦RNEnv LVar Γ⟧ vs svs) ∗  ℛ⟦RVal τ⟧ v sv ⊢
          ℛ⟦RNEnv LVar (Γ ▻ x∷τ)⟧ (vs.[x∷τ ↦ v])%env (sub_snoc svs (x∷τ) sv).
      Proof.
        iIntros "[H1 H2]".
        iApply (repₚ_cong₂ (T1 := fun w => NamedEnv (Term w) Γ) (T2 := STerm τ) (T3 := fun w => NamedEnv (Term w) (Γ ▻ (x∷τ))) (fun vs v => vs.[x∷τ ↦ v]) (fun vs (v : Term w τ) => sub_snoc vs (x∷τ) v) with "[$H1 $H2]").
        now intros.
      Qed.

      Lemma refine_env_snoc {Δ : Ctx Ty} {τ} {w : World} {vs : Env Val Δ} {svs : Env (Term w) Δ} {v : Val τ} {sv : Term w τ} :
        ℛ⟦REnv Δ⟧ vs svs ∗ ℛ⟦RVal τ⟧ v sv ⊢ ℛ⟦REnv (Δ ▻ τ)⟧ (vs ► ( τ ↦ v ))%env (svs ► (τ ↦ sv ))%env.
      Proof.
        iIntros "[Hvs Hv]".
        iApply (repₚ_cong₂ (T1 := fun w => Env (Term w) Δ) (T2 := STerm τ) (T3 := fun w => Env (Term w) (Δ ▻ τ)) (fun vs v => vs ► ( τ ↦ v )) (fun vs (v : Term w τ) => vs ► ( τ ↦ v )) with "[$Hvs $Hv]").
        now intros.
      Qed.

      Lemma refine_env_nil {w : World} {vs : Env Val [ctx]} {svs : Env (Term w) [ctx]} :
        ⊢ ℛ⟦REnv [ctx]⟧ vs (w := w) svs.
      Proof.
        unfold REnv, RInst; cbn.
        env.destroy vs.
        env.destroy svs.
        now iApply (repₚ_triv (T := fun w => Env (Term w) [ctx])).
      Qed.


      Lemma refine_namedenv_nil {N} {w : World} :
         ⊢ ℛ⟦RNEnv N [ctx] ⟧ env.nil (env.nil : NamedEnv (Term w) [ctx]).
      Proof.
        iApply (repₚ_triv (T := fun w => NamedEnv (Term w) [ctx])).
        now intros.
      Qed.

      #[export] Instance refine_compat_namedenv_nil {N} {w : World} :
        RefineCompat (RNEnv N [ctx]) env.nil w (env.nil : NamedEnv (Term w) [ctx]) _ :=
        MkRefineCompat refine_namedenv_nil.

      Lemma refine_namedenv_singleton {N : Set} {x : N} {σ : Ty} {w : World} {v : Val σ} {sv : Term w σ} :
        ℛ⟦RVal σ⟧ v sv ⊢ ℛ⟦RNEnv N (ctx.nil ▻ x∷σ)⟧ ([env].[x∷σ ↦ v])%env ([env].[x∷σ ↦ sv])%env.
      Proof.
        iIntros "Hv"; rsolve.
      Qed.

      Lemma refine_namedenv_sub_acc_trans {Σ : LCtx} {w1 w2 : World} {ι : Valuation Σ} { ω1 : wlctx Σ ⊒ w1} {ω2 : w1 ⊒ w2}:
        forgetting ω2 (repₚ (w := w1) ι (sub_acc ω1)) ⊢
          ℛ⟦RNEnv LVar (wlctx Σ)⟧ ι (sub_acc (acc_trans ω1 ω2)).
      Proof.
        rewrite <-forgetting_repₚ.
        now rewrite sub_acc_trans persist_subst.
      Qed.

      Lemma refine_namedenv_cat {N} {Δ : NCtx N Ty} {Γ} {w : World} :
        ⊢ ℛ⟦RNEnv N Δ -> RNEnv N Γ -> RNEnv N (Δ ▻▻ Γ)⟧ (w := w) env.cat env.cat.
      Proof.
        iIntros (vs1 svs1) "Hvs1 %vs2 %svs2 Hvs2".
        iApply (repₚ_cong₂ (T1 := fun w => NamedEnv (Term w) Δ) (T2 := fun w => NamedEnv (Term w) Γ) (T3 := fun w => NamedEnv (Term w) (Δ ▻▻ Γ)) (v1 := vs1) (v2 := vs2) (vs1 := svs1) (vs2 := svs2) env.cat env.cat with "[$Hvs1 $Hvs2]").
        intros.
        now rewrite inst_env_cat.
      Qed.

      #[export] Instance refine_compat_namedenv_cat {N} {Δ : NCtx N Ty} {Γ} {w : World} :
        RefineCompat (RNEnv N Δ -> RNEnv N Γ -> RNEnv N (Δ ▻▻ Γ)) env.cat w env.cat emp :=
        MkRefineCompat refine_namedenv_cat.

      Lemma refine_namedenv_sub_acc {Σ : LCtx} {w : World} {ι : Valuation Σ} {ω : wlctx Σ ⊒ w}:
        forgetting ω (repₚ (w := wlctx Σ) ι (sub_id Σ)) ⊢
          ℛ⟦RNEnv LVar (wlctx Σ)⟧ ι (sub_acc ω).
      Proof.
        rewrite <-forgetting_repₚ.
        now rewrite persist_subst sub_comp_id_left.
      Qed.

    End WithNotations.

    Lemma refine_chunk_ptsreg {w τ} {pc a ta} : 
      ℛ⟦RVal τ ⟧ a ta ⊢ ℛ⟦RChunk⟧ (chunk_ptsreg pc a) (w := w) (chunk_ptsreg pc ta).
    Proof.
      unfold RChunk, RVal, RInst; cbn.
      crushPredEntails3; now subst.
    Qed.

    Lemma refine_chunk_user {w : World} { c vs svs} :
      ℛ⟦REnv (𝑯_Ty c)⟧ vs svs ⊢ ℛ⟦RChunk⟧ (chunk_user c vs) (w := w) (chunk_user c svs).
    Proof.
      unfold REnv, RChunk, RInst; crushPredEntails3.
      now subst.
    Qed.

    Lemma refine_pattern_match {w : World} {σ} {v : Val σ} {sv : Term w σ}
      {p : Pattern (N:=LVar) σ} :
      ℛ⟦ RVal σ ⟧ v sv ⊢
        let (pc, δpc) := pattern_match_val p v in
        knowing (w1 := wmatch w sv p pc) (acc_match_right pc)
          (ℛ⟦ RNEnv LVar (PatternCaseCtx pc) ⟧  δpc
             (sub_cat_right (PatternCaseCtx pc) : NamedEnv _ _)).
    Proof.
      pose proof (pattern_match_val_inverse_left p v) as eq.
      destruct (pattern_match_val p v) as [pc args].
      unfold pattern_match_val_reverse' in eq; cbn in eq.
      unfold knowing, RVal, RNEnv, RInst.
      crushPredEntails3.
      exists (env.cat ι args).
      now rewrite instprop_subst inst_subst !inst_sub_cat_left
        inst_pattern_match_term_reverse inst_sub_cat_right eq.
    Qed.

    Lemma refine_pattern_match_val_term_reverse {N} {w : World} {σ}
      {pat : Pattern (N:=N) σ} {ι} :
      ⊢ ℛ⟦RNEnv N (PatternCaseCtx ι) -> RVal σ⟧ (pattern_match_val_reverse pat ι) (pattern_match_term_reverse pat ι : _ -> STerm σ w).
    Proof.
      unfold RSat, RNEnv, RVal, RInst, RImpl, repₚ.
      intros; crushPredEntails3.
      rewrite inst_pattern_match_term_reverse.
      now subst.
    Qed.

    #[export] Instance refine_compat_pattern_match_val_term_reverse {N} {w : World} {σ}
      {pat : Pattern (N:=N) σ} {ι} :
        RefineCompat (RNEnv N (PatternCaseCtx ι) -> RVal σ) (pattern_match_val_reverse pat ι) w (pattern_match_term_reverse pat ι) _ :=
      MkRefineCompat refine_pattern_match_val_term_reverse.

    Import ctx.notations.
    Lemma refine_pattern_match_var {w : World} {σ} {v : Val σ} {x : LVar} {xIn : ctx.In (x∷σ) w}
      {p : Pattern (N:=LVar) σ} :
      ℛ⟦ RIn (x∷σ) ⟧ v xIn ⊢
        let (pc, δpc) := pattern_match_val p v in
        knowing (w1 := wmatchvar w xIn p pc) (acc_matchvar_right (x := x) pc)
        (ℛ⟦ RNEnv LVar (PatternCaseCtx pc) ⟧  δpc
           (wmatchvar_patternvars pc : NamedEnv (Term (wmatchvar w xIn p pc)) _)).
    Proof.
      pose proof (pattern_match_val_inverse_left p v) as eq.
      destruct (pattern_match_val p v) as [pc args].
      unfold pattern_match_val_reverse' in eq; cbn in eq.
      unfold knowing, RVal, RNEnv, RInst.
      crushPredEntails3.
      exists (env.remove (x∷σ) (env.cat ι args) (ctx.in_cat_left (PatternCaseCtx pc) xIn)).
      rewrite !instprop_subst !inst_subst.
      rewrite inst_sub_single2 inst_pattern_match_term_reverse.
      unfold wmatchvar_patternvars.
      rewrite inst_eq_rect.
      rewrite env.remove_cat_left.
      rewrite eq_rect_sym1.
      rewrite inst_sub_cat_right.
      rewrite eq.
      rewrite <-env.insert_cat_left.
      rewrite <-H0.
      rewrite env.insert_remove.
      now rewrite inst_sub_cat_left.
    Qed.

    Lemma refine_unfreshen_patterncaseenv {N : Set} {w : World} {Σ} {n : N -> LVar} {σ}
      {p : Pattern (N:=N) σ} {pc : PatternCase (freshen_pattern n Σ p)}
      {vs : NamedEnv Val (PatternCaseCtx pc)}
      {svs : NamedEnv (Term w) (PatternCaseCtx pc)} :
      ℛ⟦RNEnv LVar (PatternCaseCtx pc)⟧ vs svs
          ⊢ ℛ⟦RNEnv N (PatternCaseCtx (unfreshen_patterncase n Σ p pc))⟧ (unfreshen_patterncaseenv n p pc vs) (unfreshen_patterncaseenv n p pc svs).
    Proof.
      unfold RNEnv, RInst, repₚ; cbn.
      crushPredEntails3.
      now rewrite inst_unfreshen_patterncaseenv H0.
    Qed.


    Lemma RVal_eqₚ {σ v} {w : World} {sv1 sv2 : Term w σ}:
      ℛ⟦ RVal σ ⟧ v sv1 ∗ eqₚ sv1 sv2 ⊢ ℛ⟦ RVal σ ⟧ v sv2.
    Proof.
      unfold RVal, RInst.
      crushPredEntails3.
      now subst.
    Qed.

    Lemma RVal_pair {σ1 σ2 v1 v2} {w : World} {sv1 : Term w σ1} {sv2 : Term w σ2}:
      ℛ⟦ RVal σ1 ⟧ v1 sv1 ∗ ℛ⟦ RVal σ2 ⟧ v2 sv2 ⊣⊢ ℛ⟦ RVal (ty.prod σ1 σ2) ⟧ (v1 , v2) (term_binop bop.pair sv1 sv2).
    Proof.
      unfold RVal, RInst, repₚ.
      crushPredEntails3.
      - now f_equal.
      - now inversion H0.
      - now inversion H0.
    Qed.

    Lemma RVal_union_invertK {U : unioni} {K1 K2 : unionk U} {vf : Val (unionk_ty U K1)} {w : World} {tf : Term w (unionk_ty U K2)} :
      ℛ⟦RVal (ty.union U)⟧ (unionv_fold U (existT K1 vf)) (term_union U K2 tf) ⊢ bi_pure (K1 = K2).
    Proof.
      unfold RVal, RInst, repₚ; crushPredEntails3.
      rewrite unionv_fold_inj in H0.
      now inversion H0.
    Qed.

    Lemma RVal_union {U : unioni} {K : unionk U} {vf : Val (unionk_ty U K)} {w : World} {tf : Term w (unionk_ty U K)} :
      ℛ⟦RVal (ty.union U)⟧ (unionv_fold U (existT K vf)) (term_union U K tf) ⊣⊢
        ℛ⟦RVal (unionk_ty U K)⟧ vf tf.
    Proof.
      unfold RVal, RInst, repₚ; crushPredEntails3; last by subst.
      rewrite unionv_fold_inj in H0.
      now apply inj_right_pair in H0.
    Qed.

    Lemma refine_tuple_pattern_match_env {N Δ σs} {p : TuplePat σs Δ} {w : World} :
      ⊢ ℛ⟦REnv σs -> RNEnv N Δ⟧ (tuple_pattern_match_env p) (tuple_pattern_match_env (T := Term w) p).
    Proof.
      iIntros (e se) "He". iStopProof.
      unfold RNEnv, REnv, RInst, repₚ.
      crushPredEntails3; subst.
      now rewrite inst_tuple_pattern_match.
    Qed.

    Lemma RVal_tuple {σs} {v : Val (ty.tuple σs)} {w : World} {a : Env (Term w) σs} :
      ℛ⟦RVal (ty.tuple σs)⟧ v (term_tuple a) ⊣⊢ ℛ⟦REnv σs⟧ (envrec.to_env σs v) a.
    Proof.
      unfold RVal, REnv, RInst, repₚ.
      crushPredEntails3; subst.
      - now rewrite envrec.to_of_env.
      - now rewrite H0 envrec.of_to_env.
    Qed.

    Lemma refine_record_pattern_match_env {N R Δ} {p : RecordPat (recordf_ty R) Δ} {w : World}
      {e} {se : NamedEnv (Term w) (recordf_ty R)} :
      ℛ⟦RNEnv recordf (recordf_ty R)⟧ e se ⊣⊢
        ℛ⟦RNEnv N Δ⟧ (record_pattern_match_env p e) (record_pattern_match_env p se).
    Proof.
      unfold RNEnv, RInst, repₚ.
      crushPredEntails3; subst.
      - now rewrite inst_record_pattern_match.
      - rewrite inst_record_pattern_match in H0.
        apply (f_equal (record_pattern_match_env_reverse p)) in H0.
        now rewrite !record_pattern_match_env_inverse_left in H0.
    Qed.

    Lemma RVal_record {R} {w : World} {v : NamedEnv Val (recordf_ty R)} {a : NamedEnv (Term w) (recordf_ty R)} :
      ℛ⟦RNEnv recordf (recordf_ty R)⟧ v a ⊣⊢
       ℛ⟦RVal (ty.record R)⟧ (recordv_fold R v) (term_record R a).
    Proof.
      unfold RNEnv, RVal, RInst, repₚ.
      crushPredEntails3; subst; first done.
      apply (f_equal (recordv_unfold R)) in H0.
      now rewrite !recordv_unfold_fold in H0.
    Qed.

    Lemma RVal_invert_inl {σ τ} {v} {w : World} {sl : Term w σ} : 
      ℛ⟦RVal (ty.sum σ τ)⟧ v (term_inl sl) ⊢ ∃ (vl : Val σ), bi_pure (v = inl vl) ∗ ℛ⟦RVal σ⟧ vl sl.
    Proof.
      unfold RVal, RInst, repₚ, bi_pure; simpl.
      crushPredEntails3; subst.
      eexists. split; reflexivity.
    Qed.

    Lemma RVal_invert_inr {σ τ} {v} {w : World} {sl : Term w τ} : 
      ℛ⟦RVal (ty.sum σ τ)⟧ v (term_inr sl) ⊢ ∃ (vl : Val τ), bi_pure (v = inr vl) ∗ ℛ⟦RVal τ⟧ vl sl.
    Proof.
      unfold RVal, RInst, repₚ, bi_pure; simpl.
      crushPredEntails3; subst.
      eexists. split; reflexivity.
    Qed.

  End LRCompat.

  Import logicalrelation RSolve.
  Import env.notations.
  Import ctx.notations.
  Import ModalNotations.
  
  #[export] Hint Extern 0 (RefineCompat _ (inst ?vs) ?w (subst ?vs) _) => refine (refine_compat_inst_subst vs (w := w)) : typeclass_instances.
  #[export] Hint Extern 0 (RefineCompat (RList ?R) nil _ _ _) => refine (refine_compat_nil (R := R)) : typeclass_instances.
  #[export] Hint Extern 0 (RefineCompat RHeap nil _ _ _) => refine (refine_compat_nil (R := RChunk)) : typeclass_instances.


  (* Outside the LRCompat section because of Coq restriction *)
  #[export] Instance refine_compat_term_val {σ} {v w} : RefineCompat (RVal σ) v w (term_val σ v) _ :=
    MkRefineCompat refine_term_val.

  Definition refine_compat_inst_persist {AT A} `{InstSubst AT A, @SubstLaws AT _} {v} {w1 w2} {ω : Acc w1 w2} {t} :
    RefineCompat (RInst AT A) v w2 (persist t ω) _ :=
    MkRefineCompat (refine_inst_persist _).
  #[global] Opaque refine_compat_inst_persist.
  #[export] Hint Extern 0 (RefineCompat _ ?v _ (persist ?t ?ω) _) => refine (refine_compat_inst_persist (v := v) (t := t) (ω := ω)) : typeclass_instances.

  #[export] Instance refine_compat_inst_persist_term {σ} {v} {w1 w2} {ω : Acc w1 w2} {t} :
    RefineCompat (RVal σ) v w2 (persist__term t ω) _ :=
    MkRefineCompat (refine_inst_persist _).

  Definition refine_compat_term_binop {w τ1 τ2 τ3} {op : BinOp τ1 τ2 τ3} {a1 sa1 a2 sa2} :
    RefineCompat (RVal τ3) (bop.eval op a1 a2)  w (term_binop op sa1 sa2) _ :=
    MkRefineCompat refine_term_binop.
  #[global] Opaque refine_compat_term_binop.
  #[export] Hint Extern 0 (RefineCompat (RVal _) _ _ (term_binop ?binop _ _) _) => ( refine (refine_compat_term_binop (op := binop)) ) : typeclass_instances.

  #[export] Instance refine_compat_formula_true {w : World} :
    RefineCompat RFormula True%type w formula_true _ :=
    MkRefineCompat refine_formula_true.

  #[export] Instance refine_compat_formula_bool {w : World} {v} {sv : Term w ty.bool} :
    RefineCompat RFormula (v = true) w (formula_bool sv) _ :=
    MkRefineCompat refine_formula_bool.

  Definition refine_compat_formula_relop {w : World} {σ v1 v2} {sv1 sv2 : Term w σ}  {relop : RelOp σ} :
    RefineCompat RFormula (bop.eval_relop_prop relop v1 v2) w (formula_relop relop sv1 sv2) _ :=
    MkRefineCompat refine_formula_relop.
  #[global] Opaque refine_compat_formula_relop.
  #[export] Hint Extern 0 (RefineCompat RFormula _ _ (formula_relop ?relop _ _) _) => ( refine (refine_compat_formula_relop (relop := relop)) ) : typeclass_instances.

  #[export] Instance refine_compat_chunk_ptsreg {w σ} {pc a ta} :
    RefineCompat RChunk (chunk_ptsreg pc a) w(chunk_ptsreg (σ := σ) pc ta) _ :=
    MkRefineCompat refine_chunk_ptsreg.

  #[export] Instance refine_compat_chunk_user {w c vs svs} :
    RefineCompat RChunk (chunk_user c vs) w (chunk_user c svs) _ :=
    MkRefineCompat refine_chunk_user.

  #[export] Instance refine_compat_env_snoc {Δ : Ctx Ty} {τ} {w : World} {vs : Env Val Δ} {svs : Env (Term w) Δ} {v : Val τ} {sv : Term w τ} :
    RefineCompat (REnv (Δ ▻ τ)) (vs ► ( τ ↦ v ))%env w (svs ► (τ ↦ sv ))%env _ :=
    MkRefineCompat refine_env_snoc.

  #[export] Instance refine_compat_sub_snoc {τ : Ty} {Γ : LCtx} {x : LVar}
    {w : World} {vs : NamedEnv Val Γ} {svs : NamedEnv (Term w) Γ}
    {v : Val τ} {sv : Term w τ} :
    RefineCompat (RNEnv LVar (Γ ▻ x∷τ)) (vs.[x∷τ ↦ v])%env w (sub_snoc svs (x∷τ) sv) _ :=
    MkRefineCompat refine_sub_snoc.

  #[export] Instance refine_compat_env_nil {w : World} {vs : Env Val [ctx]} {svs : Env (Term w) [ctx]} :
    RefineCompat (REnv [ctx]) vs  w svs _ :=
    MkRefineCompat refine_env_nil.

  #[export] Instance refine_compat_named_env_sub_acc_trans {Σ : LCtx} {w1 w2 : World} {ι : Valuation Σ} {ω1 : wlctx Σ ⊒ w1} {ω2 : w1 ⊒ w2}:
    RefineCompat (RNEnv LVar (wlctx Σ)) ι w2 (sub_acc (acc_trans ω1 ω2)) _ :=
    MkRefineCompat refine_namedenv_sub_acc_trans.

  (* #[export] Instance refine_compat_named_env_sub_acc {Σ : LCtx} {w : World} {ι : Valuation Σ} {ω : wlctx Σ ⊒ w} : *)
  (*   RefineCompat (RNEnv LVar (wlctx Σ)) ι w (sub_acc ω) _ | 10 := *)
  (*   MkRefineCompat refine_namedenv_sub_acc. *)


  Import notations logicalrelation.notations logicalrelation iris.proofmode.proofmode.
  Global Hint Extern 0 (environments.envs_entails _ (ℛ⟦ RUnit ⟧ _ _)) => iApply refine_unit : core.

  #[export] Instance instpredsubst_ctx `{InstPredSubst A, !SubstLaws A} : InstPredSubst (fun Σ => Ctx (A Σ)).
  Proof. constructor; last by typeclasses eauto.
         intros ? ? ζ x. induction x; cbn.
         - now rewrite persist_subst forgetting_emp.
         - rewrite forgetting_sep.
           rewrite persist_subst; cbn; rewrite -!persist_subst.
           change (instpred_ctx ?P) with (instpred P).
           now rewrite IHx instpred_subst.
  Qed.

  Module AutorewriteUnifLogic.
    Import DList.

    #[export] Hint Rewrite @recordv_fold_inj @unionv_fold_inj : uniflogic.
    #[export] Hint Rewrite @term_eq_true_r @term_eq_true_l @term_eq_false_l @term_eq_false_r @term_not_or @term_not_and @term_unop_val @term_binop_val : uniflogic.
    #[export] Hint Rewrite formula_bool_and formula_bool_relop formula_bool_relop_neg : uniflogic.
    #[export] Hint Rewrite @repₚ_term_prod @rep_term_cons rep_eq_terms_true eq_val_rep_l eq_val_rep_r @eq_term_cons @eqₚ_term_prod @repₚ_unionv_fold @eqₚ_unionv_fold @rep_neq_nil_cons @repₚ_term_or_false @repₚ_term_inr_inl @repₚ_term_inl_inr @eqₚ_term_inl_inr @eqₚ_term_inr_inl @repₚ_term_inr @eqₚ_term_inr @repₚ_term_inl @eqₚ_term_inl @repₚ_term_unsigned @eqₚ_term_unsigned @repₚ_term_signed @eqₚ_term_signed @repₚ_term_neg' @repₚ_term_not' @repₚ_term_and repₚ_term_tuple_snoc eqₚ_term_tuple_snoc @repₚ_term_bvapp @eqₚ_term_bvapp @repₚ_term_bvcons @eqₚ_term_bvcons @repₚ_term_record @eqₚ_term_record @repₚ_namedenv_nil @repₚ_namedenv_snoc @eqₚ_namedenv_snoc @eq_term_val @rep_term_val : uniflogic.
    #[export] Hint Rewrite @instpred_formula_relop_neg @formula_relop_term @instpred_formula_relop_eq_val @instpred_formula_relop_eq_val' @instpred_formula_relop_val @instpred_formula_relop_val' : uniflogic.
    #[export] Hint Rewrite @instpred_dlist_empty instpred_dlist_cat instpred_dlist_singleton : uniflogic.

    #[global] Ltac arw :=
      repeat
        (try progress cbn in *;
         repeat
           match goal with
           (* | |- _ /\ _ => split *)
           | |- True => exact I (* cannot keep the match list empty apparently  *)
           end; try easy;
         (* use the more efficient rewrite_db... *)
         rewrite_db uniflogic).
    #[global] Ltac arw_slow :=
      repeat
        (try progress cbn in *;
         repeat
           match goal with
           (* | |- _ /\ _ => split *)
           | |- True => exact I (* cannot keep the match list empty apparently  *)
           end; try easy;
         (* use the slower autorewrite... *)
         autorewrite with uniflogic in * ).
  End AutorewriteUnifLogic.

End UnifLogicOn.
