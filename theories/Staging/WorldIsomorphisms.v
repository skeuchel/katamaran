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
  Classes.Morphisms_Prop
  Classes.RelationClasses
  Relations.Relation_Definitions
.
From Equations Require Import
  Equations.
From stdpp Require Import base.
From Katamaran Require Import
  Prelude
  Base
  Environment
  Symbolic.Worlds
  Symbolic.UnifLogic
  Syntax.Predicates
.
From iris Require bi.derived_connectives bi.interface proofmode.proofmode.

Set Implicit Arguments.

Module Type WorldIsomorphisms
  (Import GLOBAL : GlobalState)
  (Import P      : PredicateKit GLOBAL)
  (Import W      : WorldsMixin GLOBAL P)
  (Import UL     : UnifLogicOn GLOBAL P W).

  Import ctx.notations.
  Import ModalNotations.
  Import iris.bi.interface.
  Import iris.proofmode.proofmode.


  Definition Inverse {w1 w2 : World} (ω12 : Sub w1 w2) (ω21 : Sub w2 w1) :=
    forall ι, instprop (wco w1) ι -> inst ω12 (inst ω21 ι) = ι.

  Record IsIsomorphism {w1 w2 : World} (ω12 : Sub w1 w2) (ω21 : Sub w2 w1) :=
    MkIsIsomorphism {
        wiso_there : Inverse ω12 ω21
      ; wiso_back : Inverse ω21 ω12
      }.

  Lemma iso_symm {w1 w2 : World} {ω12 : Sub w1 w2} {ω21 : Sub w2 w1} :
    IsIsomorphism ω12 ω21 -> IsIsomorphism ω21 ω12.
  Proof.
    intros [Ht Hb].
    now constructor.
  Qed.

  Lemma knowing_forgetting_iso {w1 w2 : World} {ω : Sub w1 w2} {ω' : Acc w2 w1} {P : Pred w1}
    (H : IsIsomorphism ω (sub_acc ω')) :
    P ⊣⊢ knowing ω (forgetting ω P).
  Proof.
    rewrite /forgetting /knowing.
    crushPredEntails3.
    - exists (inst (sub_acc ω') ι).
      rewrite wiso_there; intuition.
      now apply acc_pathcond.
    - now subst.
  Qed.

  Lemma assuming_forgetting_inv {w1 w2 : World} {ω : Sub w1 w2} {ω' : Acc w2 w1} {P : Pred w1}
    (inv : Inverse ω (sub_acc ω')) :
    P ⊣⊢ assuming ω (forgetting ω P).
  Proof.
    rewrite /forgetting /assuming.
    crushPredEntails3.
    - now subst.
    - specialize (H0 (inst (sub_acc ω') ι)).
      rewrite inv in H0; intuition.
      now apply H1, acc_pathcond.
  Qed.

  Lemma forgetting_knowing_iso {w1 w2 : World} {ω : Sub w1 w2} {ω' : Sub w2 w1} {P : Pred w2}
    (inv : Inverse ω' ω) :
    P ⊣⊢ forgetting ω (knowing ω P).
  Proof.
    rewrite /forgetting /knowing.
    crushPredEntails3.
    apply (f_equal (inst ω')) in H0.
    rewrite !inv in H0; intuition.
    now subst.
  Qed.

  Lemma knowing_knowing_iso {w1 w2 : World} {ω : Sub w1 w2} {ω' : Acc w2 w1} {P : Pred w1}
    (inv : Inverse ω (sub_acc ω')) :
    knowing ω (knowing (sub_acc ω') P) ⊣⊢ P.
  Proof.
    unfold knowing.
    crushPredEntails3.
    - subst.
      now rewrite inv.
    - exists (inst (sub_acc ω') ι).
      repeat split.
      + now apply inv.
      + now apply acc_pathcond.
      + now exists ι.
  Qed.


  Lemma forgetting_knowing_iso2 {w1 w2 : World} {ω : Acc w1 w2} {ω' : Acc w2 w1} {P : Pred w1}
    (H : IsIsomorphism (sub_acc ω) (sub_acc ω')) :
    knowing (sub_acc ω') P ⊣⊢ forgetting (sub_acc ω) P.
  Proof.
    rewrite (forgetting_knowing_iso (P := (knowing (sub_acc ω') P)) (wiso_back H)).
    now rewrite (knowing_knowing_iso (wiso_there H)).
  Qed.

  Lemma assuming_assuming_inv {w1 w2 : World} {ω : Sub w1 w2} {ω' : Acc w2 w1} {P : Pred w1}
    (iso : Inverse ω (sub_acc ω')) :
    P ⊣⊢ assuming ω (assuming (sub_acc ω') P).
  Proof.
    rewrite /assuming.
    crushPredEntails3; subst.
    - now rewrite iso in H0.
    - eapply H0; try easy.
      + now apply iso.
      + now apply acc_pathcond.
  Qed.

  Lemma forgetting_assuming_iso {w1 w2 : World} {ω : Sub w1 w2} {ω' : Sub w2 w1} {P : Pred w2}
    (iso : Inverse ω' ω) :
    P ⊣⊢ forgetting ω (assuming ω P).
  Proof.
    rewrite /forgetting /assuming.
    crushPredEntails3.
    apply (f_equal (inst ω')) in H1.
    rewrite !iso in H1; intuition.
    now subst.
  Qed.

  Lemma cancel_forgetting_iso {w1 w2 : World} {ω : Sub w1 w2} {ω' : Acc w2 w1} `{iso : IsIsomorphism ω (sub_acc ω')}
    {P Q : Pred w1} :
    (forgetting ω P ⊢ forgetting ω Q) -> P ⊢ Q.
  Proof.
    intros H.
    rewrite (knowing_forgetting_iso (P := P) iso) (knowing_forgetting_iso (P := Q) iso).
    now rewrite H.
  Qed.

  Lemma cancel_knowing_inv {w1 w2 : World} {ω : Acc w1 w2} {ω' : Acc w2 w1} `{inv : Inverse (sub_acc ω') (sub_acc ω)}
    {P Q : Pred w2} :
    (knowing (sub_acc ω) P ⊢ knowing (sub_acc ω) Q) -> P ⊢ Q.
  Proof.
    intros H.
    rewrite (forgetting_knowing_iso (P := P) inv)
      (forgetting_knowing_iso (P := Q) inv).
    now rewrite H.
  Qed.

  Lemma forgetting_knowing_adjoint_bientails_iso {w1 w2 : World} {ω : Acc w1 w2} {ω'} {P Q}
    (iso : IsIsomorphism (sub_acc ω) (sub_acc ω')) :
    (knowing (sub_acc ω) P ⊣⊢ Q) <-> (P ⊣⊢ forgetting (sub_acc ω) Q).
  Proof.
    rewrite /forgetting /assuming /knowing.
    split; crushPredEntails3.
    - apply (fromBientails H); auto using acc_pathcond.
      now exists ι.
            - destruct H as [H].
              specialize  (H (inst (sub_acc ω) ι) (acc_pathcond ω ι H0)).
              rewrite <-H in H1.
              destruct H1 as (ι2 & eq & Hι2 & HP).
              apply (f_equal (inst (sub_acc ω'))) in eq.
              rewrite !(wiso_back iso) in eq; try assumption.
              now subst.
            - now subst.
            - exists (inst (sub_acc ω') ι).
              repeat split.
              + now rewrite wiso_there.
              + now apply acc_pathcond.
              + apply (fromBientails H).
                now apply acc_pathcond.
                now rewrite wiso_there.
  Qed.

  Program Definition acc_let_right {w} (b : LVar ∷ Ty) v : w ⊒ wlet w b v :=
    @acc_sub w (wlet w b v) sub_wk1 _.
  Next Obligation.
    intros * ι Hpc.
    now apply proj1 in Hpc.
  Defined.

  Program Definition acc_let_left {w} (b : LVar ∷ Ty) v : wlet w b v ⊒ w :=
    acc_sub (sub_snoc (sub_id w) b (term_val _ v)) _.
  Next Obligation.
    intros * ι Hpc.
    split; last reflexivity.
    change (subst_ctx ?pc ?ς)
      with (subst pc ς).
    now rewrite <-subst_sub_comp, sub_comp_wk1_tail, subst_sub_id.
  Defined.

  Program Definition acc_let_snoc {w} (b : LVar ∷ Ty) v : wsnoc w b ⊒ wlet w b v :=
    acc_sub (sub_id (w ▻ b) : Sub (wsnoc w b) (wlet w b v)) _.
  Next Obligation.
    intros * ι.
    destruct (env.view ι) as [ι v'].
    unfold wlet; simpl.
    intros Hpc.
    destruct (proj1 (instprop_snoc _ _ _) Hpc) as [Hpc' H].
    now rewrite instprop_subst inst_sub_id.
  Defined.
  
  (* Lemma acc_let_iso w b v : IsIsomorphism (@acc_let_right w b v) (acc_let_left b v). *)
  (* Proof. *)
  (*   constructor; intros; simpl. *)
  (*   - now rewrite inst_sub_snoc, inst_sub_id, inst_sub_wk1. *)
  (*   - rewrite inst_sub_snoc, inst_sub_id. *)
  (*     destruct (env.view ι) as (ι & v'). *)
  (*     destruct H as (Hpc & Hbv); cbn in Hbv. *)
  (*     subst. *)
  (*     now rewrite inst_sub_wk1. *)
  (* Qed. *)

  (* Lemma assuming_acc_let_snoc {w b v P} : *)
  (*   assuming (acc_let_left (w := w) b v) P ⊣⊢ (repₚ v term_var_zero -∗ forgetting acc_snoc_right P). *)
  (* Proof. *)
  (*   unfold assuming, forgetting, repₚ. *)
  (*   crushPredEntails3; destruct (env.view ι) as [ι v']; subst; cbn in *. *)
  (*   - rewrite instprop_subst inst_sub_wk1 in H; subst. *)
  (*     crushPredEntails3. *)
  (*     rewrite inst_sub_wk1. *)
  (*     apply H0; try done. *)
  (*     f_equal; try done. *)
  (*     now apply inst_sub_id. *)
  (*   - rewrite inst_sub_wk1 in H0. *)
  (*     change (env.map _ _) with (inst (sub_id w) ιpast) in H1. *)
  (*     rewrite inst_sub_id in H1. *)
  (*     destruct (proj1 (env.inversion_eq_snoc ιpast ι v v') H1) as [-> ->]. *)
  (*     now apply H0. *)
  (* Qed. *)

End WorldIsomorphisms.
