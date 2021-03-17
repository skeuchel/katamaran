(******************************************************************************)
(* Copyright (c) 2019 Steven Keuchel                                          *)
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

From Coq Require Import
     Bool.Bool
     Program.Equality
     Program.Tactics
     ZArith.ZArith
     Strings.String
     Classes.Morphisms
     Classes.RelationClasses
     Classes.Morphisms_Prop
     Classes.Morphisms_Relations.
Require Import Basics.

From Coq Require Lists.List.

From Equations Require Import
     Equations.

From MicroSail Require Import
     Sep.Spec
     Sep.Logic
     Sep.Hoare
     Syntax
     Tactics
     Symbolic.Mutator.
From MicroSail Require Import
     SemiConcrete.Mutator
     SemiConcrete.Outcome
     SemiConcrete.Sound.

Set Implicit Arguments.

Import CtxNotations.
Import EnvNotations.

Module Soundness
       (Import termkit : TermKit)
       (Import progkit : ProgramKit termkit)
       (Import assertkit : AssertionKit termkit progkit)
       (Import contractkit : SymbolicContractKit termkit progkit assertkit).
  Module MUT := Mutators termkit progkit assertkit contractkit.
  Import MUT.
  Module LOG := ProgramLogic termkit progkit assertkit contractkit.
  Import LOG.
  Module SCMUT := SemiConcrete.Sound.Soundness termkit progkit assertkit contractkit.
  Import SCMUT.MUT.

  Module DynMutV1Soundness.

    Import DynMutV1.

    Global Instance inst_heap : Inst SymbolicHeap SCHeap :=
      instantiate_list.
    Global Instance instlaws_heap : InstLaws SymbolicHeap SCHeap.
    Proof. apply instantiatelaws_list. Qed.

    Global Instance inst_symbolicstate {Γ} : Inst (SymbolicState Γ) (SCState Γ) :=
      {| inst Σ ι '(MkSymbolicState δ h) := MkSCState (inst ι δ) (inst ι h);
         lift Σ '(MkSCState δ h) := MkSymbolicState (lift δ) (lift h);
      |}.

    Global Instance instlaws_symbolicState {Γ} : InstLaws (SymbolicState Γ) (SCState Γ).
    Proof.
      constructor.
      - intros ? ? []; cbn; now rewrite ?inst_lift.
      - intros ? ? ? ? []; cbn; now rewrite ?inst_subst.
    Qed.

    Definition DynamicMutatorArrow Γ1 Γ2 A B Σ0 : Type :=
      forall Σ1, Sub Σ0 Σ1 -> A Σ1 -> DynamicMutator Γ1 Γ2 B Σ1.

    Definition DynamicMutatorArrow' Γ1 Γ2 A B Σ0 : Type :=
      forall Σ1,
        Sub Σ0 Σ1 -> A Σ1 -> PathCondition Σ1 ->
        SymbolicState Γ1 Σ1 -> Outcome (DynamicMutatorError) (DynamicMutatorResult Γ2 B Σ1).

    Definition dmut_bind' {Γ1 Γ2 Γ3 A B Σ0}
               (ma : DynamicMutator Γ1 Γ2 A Σ0) (f : DynamicMutatorArrow' Γ2 Γ3 A B Σ0) : DynamicMutator Γ1 Γ3 B Σ0 :=
      fun (Σ1 : LCtx) (ζ01 : Sub Σ0 Σ1) pc1 (s1 : SymbolicState Γ1 Σ1) =>
        outcome_bind (ma Σ1 ζ01 pc1 s1) (fun r : DynamicMutatorResult Γ2 A Σ1 =>
        outcome_bind (f (dmutres_context r) (sub_comp ζ01 (dmutres_substitution r)) (dmutres_result_value r) (dmutres_pathcondition r) (dmutres_result_state r))
                     (fun r2 : DynamicMutatorResult Γ3 B (dmutres_context r) => outcome_pure (cosubst_dmutres (dmutres_substitution r) r2))).


    Local Notation "[ ι ] x == y" := (inst ι x = inst ι y) (at level 50).

    (* Read: If ς is equivalent to t in ι, then substituting t for ς is equivalent to the identity. *)
    Lemma inst_single_shift {Σ ς σ} (ςInΣ : ς :: σ ∈ Σ) (t : Term (Σ - (ς :: σ)) σ) ι :
      [ ι ] term_var ς == subst (sub_shift ςInΣ) t ->
      [ ι ] sub_comp (sub_single ςInΣ t) (sub_shift ςInΣ) == sub_id _.
    Proof.
      intros H.
      apply env_lookup_extensional; cbn.
      intros [] bIn.
      unfold sub_id, sub_comp, subst, SubstEnv, inst; cbn.
      rewrite ?env_lookup_map, ?env_lookup_tabulate.
      pose proof (occurs_check_var_spec ςInΣ bIn).
      destruct (occurs_check_var ςInΣ bIn) eqn:?.
      - dependent elimination e. cbn in H0. subst.
        rewrite lookup_sub_single_eq. symmetry. exact H.
      - f_equal.
        destruct H0. subst bIn.
        rewrite lookup_sub_single_neq.
        cbn. unfold sub_shift.
        rewrite env_lookup_tabulate.
        reflexivity.
    Qed.

    (* Avoid some Prop <-> Type confusion. *)
    Notation instpc ι pc := (@inst _ _ instantiate_pathcondition _ ι pc).

    (* A preorder on path conditions. This encodes that either pc1 belongs to a
       longer symbolic execution path (or that it's the same path, but with
       potentially some constraints substituted away). *)
    Definition entails {Σ} (pc1 pc0 : PathCondition Σ) : Prop :=
      forall (ι : SymInstance Σ),
        instpc ι pc1 ->
        instpc ι pc0.
    Infix "⊢" := (@entails _) (at level 80, no associativity).

    Lemma entails_cons {Σ} (pc1 pc2 : PathCondition Σ) (f : Formula Σ) :
      (pc1 ⊢ pc2 /\ (forall ι, (inst ι pc1 : Prop) -> inst ι f : Prop)) <-> pc1 ⊢ (f :: pc2)%list.
    Proof.
      split.
      - intros (pc12 & pc1f).
        intros ι ιpc1. cbn.
        unfold inst, inst_pathcondition. cbn.
        rewrite fold_right_1_10_prop.
        intuition.
      - intros pc1f2.
        split; intros ι ιpc1;
          specialize (pc1f2 ι ιpc1); cbn in pc1f2;
          unfold inst, inst_pathcondition in pc1f2; cbn in pc1f2;
          rewrite fold_right_1_10_prop in pc1f2;
          destruct pc1f2 as [Hf Hpc2]; auto.
    Qed.

    Global Instance preorder_entails {Σ} : PreOrder (@entails Σ).
    Proof.
      split.
      - intuition.
      - intros x y z xy yz ι ιx.
        eauto.
    Qed.

    Global Instance proper_subst_pc_entails {Σ1 Σ2} {ζ}: Proper ((@entails Σ1) ==> (@entails Σ2)) (subst ζ).
    Proof.
      intros pc1 pc2 pc12 ι.
      rewrite ?inst_subst; eauto.
    Qed.

    Definition entails_eq {AT A} `{Inst AT A} {Σ} (pc : PathCondition Σ) (a0 a1 : AT Σ) : Prop :=
      forall (ι : SymInstance Σ), instpc ι pc -> inst ι a0 = inst ι a1.
    Notation "pc ⊢ a0 == a1" :=
      (entails_eq pc a0 a1)
      (at level 80, a0 at next level, no associativity).

    Global Instance proper_subst_entails_eq {AT A} `{InstLaws AT A} {Σ1 Σ2} {ζ : Sub Σ1 Σ2} {pc : PathCondition Σ1} :
      Proper ((entails_eq pc) ==> (entails_eq (subst ζ pc))) (subst ζ).
    Proof.
      intros a1 a2 a12 ι.
      rewrite ?inst_subst; auto.
    Qed.

    Global Instance proper_subst_entails_eq_pc
           {Σ1 Σ2} `{InstLaws AT A}
           (pc : PathCondition Σ2):
      Proper (entails_eq pc ==> eq ==> entails_eq pc) (@subst AT _ Σ1 Σ2).
    Proof.
      intros ζ1 ζ2 ζ12 a1 a2 [] ι ιpc.
      rewrite ?inst_subst.
      now rewrite (ζ12 ι ιpc).
    Qed.


    (* Not sure this instance is a good idea...
       This seems to cause rewrite to take very long... *)
    Global Instance proper_entails_pc_iff
           {Σ} `{InstLaws AT A}
           (pc : PathCondition Σ):
         Proper (entails_eq pc ==> iff) (entails pc).
    Proof.
      intros pc1 pc2 pc12.
      split; intros HYP ι ιpc;
        specialize (pc12 ι ιpc);
        specialize (HYP ι ιpc);
        congruence.
    Qed.

    Global Instance proper_entails_eq_impl {AT A} `{Inst AT A} {Σ} : Proper (flip (@entails Σ) ==> eq ==> eq ==> impl) entails_eq.
    Proof.
      intros pc1 pc2 pc21 a1 _ [] a2 _ [] eq1 ι ιpc2; eauto.
    Qed.

    Global Instance proper_entails_eq_flip_impl {AT A} `{Inst AT A} {Σ} : Proper ((@entails Σ) ==> eq ==> eq ==> flip impl) entails_eq.
    Proof.
      intros pc1 pc2 pc21 a1 _ [] a2 _ [] eq1 ι ιpc2; eauto.
    Qed.

    Global Instance equiv_entails_eq `{instA : Inst AT A} {Σ} {pc : PathCondition Σ} : Equivalence (entails_eq pc).
    Proof.
      split.
      - intuition.
      - intros x y xy ι ipc; specialize (xy ι); intuition.
      - intros x y z xy yz ι ipc.
        specialize (xy ι ipc).
        specialize (yz ι ipc).
        intuition.
    Qed.

    Global Instance proper_entails_eq_flip_impl_pc {AT A} `{Inst AT A} {Σ} {pc : PathCondition Σ}: Proper (entails_eq pc ==> entails_eq pc ==> iff) (entails_eq pc).
    Proof.
      split; intros Heq.
      - transitivity x; [|transitivity x0]; easy.
      - transitivity y; [|transitivity y0]; easy.
    Qed.

    Global Instance proper_entails_eq_sub_comp
           {Σ1 Σ2 Σ3} {ζ : Sub Σ1 Σ2} (pc : PathCondition Σ3):
      Proper (entails_eq pc ==> entails_eq pc) (sub_comp ζ).
    Proof.
      intros ζ1 ζ2 ζ12.
      unfold sub_comp; rewrite ζ12; easy.
    Qed.

    (* A proper preorder on the result of a symbolic execution. *)
    Definition dmutres_geq {AT A} `{Subst AT, Inst AT A} {Γ Σ} (r1 r2 : DynamicMutatorResult Γ AT Σ) : Prop :=
      match r1 , r2 with
      | MkDynMutResult ζ1 pc1 a1 s1, MkDynMutResult ζ2 pc2 a2 s2 =>
        exists ζ12,
        pc2 ⊢ subst ζ12 pc1 /\
        pc2 ⊢ subst ζ12 ζ1 == ζ2 /\
        pc2 ⊢ subst ζ12 a1 == a2 /\
        pc2 ⊢ subst ζ12 s1 == s2
      end.

    Global Instance dmutres_geq_preorder {Γ AT A Σ} `{Subst AT, SubstLaws AT, Inst AT A, InstLaws AT A} : PreOrder (@dmutres_geq AT A _ _ Γ Σ).
    Proof.
      split.
      - intros [ζ1 pc1 a1 s1]. exists (sub_id _).
        rewrite ?subst_sub_id; easy.
      - intros [Σ1 ζ1 pc1 a1 s1] [Σ2 ζ2 pc2 a2 s2] [Σ3 ζ3 pc3 a3 s3] (ζ12 & pc21 & ζ12' & a12 & s12) (ζ23 & pc32 & ζ23' & a23 & s23).
        exists (sub_comp ζ12 ζ23).
        rewrite ?subst_sub_comp; repeat split.
        + now rewrite pc32, pc21.
        + now rewrite <-ζ23', pc32, ζ12'.
        + now rewrite <-a23, pc32, a12.
        + now rewrite <-s23, pc32, s12.
    Qed.

    (* A frequent special case. *)
    Lemma dmutres_geq_syntactic {Γ A V Σ} `{InstLaws A V} :
      forall r1 r2 : DynamicMutatorResult Γ A Σ,
        (match r1 , r2 with
         | MkDynMutResult ζ1 pc1 a1 s1, MkDynMutResult ζ2 pc2 a2 s2 =>
           exists ζ12,
           ζ2  = sub_comp ζ1 ζ12 /\
           pc2 = subst ζ12 pc1 /\
           a2  = subst ζ12 a1 /\
           s2  = subst ζ12 s1
         end
        ) ->
        dmutres_geq r1 r2.
    Proof.
      intros [Σ1 ζ1 pc1 a1 s1] [Σ2 ζ2 pc2 a2 s2] (ζ12 & ζ12' & pc12 & a12 & s12).
      exists ζ12; intuition.
      intros ι ιpc2; intuition.
    Qed.


    Definition dmutres_equiv {AT A} `{Subst AT, Inst AT A} {Γ Σ} (r1 r2 : DynamicMutatorResult Γ AT Σ) : Prop :=
      dmutres_geq r1 r2 /\ dmutres_geq r2 r1.

    Global Instance dmutres_equiv_equiv {Γ Σ} `{Subst AT, SubstLaws AT, Inst AT A, InstLaws AT A} : Equivalence (@dmutres_equiv _ _ _ _ Γ Σ).
    Proof.
      split.
      - easy.
      - intros x y [xy yx]; easy.
      - intros x y z [xy yx] [yz zy]; split; transitivity y; easy.
    Qed.

    Lemma dmutres_geq_pre_comp {AT A} `{Inst AT A, Subst AT} {Γ Σ}
          (r1 r2 : DynamicMutatorResult Γ AT Σ) {Σ0} (ζ : Sub Σ0 Σ) :
        dmutres_geq r1 r2 ->
        dmutres_geq (cosubst_dmutres ζ r1) (cosubst_dmutres ζ r2).
    Proof.
      destruct r1 as [Σ1 ζ1 pc1 a1 s1].
      destruct r2 as [Σ2 ζ2 pc2 a2 s2].
      intros [ζ23]. exists ζ23. intuition.
      unfold sub_comp.
      now rewrite subst_assoc, H1.
    Qed.

    Lemma subst_sub_id_right {Σ1 Σ2} (ζ : Sub Σ1 Σ2) :
      subst ζ (sub_id _) = ζ.
    Proof. exact (sub_comp_id_left ζ). Qed.

    Lemma dmutres_try_assume_eq_spec {Γ Σ0 σ} (pc0 : PathCondition Σ0) (t1 t2 : Term Σ0 σ) (s0 : SymbolicState Γ Σ0) :
      OptionSpec
        (dmutres_equiv (MkDynMutResult (sub_id _) (cons (formula_eq t1 t2) pc0) tt s0))
        True
        (dmutres_try_assume_eq pc0 t1 t2 s0).
    Proof.
      destruct t1; cbn; try (constructor; auto; fail).
      destruct (occurs_check ςInΣ t2) eqn:?; constructor; auto.
      apply (@occurs_check_sound _ _ (@OccursCheckTerm _) OccursCheckLawsTerm) in Heqo.
      subst t2.
      split.
      - exists (sub_single ςInΣ t).
        repeat split.
        + unfold subst at 2, SubstList; cbn.
          rewrite <-subst_sub_comp, sub_comp_shift_single, subst_sub_id, lookup_sub_single_eq.
          now rewrite <-entails_cons.
        + now rewrite subst_sub_id_right.
      - exists (sub_shift ςInΣ).
        repeat split; intros ι [eq ιpc]%inst_pathcondition_cons.
        + now rewrite <-subst_sub_comp, inst_subst, (inst_single_shift ςInΣ t ι eq), inst_sub_id.
        + refine (inst_single_shift ςInΣ t ι eq).
        + now rewrite <-subst_sub_comp, inst_subst, (inst_single_shift ςInΣ t ι eq), inst_sub_id.
    Qed.

    Opaque dmutres_try_assume_eq_spec.

    Lemma dmutres_assume_formula_spec {Γ Σ} (pc : PathCondition Σ) (fml : Formula Σ) (s : SymbolicState Γ Σ) :
      dmutres_equiv (dmutres_assume_formula pc fml s) (MkDynMutResult (sub_id _) (cons fml pc) tt s).
    Proof.
      destruct fml; cbn; try easy.
      destruct (dmutres_try_assume_eq_spec pc t1 t2 s); try easy. clear H.
      destruct (dmutres_try_assume_eq_spec pc t2 t1 s); try easy.
      rewrite <-H.
      split; cbn; exists (sub_id _);
        rewrite ?subst_sub_id; intuition;
          (* do we need a notion of pc-entails-formula and Proper instances for cons-formula-pathcondition? *)
          intros ι ιpc;
          rewrite ?inst_pathcondition_cons in *; cbn; intuition.
    Qed.

    (* Relate two symbolic instances at different points during execution. This
       essentially encodes a preorder on the total space { Σ & SymInstance Σ },
       which encodes that ι2 is a future of ι1, i.e. it is derived by compatible
       for existing variables and values for new universal variables. *)
    Definition syminstance_rel {Σ1 Σ2} (ζ : Sub Σ1 Σ2) (ι1 : SymInstance Σ1) (ι2 : SymInstance Σ2) : Prop :=
      inst ι2 ζ = ι1.
    Hint Unfold syminstance_rel : core.

    Lemma syminstance_rel_refl {Σ} (ι : SymInstance Σ) :
      syminstance_rel (sub_id Σ) ι ι.
    Proof. apply inst_sub_id. Qed.

    Lemma syminstance_rel_refl_inv {Σ} (ι1 ι2 : SymInstance Σ) :
      syminstance_rel (sub_id Σ) ι1 ι2 -> ι2 = ι1.
    Proof. unfold syminstance_rel. now rewrite inst_sub_id. Qed.

    Lemma syminstance_rel_snoc {Σ1 Σ2 x τ} (ζ : Sub Σ1 Σ2) (ι1 : SymInstance Σ1) ι2 :
      forall t v,
        syminstance_rel (env_snoc ζ (x,τ) t) (env_snoc ι1 (x,τ) v) ι2 <->
        syminstance_rel ζ ι1 ι2 /\ v = inst ι2 t.
    Proof.
      unfold syminstance_rel. intros. split.
      - cbn; intros.
        now dependent elimination H.
      - cbn; intros []; subst; now cbn.
    Qed.

    Lemma syminstance_rel_comp {Σ0 Σ1 Σ2} (ζ1 : Sub Σ0 Σ1) (ζ2 : Sub Σ1 Σ2)
          (ι0 : SymInstance Σ0) (ι2 : SymInstance Σ2):
      syminstance_rel (sub_comp ζ1 ζ2) ι0 ι2 <->
      syminstance_rel ζ1 ι0 (inst ι2 ζ2).
    Proof. unfold syminstance_rel. now rewrite <- inst_subst. Qed.

    Lemma syminstance_rel_trans {Σ0 Σ1 Σ2} {ζ1 : Sub Σ0 Σ1} {ζ2 : Sub Σ1 Σ2}
          {ι0 : SymInstance Σ0} {ι1 : SymInstance Σ1} {ι2 : SymInstance Σ2} :
      syminstance_rel ζ1 ι0 ι1 -> syminstance_rel ζ2 ι1 ι2 ->
      syminstance_rel (sub_comp ζ1 ζ2) ι0 ι2.
    Proof. intros. apply syminstance_rel_comp. congruence. Qed.

    Lemma syminstance_rel_wk1 {Σ : NCtx 𝑺 Ty} {x τ} (ι : SymInstance Σ) (v : Lit τ) :
      syminstance_rel sub_wk1 ι (ι ► ((x, τ) ↦ v)).
    Proof. apply inst_sub_wk1. Qed.

    Lemma syminstance_rel_up {Σ1 Σ2 x τ} (ζ : Sub Σ1 Σ2) (ι1 : SymInstance Σ1) ι2 :
      forall v,
        syminstance_rel (sub_up1 ζ) (env_snoc ι1 (x,τ) v) (env_snoc ι2 (x,τ) v) <->
        syminstance_rel ζ ι1 ι2.
    Proof.
      unfold syminstance_rel. intros v.
      change (inst (ι2 ► (x :: τ ↦ v)) (sub_comp ζ sub_wk1) ► (x :: τ ↦ v) =
              ι1 ► (x :: τ ↦ v) <-> inst ι2 ζ = ι1).
      unfold sub_comp. rewrite inst_subst, inst_sub_wk1.
      split; intros H.
      - now dependent elimination H.
      - now f_equal.
    Qed.

    Section StateProp.

      Definition StateProperty Γ A Σ :=
        forall Σ1, Sub Σ Σ1 -> PathCondition Σ1 -> A Σ1 -> SymbolicState Γ Σ1 -> Prop.

      Definition stateprop_downwards_closed {Γ Σ AT A} `{Inst AT A} `{Subst AT} (p : StateProperty Γ AT Σ) : Prop :=
        forall Σ1 (ζ1 : Sub Σ Σ1) pc1 a1 s1 Σ2 (ζ2 : Sub Σ Σ2) pc2 a2 s2,
          dmutres_geq (MkDynMutResult ζ1 pc1 a1 s1) (MkDynMutResult ζ2 pc2 a2 s2) ->
          p Σ1 ζ1 pc1 a1 s1 -> p Σ2 ζ2 pc2 a2 s2.

      (* The property always holds vacuously on inconsistent paths. *)
      Definition stateprop_vacuous {Γ AT Σ} (p : StateProperty Γ AT Σ) : Prop :=
        forall Σ1 (ζ1 : Sub Σ Σ1) pc a1 s1, inconsistent pc -> p Σ1 ζ1 pc a1 s1.

      Definition stateprop_impl {Γ A Σ} (P Q : StateProperty Γ A Σ) : Prop :=
        forall Σ1 (ζ : Sub Σ Σ1) (pc : PathCondition Σ1) (a : A Σ1) (s : SymbolicState Γ Σ1),
          P Σ1 ζ pc a s -> Q Σ1 ζ pc a s.

      Definition stateprop_specialize {Γ A Σ1 Σ2} (ζ : Sub Σ1 Σ2) (p: StateProperty Γ A Σ1) :
        StateProperty Γ A Σ2 := fun Σ3 ζ3 => p Σ3 (sub_comp ζ ζ3).

      Definition stateprop_lift {Γ AT A Σ} {instA : Inst AT A} (ι : SymInstance Σ) (POST : A -> SCState Γ -> Prop) :
        StateProperty Γ AT Σ :=
        fun Σ1 ζ1 pc1 v1 s1 =>
          forall ι1,
            syminstance_rel ζ1 ι ι1 ->
            (inst ι1 pc1 : Prop) ->
            POST (inst ι1 v1) (inst ι1 s1).

      Lemma stateprop_lift_dcl {Γ AT A Σ1} `{Inst AT A} `{InstLaws AT A} (ι1 : SymInstance Σ1) (POST : A -> SCState Γ -> Prop) :
        stateprop_downwards_closed (stateprop_lift ι1 POST).
      Proof.
        unfold stateprop_downwards_closed, stateprop_lift.
        intros Σ2 ζ2 pc2 a2 s2 Σ3 ζ3 pc3 a3 s3.
        intros [ζ23 (pc23 & ζ23' & a23 & s23)] Hpost ι3 rel13 Hpc3.
        specialize (Hpost (inst ι3 ζ23)).
        unfold syminstance_rel in Hpost, rel13.
        rewrite <-?inst_subst, (ζ23' ι3 Hpc3), (a23 ι3 Hpc3), (s23 ι3 Hpc3) in Hpost.
        intuition.
      Qed.

      Lemma stateprop_lift_vac {Γ AT A Σ1} `{Inst AT A} (ι1 : SymInstance Σ1) (POST : A -> SCState Γ -> Prop) :
        stateprop_vacuous (stateprop_lift ι1 POST).
      Proof. unfold stateprop_vacuous, stateprop_lift. intuition. Qed.

    End StateProp.

    Section ResultProp.

      Definition ResultProperty Γ A Σ :=
        DynamicMutatorResult Γ A Σ -> Prop.

      Definition resultprop_specialize {Γ A Σ1 Σ2} (ζ : Sub Σ1 Σ2) :
        ResultProperty Γ A Σ1 -> ResultProperty Γ A Σ2 :=
        fun p r => p (cosubst_dmutres ζ r).

      Definition resultprop_downwards_closed {Γ AT Σ A} `{Inst AT A, Subst AT} (p : ResultProperty Γ AT Σ) : Prop :=
        forall (r1 r2 : DynamicMutatorResult Γ AT Σ),
          dmutres_geq r1 r2 -> p r1 -> p r2.

      Definition resultprop_vacuous {Γ AT Σ A} `{Inst AT A} (p : ResultProperty Γ AT Σ) : Prop :=
        forall r, inconsistent (dmutres_pathcondition r) -> p r.

      Lemma resultprop_specialize_vac {Γ A AV Σ1 Σ2} `{Inst A AV} (ζ : Sub Σ1 Σ2)
            (P : ResultProperty Γ A Σ1) (P_vac : resultprop_vacuous P) :
        resultprop_vacuous (resultprop_specialize ζ P).
      Proof.
        intros [Σ3 ζ23 pc3 a3 s3]; unfold resultprop_specialize; cbn.
        intros HYP. apply P_vac; auto.
      Qed.

      Lemma resultprop_specialize_dcl {Γ A AV Σ1 Σ2} `{InstLaws A AV} (ζ : Sub Σ1 Σ2)
            (POST : ResultProperty Γ A Σ1) (POST_dcl : resultprop_downwards_closed POST) :
        resultprop_downwards_closed (resultprop_specialize ζ POST).
      Proof.
        unfold resultprop_downwards_closed, resultprop_specialize.
        eauto using POST_dcl, dmutres_geq_pre_comp.
      Qed.

      Lemma resultprop_specialize_id {Γ A Σ} (P : ResultProperty Γ A Σ) :
        forall r, resultprop_specialize (sub_id _) P r <-> P r.
      Proof.
        intros [Σ' ζ pc a s]; unfold resultprop_specialize; cbn.
        now rewrite sub_comp_id_left.
      Qed.

      Lemma resultprop_specialize_comp {Γ A Σ1 Σ2 Σ3} (ζ12 : Sub Σ1 Σ2) (ζ23 : Sub Σ2 Σ3) (P : ResultProperty Γ A Σ1) :
        forall r,
          resultprop_specialize (sub_comp ζ12 ζ23) P r <->
          resultprop_specialize ζ23 (resultprop_specialize ζ12 P) r.
      Proof.
        intros [Σ' ζ pc a s]; unfold resultprop_specialize; cbn.
        now rewrite sub_comp_assoc.
      Qed.

      Definition resultprop_lift {Γ AT A Σ1} {instA : Inst AT A} (ι1 : SymInstance Σ1) (POST : A -> SCState Γ -> Prop) :
        ResultProperty Γ AT Σ1 :=
        fun dres =>
          match dres with
          | MkDynMutResult ζ2 pc2 a2 s2 =>
            stateprop_lift ι1 POST ζ2 pc2 a2 s2
          end.

      Definition resultprop_lift_dcl {Γ AT A Σ1} `{InstLaws AT A} (ι1 : SymInstance Σ1) (POST : A -> SCState Γ -> Prop) :
        resultprop_downwards_closed (resultprop_lift ι1 POST).
      Proof.
        unfold resultprop_downwards_closed, resultprop_lift.
        intros [Σ3 ζ3 pc3 a3 s3] [Σ4 ζ4 pc4 a4 s4].
        apply stateprop_lift_dcl.
      Qed.

      Definition resultprop_lift_vac {Γ AT A Σ1} `{InstLaws AT A} (ι1 : SymInstance Σ1) (POST : A -> SCState Γ -> Prop) :
        resultprop_vacuous (resultprop_lift ι1 POST).
      Proof.
        unfold resultprop_vacuous, resultprop_lift, stateprop_lift.
        intros [Σ2 ζ2 pc2 a2 s2] Hpc2; cbn in *. intuition.
      Qed.


      Global Instance resultprop_lift_proper {Γ AT A Σ} `{InstLaws AT A} {ι : SymInstance Σ} {POST : A -> SCState Γ -> Prop} :
        Proper (dmutres_geq ==> impl) (resultprop_lift ι POST) := resultprop_lift_dcl _ _.

      Global Instance resultprop_lift_proper_equiv {Γ AT A Σ} `{InstLaws AT A} {ι : SymInstance Σ} {POST : A -> SCState Γ -> Prop} :
        Proper (dmutres_equiv ==> impl) (resultprop_lift ι POST).
      Proof.
        intros r1 r2 (r12 & r21).
        now eapply resultprop_lift_proper.
      Qed.


    End ResultProp.

    Section Vacuous.

      Definition outcome_vac `{Inst AT A} {Γ Σ} (pc : PathCondition Σ) (o : Outcome (DynamicMutatorError) (DynamicMutatorResult Γ AT Σ)) : Prop :=
        forall (P : ResultProperty Γ AT Σ) (P_vac : resultprop_vacuous P),
          inconsistent pc -> outcome_satisfy o contradiction P.
      Local Hint Unfold outcome_satisfy : core.
      Local Hint Unfold outcome_vac : core.

      Definition dmut_vac `{Inst AT A} {Γ1 Γ2 Σ0} (d : DynamicMutator Γ1 Γ2 AT Σ0) : Prop :=
        forall Σ1 (ζ01 : Sub Σ0 Σ1) pc1 s1, outcome_vac pc1 (d Σ1 ζ01 pc1 s1).
      Local Hint Unfold dmut_vac : core.

      (* TODO: It would be great to reformulate this to use the above. *)
      Definition dmut_arrow_vac `{Inst AT A, Inst BT B} {Γ1 Γ2 Σ0}
        (f : DynamicMutatorArrow Γ1 Γ2 AT BT Σ0) : Prop :=
        forall Σ1 (ζ01 : Sub Σ0 Σ1) pc1 (a1 : AT Σ1) s1,
          outcome_vac pc1 (f Σ1 ζ01 a1 Σ1 (sub_id _) pc1 s1).
      Local Hint Unfold dmut_arrow_vac : core.

      Definition dmut_arrow_vac' `{Inst AT A, Inst BT B} {Γ1 Γ2 Σ0}
        (f : DynamicMutatorArrow' Γ1 Γ2 AT BT Σ0) : Prop :=
        forall Σ1 (ζ01 : Sub Σ0 Σ1) pc1 (a1 : AT Σ1) s1,
          outcome_vac pc1 (f Σ1 ζ01 a1 pc1 s1).
      Local Hint Unfold dmut_arrow_vac' : core.

      Lemma dmut_pure_vac `{Subst AT, Inst AT A} {Γ Σ} (a : AT Σ) :
        dmut_vac (dmut_pure (Γ := Γ) a).
      Proof. unfold dmut_pure; auto. Qed.
      Local Hint Resolve dmut_pure_vac : core.

      Lemma dmut_block_vac `{Inst AT A} {Γ1 Γ2 Σ} :
        dmut_vac (@dmut_block Γ1 Γ2 AT Σ).
      Proof. unfold dmut_block; auto. Qed.
      Local Hint Resolve dmut_block_vac : core.

      Lemma dmut_contradiction_vac `{Inst AT A} {D Γ1 Γ2 Σ} func msg data :
        dmut_vac (@dmut_contradiction Γ1 Γ2 AT Σ D func msg data).
      Proof.
        unfold dmut_contradiction, dmut_vac, outcome_vac; cbn; intros.
        constructor; auto. constructor; auto.
      Qed.
      Local Hint Resolve dmut_contradiction_vac : core.

      Lemma dmut_fail_vac `{Inst AT A} {D Γ1 Γ2 Σ} func msg data :
        dmut_vac (@dmut_fail Γ1 Γ2 AT Σ D func msg data).
      Proof. unfold dmut_fail, dmut_vac, outcome_vac, contradiction; cbn; auto. Qed.
      Local Hint Resolve dmut_fail_vac : core.

      Lemma dmut_bind_vac' `{Inst AT A, Inst BT B} {Γ1 Γ2 Γ3 Σ0}
        (d : DynamicMutator Γ1 Γ2 AT Σ0) (vac_d : dmut_vac d)
        (f : DynamicMutatorArrow' Γ2 Γ3 AT BT Σ0) (vac_f : dmut_arrow_vac' f) :
        dmut_vac (dmut_bind' d f).
      Proof. (* LESS IMPORTANT *) Admitted.
      Local Hint Resolve dmut_bind_vac' : core.

      Lemma dmut_bind_vac `{Inst AT A, Inst BT B} {Γ1 Γ2 Γ3 Σ0}
        (d : DynamicMutator Γ1 Γ2 AT Σ0) (vac_d : dmut_vac d)
        (f : DynamicMutatorArrow Γ2 Γ3 AT BT Σ0) (vac_f : dmut_arrow_vac f) :
        dmut_vac (dmut_bind d f).
      Proof. (* MORE IMPORTANT *) Admitted.
      Local Hint Resolve dmut_bind_vac : core.

      Lemma dmut_sub_vac `{Inst AT A} {Γ1 Γ2 Σ0} (d : DynamicMutator Γ1 Γ2 AT Σ0) (vac_d : dmut_vac d) :
        forall (Σ1 : LCtx) (ζ1 : Sub Σ0 Σ1), dmut_vac (dmut_sub ζ1 d).
      Proof. unfold dmut_sub; auto. Qed.
      Local Hint Resolve dmut_sub_vac : core.

      Lemma dmut_bind_right_vac `{Inst AT A, Inst BT B} {Γ1 Γ2 Γ3 Σ0}
        (d1 : DynamicMutator Γ1 Γ2 AT Σ0) (d2 : DynamicMutator Γ2 Γ3 BT Σ0) (vac_d1 : dmut_vac d1) (vac_d2 : dmut_vac d2) :
        dmut_vac (dmut_bind_right d1 d2).
      Proof. unfold dmut_bind_right; eauto. Qed.
      Local Hint Resolve dmut_bind_right_vac : core.

      Local Hint Extern 5 (outcome_vac _ (dmut_bind_right _ _ _ _ _)) =>
        apply dmut_bind_right_vac : core.
      Local Hint Extern 5 (outcome_vac _ (dmut_bind _ _ _ _ _)) =>
        apply dmut_bind_vac; unfold dmut_arrow_vac; intros; destruct_conjs : core.
      Local Hint Extern 5 (outcome_vac _ (dmut_pure _ _ _ _)) =>
        apply dmut_pure_vac : core.

      Lemma dmut_fmap_vac `{Subst AT, Subst BT, Inst AT A, Inst BT B} {Γ1 Γ2 Σ0}
            (da : DynamicMutator Γ1 Γ2 AT Σ0) (da_vac : dmut_vac da)
            (f : forall Σ1, Sub Σ0 Σ1 -> AT Σ1 -> BT Σ1) :
        dmut_vac (dmut_fmap da f).
      Proof. unfold dmut_fmap; auto. Qed.
      Local Hint Resolve dmut_fmap_vac : core.

      Lemma dmut_fmap2_vac `{Subst AT, Subst BT, Subst CT, Inst AT A, Inst BT B, Inst CT C} {Γ1 Γ2 Γ3 Σ0}
            (da : DynamicMutator Γ1 Γ2 AT Σ0) (da_vac : dmut_vac da)
            (db : DynamicMutator Γ2 Γ3 BT Σ0) (db_vac : dmut_vac db)
            (f : forall Σ1, Sub Σ0 Σ1 -> AT Σ1 -> BT Σ1 -> CT Σ1) :
        dmut_vac (dmut_fmap2 da db f).
      Proof. unfold dmut_fmap2; auto. Qed.
      Local Hint Resolve dmut_fmap2_vac : core.

      Lemma dmut_pair_vac `{Subst AT, Subst BT, Inst AT A, Inst BT B} {Γ1 Γ2 Γ3 Σ0}
            (da : DynamicMutator Γ1 Γ2 AT Σ0) (da_vac : dmut_vac da)
            (db : DynamicMutator Γ2 Γ3 BT Σ0) (db_vac : dmut_vac db) :
        dmut_vac (dmut_pair da db).
      Proof. unfold dmut_pair; eauto. Qed.
      Local Hint Resolve dmut_pair_vac : core.
      Local Hint Unfold outcome_satisfy : core.

      Lemma dmut_demonic_binary_vac `{Inst AT A} {Γ1 Γ2 Σ0}
        (d1 d2 : DynamicMutator Γ1 Γ2 AT Σ0) (vac_d1 : dmut_vac d1) (vac_d2 : dmut_vac d2) :
        dmut_vac (dmut_demonic_binary d1 d2).
      Proof.
        unfold dmut_demonic_binary.
        unfold dmut_vac in *.
        unfold outcome_vac in *.
        now cbn; eauto.
      Qed.

      Local Hint Resolve dmut_demonic_binary_vac : core.

      Local Hint Extern 5 (outcome_vac _ (dmut_demonic_binary _ _ _ _ _)) =>
        apply dmut_demonic_binary_vac : core.

      Lemma dmut_angelic_binary_vac `{Inst AT A} {Γ1 Γ2 Σ0}
        (d1 d2 : DynamicMutator Γ1 Γ2 AT Σ0) (vac_d1 : dmut_vac d1) (vac_d2 : dmut_vac d2) :
        dmut_vac (dmut_angelic_binary d1 d2).
      Proof.
        unfold dmut_angelic_binary.
        unfold dmut_vac in *.
        unfold outcome_vac in *.
        now cbn; eauto.
      Qed.
      Local Hint Resolve dmut_angelic_binary_vac : core.

      Lemma dmut_angelic_list_vac {AT A} `{Subst AT, Inst AT A} {Γ1 Γ2 Σ}
            {D} {func : string} {msg : string} {data:D}
            (l : list (DynamicMutator Γ1 Γ2 AT Σ)) :
        List.Forall dmut_vac l ->
        dmut_vac (dmut_angelic_list func msg data l).
      Proof.
        induction 1 as [|r rs vacr vacrs]; cbn; eauto.
        generalize rs at 1.
        intros rs'; destruct rs'; auto.
      Qed.
      Local Hint Resolve dmut_angelic_list_vac : core.

      Lemma dmut_demonic_list_vac {AT A} {F : Type} `{Subst AT, Inst AT A} {Γ1 Γ2 Σ} (l : list (DynamicMutator Γ1 Γ2 AT Σ)) :
        List.Forall dmut_vac l ->
        dmut_vac (dmut_demonic_list l).
      Proof.
        induction 1 as [|r rs vacr vacrs]; cbn; eauto.
        generalize rs at 1.
        intros rs'; destruct rs'; auto.
      Qed.
      Local Hint Resolve dmut_demonic_list_vac : core.

      Lemma dmut_demonic_finite_vac {AT A} {F : Type} `{Subst AT, Inst AT A, finite.Finite F} {Γ Σ} (k : F -> DynamicMutator Γ Γ AT Σ) :
        (forall v, dmut_vac (k v)) ->
        dmut_vac (dmut_demonic_finite F k).
      Proof.
        intros kvac.
        unfold dmut_demonic_finite.
        enough (List.Forall dmut_vac (List.map k (finite.enum F))) by eauto.
        eapply List.Forall_forall.
        intros x [f [eq fInF]]%List.in_map_iff.
        subst x.
        now eapply kvac.
      Qed.
      Local Hint Resolve dmut_demonic_finite_vac : core.

      Lemma dmut_angelic_finite_vac {AT A} {F : Type} `{Subst AT, Inst AT A, finite.Finite F} {Γ Σ} (k : F -> DynamicMutator Γ Γ AT Σ) :
        (forall v, dmut_vac (k v)) ->
        dmut_vac (dmut_angelic_finite F k).
      Proof.
        intros kvac.
        unfold dmut_angelic_finite.
        enough (List.Forall dmut_vac (List.map k (finite.enum F))) by eauto.
        eapply List.Forall_forall.
        intros x [f [eq fInF]]%List.in_map_iff.
        subst x.
        now eapply kvac.
      Qed.
      Local Hint Resolve dmut_angelic_finite_vac : core.

      Lemma dmut_state_vac {AT A} `{Inst AT A} {Γ1 Γ2 Σ} (f : forall Σ' : LCtx, Sub Σ Σ' -> SymbolicState Γ1 Σ' -> AT Σ' * SymbolicState Γ2 Σ') :
        dmut_vac (dmut_state f).
      Proof.
        unfold dmut_vac, dmut_state, outcome_vac; intros.
        destruct (f Σ1 ζ01 s1); cbn. now apply P_vac.
      Qed.
      Local Hint Resolve dmut_state_vac : core.

      Lemma inconsistent_cons {Σ} {pc : PathCondition Σ} {f : Formula Σ} :
        inconsistent pc -> inconsistent (f :: pc)%list.
      Proof.
        intros ipc ι; cbn; unfold instpc, inst_pathcondition; cbn.
        rewrite fold_right_1_10_prop.
        intros [Hf Hl].
        exact (ipc _ Hl).
      Qed.

      Lemma dmutres_assume_formula_inconsistent {Γ Σ Σ1} {f : Formula Σ} {ζ1 : Sub Σ Σ1}
            {pc1 : PathCondition Σ1} {s1 : SymbolicState Γ Σ1} :
        inconsistent pc1 ->
        inconsistent (dmutres_pathcondition (dmutres_assume_formula pc1 (subst ζ1 f) s1)).
      Proof.
        intros ipc1 ι Hpc2.
        destruct (dmutres_assume_formula_spec pc1 (subst ζ1 f) s1) as [_ geq2].
        revert ι Hpc2 geq2.
        generalize (dmutres_assume_formula pc1 (subst ζ1 f) s1).
        intros [Σ2 ζ2 pc2 a2 s2] ι Hpc2 [ζ (pc21 & _)].
        cbn in *.
        eapply (ipc1 (inst ι ζ)).
        specialize (pc21 ι Hpc2).
        unfold inst, instantiate_pathcondition, inst_pathcondition in pc21.
        cbn in pc21.
        rewrite fold_right_1_10_prop in pc21.
        destruct pc21 as (Hf & Hpc1).
        change (instpc ι (subst ζ pc1)) in Hpc1.
        now rewrite inst_subst in Hpc1.
      Qed.

      Lemma dmut_assume_formula_vac {Γ Σ} (f : Formula Σ) :
        dmut_vac (@dmut_assume_formula Γ Σ f).
      Proof.
        unfold dmut_assume_formula.
        intros Σ1 ζ1 pc1 s1.
        destruct (try_solve_formula (subst ζ1 f)).
        - destruct b; auto.
        - intros P Pvac inc1.
          unfold outcome_satisfy; cbn.
          now eapply Pvac, dmutres_assume_formula_inconsistent.
      Qed.
      Local Hint Resolve dmut_assume_formula_vac : core.

      Lemma dmut_assume_formulas_vac {Γ Σ} (pc : PathCondition Σ) :
        dmut_vac (@dmut_assume_formulas Γ Σ pc).
      Proof.
        unfold dmut_assume_formulas.
        induction pc; cbn; eauto.
      Qed.
      Local Hint Resolve dmut_assume_formulas_vac : core.

      Lemma dmut_modify_vac {Γ Γ' Σ} (f : forall Σ', Sub Σ Σ' -> SymbolicState Γ Σ' -> SymbolicState Γ' Σ') :
        dmut_vac (dmut_modify f).
      Proof.
        unfold dmut_modify; eauto.
      Qed.
      Local Hint Resolve dmut_modify_vac : core.

      Lemma dmut_produce_chunk_vac {Γ Σ} (c : Chunk Σ) :
        dmut_vac (@dmut_produce_chunk Γ Σ c).
      Proof.
        unfold dmut_produce_chunk; eauto.
      Qed.
      Local Hint Resolve dmut_produce_chunk_vac : core.

      Lemma dmut_fresh_vac {AT A} `{Inst AT A} {Γ Σ σ x} (d : DynamicMutator Γ Γ AT (Σ ▻ (x :: σ))) (d_vac : dmut_vac d) :
        dmut_vac (dmut_fresh x σ d).
      Proof.
        unfold dmut_fresh, dmut_vac.
        intros Σ1 ζ01 pc1 s1 P Pvac ipc1.
        rewrite outcome_satisfy_map.
        eapply d_vac.
        - intros [Σ2 ζ2 pc2 a2 s2] incr.
          now eapply Pvac.
        - intros ι Hpc1.
          unfold wk1 in Hpc1.
          rewrite inst_subst in Hpc1.
          now eapply (ipc1 (inst ι sub_wk1)).
      Qed.

      Local Hint Resolve dmut_fresh_vac : core.

      Lemma dmut_freshtermvar_vac {Γ Σ σ x} :
        dmut_vac (@dmut_freshtermvar Γ Σ σ x).
      Proof. unfold dmut_freshtermvar; auto. Qed.
      Local Hint Resolve dmut_freshtermvar_vac : core.

      Lemma dmut_freshen_recordpat'_vac {Γ Σ σs Δ} (p : RecordPat σs Δ) :
        dmut_vac (@dmut_freshen_recordpat' 𝑺 id σs Δ p Γ Σ).
      Proof. induction p; cbn; eauto. Qed.
      Local Hint Resolve dmut_freshen_recordpat'_vac : core.

      Lemma dmut_freshen_recordpat_vac {Γ Σ R Δ} (p : RecordPat (𝑹𝑭_Ty R) Δ) :
        dmut_vac (@dmut_freshen_recordpat 𝑺 id R Δ p Γ Σ).
      Proof. unfold dmut_freshen_recordpat; eauto. Qed.
      Local Hint Resolve dmut_freshen_recordpat_vac : core.

      Lemma dmut_produce_vac {Γ Σ} (asn : Assertion Σ) :
        dmut_vac (@dmut_produce Γ Σ asn).
      Proof.
        induction asn; cbn [dmut_produce]; unfold dmut_assume_term; eauto.
        - apply dmut_bind_vac; auto.
          unfold dmut_arrow_vac; intros.
          destruct (term_get_sum a1) as [[]|]; eauto 10.
        - destruct (term_get_pair s) as [[]|]; eauto 10.
        - apply dmut_bind_vac; auto.
          unfold dmut_arrow_vac; intros.
          destruct (term_get_record a1); eauto.
        - destruct (term_get_union s) as [[]|]; eauto.
      Qed.
      Local Hint Resolve dmut_produce_vac : core.

      Lemma dmut_assert_formula_vac {Γ Σ} (f : Formula Σ) :
        dmut_vac (@dmut_assert_formula Γ Σ f).
      Proof.
        unfold dmut_assert_formula.
        intros Σ1 ζ1 pc1 s1.
        destruct (try_solve_formula (subst ζ1 f)).
        - destruct b; auto.
        - intros P Pvac inc1.
          unfold outcome_satisfy; cbn.
          split.
          + constructor. clear s1.
            eapply Forall_forall.
            intros E ιpc1.
            exfalso; eapply inc1; eauto.
          + now eapply Pvac, dmutres_assume_formula_inconsistent.
      Qed.
      Local Hint Resolve dmut_assert_formula_vac : core.

      Lemma dmut_modify_heap_vac {Γ Σ}
            (f : forall Σ', Sub Σ Σ' -> SymbolicHeap Σ' -> SymbolicHeap Σ') :
        dmut_vac (@dmut_modify_heap Γ Σ f).
      Proof.
        unfold dmut_modify_heap; eauto.
      Qed.
      Local Hint Resolve dmut_modify_heap_vac : core.

      Lemma dmut_put_heap_vac {Γ Σ} (h : SymbolicHeap Σ) :
        dmut_vac (@dmut_put_heap Γ Σ h).
      Proof.
        unfold dmut_put_heap; eauto.
      Qed.
      Local Hint Resolve dmut_put_heap_vac : core.

      Lemma dmut_get_heap_vac {Γ Σ} :
        dmut_vac (@dmut_get_heap Γ Σ).
      Proof.
        unfold dmut_get_heap; eauto.
      Qed.
      Local Hint Resolve dmut_get_heap_vac : core.

      Lemma dmut_consume_chunk_vac {Γ Σ} (c : Chunk Σ) :
        dmut_vac (@dmut_consume_chunk Γ Σ c).
      Proof.
        unfold dmut_consume_chunk.
        eapply dmut_bind_vac; eauto.
        intros Σ2 ζ2 pc2 a2 s2.
        eapply dmut_angelic_list_vac.
        eapply List.Forall_forall.
        intros d [[pc3 h2] (eq & r)]%List.in_map_iff.
        subst d; eauto.
      Qed.
      Local Hint Resolve dmut_consume_chunk_vac : core.

      (* Lemma dmut_angelic_vac {Γ1 Γ2 I AT A Σ} `{Inst AT A} *)
      (*       {ms : I -> DynamicMutator Γ1 Γ2 AT Σ} : *)
      (*   (exists i, dmut_vac (ms i)) -> *)
      (*   dmut_vac (dmut_angelic ms). *)
      (* Proof. *)
      (*   unfold dmut_angelic. *)
      (*   intros [i msvac] Σ1 ζ1 pc1 s1 P Pvac Hpc1. *)
      (*   cbn. exists i. now eapply msvac. *)
      (* Qed. *)
      (* Local Hint Resolve dmut_angelic_vac : core. *)

      Lemma dmut_consume_vac {Γ Σ} (asn : Assertion Σ) :
        dmut_vac (@dmut_consume Γ Σ asn).
      Proof.
        induction asn; cbn [dmut_consume];
          unfold dmut_assert_term, dmut_assume_term; eauto 10.
        - destruct (term_get_sum s) as [[s'|s']|s']; eauto.
          eapply dmut_angelic_binary_vac.
          + intros Σ1 ζ1 pc1 s1 P Pvac incpc1 [ι' Hpc1].
            exfalso. eapply (incpc1 _ Hpc1).
          + intros Σ1 ζ1 pc1 s1 P Pvac incpc1 [ι' Hpc1].
            exfalso. eapply (incpc1 _ Hpc1).
        - destruct (term_get_pair s) as [[t1 t2]|]; eauto.
          intros Σ1 ζ1 pc1 s1 P Pva incpc1 [ι' Hpc1].
          exfalso. eapply (incpc1 _ Hpc1).
        - destruct (term_get_record s).
          eauto.
          intros Σ1 ζ1 pc1 s1 P Pva incpc1 [ι' Hpc1].
          exfalso. eapply (incpc1 _ Hpc1).
        - intros Σ1 ζ1 pc1 s1 P Pva incpc1 [ι' Hpc1].
          exfalso. eapply (incpc1 _ Hpc1).
      Qed.
      Local Hint Resolve dmut_consume_vac : core.

      Lemma dmut_exec_vac {Γ Σ τ} (s : Stm Γ τ) :
        dmut_vac (@dmut_exec Γ τ Σ s).
      Proof.
        induction s; cbn [dmut_exec]; eauto.
      Admitted.
      Local Hint Resolve dmut_exec_vac : core.

      Lemma dmut_call_vac {Γ Δ τ Σ} (c : SepContract Δ τ) (ts : NamedEnv (Term Σ) Δ) :
        dmut_vac (@dmut_call Γ Δ τ Σ c ts).
      Proof. Admitted.
      Local Hint Resolve dmut_call_vac : core.

      Lemma dmut_leakcheck_vac {Γ Σ} :
        dmut_vac (@dmut_leakcheck Γ Σ).
      Proof. Admitted.
      Local Hint Resolve dmut_leakcheck_vac : core.

      Lemma dmut_contract_vac {Γ τ} (c : SepContract Γ τ) (s : Stm Γ τ)  :
        dmut_vac (@dmut_contract Γ τ c s).
      Proof. destruct c; cbn; eauto 10. Qed.

    End Vacuous.

    Definition resultprop_specialize_pc {Γ A Σ1 Σ2} (ζ : Sub Σ1 Σ2) (pc2 : PathCondition Σ2) :
      ResultProperty Γ A Σ1 -> ResultProperty Γ A Σ2 :=
      fun p r => dmutres_pathcondition r ⊢ subst (dmutres_substitution r) pc2 /\ p (cosubst_dmutres ζ r).

    Lemma resultprop_specialize_pc_dcl {Γ A AV Σ1 Σ2} `{InstLaws A AV}
          (ζ12 : Sub Σ1 Σ2) (pc2 : PathCondition Σ2)
          (POST : ResultProperty Γ A Σ1) (POST_dcl : resultprop_downwards_closed POST) :
      resultprop_downwards_closed (resultprop_specialize_pc ζ12 pc2 POST).
    Proof.
      unfold resultprop_downwards_closed, resultprop_specialize_pc.
      intros r3 r4 r34 [Hpc23 Hpost].
      split.
      - destruct r3 as [Σ3 ζ23 pc3 a3 s3].
        destruct r4 as [Σ4 ζ24 pc4 a4 s4].
        destruct r34 as [ζ34 ?].
        cbn in *. destruct_conjs.
        rewrite <- H4, <- subst_assoc.
        transitivity (subst ζ34 pc3); auto.
        now rewrite Hpc23.
      - refine (POST_dcl _ _ _ Hpost).
        now eapply dmutres_geq_pre_comp.
    Qed.

    Definition dmut_dcl {Γ1 Γ2 AT Σ0 A} `{Inst AT A, Subst AT} (d : DynamicMutator Γ1 Γ2 AT Σ0) : Prop :=
      forall Σ1 Σ2 (ζ01 : Sub Σ0 Σ1) pc1 (s1 : SymbolicState Γ1 Σ1) (ζ12 : Sub Σ1 Σ2) pc2 s2 ζ02,
        pc2 ⊢ subst ζ12 pc1 ->
        pc2 ⊢ subst ζ12 s1 == s2 ->
        pc2 ⊢ subst ζ12 ζ01 == ζ02 ->
        forall (P : ResultProperty Γ2 AT Σ1) (P_dcl : resultprop_downwards_closed P) (P_vac : resultprop_vacuous P)
               (Q : ResultProperty Γ2 AT Σ2) (PQ : forall r, resultprop_specialize_pc ζ12 pc2 P r -> Q r),
          outcome_satisfy (d Σ1 ζ01 pc1 s1) contradiction P ->
          outcome_satisfy (d Σ2 ζ02 pc2 s2) contradiction Q.

    Definition dmut_arrow_dcl {Γ1 Γ2 AT A BT B Σ0} `{Inst AT A, Subst AT, Inst BT B, Subst BT}
               (f : DynamicMutatorArrow Γ1 Γ2 AT BT Σ0) : Prop :=
      forall Σ1 Σ2 Σ3 Σ4 (ζ01 : Sub Σ0 Σ1) (ζ12 : Sub Σ1 Σ2) (ζ03 : Sub Σ0 Σ3) (ζ34 : Sub Σ3 Σ4) (ζ24 : Sub Σ2 Σ4) (pc2 : PathCondition Σ2) (pc4 : PathCondition Σ4) (a1 : AT Σ1) (a3 : AT Σ3) (s2 : SymbolicState Γ1 Σ2) (s4 : SymbolicState Γ1 Σ4),
        pc4 ⊢ subst ζ24 pc2 ->
        pc4 ⊢ subst (subst ζ24 ζ12) ζ01 == subst ζ34 ζ03 ->
        pc4 ⊢ subst (subst ζ24 ζ12) a1 == subst ζ34 a3 ->
        pc4 ⊢ subst ζ24 s2 == s4 ->
        forall (P : ResultProperty Γ2 BT Σ2) (P_dcl : resultprop_downwards_closed P) (P_vac : resultprop_vacuous P)
          (Q : ResultProperty Γ2 BT Σ4) (PQ : forall r, resultprop_specialize_pc ζ24 pc4 P r -> Q r),
          outcome_satisfy (f Σ1 ζ01 a1 Σ2 ζ12 pc2 s2) contradiction P ->
          outcome_satisfy (f Σ3 ζ03 a3 Σ4 ζ34 pc4 s4) contradiction Q.

    Lemma dmut_bind_dcl {AT A BT B} `{InstLaws BT B} `{InstLaws AT A}
          {Γ1 Γ2 Γ3 Σ0} (d : DynamicMutator Γ1 Γ2 AT Σ0) (d_dcl : dmut_dcl d)
          (f : DynamicMutatorArrow Γ2 Γ3 AT BT Σ0)
          (f_dcl : dmut_arrow_dcl f)
          (f_vac : dmut_arrow_vac f) :
      dmut_dcl (dmut_bind d f).
    Proof.
      unfold dmut_bind.
      intros Σ1 Σ2 ζ01 pc1 s1 ζ12 pc2 s2 ζ02 Hpc12 Hs12 Hζ12 P P_dcl P_vac Q PQ.
      rewrite ?outcome_satisfy_bind; cbn.
      eapply d_dcl; eauto.
      - clear - f_dcl P P_dcl P_vac H2 H6.
        unfold resultprop_downwards_closed.
        intros [Σ2 ζ12 pc2 a2 s2] [Σ3 ζ13 pc3 a3 s3] [ζ23 (Hpc23 & Hζ23 & Ha23 & Hs23)]; cbn in *.
        rewrite ?outcome_satisfy_bind; cbn.
        eapply f_dcl; eauto.
        + rewrite subst_sub_id_right, subst_sub_id.
          repeat unfold sub_comp.
          now rewrite subst_assoc, Hζ23.
        + now rewrite subst_sub_id, subst_sub_id_right.
        + (* rewrite inside bind? *)
          unfold resultprop_downwards_closed.
          intros [] [] Hgeq; cbn - [dmutres_geq].
          apply P_dcl.
          exact (dmutres_geq_pre_comp _ _ ζ12 Hgeq).
        + unfold resultprop_vacuous.
          intros [] Hpc; cbn in *. now apply P_vac.
        + intros [Σ4 ζ34 pc4 b4 s4]; unfold resultprop_specialize_pc; cbn.
          intros [Hpc34 HP]; revert HP. apply P_dcl.
          exists (sub_id _).
          rewrite ?subst_sub_id.
          unfold sub_comp.
          repeat split; try easy.
          now rewrite Hpc34, <-subst_assoc, Hζ23.
      - intros [Σ3 ζ23 pc3 a3 s3]; cbn.
        rewrite outcome_satisfy_bind; cbn.
        apply f_vac.
        intros [Σ4 ζ34 pc4 a4 s4]; cbn.
        intros.
        now apply P_vac.
      - intros [Σ3 ζ23 pc3 a3 s3]; unfold resultprop_specialize_pc; cbn.
        rewrite ?outcome_satisfy_bind; cbn.
        intros [Hpc23 Hpost]; revert Hpost.
        eapply f_dcl; rewrite ?subst_sub_id; try easy.
        + clear - Hζ12 Hpc23.
          unfold sub_comp.
          now rewrite <-subst_assoc, Hpc23, Hζ12.
        + unfold resultprop_downwards_closed.
          intros [] [] Hgeq; cbn - [dmutres_geq].
          apply P_dcl.
          exact (dmutres_geq_pre_comp _ _ (sub_comp ζ12 ζ23) Hgeq).
        + unfold resultprop_vacuous.
          intros [] Hpc; cbn in *. now apply P_vac.
        + intros [Σ4 ζ34 pc4 b4 s4]; unfold resultprop_specialize_pc; cbn.
          intros [Hpc34 Hpost].
          eapply PQ. split; cbn; unfold sub_comp.
          * now rewrite <-subst_assoc, <-Hpc23.
          * rewrite sub_comp_id_left in Hpost.
            unfold sub_comp in Hpost.
            now rewrite subst_assoc in Hpost.
    Qed.

    (* These should be kept abstract in the rest of the proof. If you need some
       property, add a lemma above. *)
    Local Opaque dmutres_try_assume_eq.
    Local Opaque dmutres_assume_formula.

    Section DownwardsClosure.

      Definition dmut_dcl' {Γ1 Γ2 AT Σ0 A} `{Inst AT A, Subst AT} (d : DynamicMutator Γ1 Γ2 AT Σ0) : Prop :=
        forall Σ1 Σ2 (ζ01 : Sub Σ0 Σ1) pc1 (s1 : SymbolicState Γ1 Σ1) (ζ12 : Sub Σ1 Σ2) pc2 s2 ζ02,
          pc2 ⊢ subst ζ12 pc1 ->
          pc2 ⊢ subst ζ12 s1 == s2 ->
          pc2 ⊢ subst ζ12 ζ01 == ζ02 ->
          forall (P : ResultProperty Γ2 AT Σ1) (P_dcl : resultprop_downwards_closed P) (P_vac : resultprop_vacuous P),
            outcome_satisfy (d Σ1 ζ01 pc1 s1) contradiction P ->
            outcome_satisfy (d Σ2 ζ02 pc2 s2) contradiction (resultprop_specialize_pc ζ12 pc2 P).

      Lemma dmut_dcl_dcl' {Γ1 Γ2 AT Σ0 A} `{Inst AT A, Subst AT}
            (d : DynamicMutator Γ1 Γ2 AT Σ0) :
        dmut_dcl d <-> dmut_dcl' d.
      Proof.
        split.
        - unfold dmut_dcl, dmut_dcl'.
          intros d_dcl * Hpc12 Hs12 Hζ12 P P_dcl P_vac.
          eapply d_dcl; eauto.
        - unfold dmut_dcl, dmut_dcl'.
          intros d_dcl * Hpc12 Hs12 Hζ12 P P_dcl P_vac Q PQ.
          intros HP. eapply d_dcl in HP; eauto. revert HP.
          apply outcome_satisfy_monotonic. intros r. apply PQ.
      Qed.

      Lemma dmut_pure_dcl {Γ AT Σ A} {subA: Subst AT} {sublAT: SubstLaws AT}
            {instA : Inst AT A} {instlA : InstLaws AT A} (a : AT Σ) :
        dmut_dcl (dmut_pure (Γ := Γ) a).
      Proof.
        unfold dmut_dcl, dmut_pure.
        intros * Hpc12 Hs12 Hζ12 P P_dcl P_vac Q PQ HP.
        cbn in *.
        eapply PQ.
        unfold resultprop_specialize_pc.
        cbn; rewrite subst_sub_id; intuition.
        revert HP. eapply P_dcl.
        exists ζ12; unfold sub_comp;
          rewrite ?subst_sub_id, ?subst_sub_id_right, subst_assoc, Hζ12; easy.
      Qed.

      Lemma dmut_fail_dcl `{Inst AT A, Subst AT} {D Γ1 Γ2 Σ} func msg data :
        dmut_dcl (@dmut_fail Γ1 Γ2 AT Σ D func msg data).
      Proof.
        apply dmut_dcl_dcl'.
        unfold dmut_dcl', dmut_fail, contradiction, inconsistent, not; cbn.
        intros. unfold entails in H1. apply (H4 (inst ι ζ12)).
        rewrite <- inst_subst. intuition.
      Qed.

      Lemma dmut_sub_dcl {Γ1 Γ2 AT A Σ0} `{Inst AT A, Subst AT} (d : DynamicMutator Γ1 Γ2 AT Σ0) (d_dcl : dmut_dcl d) :
        forall (Σ1 : LCtx) (ζ1 : Sub Σ0 Σ1), dmut_dcl (dmut_sub ζ1 d).
      Proof.
        unfold dmut_dcl, dmut_sub.
        intros * Hpc12 Hs12 Hζ12 P P_dcl Q PQ.
        eapply d_dcl; eauto. unfold sub_comp.
        now rewrite subst_assoc, Hζ12.
      Qed.

      Lemma dmut_bind_right_dcl `{InstLaws AT A, InstLaws BT B} {Γ1 Γ2 Γ3 Σ0}
        (d1 : DynamicMutator Γ1 Γ2 AT Σ0) (d2 : DynamicMutator Γ2 Γ3 BT Σ0)
        (d1_dcl : dmut_dcl d1) (d2_dcl : dmut_dcl d2) (d2_vac : dmut_vac d2) :
        dmut_dcl (dmut_bind_right d1 d2).
      Proof.
        unfold dmut_bind_right.
        apply dmut_bind_dcl; auto.
        - unfold dmut_arrow_dcl.
          intros until Q. intros PQ.
          unfold dmut_sub; cbn.
          eapply d2_dcl; eauto.
          unfold sub_comp; now rewrite subst_assoc.
        - unfold dmut_arrow_vac.
          intros.
          now apply dmut_sub_vac.
      Qed.

      Lemma dmut_demonic_binary_dcl {Γ1 Γ2 AT A Σ0} `{Inst AT A, Subst AT} (d1 d2 : DynamicMutator Γ1 Γ2 AT Σ0) (d_wf1 : dmut_dcl d1) (d_wf2 : dmut_dcl d2) :
        dmut_dcl (dmut_demonic_binary d1 d2).
      Proof.
        unfold dmut_dcl, dmut_demonic_binary; cbn.
        intros * Hpc12 Hs12 Hζ12 P P_dcl P_vac Q PQ [H1 H2].
        split.
        - revert PQ H1. apply d_wf1; auto.
        - revert PQ H2. apply d_wf2; auto.
      Qed.

      Lemma dmut_angelic_binary_dcl {Γ1 Γ2 AT A Σ0} `{Inst AT A, Subst AT} (d1 d2 : DynamicMutator Γ1 Γ2 AT Σ0) (d1_dcl : dmut_dcl d1) (d2_dcl : dmut_dcl d2) :
        dmut_dcl (dmut_angelic_binary d1 d2).
      Proof.
        unfold dmut_dcl, dmut_angelic_binary. cbn.
        intros * Hpc12 Hs12 Hζ12 P P_dcl P_vac Q PQ [H1|H1].
        - left. revert PQ H1. apply d1_dcl; auto.
        - right. revert PQ H1. apply d2_dcl; auto.
      Qed.

      (* Redo these once the new definition of dmut_dcl is ready. *)

      (* Lemma dmut_state_dcl {AT A} `{Inst AT A} {Γ1 Γ2 Σ} *)
      (*       (f : forall Σ' : LCtx, Sub Σ Σ' -> SymbolicState Γ1 Σ' -> AT Σ' * SymbolicState Γ2 Σ') *)
      (*       (f_dcl : True) : *)
      (*   dmut_dcl (dmut_state f). *)
      (* Proof. *)
      (*   (* unfold dmut_dcl, dmut_state; intros until Q. intros PQ. *) *)
      (*   (* destruct (f Σ1 ζ01 s1) eqn:?, (f Σ2 ζ02 s2) eqn:?; cbn. *) *)
      (*   (* intros Hp. apply PQ. split; cbn. apply geqpc_refl. *) *)
      (*   (* revert Hp. rewrite sub_comp_id_right. *) *)
      (*   (* apply P_dcl. exists ζ12. *) *)
      (* Admitted. *)
      (* Local Hint Resolve dmut_state_dcl : core. *)

      (* Lemma dmut_assume_formula_dcl {Γ Σ} (f : Formula Σ) : *)
      (*   dmut_dcl (@dmut_assume_formula Γ Σ f). *)
      (* Proof. *)
      (*   apply dmut_dcl_dcl'. unfold dmut_assume_formula, dmut_dcl'. *)
      (*   intros * Hpc12 Hs12 Hζ12 P P_dcl P_vac H. *)
      (*   remember (dmutres_assume_formula pc2 (subst ζ02 f) s2) as r. *)
      (*   destruct (try_solve_formula_spec (subst ζ01 f)); *)
      (*   destruct (try_solve_formula_spec (subst ζ02 f)); cbn in *. *)
      (*   - clear r Heqr. destruct a, a0; cbn in *; auto. *)
      (*     + split; cbn. apply geqpc_refl. *)
      (*       revert H. apply P_dcl. *)
      (*       exists ζ12. rewrite sub_comp_id_right. *)
      (*       repeat split; auto. intros ? ? <-; now rewrite inst_sub_id. *)
      (*     + apply resultprop_specialize_pc_vac; cbn; auto. *)
      (*       intros ι Hpc2. specialize (Hζ12 _ ι eq_refl Hpc2). *)
      (*       specialize (H0 (inst ι ζ12)). specialize (H1 ι). *)
      (*       rewrite inst_subst in H0. rewrite inst_subst in H1. *)
      (*       rewrite Hζ12 in H0. clear - H0 H1. intuition. *)
      (*   - clear H1. destruct a; cbn in *; auto. *)
      (*     + subst r. pose proof (dmutres_assume_formula_geq pc2 (subst ζ02 f) s2) as Hgeq. *)
      (*       destruct (dmutres_assume_formula pc2 (subst ζ02 f) s2) as [Σ3 ζ23 pc3 [] s3]; cbn in *. *)
      (*       destruct Hgeq as [Hpc23 Hs23]. *)
      (*       split; cbn. *)
      (*       * intros ι2 ι3 rel23 Hpc3. specialize (Hpc23 ι2 ι3 rel23 Hpc3). *)
      (*         rewrite inst_pathcondition_cons in Hpc23. now destruct Hpc23. *)
      (*       * revert H. apply P_dcl. apply dmutres_geq_low_equiv. exists (sub_comp ζ12 ζ23). *)
      (*         intros ι1 ι3 rel13 Hpc3. rewrite inst_sub_id. *)
      (*         apply syminstance_rel_comp in rel13. *)
      (*         pose (inst ι3 ζ23) as ι2. *)
      (*         specialize (Hpc23 ι2 ι3 eq_refl Hpc3). *)
      (*         specialize (Hs23 ι2 ι3 eq_refl Hpc3). *)
      (*         rewrite inst_pathcondition_cons in Hpc23. destruct Hpc23 as [Hfml Hpc2]. *)
      (*         specialize (Hpc12 ι1 ι2 rel13 Hpc2). *)
      (*         specialize (Hs12 ι1 ι2 rel13 Hpc2). *)
      (*         specialize (Hζ12 ι1 ι2 rel13 Hpc2). *)
      (*         unfold sub_comp. rewrite inst_subst. *)
      (*         cbn. repeat split; auto. *)
      (*         now transitivity (inst ι2 s2). *)
      (*     + subst r. pose proof (dmutres_assume_formula_geq pc2 (subst ζ02 f) s2) as Hgeq. *)
      (*       destruct (dmutres_assume_formula pc2 (subst ζ02 f) s2) as [Σ3 ζ23 pc3 [] s3]; cbn in *. *)
      (*       destruct Hgeq as [Hpc23 Hs23]. *)
      (*       split; cbn. *)
      (*       * intros ι2 ι3 rel23 Hpc3. specialize (Hpc23 ι2 ι3 rel23 Hpc3). *)
      (*         rewrite inst_pathcondition_cons in Hpc23. now destruct Hpc23. *)
      (*       * clear - H0 Hpc23 Hpc12. admit. *)
      (*   - clear H0 r Heqr. destruct a; cbn; auto. split; cbn. *)
      (*     apply geqpc_refl. rewrite sub_comp_id_right. *)
      (*     apply (dmutres_assume_formula_spec pc1 (subst ζ01 f) s1) in H; auto. *)
      (*     revert H. apply P_dcl. apply dmutres_geq_low_equiv. *)
      (*     exists ζ12. intros ι1 ι2 <- Hpc2. *)
      (*     rewrite inst_pathcondition_cons, inst_sub_id, ?inst_subst; cbn. *)
      (*     intuition. *)
      (*     specialize (Hζ12 _ ι2 eq_refl Hpc2). rewrite Hζ12. *)
      (*     rewrite <- inst_subst. now apply H1. *)
      (*   - clear H0 H1. subst r. *)
      (*     pose proof (dmutres_assume_formula_geq pc2 (subst ζ02 f) s2) as Hgeq. *)
      (*     destruct (dmutres_assume_formula pc2 (subst ζ02 f) s2) as [Σ3 ζ23 pc3 [] s3]; cbn in *. *)
      (*     destruct Hgeq as [Hpc23 Hs23]. *)
      (*     split; cbn. *)
      (*     * intros ι2 ι3 rel23 Hpc3. specialize (Hpc23 ι2 ι3 rel23 Hpc3). *)
      (*       rewrite inst_pathcondition_cons in Hpc23. now destruct Hpc23. *)
      (*     * apply (dmutres_assume_formula_spec pc1 (subst ζ01 f) s1) in H; auto. *)
      (*       revert H. apply P_dcl. apply dmutres_geq_low_equiv. *)
      (*       exists (sub_comp ζ12 ζ23). intros ι1 ι3 <- Hpc3. *)
      (*       rewrite inst_pathcondition_cons, inst_sub_id. *)
      (*       unfold sub_comp; rewrite ?inst_subst; cbn. *)
      (*       repeat split; auto. *)
      (*       admit. *)
      (*       admit. *)
      (*       admit. *)
      (* Admitted. *)

      (* Lemma dmut_produce_chunk_dcl {Γ Σ} (c : Chunk Σ) : *)
      (*   dmut_dcl (@dmut_produce_chunk Γ Σ c). *)
      (* Proof. Admitted. *)

      (* Lemma dmut_fresh_dcl {AT A} `{Inst AT A} {Γ Σ σ x} (d : DynamicMutator Γ Γ AT (Σ ▻ (x :: σ))) (d_dcl : dmut_dcl d) : *)
      (*   dmut_dcl (dmut_fresh (x :: σ) d). *)
      (* Proof. Admitted. *)

      (* Lemma dmut_freshtermvar_dcl {Γ Σ σ x} : *)
      (*   dmut_dcl (@dmut_freshtermvar Γ Σ σ x). *)
      (* Proof. *)
      (*   apply dmut_dcl_dcl'. unfold dmut_dcl', dmut_freshtermvar; cbn - [dmut_fresh]. *)
      (*   intros * Hpc12 Hs12 Hζ12 P P_dcl P_vac. *)
      (*   eapply dmut_fresh_dcl; eauto. *)
      (*   apply dmut_pure_dcl. *)
      (* Qed. *)

      (* Lemma dmut_produce_dcl {Γ Σ} (asn : Assertion Σ) : *)
      (*   dmut_dcl (@dmut_produce Γ Σ asn). *)
      (* Proof. *)
      (*   induction asn; cbn [dmut_produce]; unfold dmut_assume_term. *)
      (*   - apply dmut_assume_formula_dcl. *)
      (*   - apply dmut_produce_chunk_dcl. *)
      (*   - apply dmut_demonic_binary_dcl. *)
      (*     apply dmut_bind_right_dcl; *)
      (*       auto using dmut_assume_formula_dcl, dmut_produce_vac. *)
      (*     apply dmut_bind_right_dcl; *)
      (*       auto using dmut_assume_formula_dcl, dmut_produce_vac. *)
      (*   - admit. *)
      (*   - admit. *)
      (*   - apply dmut_fail_dcl. *)
      (*   - admit. *)
      (*   - apply dmut_fail_dcl. *)
      (*   - admit. *)
      (*   - admit. *)
      (*   - apply dmut_bind_right_dcl; auto using dmut_produce_vac. *)
      (*   - now apply dmut_fresh_dcl. *)
      (* Admitted. *)

      (* Lemma dmut_consume_dcl {Γ Σ} (asn : Assertion Σ) : *)
      (*   dmut_dcl (@dmut_consume Γ Σ asn). *)
      (* Proof. Admitted. *)

      (* Lemma dmut_exec_dcl {Γ Σ τ} (s : Stm Γ τ) : *)
      (*   dmut_dcl (@dmut_exec Γ τ Σ s). *)
      (* Proof. Admitted. *)

      Lemma dmut_contract_dcl {Γ τ} (c : SepContract Γ τ) (s : Stm Γ τ) :
        dmut_dcl (@dmut_contract Γ τ c s).
      Proof. Admitted.

    End DownwardsClosure.

    Ltac auto_dcl :=
      try
        match goal with
        | |- dmut_dcl _ => admit
        | |- dmut_arrow_dcl _ => admit
        end.

    Definition scmut_wp {Γ1 Γ2 A}
      (m : SCMut Γ1 Γ2 A)
      (POST : A -> SCState Γ2 -> Prop)
      (s1 : SCState Γ1) : Prop :=
      outcome_satisfy (m s1) (fun _ => False) (fun r => POST (scmutres_value r) (scmutres_state r)).

    Lemma scmut_wp_bind {Γ1 Γ2 Γ3 A B} (ma : SCMut Γ1 Γ2 A) (f : A -> SCMut Γ2 Γ3 B)
          (POST : B -> SCState Γ3 -> Prop) :
      forall s1 : SCState Γ1,
        scmut_wp (scmut_bind ma f) POST s1 <->
        scmut_wp ma (fun a => scmut_wp (f a) POST) s1.
    Proof.
      unfold SCMut, scmut_bind, scmut_wp in *; cbn; intros.
      now rewrite outcome_satisfy_bind.
    Qed.

    Definition dmut_wp {Γ1 Γ2 Σ0 Σ1 A}
      (m : DynamicMutator Γ1 Γ2 A Σ0)
      (POST : StateProperty Γ2 A Σ0)
      (ζ1 : Sub Σ0 Σ1)
      (pc1 : PathCondition Σ1)
      (s1 : SymbolicState Γ1 Σ1) : Prop :=
        outcome_satisfy
          (m Σ1 ζ1 pc1 s1)
          contradiction
          (fun '(MkDynMutResult ζ2 pc2 a2 s2) =>
             POST _ (sub_comp ζ1 ζ2) pc2 a2 s2).

    Lemma dmut_wp_monotonic {Γ1 Γ2 Σ0 A} (m : DynamicMutator Γ1 Γ2 A Σ0)
          (P Q : StateProperty Γ2 A Σ0) (HYP : stateprop_impl P Q) :
      forall {Σ1} (ζ : Sub Σ0 Σ1) (pc : PathCondition Σ1) (s : SymbolicState Γ1 Σ1),
        dmut_wp m P ζ pc s -> dmut_wp m Q ζ pc s.
    Proof.
      unfold dmut_wp; cbn; intros Σ1 ζ1 pc1 s1.
      apply outcome_satisfy_monotonic.
      intros [Σ2 ζ2 pc2 a2 s2]; cbn.
      intuition.
    Qed.

    Lemma dmut_wp_angelic {A B Γ1 Γ2 Σ0} (m : B Σ0 -> DynamicMutator Γ1 Γ2 A Σ0)
          {Σ1} (ζ01 : Sub Σ0 Σ1) (POST : StateProperty Γ2 A Σ1) :
      forall {Σ2} (ζ12 : Sub Σ1 Σ2) pc2 s2,
        dmut_wp (dmut_sub ζ01 (dmut_angelic m)) POST ζ12 pc2 s2 <->
        ((exists ι, inst ι pc2) -> exists b, dmut_wp (dmut_sub ζ01 (m b)) POST ζ12 pc2 s2).
    Proof. reflexivity. Qed.

    Definition dmut_wp_sub_id {Γ1 Γ2 Σ0 A} (m : DynamicMutator Γ1 Γ2 A Σ0) (P : StateProperty Γ2 A Σ0) :
      forall Σ1 (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (s1 : SymbolicState Γ1 Σ1),
      dmut_wp (dmut_sub (sub_id _) m) P ζ01 pc1 s1 <-> dmut_wp m P ζ01 pc1 s1.
    Proof.
      unfold dmut_wp, dmut_sub. intros.
      now rewrite ?sub_comp_id_left.
    Qed.

    Definition APPROX Γ1 Γ2 AT A {instA : Inst AT A} : Type :=
      forall Σ (ι : SymInstance Σ),
        DynamicMutator Γ1 Γ2 AT Σ -> SCMut Γ1 Γ2 A -> Prop.
    Arguments APPROX _ _ _ _ {_}.

    Definition box {Γ1 Γ2 AT A} {instA : Inst AT A} (R : APPROX Γ1 Γ2 AT A) : APPROX Γ1 Γ2 AT A :=
      fun Σ ι dm sm =>
        forall Σ1 (ζ1 : Sub Σ Σ1) (ι1 : SymInstance Σ1),
          syminstance_rel ζ1 ι ι1 ->
          R Σ1 ι1 (dmut_sub ζ1 dm) sm.

    Lemma box_proj {Γ1 Γ2 AT A} {instA : Inst AT A} (R : APPROX Γ1 Γ2 AT A) :
      forall Σ (ι : SymInstance Σ) dm sm,
        box R ι dm sm -> R _ ι dm sm.
    Proof.
      intros ? ? ? ? b.
      unfold box in b.
      inster b by apply syminstance_rel_refl.
      unfold dmut_sub in b.
      (* apply b. *)
    Abort.

    Definition box_box {Γ1 Γ2 AT A} {instA : Inst AT A} (R : APPROX Γ1 Γ2 AT A) :
      forall Σ (ι : SymInstance Σ) dm sm,
        box R ι dm sm -> box (box R) ι dm sm.
    Proof.
      intros ? ? ? ?. unfold box. intros bb Σ1 ζ1 ι1 ? Σ2 ζ2 ι2 ?.
      specialize (bb Σ2 (sub_comp ζ1 ζ2) ι2).
      inster bb by eapply syminstance_rel_trans; eauto.
      (* apply bb. *)
    Abort.

    Definition approximates {Γ1 Γ2 AT A} {instA : Inst AT A} : APPROX Γ1 Γ2 AT A :=
      fun Σ ι dm sm =>
        forall Σ1 (ζ : Sub Σ Σ1) pc (s__sym : SymbolicState Γ1 Σ1) ι1 (POST : A -> SCState Γ2 -> Prop)
               (Heqι : ι = inst ι1 ζ)
               (Hpc : inst ι1 pc : Prop)
               (Hwp : dmut_wp dm (stateprop_lift ι POST) ζ pc s__sym),
          scmut_wp sm POST (inst ι1 s__sym).

    Lemma approximates_proj {Γ1 Γ2 AT A} {instA : Inst AT A} {Σ} (ι : SymInstance Σ)
      (dm : DynamicMutator Γ1 Γ2 AT Σ) (sm : SCMut Γ1 Γ2 A) :
      box approximates ι dm sm -> approximates ι dm sm.
    Proof.
      (* unfold approximates, box. intros Happrox * Hdwp Hpc. *)
      (* inster Happrox by apply syminstance_rel_refl. *)
      (* specialize (Happrox pc). apply Happrox; auto. *)
      (* unfold dmut_wp, dmut_sub. intros Σ1 ζ1. *)
      (* rewrite sub_comp_id_left. apply Hdwp. *)
    Admitted.

    Lemma approximates_box_box {Γ1 Γ2 AT A} {instA : Inst AT A} {Σ} (ι : SymInstance Σ)
      (dm : DynamicMutator Γ1 Γ2 AT Σ) (sm : SCMut Γ1 Γ2 A) :
      box approximates ι dm sm -> box (box approximates) ι dm sm.
    Proof.
      (* unfold approximates, box, dmut_wp, dmut_sub. intros. *)
      (* inster H by eapply syminstance_rel_trans; eauto. *)
      (* specialize (H pc). apply H; auto. *)
      (* intros. now rewrite sub_comp_assoc. *)
    Admitted.

    Lemma approximates_sub {Γ Σ Σ1} (ζ1 : Sub Σ Σ1) (ι : SymInstance Σ) (ι1 : SymInstance Σ1)
      (relι1 : syminstance_rel ζ1 ι ι1) (d : DynamicMutator Γ Γ Unit Σ) (s : SCMut Γ Γ unit) :
      box approximates ι d s -> box approximates ι1 (dmut_sub ζ1 d) s.
    Proof. intros H. eapply approximates_box_box; eauto. Qed.

    Lemma approximates_pure {AT A} `{Subst AT, Inst AT A} {Γ Σ} (ι : SymInstance Σ) (a : AT Σ) :
      box approximates ι (dmut_pure (Γ := Γ) a) (scmut_pure (inst ι a)).
    Proof. Admitted.

    Lemma approximates_fail `{Inst AT A} {D Γ1 Γ2 Σ} func msg data ι s :
      box approximates ι (@dmut_fail Γ1 Γ2 AT Σ D func msg data) s.
    Proof. Admitted.

    Lemma approximates_block `{Inst AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ) :
      box approximates ι (@dmut_block Γ1 Γ2 AT Σ) (@scmut_block Γ1 Γ2 A).
    Proof. Admitted.

    Lemma scmut_wp_demonic_binary {Γ1 Γ2 A} (sm1 sm2 : SCMut Γ1 Γ2 A) (s__sc : SCState Γ1) (POST : A -> SCState Γ2 -> Prop) :
      scmut_wp (scmut_demonic_binary sm1 sm2) POST s__sc <->
      scmut_wp sm1 POST s__sc /\ scmut_wp sm2 POST s__sc.
    Proof. unfold scmut_wp, scmut_demonic_binary; cbn; intuition. Qed.

    Lemma dmut_wp_demonic_binary {Γ1 Γ2 Σ0 A} (m1 m2 : DynamicMutator Γ1 Γ2 A Σ0) (POST : StateProperty Γ2 A Σ0) :
      forall Σ1 (ζ01 : Sub Σ0 Σ1) pc1 s1,
        dmut_wp (dmut_demonic_binary m1 m2) POST ζ01 pc1 s1 <->
        dmut_wp m1 POST ζ01 pc1 s1 /\ dmut_wp m2 POST ζ01 pc1 s1.
    Proof. unfold dmut_wp, dmut_demonic_binary; cbn; intuition. Qed.

    Lemma dmut_wp_sub_demonic_binary {A Γ1 Γ2 Σ0 Σ1} (ζ01 : Sub Σ0 Σ1) (m1 m2 : DynamicMutator Γ1 Γ2 A Σ0) (POST : StateProperty Γ2 A Σ1) :
      forall Σ2 (ζ12 : Sub Σ1 Σ2) pc2 s2,
        dmut_wp (dmut_sub ζ01 (dmut_demonic_binary m1 m2)) POST ζ12 pc2 s2 <->
        dmut_wp (dmut_sub ζ01 m1) POST ζ12 pc2 s2 /\ dmut_wp (dmut_sub ζ01 m2) POST ζ12 pc2 s2.
    Proof. unfold dmut_wp, dmut_demonic_binary; cbn; intuition. Qed.

    Lemma approximates_demonic_binary {Γ1 Γ2 Σ} (ι : SymInstance Σ)
          (dm1 dm2 : DynamicMutator Γ1 Γ2 Unit Σ) (sm1 sm2 : SCMut Γ1 Γ2 unit) :
      box approximates ι dm1 sm1 ->
      box approximates ι dm2 sm2 ->
      box approximates ι (dmut_demonic_binary dm1 dm2) (scmut_demonic_binary sm1 sm2).
    Proof.
      (* unfold box. intros H1 H2 Σ1 ζ1 ι1 H__ι. *)
      (* specialize (H1 Σ1 ζ1 ι1 H__ι). specialize (H2 Σ1 ζ1 ι1 H__ι). *)
      (* intros pc s1 POST Hwp Hpc. apply dmut_wp_sub_demonic_binary in Hwp. *)
      (* destruct Hwp as [Hwp1 Hwp2]. *)
      (* specialize (H1 pc s1 POST Hwp1 Hpc). specialize (H2 pc s1 POST Hwp2 Hpc). *)
      (* apply scmut_wp_demonic_binary. split; auto. *)
    Admitted.

    Lemma scmut_wp_angelic {Γ1 Γ2 A B} (sm : B -> SCMut Γ1 Γ2 A) (s__sc : SCState Γ1) (POST : A -> SCState Γ2 -> Prop) :
      scmut_wp (scmut_angelic sm) POST s__sc <-> exists v, scmut_wp (sm v) POST s__sc.
    Proof. unfold scmut_wp, scmut_angelic; cbn; intuition. Qed.

    (* Lemma dmut_wp_angelic {A B Γ1 Γ2 Σ0 Σ1} (ζ01 : Sub Σ0 Σ1) (m : B -> DynamicMutator Γ1 Γ2 A Σ0) (POST : StateProperty Γ2 A Σ1) : *)
    (*   forall pc1 s1, *)
    (*     dmut_wp (dmut_sub ζ01 (dmut_angelic m)) POST pc1 s1 <-> *)
    (*     exists b, dmut_wp (dmut_sub ζ01 (m b)) POST pc1 s1. *)
    (* Proof. Admitted. *)

    Lemma approximates_angelic {AT A BT B} `{InstLaws AT A, InstLaws BT B} {Γ1 Γ2 Σ}
          (ι : SymInstance Σ)
      (dm : AT Σ -> DynamicMutator Γ1 Γ2 BT Σ) (dm_dcl : forall a, dmut_dcl (dm a))
      (sm : A -> SCMut Γ1 Γ2 B)
      (HYP : forall a, box approximates ι (dm a) (sm (inst ι a))) :
      box approximates ι
        (dmut_angelic dm)
        (scmut_angelic sm).
    Proof.
      (* unfold box, approximates, dmut_wp, dmut_sub, dmut_angelic; cbn. *)
      (* intros * Hrel * Hwp Hpc. specialize (Hwp Σ1 (sub_id _)). *)
      (* destruct Hwp as [a Hwp]. exists (inst ι a). eapply HYP; eauto. *)
      (* unfold dmut_wp, dmut_sub. intros. revert Hwp. *)
      (* rewrite sub_comp_id_right, ?subst_sub_id. *)
      (* eapply (dm_dcl a) with ζ0; eauto; try easy. *)
      (* - intros [Σ2 ζ2 pc2 a2 s2] [Σ3 ζ3 pc3 a3 s3] ?. *)
      (*   rewrite ?sub_comp_id_left. *)
      (*   now apply stateprop_lift_dcl. *)
      (* - intros [Σ2 ζ2 pc2 a2 s2] ?. *)
      (*   rewrite ?sub_comp_id_left. *)
      (*   now apply stateprop_lift_vac. *)
      (* - intros [Σ2 ζ2 pc2 a2 s2] []; unfold resultprop_specialize_pc; cbn in *. *)
      (*   now rewrite sub_comp_id_left in H8. *)
    Admitted.

    Lemma scmut_wp_demonic {Γ1 Γ2 A B} (sm : B -> SCMut Γ1 Γ2 A) (s__sc : SCState Γ1) (POST : A -> SCState Γ2 -> Prop) :
      scmut_wp (scmut_demonic sm) POST s__sc <-> forall v, scmut_wp (sm v) POST s__sc.
    Proof. unfold scmut_wp, scmut_demonic; cbn; intuition. Qed.

    (* Lemma dmut_wp_sub_demonic {A B Γ1 Γ2 Σ0 Σ1} (ζ01 : Sub Σ0 Σ1) (m : B -> DynamicMutator Γ1 Γ2 A Σ0) (POST : StateProperty Γ2 A Σ1) : *)
    (*   forall pc1 s1, *)
    (*     dmut_wp (dmut_sub ζ01 (dmut_demonic m)) POST pc1 s1 <-> *)
    (*     forall b, dmut_wp (dmut_sub ζ01 (m b)) POST pc1 s1. *)
    (* Proof. unfold dmut_wp, dmut_demonic; cbn; intuition. Qed. *)

    Lemma approximates_demonic {A BT B} `{Inst BT B} {Γ1 Γ2 Σ} (ι : SymInstance Σ)
      (dm : A -> DynamicMutator Γ1 Γ2 BT Σ)
      (sm : A -> SCMut Γ1 Γ2 B)
      (HYP : forall a, box approximates ι (dm a) (sm a)) :
      box approximates ι
        (dmut_demonic dm)
        (scmut_demonic sm).
    Proof.
      (* unfold box, approximates. *)
      (* intros Σ1 ζ01 ι1 Hrel * Hwp Hpc. *)
      (* apply scmut_wp_demonic. intros a. *)
      (* rewrite dmut_wp_sub_demonic in Hwp. *)
      (* specialize (Hwp a). *)
      (* apply (HYP a) in Hwp; auto. *)
    Admitted.

    Lemma subst_symbolicstate_produce_chunk {Γ Σ Σ1} (ζ1 : Sub Σ Σ1) (c : Chunk Σ) (s : SymbolicState Γ Σ) :
      subst ζ1 (symbolicstate_produce_chunk c s) = symbolicstate_produce_chunk (subst ζ1 c) (subst ζ1 s).
    Proof. now destruct s. Qed.

    (* Lemma dmut_wp_produce_chunk {Γ Σ Σ1} (ζ1 : Sub Σ Σ1) (c : Chunk _) pc (s__sym : SymbolicState Γ _) *)
    (*       (POST : StateProperty Γ Unit _) (POST_dcl : stateprop_downwards_closed POST) : *)
    (*   dmut_wp (dmut_sub ζ1 (dmut_produce_chunk c)) POST pc s__sym <-> *)
    (*   POST Σ1 (sub_id Σ1) pc tt (symbolicstate_produce_chunk (subst ζ1 c) s__sym). *)
    (* Proof. *)
    (*   split. *)
    (*   - intros dwp. *)
    (*     specialize (dwp Σ1 (sub_id Σ1)). cbn in dwp. *)
    (*     now rewrite ?sub_comp_id_right, ?subst_sub_id in dwp. *)
    (*   - intros p Σ2 ζ2. cbn. rewrite subst_sub_comp. revert p. *)
    (*     apply POST_dcl. apply dmutres_geq_syntactic. *)
    (*     exists ζ2. *)
    (*     rewrite sub_comp_id_right, sub_comp_id_left. *)
    (*     now rewrite subst_symbolicstate_produce_chunk. *)
    (* Qed. *)

    Lemma dmut_produce_chunk_sound {Γ Σ} (ι : SymInstance Σ) (c : Chunk Σ) :
      box approximates
        (Γ1 := Γ) (Γ2 := Γ) ι
        (dmut_produce_chunk c)
        (scmut_produce_chunk (inst ι c)).
    Proof.
      (* intros ? ? ? <- ? ? ? Hwp Hpc. cbn. *)
      (* apply dmut_wp_produce_chunk in Hwp. *)
      (* - specialize (Hwp ι1). inster Hwp by apply syminstance_rel_refl. *)
      (*   specialize (Hwp Hpc). destruct s__sym as [δ h]; cbn. *)
      (*   now rewrite <- inst_subst. *)
      (* - apply stateprop_lift_dcl. *)
    Admitted.

    (* Lemma dmut_wp_sub {Γ1 Γ2 A Σ0} (d : DynamicMutator Γ1 Γ2 A Σ0) *)
    (*       (POST : StateProperty Γ2 A Σ0) pc (s : SymbolicState Γ1 Σ0) Σ1 (ζ : Sub Σ0 Σ1) : *)
    (*     dmut_wp d POST pc s -> *)
    (*     dmut_wp (dmut_sub ζ d) (stateprop_specialize ζ POST) (subst ζ pc) (subst ζ s). *)
    (* Proof. *)
    (*   unfold dmut_sub, dmut_wp. intros * Hpost *. *)
    (*   specialize (Hpost Σ2 (sub_comp ζ ζ1)). *)
    (*   rewrite ?subst_sub_comp in Hpost. revert Hpost. *)
    (*   apply outcome_satisfy_monotonic. clear. intros [Σ3 ζ3 pc3 a3 s3]. *)
    (*   unfold stateprop_specialize. now rewrite sub_comp_assoc. *)
    (* Qed. *)

    Opaque subst.
    Opaque sub_up1.
    Opaque sub_snoc.
    Opaque wk1.
    Opaque SubstEnv.

    Lemma dmut_wp_bind {AT A BT B} {instA : Inst AT A} {instB : Inst BT B} {subB: Subst BT}
          {Γ1 Γ2 Γ3 Σ0 Σ1} (ζ1 : Sub Σ0 Σ1)
          (ma : DynamicMutator Γ1 Γ2 AT Σ0)
          (f : forall Σ', Sub Σ0 Σ' -> AT Σ' -> DynamicMutator Γ2 Γ3 BT Σ')
          (f_dcl : forall Σ ζ a, dmut_dcl (f Σ ζ a))
          (POST : StateProperty Γ3 BT Σ1) (POST_dcl : stateprop_downwards_closed POST) :
      forall Σ2 (ζ12 : Sub Σ1 Σ2) pc2 s2,
        dmut_wp (dmut_sub ζ1 (dmut_bind ma f)) POST ζ12 pc2 s2 <->
        dmut_wp
          (dmut_sub ζ1 ma)
          (fun Σ2 ζ2 pc2 a2 => dmut_wp (f Σ2 (sub_comp ζ1 ζ2) a2) (stateprop_specialize ζ2 POST) (sub_id _) pc2)
          ζ12 pc2 s2.
    Proof.
      (* unfold DynamicMutator, dmut_bind, dmut_sub, dmut_wp, dmut_dcl in *; cbn; intros pc1 s1. *)
      (* split; intros H Σ2 ζ2; specialize (H Σ2 ζ2). revert H. *)
      (* - rewrite outcome_satisfy_bind. apply outcome_satisfy_monotonic. *)
      (*   intros [Σ3 ζ3 pc3 a3 s3] H Σ4 ζ4. revert H. *)
      (*   rewrite outcome_satisfy_bind. *)
      (*   eapply f_dcl. *)

      (* OLD: *)
      (*   apply (f_wf Σ3 (sub_comp (sub_comp ζ1 ζ2) ζ3) a3 Σ3 Σ4 (sub_id Σ3) ζ4) in H. *)
      (*   + revert H. rewrite sub_comp_id_left, sub_comp_assoc. *)
      (*     apply outcome_satisfy_monotonic. *)
      (*     intros [Σ5 ζ5 b5 s5]. cbn. *)
      (*     now rewrite <- sub_comp_assoc. *)
      (*   + revert POST_dcl. clear. intros. *)
      (*     unfold resultprop_downwards_closed. *)
      (*     intros [Σ4 ζ4 b4 s4] [Σ5 ζ5 b5 s5] Hgeq. *)
      (*     cbn. apply POST_dcl. rewrite <- ?sub_comp_assoc. *)
      (*     revert Hgeq. apply dmutres_geq_sem_pre_comp. *)
      (* - rewrite outcome_satisfy_bind. revert H. *)
      (*   apply outcome_satisfy_monotonic. *)
      (*   intros [Σ3 ζ3 a3 s3] H. specialize (H Σ3 (sub_id _)). *)
      (*   revert H. rewrite outcome_satisfy_bind, subst_sub_id, sub_comp_assoc. *)
      (*   apply outcome_satisfy_monotonic. *)
      (*   intros [Σ4 ζ4 b4 s4]. cbn. *)
      (*   unfold stateprop_specialize. *)
      (*   now rewrite sub_comp_id_left, sub_comp_assoc. *)
    Admitted.

    Lemma inst_snoc_wk1 {Σ2 x τ} {ι0 : SymInstance (Σ2 ▻ (x :: τ))} {ι1} `{Subst AT} {substLawsA : SubstLaws AT} `{Inst AT A} {instLaws : InstLaws AT A} {t : AT Σ2} {v} :
      syminstance_rel (sub_id Σ2 ► (x :: τ ↦ v)) ι0 ι1 -> inst ι0 (wk1 t) = inst ι1 t.
    Proof.
      unfold syminstance_rel.
      intros; subst ι0.
      change (wk1 t) with (subst (sub_wk1 (b := x :: τ)) t).
      rewrite inst_subst.
      f_equal.
      rewrite <-inst_subst.
      change (subst (sub_id Σ2 ► (x :: τ ↦ v)) sub_wk1) with (sub_comp sub_wk1 (sub_id Σ2 ► (x :: τ ↦ v))).
      rewrite sub_comp_wk1_tail. cbn.
      now rewrite inst_sub_id.
    Qed.

    (* Section WpSubFresh. *)
    (*   Local Transparent wk1 subst. *)
    (*   Lemma dmut_wp_sub_fresh {Γ Σ0 Σ1 AT A x τ} `{Subst AT, Inst AT A} *)
    (*         (ζ1 : Sub Σ0 Σ1) *)
    (*         (d : DynamicMutator Γ Γ AT (Σ0 ▻ (x,τ))%ctx) *)
    (*         (POST : StateProperty Γ AT Σ1) *)
    (*         (POST_dcl : stateprop_downwards_closed POST) *)
    (*         (POST_vac : stateprop_vacuous POST) *)
    (*         (pc : PathCondition Σ1) *)
    (*         (s : SymbolicState Γ Σ1) (wfd : dmut_dcl d) : *)
    (*     dmut_wp (dmut_sub ζ1 (dmut_fresh x τ d)) POST pc s <-> *)
    (*     dmut_wp (dmut_sub (sub_up1 ζ1) d) (stateprop_specialize sub_wk1 POST) (subst sub_wk1 pc) (subst sub_wk1 s). *)
    (*   Proof. *)
    (*     unfold dmut_wp, dmut_sub, dmut_fresh. cbn; split; intros HYP Σ2 ζ2. *)
    (*     - dependent elimination ζ2 as [@env_snoc Σ1 ζ2 _ v]; cbn in v. *)
    (*       rewrite <- ?subst_sub_comp, ?sub_comp_wk1_tail; cbn. *)
    (*       specialize (HYP Σ2 ζ2). *)
    (*       rewrite outcome_satisfy_map in HYP; cbn in *. *)
    (*       refine (wfd _ Σ2 _ _ _ (env_snoc (sub_id _) (_,τ) v) _ _ _ _ _ _ _ _ _ _ _ HYP); clear wfd HYP; unfold wk1. *)
    (*       + rewrite <-subst_sub_comp, sub_comp_wk1_tail; cbn. *)
    (*         now rewrite subst_sub_id. *)
    (*       + rewrite <-subst_sub_comp, sub_comp_wk1_tail; cbn. *)
    (*         now rewrite subst_sub_id. *)
    (*       + change (subst _ (sub_comp _ sub_wk1 ► (x :: τ ↦ _))) with *)
    (*             (sub_comp (sub_comp (sub_comp ζ1 ζ2) sub_wk1) (sub_id Σ2 ► (fresh Σ2 (Some x) :: τ ↦ v)) ► (x :: τ ↦ v)). *)
    (*         rewrite <-sub_snoc_comp, sub_comp_assoc, sub_comp_wk1_tail; cbn. *)
    (*         now rewrite sub_comp_id_right. *)
    (*       + revert POST_dcl. clear. intros. *)
    (*         unfold resultprop_downwards_closed. *)
    (*         intros [Σ3 ζ3 pc3 a3 s3] [Σ4 ζ4 pc4 a4 s4] Hgeq. *)
    (*         cbn. apply POST_dcl. *)
    (*         rewrite <- ?sub_comp_assoc. *)
    (*         revert Hgeq. exact (dmutres_geq_pre_comp _ _ (sub_comp ζ2 sub_wk1)). *)
    (*       + unfold resultprop_vacuous. *)
    (*         intros [Σ3 ζ3 pc3 a3 s3]. *)
    (*         cbn. *)
    (*         eapply POST_vac. *)
    (*       + intros [Σ3 ζ3 pc3 a3 s3]. *)
    (*         unfold resultprop_specialize_pc. cbn. *)
    (*         intros [geqpc post]. *)
    (*         rewrite <-(sub_comp_assoc sub_wk1), sub_comp_wk1_tail in post. *)
    (*         cbn in post. *)
    (*         rewrite sub_comp_id_left in post. *)
    (*         unfold stateprop_specialize. *)
    (*         now rewrite <-(sub_comp_assoc sub_wk1), sub_comp_wk1_tail. *)
    (*     - rewrite outcome_satisfy_map. *)
    (*       specialize (HYP (Σ2 ▻ (x,τ)) (sub_up1 ζ2)). *)
    (*       rewrite <- ?subst_sub_comp, ?sub_comp_wk1_comm in HYP. *)
    (*       change (wk1 (b := (x,τ)) (subst ζ2 ?t)) with (subst (sub_wk1 (b := (x,τ))) (subst ζ2 t)). *)
    (*       rewrite ?sub_up_comp, <- ?subst_sub_comp. *)
    (*       revert HYP. *)
    (*       (* apply outcome_satisfy_monotonic. *) *)
    (*       (* intros [Σ3 ζ3 pc3 a3 s3]. clear. *) *)
    (*       (* dependent elimination ζ3 as [@env_snoc Σ2 ζ3 _ t]. *) *)
    (*       (* unfold stateprop_specialize. cbn. *) *)
    (*       (* now rewrite <- ?sub_comp_assoc, <- sub_comp_wk1_comm. *) *)
    (*   Admitted. *)
    (* End WpSubFresh. *)

    (* Lemma dmut_wp_fresh {Γ Σ0 AT A x τ} `{Subst AT, Inst AT A} *)
    (*       (d : DynamicMutator Γ Γ AT (Σ0 ▻ (x,τ))%ctx) (d_dcl : dmut_dcl d) *)
    (*       (POST : StateProperty Γ AT Σ0) *)
    (*       (POST_dcl : stateprop_downwards_closed POST) *)
    (*       (POST_vac : stateprop_vacuous POST) *)
    (*       (pc : PathCondition Σ0) (s : SymbolicState Γ Σ0) : *)
    (*   dmut_wp (dmut_fresh x τ d) POST pc s <-> *)
    (*   dmut_wp d (stateprop_specialize sub_wk1 POST) (subst sub_wk1 pc) (subst sub_wk1 s). *)
    (* Proof. *)
    (*   rewrite <-dmut_wp_sub_id. *)
    (*   rewrite dmut_wp_sub_fresh; try assumption . *)
    (*   now rewrite sub_up1_id, dmut_wp_sub_id. *)
    (* Qed. *)

    Lemma dmut_bind_sound {Γ1 Γ2 Γ3 Σ0 AT A BT B}
      `{Subst AT, Inst AT A, InstLaws BT B} (ι0 : SymInstance Σ0)
      (dma : DynamicMutator Γ1 Γ2 AT Σ0) (dm_dcl : dmut_dcl dma)
      (sma : SCMut Γ1 Γ2 A)
      (dmf : forall Σ1, Sub Σ0 Σ1 -> AT Σ1 -> DynamicMutator Γ2 Γ3 BT Σ1)
      (dmf_dcl : dmut_arrow_dcl dmf)
      (dmf_dcl' : forall (Σ : LCtx) (ζ : Sub Σ0 Σ) (a : AT Σ), dmut_dcl (dmf Σ ζ a))
      (smf : A -> SCMut Γ2 Γ3 B) :
      box approximates ι0 dma sma ->
      (forall Σ1 (ζ1 : Sub Σ0 Σ1) (a1 : AT Σ1) (ι1 : SymInstance Σ1),
          syminstance_rel ζ1 ι0 ι1 ->
          box approximates ι1 (dmf Σ1 ζ1 a1) (smf (inst ι1 a1))) ->
      box approximates ι0 (dmut_bind dma dmf) (scmut_bind sma smf).
    Proof.
      (* intros H__a H__f. *)
      (* intros Σ1 ζ1 ι1 relι1 pc1 s__sym1 POST H__wp Hpc. *)
      (* apply scmut_wp_bind. revert Hpc. *)
      (* apply dmut_wp_sub_bind in H__wp; auto using stateprop_lift_dcl. *)
      (* specialize (H__a Σ1 ζ1 ι1 relι1). *)
      (* apply H__a. revert H__wp. apply dmut_wp_monotonic. *)
      (* intros Σ2 ζ2 pc2 a2 s2 Hwp2 ι2 rel12 Hpc2. revert Hpc2. *)
      (* specialize (H__f Σ2 (sub_comp ζ1 ζ2) a2 ι2). *)
      (* inster H__f by eapply syminstance_rel_trans; eauto. *)
      (* apply approximates_proj in H__f. apply H__f. *)
      (* revert Hwp2. apply dmut_wp_monotonic. *)
      (* intros Σ3 ζ3 pc3 b3 s__sym3 H__post ι3 rel23 Hpc3. *)
      (* apply H__post. apply (syminstance_rel_trans rel12 rel23). assumption. *)
    Admitted.

    Lemma dmut_bind_right_sound {Γ1 Γ2 Γ3 Σ0 AT A BT B}
      `{Subst AT, Inst AT A, InstLaws BT B} (ι0 : SymInstance Σ0)
      (dma : DynamicMutator Γ1 Γ2 AT Σ0) (dm_dcl : dmut_dcl dma) (sma : SCMut Γ1 Γ2 A)
      (dmb : DynamicMutator Γ2 Γ3 BT Σ0) (dmb_dcl : dmut_dcl dmb) (smb : SCMut Γ2 Γ3 B) :
      box approximates ι0 dma sma ->
      box approximates ι0 dmb smb ->
      box approximates ι0 (dmut_bind_right dma dmb) (scmut_bind_right sma smb).
    Proof.
    Admitted.

    Lemma dmut_fresh_sound {Γ Σ ς τ} (ι : SymInstance Σ)
          (dm : DynamicMutator Γ Γ Unit (Σ ▻ (ς,τ))) (dm_dcl : dmut_dcl dm)
          (sm : Lit τ -> SCMut Γ Γ unit) :
      (forall v, box approximates (env_snoc ι _ v) dm (sm v)) ->
      box approximates ι
        (dmut_fresh ς τ dm)
        (scmut_demonic sm).
    Proof.
      (* intros HYP. unfold box, approximates. *)
      (* intros * <- pc1 s1 POST Hwp Hpc. *)
      (* apply scmut_wp_demonic. intros v. *)
      (* specialize (HYP v (Σ1 ▻ (ς,τ)) (sub_up1 ζ1) (env_snoc ι1 (ς,τ) v)). *)
      (* inster HYP by apply syminstance_rel_up; auto. *)
      (* unfold approximates in HYP. *)
      (* specialize (HYP (subst sub_wk1 pc1) (subst (sub_wk1) s1) POST). *)
      (* rewrite ?inst_subst, ?inst_sub_wk1 in HYP. apply HYP; auto. *)
      (* apply dmut_wp_sub_fresh in Hwp; auto. *)
      (* - revert Hwp. *)
      (*   apply dmut_wp_monotonic; cbn. *)
      (*   unfold stateprop_impl, stateprop_specialize, stateprop_lift. *)
      (*   intros ? ζ * Hpost ι0 rel10. *)
      (*   dependent elimination ζ as [@env_snoc Σ0 ζ _ t]. *)
      (*   apply syminstance_rel_snoc in rel10. *)
      (*   apply Hpost. now rewrite sub_comp_wk1_tail. *)
      (* - apply stateprop_lift_dcl. *)
      (* - eapply stateprop_lift_vac. *)
    Admitted.

    Lemma dmut_wp_assume_formula {Γ Σ0 Σ1} (ζ01 : Sub Σ0 Σ1) (fml : Formula Σ0) (POST : StateProperty Γ Unit Σ1)
      (POST_dcl : stateprop_downwards_closed POST) (POST_vac : stateprop_vacuous POST) :
      forall Σ2 (ζ12 : Sub Σ1 Σ2) pc2 s2,
        dmut_wp (dmut_sub ζ01 (dmut_assume_formula (Γ := Γ) fml)) POST ζ12 pc2 s2 <->
        POST Σ2 ζ12 (cons (subst (sub_comp ζ01 ζ12) fml) pc2) tt s2.
    Proof.
      (* unfold dmut_wp, dmut_assume_formula, dmut_sub; intros; split; intros. *)
      (* specialize (H Σ1 (sub_id _)). *)
      (* - destruct (try_solve_formula_spec (subst (sub_comp ζ01 (sub_id Σ1)) fml)). *)
      (*   destruct a; cbn in H. *)
      (*   + unfold sub_comp in H. rewrite ?subst_sub_id in H. *)
      (*     revert H. apply POST_dcl. exists (sub_id _). admit. *)
      (*   + apply POST_vac. unfold inconsistent. intros ι. *)
      (*     specialize (H0 ι). rewrite sub_comp_id_right in H0. *)
      (*     rewrite inst_pathcondition_cons. intuition. *)
      (*   + cbn in H. unfold sub_comp in H. rewrite ?subst_sub_id in H. *)
      (*     admit. *)
      (* - admit. *)
    Admitted.

    Lemma dmut_assume_formula_sound {Γ Σ} (ι : SymInstance Σ) (fml : Formula Σ) :
      box approximates
        (Γ1 := Γ) (Γ2 := Γ) ι
        (dmut_assume_formula fml)
        (scmut_assume_formula ι fml).
    Proof.
      (* OLD PROOF. This one didn't use the lemma dmut_wp_assume_formula before, but should. *)
      (* unfold box, approximates. *)
      (* intros * <- ? ? POST Hwp Hpc. *)
      (* unfold dmut_wp, dmut_sub, dmut_assume_formula in Hwp. *)
      (* specialize (Hwp Σ1 (sub_id Σ1)). *)
      (* rewrite sub_comp_id_right in Hwp. *)
      (* unfold scmut_wp, scmut_assume_formula. cbn. *)
      (* intros Hfml. rewrite ?subst_sub_id in Hwp. *)
      (* destruct (try_solve_formula_spec (subst ζ1 fml)). *)
      (* - specialize (H ι1). rewrite inst_subst in H. *)
      (*   apply H in Hfml. clear H. *)
      (*   unfold is_true in Hfml. subst a. *)
      (*   cbn in Hwp. *)
      (*   rewrite ?sub_comp_id_left in Hwp. *)
      (*   unfold stateprop_lift in Hwp. *)
      (*   inster Hwp by apply syminstance_rel_refl. *)
      (*   now apply Hwp. *)
      (* - clear H. *)
      (*   destruct (dmutres_assume_formula pc (subst ζ1 fml) s__sym) as [Σ2 ζ2 [] s2] eqn:?. *)
      (*   + cbn in Hwp. rewrite sub_comp_id_left in Hwp. *)
      (*     assert (resultprop_lift ι1 POST (dmutres_assume_formula pc (subst ζ1 fml) s__sym)) *)
      (*       by (rewrite Heqd; apply Hwp). *)
      (*     rewrite (dmutres_assume_formula_spec pc (subst ζ1 fml) s__sym) in H; auto using resultprop_lift_dcl. *)
      (*     unfold resultprop_lift, stateprop_lift in H. *)
      (*     inster H by apply syminstance_rel_refl. apply H. *)
      (*     rewrite inst_pathcondition_cons. *)
      (*     rewrite inst_subst. auto. *)
      (*   + cbn in Hwp. rewrite sub_comp_id_left in Hwp. *)
      (*     assert (resultprop_lift ι1 POST (dmutres_assume_formula pc (subst ζ1 fml) s__sym)) *)
      (*       by (rewrite Heqd; apply Hwp). *)
      (*     rewrite dmutres_assume_formula_spec in H; auto using resultprop_lift_dcl. *)
      (*     unfold resultprop_lift, stateprop_lift in H. *)
      (*     inster H by apply syminstance_rel_refl. apply H. *)
      (*     rewrite inst_pathcondition_cons. *)
      (*     rewrite inst_subst. auto. *)
    Admitted.

    (* Lemma dmut_wp_angelic_list {Γ1 Γ2 AT D} `{Subst AT} {Σ0 Σ1} (ζ01 : Sub Σ0 Σ1) (func msg : string) (data : D) *)
    (*       (xs : list (DynamicMutator Γ1 Γ2 AT Σ0)) : *)
    (*   forall POST pc s, *)
    (*     dmut_wp (dmut_sub ζ01 (dmut_angelic_list func msg data xs)) POST pc s <-> *)
    (*     exists d, List.In d xs /\ dmut_wp (dmut_sub ζ01 d) POST pc s. *)
    (* Proof. *)
    (* Admitted. *)

    (* Lemma dmut_wp_angelic_finite {Γ1 Γ2 AT F} `{finite.Finite F, Subst AT} {Σ0 Σ1} (ζ01 : Sub Σ0 Σ1) (k : F -> DynamicMutator Γ1 Γ2 AT Σ0) : *)
    (*   forall POST pc s, *)
    (*     dmut_wp (dmut_sub ζ01 (dmut_angelic_finite F k)) POST pc s <-> *)
    (*     exists x : F, dmut_wp (dmut_sub ζ01 (k x)) POST pc s. *)
    (* Proof. *)
    (*   intros *. unfold dmut_angelic_finite. rewrite dmut_wp_angelic_list. *)
    (*   split. *)
    (*   - intros [d [HIn Hwp]]. *)
    (*     apply List.in_map_iff in HIn. *)
    (*     destruct HIn as [x [<- ?]]. *)
    (*     now exists x. *)
    (*   - intros [x Hwp]. exists (k x). split; auto. *)
    (*     apply List.in_map. *)
    (*     apply base.elem_of_list_In. *)
    (*     apply finite.elem_of_enum. *)
    (* Qed. *)

    (* Lemma dmut_wp_demonic_finite {Γ1 Γ2 AT F} `{finite.Finite F, Subst AT} {Σ0 Σ1} (ζ01 : Sub Σ0 Σ1) (k : F -> DynamicMutator Γ1 Γ2 AT Σ0) : *)
    (*   forall POST pc s, *)
    (*     dmut_wp (dmut_sub ζ01 (dmut_demonic_finite F k)) POST pc s <-> *)
    (*     forall x : F, dmut_wp (dmut_sub ζ01 (k x)) POST pc s. *)
    (* Proof. *)
    (* Admitted. *)

    Opaque dmut_assume_formula.

    Lemma dmut_produce_sound {Γ Σ} (asn : Assertion Σ) (ι : SymInstance Σ) :
      box approximates
        (Γ1 := Γ) (Γ2 := Γ) ι
        (dmut_produce asn)
        (scmut_produce ι asn).
    Proof.
      induction asn; cbn.
      - apply dmut_assume_formula_sound.
      - apply dmut_produce_chunk_sound.
      - apply approximates_demonic_binary.
        + unfold dmut_assume_term, scmut_assume_term.
          apply dmut_bind_right_sound; auto_dcl;
            auto using dmut_assume_formula_sound.
        + unfold dmut_assume_term, scmut_assume_term.
          apply dmut_bind_right_sound; auto_dcl;
            auto using dmut_assume_formula_sound.
      - (* unfold box, approximates. intros. *)
        (* rewrite dmut_wp_demonic_finite in H1. *)
        (* specialize (H1 (inst (T := fun Σ => Term Σ (ty_enum E)) ι k)). *)
        (* unfold dmut_bind_right in H1. *)
        (* rewrite dmut_wp_sub_bind in H1. *)
        (* rewrite dmut_wp_assume_formula in H1. *)
        (* rewrite sub_comp_id_right in H1. *)
        (* specialize (H (inst (T := fun Σ => Term Σ (ty_enum E)) ι k)). *)
        (* unfold box, approximates in H. *)
        admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - apply dmut_bind_right_sound; auto_dcl; auto.
      - apply dmut_fresh_sound; auto_dcl; auto.
    Admitted.

    Lemma dmut_assert_formula_sound {Γ Σ} (ι : SymInstance Σ) (fml : Formula Σ) :
      box approximates
        (Γ1 := Γ) (Γ2 := Γ) ι
        (dmut_assert_formula fml)
        (scmut_assert_formula ι fml).
    Proof. Admitted.

    Lemma dmut_consume_chunk_sound {Γ Σ} (c : Chunk Σ) (ι : SymInstance Σ) :
      box approximates
        (Γ1 := Γ) (Γ2 := Γ) ι
        (dmut_consume_chunk c)
        (scmut_consume_chunk (inst ι c)).
    Proof. Admitted.

    Lemma dmut_consume_sound {Γ Σ} (asn : Assertion Σ) (ι : SymInstance Σ) :
      box approximates
        (Γ1 := Γ) (Γ2 := Γ) ι
        (dmut_consume asn)
        (scmut_consume ι asn).
    Proof.
      induction asn; cbn [dmut_consume scmut_consume].
      - apply dmut_assert_formula_sound.
      - apply dmut_consume_chunk_sound.
      - apply approximates_demonic_binary.
        + apply dmut_bind_right_sound; auto_dcl;
            unfold dmut_assume_term, scmut_assume_term;
            auto using dmut_assume_formula_sound.
        + apply dmut_bind_right_sound; auto_dcl;
            unfold dmut_assume_term, scmut_assume_term;
            auto using dmut_assume_formula_sound.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - apply dmut_bind_right_sound; auto_dcl; auto.
      - apply (approximates_angelic (AT := fun Σ => Term Σ _) (A := Lit _)).
        intros a; auto_dcl.
        intros a. apply approximates_sub with (env_snoc ι _ (inst ι a)).
        apply syminstance_rel_snoc. split.
        apply syminstance_rel_refl. reflexivity.
        apply IHasn.
    Admitted.

    Lemma dmut_eval_exp_sound {Γ Σ τ} (e : Exp Γ τ) (ι : SymInstance Σ) :
      box approximates ι (dmut_eval_exp e) (scmut_eval_exp e).
    Proof. Admitted.

    Lemma dmut_eval_exps_sound {Γ Δ Σ} (es : NamedEnv (Exp Γ) Δ) (ι : SymInstance Σ) :
      box approximates ι (dmut_eval_exps es) (scmut_eval_exps es).
    Proof. Admitted.

    Lemma dmut_state_sound {AT A} `{Inst AT A} {Γ1 Γ2 Σ1} (ι1 : SymInstance Σ1)
          (f : forall Σ2 (ζ12 : Sub Σ1 Σ2), SymbolicState Γ1 Σ2 -> AT Σ2 * SymbolicState Γ2 Σ2)
          (g  : SCState Γ1 -> A * SCState Γ2)
          (fg : forall Σ2 (ζ12 : Sub Σ1 Σ2) (ι2 : SymInstance Σ2) s2,
              syminstance_rel ζ12 ι1 ι2 ->
              inst ι2 (f Σ2 ζ12 s2) = g (inst ι2 s2)) :
      box approximates ι1 (dmut_state f) (scmut_state g).
    Proof.
      (* unfold box, approximates, dmut_state, scmut_state, stateprop_lift, dmut_wp, dmut_sub, scmut_wp; cbn. *)
      (* intros Σ2 ζ12 ι2 rel12 pc2 s2 POST Hf Hpc2; cbn in *. *)
      (* specialize (Hf Σ2 (sub_id _)). *)
      (* rewrite ?sub_comp_id_right, ?subst_sub_id in Hf. *)
      (* destruct (f Σ2 ζ12 s2) eqn:?; cbn in *. *)
      (* pose proof (f_equal (inst ι2) Heqp) as Hinst. *)
      (* rewrite fg in Hinst; auto. rewrite Hinst. cbn. *)
      (* apply Hf; auto. rewrite sub_comp_id_left. apply syminstance_rel_refl. *)
    Admitted.

    Lemma dmut_call_sound {Γ Δ τ Σ} (c : SepContract Δ τ) (ts : NamedEnv (Term Σ) Δ) (ι : SymInstance Σ) :
      box approximates ι (@dmut_call Γ Δ τ Σ c ts) (scmut_call c (inst ι ts)).
    Proof.
      destruct c as [Σ__c δ pre result post]; cbn [dmut_call scmut_call].
      apply approximates_angelic; intros; auto_dcl.
    Admitted.

    Lemma dmut_exec_sound {Γ Σ σ} (s : Stm Γ σ) (ι : SymInstance Σ) :
      box approximates ι (dmut_exec s) (scmut_exec s).
    Proof.
      induction s; cbn [dmut_exec scmut_exec].
      - pose proof (approximates_pure (Γ := Γ) (ι := ι) (a := term_lit τ l)).
        now cbn in H.
      - apply dmut_eval_exp_sound.
      - apply dmut_bind_sound; auto_dcl.
        + admit.
        + admit.
        + admit.
      - admit.
      - apply dmut_bind_sound; auto_dcl.
        + admit.
        + admit.
        + intros.
          apply dmut_bind_right_sound.
          admit.
          admit.
          apply dmut_state_sound.
          { intros ? ? ? [δ h] ?; cbn.
            f_equal. f_equal.
            unfold inst; cbn.
            rewrite env_map_update.
            rewrite inst_subst.
            unfold syminstance_rel in *. subst.
            reflexivity.
          }
          apply approximates_pure.
      - destruct (CEnv f) as [c|] eqn:?.
        + apply dmut_bind_sound; intros; auto_dcl.
          apply dmut_eval_exps_sound.
          apply dmut_call_sound.
        + admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - apply approximates_block.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - apply approximates_fail.
    Admitted.

    Lemma dmut_leakcheck_sound {Γ Σ} (ι : SymInstance Σ) :
      box approximates ι (@dmut_leakcheck Γ Σ) (@scmut_leakcheck Γ).
    Proof.
      (* unfold box, approximates, dmut_wp, scmut_wp; cbn; intros. *)
      (* specialize (H0 Σ1 (sub_id _)). *)
      (* rewrite outcome_satisfy_bind, subst_sub_id in H0. *)
      (* destruct s__sym as [σ []]; cbn in *. *)
      (* - unfold stateprop_lift in H0. specialize (H0 ι1). *)
      (*   rewrite ?sub_comp_id_left, ?subst_sub_id in H0. *)
      (*   inster H0 by apply syminstance_rel_refl. intuition. *)
      (* - unfold contradiction in H0; cbn in H0. *)
      (*   rewrite subst_sub_id in H0. intuition. *)
    Admitted.

    Opaque dmut_consume dmut_exec dmut_leakcheck dmut_produce.
    Opaque scmut_consume scmut_exec scmut_leakcheck scmut_produce.

    Lemma dmut_contract_sound {Γ τ} (c : SepContract Γ τ) (s : Stm Γ τ) (ι : SymInstance (sep_contract_logic_variables c)) :
      box approximates ι (@dmut_contract Γ τ c s) (@scmut_contract Γ τ c s ι).
    Proof.
      unfold dmut_contract, scmut_contract; destruct c as [Σ δ pre result post]; cbn in *.
      unfold dmut_bind_right.
      apply dmut_bind_sound; intros; auto_dcl.
      apply dmut_produce_sound.
      eapply approximates_sub; eauto.
      apply dmut_bind_sound; intros; auto_dcl.
      apply dmut_exec_sound.
      apply dmut_bind_sound; intros; auto_dcl.
      eapply approximates_sub; eauto.
      unfold syminstance_rel in *; subst. rewrite <- H0.
      apply dmut_consume_sound.
      eapply approximates_sub; eauto.
      apply dmut_leakcheck_sound.
    Admitted.

    Opaque scmut_contract dmut_contract.

    Lemma outcome_satisfy_bimap {E F A B : Type} (o : Outcome E A) (f : E -> F) (g : A -> B) Q (P : B -> Prop) :
      outcome_satisfy (outcome_bimap f g o) Q P <-> outcome_satisfy o (fun e => Q (f e)) (fun a => P (g a)).
    Proof. induction o; firstorder. Qed.

    Lemma outcome_satisfy_bimonotonic {E A} {P Q : E -> Prop} {R S : A -> Prop} (o : Outcome E A)
          (hype : forall e, P e -> Q e)
          (hypa : forall a, R a -> S a) :
      outcome_satisfy o P R -> outcome_satisfy o Q S.
    Proof. induction o; firstorder. Qed.

    Lemma symbolic_sound {Γ τ} (c : SepContract Γ τ) (body : Stm Γ τ) :
      ValidContractDynMut c body ->
      ValidContractSCMut c body.
    Proof.
      (* unfold ValidContractDynMut, ValidContractSCMut, outcome_safe, *)
      (*   dmut_contract_outcome, semiconcrete_outcome_contract; cbn. *)
      (* rewrite outcome_satisfy_bimap. intros Hd ι. *)
      (* pose proof (@dmut_contract_sound _ _ c body ι) as H. apply approximates_proj in H. *)
      (* specialize (H nil (symbolicstate_initial (sep_contract_localstore c))). *)
      (* rewrite outcome_satisfy_map. *)
      (* match goal with *)
      (* | |- outcome_satisfy ?o ?F ?P => *)
      (*   change (outcome_satisfy o F (fun r => (fun v s => P (MkSCMutResult v s)) (scmutres_value r) (scmutres_state r))) *)
      (* end. *)
      (* apply H; [ idtac | now compute ]. clear H. *)
      (* match goal with *)
      (* | H: outcome_satisfy ?o (fun _ : DynamicMutatorError => False) ?P |- _ => *)
      (*   apply (@outcome_satisfy_bimonotonic _ _ _ contradiction P P) in H; *)
      (*     auto; try contradiction *)
      (* end. *)
      (* intros Σ1 ζ01. revert Hd. *)
      (* eapply dmut_contract_dcl with ζ01; *)
      (*   rewrite ?subst_sub_id_right; try easy. *)
      (* intros [Σ2 ζ12 pc2 [] s2]; unfold stateprop_lift; cbn; auto. *)
    Admitted.

    Section Leftovers.

      Context `{HL: IHeaplet L} {SLL: ISepLogicLaws L}.

      Definition interpret_heap {Σ} (ι : SymInstance Σ) (h : SymbolicHeap Σ) : L :=
        List.fold_right (fun c h => ASS.inst_chunk ι c ∧ h) ltrue h.

      Transparent subst SubstEnv.
      Lemma subst_lookup {Γ Σ Σ' x σ} (xInΓ : (x ∶ σ)%ctx ∈ Γ) (ζ : Sub Σ Σ') (δ : SymbolicLocalStore Γ Σ) :
        (subst ζ (δ ‼ x)%exp = (subst ζ δ ‼ x)%exp).
      Proof.
        unfold subst at 2, subst_localstore, SubstEnv.
        now rewrite env_lookup_map.
      Qed.

      Lemma subst_symboliceval {Γ τ Σ Σ'} (e : Exp Γ τ) (ζ : Sub Σ Σ') (δ : SymbolicLocalStore Γ Σ) :
        subst (T := fun Σ => Term Σ _) ζ (symbolic_eval_exp δ e) = symbolic_eval_exp (subst ζ δ) e.
      Proof.
        induction e; cbn; f_equal; auto.
        { now rewrite (subst_lookup xInΓ). }
        all: induction es; cbn in *; destruct_conjs; f_equal; auto.
      Qed.

      Transparent inst instantiate_env.

      Lemma eval_exp_inst {Γ Σ τ} (ι : SymInstance Σ) (δΓΣ : SymbolicLocalStore Γ Σ) (e : Exp Γ τ) :
        eval e (inst ι δΓΣ) = inst ι (symbolic_eval_exp δΓΣ e).
      Proof.
        induction e; cbn; repeat f_equal; auto.
        { unfold inst; cbn. now rewrite env_lookup_map. }
        2: {
          induction es as [|eb n es IHes]; cbn in *.
          { reflexivity. }
          { destruct X as [-> Heqs].
            change (inst_term ?ι ?t) with (inst ι t).
            destruct (inst ι (symbolic_eval_exp δΓΣ eb));
              cbn; f_equal; auto.
          }
        }
        all: induction es; cbn in *; destruct_conjs; f_equal; auto.
      Qed.

    End Leftovers.

  End DynMutV1Soundness.

End Soundness.
