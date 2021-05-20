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
     Arith.PeanoNat
     Bool.Bool
     Classes.Morphisms
     Classes.Morphisms_Prop
     Classes.Morphisms_Relations
     Classes.RelationClasses
     Lists.List
     Logic.EqdepFacts
     Program.Equality
     Program.Tactics
     Relations.Relation_Definitions
     Relations.Relation_Operators
     Strings.String
     ZArith.ZArith.
From Coq Require
     Vector.
From Equations Require Import Equations.

From MicroSail Require Import
     Sep.Spec
     SemiConcrete.Outcome
     Syntax.

From stdpp Require
     base finite list option.

Import CtxNotations.
Import EnvNotations.
Import ListNotations.
Import OutcomeNotations.

Set Implicit Arguments.

Delimit Scope mutator_scope with mut.
Delimit Scope smut_scope with smut.

Module Mutators
       (termkit : TermKit)
       (progkit : ProgramKit termkit)
       (assertkit : AssertionKit termkit progkit)
       (symcontractkit : SymbolicContractKit termkit progkit assertkit).

  Export symcontractkit.

  Declare Scope modal.
  Delimit Scope modal with modal.

  Import Entailment.

  Record World : Type :=
    MkWorld
      { wctx :> LCtx;
        wco  : PathCondition wctx;
      }.

  Record Acc (w1 w2 : World) : Type :=
    MkAcc
      { wsub :> Sub w1 w2;
        (* went :  wco w2 ⊢ subst (wco w1) wsub; *)
      }.

  Notation "w1 ⊒ w2" := (Acc w1 w2) (at level 80).

  Definition went {w0 w1} (ω01 : w0 ⊒ w1) : Prop :=
    wco w1 ⊢ subst (wco w0) (wsub ω01).

  Local Obligation Tactic := idtac.
  Definition wrefl {w} : w ⊒ w :=
    {| wsub := sub_id w |}.
  (* Next Obligation. *)
  (*   intros ?. now rewrite subst_sub_id. *)
  (* Qed. *)

  Lemma went_wrefl {w} :
    went (wrefl (w := w)).
  Proof.
    intros ι. cbn.
    now rewrite subst_sub_id.
  Qed.

  Definition wtrans {w0 w1 w2} : w0 ⊒ w1 -> w1 ⊒ w2 -> w0 ⊒ w2 :=
    fun ω01 ω12 => {| wsub := subst (T := Sub _) ω01 ω12 |}.
  (* Next Obligation. *)
  (*   intros *. *)
  (*   rewrite subst_sub_comp. *)
  (*   intros ι2 Hpc2. *)
  (*   rewrite inst_subst. *)
  (*   apply (went ω01 (inst (T := Sub _) ω12 ι2)). *)
  (*   rewrite <- inst_subst. *)
  (*   apply (went ω12 ι2 Hpc2). *)
  (* Defined. *)

  Lemma went_wtrans {w0 w1 w2} {ω01 : w0 ⊒ w1} {ω12 : w1 ⊒ w2} :
    went ω01 -> went ω12 -> went (wtrans ω01 ω12).
  Proof.
    intros Hω01 Hω12. unfold went, wtrans.
    cbn [wctx wco wsub].
    rewrite subst_sub_comp.
    transitivity (subst (wco w1) ω12).
    apply Hω12.
    apply proper_subst_entails.
    apply Hω01.
  Qed.

  Definition wnil : World := @MkWorld ctx_nil nil.
  Definition wsnoc (w : World) (b : 𝑺 * Ty) : World :=
    @MkWorld (wctx w ▻ b) (subst (wco w) sub_wk1).
  Definition wformula (w : World) (f : Formula w) : World :=
    @MkWorld (wctx w) (cons f (wco w)).
  Definition wsubst (w : World) x {σ} {xIn : x :: σ ∈ w} (t : Term (w - (x :: σ)) σ) : World.
  Proof.
    apply (@MkWorld (ctx_remove xIn)).
    refine (subst (wco w) _).
    apply sub_single.
    apply t.
  Defined.
  Global Arguments wsubst w x {σ xIn} t.

  Fixpoint wcat (w : World) (Σ : LCtx) : World :=
    match Σ with
    | ctx_nil      => w
    | ctx_snoc Σ b => wsnoc (wcat w Σ) b
    end.

  Definition wsnoc_sup {w : World} {b : 𝑺 * Ty} : w ⊒ wsnoc w b :=
    MkAcc w (wsnoc w b) sub_wk1.
  (* Next Obligation. *)
  (* Proof. *)
  (*   intros w b ι Hpc. apply Hpc. *)
  (* Qed. *)

  Lemma went_wsnoc_sup {w : World} {b : 𝑺 * Ty} :
    went (@wsnoc_sup w b).
  Proof.
    intros ι Hpc. apply Hpc.
  Qed.

  Definition wsnoc_sub {w1 w2 : World} (ω12 : w1 ⊒ w2) (b : 𝑺 * Ty) (t : Term w2 (snd b)) :
    wsnoc w1 b ⊒ w2 :=
    MkAcc (wsnoc w1 b) w2 (sub_snoc ω12 b t).

  Lemma went_wsnoc_sub {w1 w2 : World} (ω12 : w1 ⊒ w2) (b : 𝑺 * Ty) (t : Term w2 (snd b)) :
    went ω12 ->
    went (@wsnoc_sub w1 w2 ω12 b t).
  Proof.
    unfold went, entails. intros Hpc12 ι2 Hpc2.
    specialize (Hpc12 ι2 Hpc2).
    rewrite inst_subst in Hpc12.
    unfold wsnoc, wsnoc_sub. cbn - [subst inst].
    rewrite ?inst_subst.
    rewrite inst_sub_snoc.
    rewrite inst_sub_wk1.
    apply Hpc12.
  Qed.

  Fixpoint wcat_sub {w1 w2 : World} (ω12 : w1 ⊒ w2) {Δ : LCtx} :
    Sub Δ w2 ->
    wcat w1 Δ ⊒ w2.
  Proof.
    destruct Δ; cbn [wcat].
    - intros _. apply ω12.
    - intros ζ. destruct (snocView ζ).
      apply wsnoc_sub.
      apply wcat_sub.
      auto.
      auto.
      auto.
  Defined.

  (* Next Obligation. *)
  (* Proof. *)
  (* Qed. *)

  Definition wformula_sup {w : World} {f : Formula w} : w ⊒ wformula w f :=
    MkAcc w (wformula w f) (sub_id (wctx w)).
  (* Next Obligation. *)
  (* Proof. *)
  (*   intros w f ι. *)
  (*   rewrite subst_sub_id. cbn. *)
  (*   rewrite inst_pathcondition_cons. *)
  (*   now intros []. *)
  (* Qed. *)

  Lemma went_wformula_sup {w f} :
    went (@wformula_sup w f).
  Proof.
    intros ι.
    rewrite subst_sub_id. cbn.
    rewrite inst_pathcondition_cons.
    now intros [].
  Qed.

  Definition wformula_sub {w : World} {f : Formula w} : wformula w f ⊒ w :=
    MkAcc (wformula w f) w (sub_id (wctx w)).
  (* Next Obligation. *)
  (* Proof. *)
  (*   intros w f ι. *)
  (*   rewrite subst_sub_id. cbn. *)
  (*   rewrite inst_pathcondition_cons. *)
  (*   now intros []. *)
  (* Qed. *)

  Definition wformulas (w : World) (fmls : List Formula w) : World :=
    @MkWorld (wctx w) (app fmls (wco w)).

  Definition wformulas_sup (w : World) (fmls : List Formula w) :
    w ⊒ wformulas w fmls.
  Proof.
    constructor.
    apply (sub_id (wctx w)).
  Defined.

  Definition wred_sup {w : World} b (t : Term w (snd b)) :
    wsnoc w b ⊒ w :=
    MkAcc (wsnoc w b) w (sub_snoc (sub_id w) b t).

  Definition wsubst_sup {w : World} {x σ} {xIn : x :: σ ∈ w} {t : Term (w - (x :: σ)) σ} :
    w ⊒ wsubst w x t :=
    MkAcc w (wsubst w x t) (sub_single xIn t).
  (* Next Obligation. *)
  (* Proof. *)
  (*   intros w x σ xIn t ι Hpc. apply Hpc. *)
  (* Qed. *)

  Definition wacc_snoc {w0 w1 : World} (ω01 : w0 ⊒ w1) (b : 𝑺 * Ty) :
    wsnoc w0 b ⊒ wsnoc w1 b :=
    MkAcc (wsnoc w0 b) (wsnoc w1 b) (sub_up1 ω01).
  (* Next Obligation. *)
  (*   intros ? ? ? ?. *)
  (*   unfold wsnoc in *. *)
  (*   cbn [wco wctx] in *. *)
  (*   rewrite <- subst_sub_comp. *)
  (*   rewrite sub_comp_wk1_comm. *)
  (*   rewrite subst_sub_comp. *)
  (*   apply proper_subst_entails. *)
  (*   apply went. *)
  (* Qed. *)

  Lemma went_wacc_snoc {w0 w1} {ω01 : w0 ⊒ w1} {b : 𝑺 * Ty} :
    went ω01 ->
    went (wacc_snoc ω01 b).
  Proof.
    unfold wacc_snoc, wsnoc.
    intros Hω01 ι1 Hpc1. cbn - [inst] in *.
    specialize (Hω01 (inst sub_wk1 ι1)).
    rewrite <- subst_sub_comp.
    rewrite sub_comp_wk1_comm.
    cbn in *.
    rewrite inst_subst in Hω01.
    rewrite ?inst_subst.
    rewrite ?inst_subst in Hpc1.
    intuition.
  Qed.

  Definition wacc_formula {w0 w1} (ω01 : w0 ⊒ w1) (fml : Formula w0) :
    wformula w0 fml ⊒ wformula w1 (subst fml ω01) :=
    MkAcc (MkWorld (cons fml (wco w0))) (MkWorld (cons (subst fml ω01) (wco w1))) ω01.

  Lemma went_wacc_formula {w0 w1} {ω01 : w0 ⊒ w1} {fml : Formula w0} :
    went ω01 ->
    went (wacc_formula ω01 fml).
  Proof.
    unfold wacc_formula, wformula.
    intros Hω01 ι1 Hpc1. specialize (Hω01 ι1).
    cbn - [inst] in *.
    rewrite ?inst_pathcondition_cons, ?inst_subst in *.
    intuition.
  Qed.

  Notation WList A := (fun w : World => list (A w)).
  Notation STerm σ := (fun Σ => Term Σ σ).

  Module WorldInstance.

    Record WInstance (w : World) : Set :=
      MkWInstance
        { ιassign :> SymInstance w;
          ιvalid  : instpc (wco w) ιassign;
        }.

    Program Definition winstance_formula {w} (ι : WInstance w) (fml : Formula w) (p : inst (A := Prop) fml ι) :
      WInstance (wformula w fml) :=
      {| ιassign := ι; |}.
    Next Obligation.
    Proof.
      intros. cbn.
      apply inst_pathcondition_cons. split; auto.
      apply ιvalid.
    Qed.

    Program Definition winstance_snoc {w} (ι : WInstance w) {b : 𝑺 * Ty} (v : Lit (snd b)) :
      WInstance (wsnoc w b) :=
      {| ιassign := env_snoc (ιassign ι) b v; |}.
    Next Obligation.
    Proof.
      intros. unfold wsnoc. cbn [wctx wco].
      rewrite inst_subst, inst_sub_wk1.
      apply ιvalid.
    Qed.

    Fixpoint winstance_cat {Σ} (ι : WInstance Σ) {Δ} (ιΔ : SymInstance Δ) :
      WInstance (wcat Σ Δ).
    Proof.
      destruct ιΔ; cbn.
      - apply ι.
      - apply winstance_snoc.
        apply winstance_cat.
        apply ι.
        apply ιΔ.
        apply db.
    Defined.

    Program Definition winstance_subst {w} (ι : WInstance w) {x σ} {xIn : x :: σ ∈ w}
      (t : Term (w - (x :: σ)) σ) (p : inst t (env_remove' (x :: σ) (ιassign ι) xIn) = env_lookup (ιassign ι) xIn) :
      WInstance (wsubst w x t) :=
      @MkWInstance (wsubst w x t) (env_remove' _ (ιassign ι) xIn) _.
    Next Obligation.
      intros. cbn. rewrite inst_subst.
      rewrite inst_sub_single.
      apply ιvalid.
      apply p.
    Qed.

    Program Definition instacc {w0 w1} (ω01 : w0 ⊒ w1) (Hω01 : went ω01) (ι : WInstance w1) : WInstance w0 :=
       {| ιassign := inst (wsub ω01) (ιassign ι) |}.
    Next Obligation.
    Proof.
      intros w0 w1 ω01 Hω01 ι.
      rewrite <- inst_subst.
      apply Hω01.
      apply ιvalid.
    Qed.

  End WorldInstance.

  Definition TYPE : Type := World -> Type.
  Bind Scope modal with TYPE.
  Definition Valid (A : TYPE) : Type :=
    forall w, A w.
  Definition Impl (A B : TYPE) : TYPE :=
    fun w => A w -> B w.
  Definition Box (A : TYPE) : TYPE :=
    fun w0 => forall w1, w0 ⊒ w1 -> A w1.
  Definition Snoc (A : TYPE) (b : 𝑺 * Ty) : TYPE :=
    fun w => A (wsnoc w b).
  Definition Forall {I : Type} (A : I -> TYPE) : TYPE :=
    fun w => forall i : I, A i w.
  Definition Cat (A : TYPE) (Δ : LCtx) : TYPE :=
    fun w => A (wcat w Δ).

  Module ModalNotations.

    Notation "⊢ A" := (Valid A%modal) (at level 100).
    Notation "A -> B" := (Impl A%modal B%modal) : modal.
    Notation "□ A" := (Box A%modal) (at level 85, format "□ A", right associativity) : modal.
    Notation "⌜ A ⌝" := (fun (_ : World) => A%type) (at level 0, format "⌜ A ⌝") : modal.
    Notation "'∀' x .. y , P " :=
      (Forall (fun x => .. (Forall (fun y => P%modal)) ..))
        (at level 99, x binder, y binder, right associativity)
      : modal.

  End ModalNotations.
  Import ModalNotations.
  Open Scope modal.

  Definition K {A B} :
    ⊢ □(A -> B) -> (□A -> □B) :=
    fun w0 f a w1 ω01 =>
      f w1 ω01 (a w1 ω01).
  Definition T {A} :
    ⊢ □A -> A :=
    fun w0 a => a w0 wrefl.
  Definition four {A} :
    ⊢ □A -> □□A :=
    fun w0 a w1 ω01 w2 ω12 =>
      a w2 (wtrans ω01 ω12).
  Global Arguments four : simpl never.

  (* faster version of (four _ sub_wk1) *)
  (* Definition four_wk1 {A} : *)
  (*   ⊢ □A -> ∀ b, Snoc (□A) b := *)
  (*   fun w0 a b w1 ω01 => a w1 (env_tail ω01). *)
  (* Arguments four_wk1 {A Σ0} pc0 a b [Σ1] ζ01 : rename. *)

  Definition valid_box {A} :
    (⊢ A) -> (⊢ □A) :=
    fun a w0 w1 ω01 => a w1.
  Global Arguments valid_box {A} a {w} [w1].

  Definition map_box {A B} (f : ⊢ A -> B) : ⊢ □A -> □B :=
    fun w0 a w1 ω01 => f w1 (a w1 ω01).

  Notation "f <$> a" := (map_box f a) (at level 40, left associativity).
  Notation "f <*> a" := (K f a) (at level 40, left associativity).

  Definition PROP : TYPE :=
    fun _ => Prop.

  Definition comp {A B C} :
    ⊢ (B -> C) -> (A -> B) -> (A -> C) :=
    fun w0 => Basics.compose.

  Definition bcomp {A B C} :
    ⊢ □(B -> C) -> □(A -> B) -> □(A -> C) :=
    fun w0 f g => comp <$> f <*> g.

  Module LogicalRelation.

    Import Entailment.

    Class LR (A : TYPE) : Type :=
      lr : forall w0 w1, w0 ⊒ w1 -> A w0 -> A w1 -> Prop.

    Class LRRefl (A : TYPE) `{LR A} : Prop :=
      { lr_refl :
          forall w0 (a : A w0),
            lr wrefl a a;
      }.
    Global Arguments LRRefl A {_}.

    Global Instance LRPROP : LR PROP :=
      fun w0 w1 ω01 (P : PROP w0) (Q : PROP w1) => (P -> Q)%type.
    Global Instance LRReflPROP : LRRefl PROP :=
      {| lr_refl w0 (P : PROP w0) (HP : P) := HP;
      |}.

    Global Instance LRTerm {σ} : LR (STerm σ) :=
      fun w0 w1 ω01 t0 t1 =>
        forall ι1 : SymInstance w1,
          inst t0 (inst (T := Sub _) ω01 ι1) = inst t1 ι1.

    Global Instance LRFormula : LR Formula :=
      fun w0 w1 ω01 f0 f1 =>
        forall ι1 : SymInstance w1,
          instpc (wco w1) ι1 ->
          inst (T := Formula) (A := Prop) f0 (inst (T:= Sub _) ω01 ι1) ->
          inst (T := Formula) (A := Prop) f1 ι1.
    Global Instance LRReflFormula : LRRefl Formula.
    Proof.
      constructor. unfold lr, LRFormula. intros *.
      unfold wrefl. cbn. now rewrite inst_sub_id.
    Qed.

    Global Instance LRImpl {A B} `{LR A, LR B} : LR (A -> B) :=
      fun w0 w1 ω01 f0 f1 =>
           forall a0 a1,
             lr ω01 a0 a1 ->
             lr ω01 (f0 a0) (f1 a1).

    (* Instance LRPair {A B} `{LR A, LR B} : LR (Pair A B) := *)
    (*   fun Σ0 pc0 Σ1 ζ01 pc1 ab1 ab2 => *)
    (*     let (a1, b1) := ab1 in *)
    (*     let (a2, b2) := ab2 in *)
    (*     lr pc0 ζ01 pc1 a1 a2 /\ lr pc0 ζ01 pc1 b1 b2. *)

    Global Instance LRBox {A} `{LR A} : LR (Box A) :=
      fun w0 w1 ω01 b1 b2 =>
        forall w2 (ω12 : w1 ⊒ w2),
          went ω12 ->
          lr ω12 (b1 _ ω01) (b2 _ ω12).

    Global Instance LRReflBox {A} `{LR A} : LRRefl (Box A).
    Proof.
      constructor. unfold lr, LRBox.
      intros w0 a0 w1 ω01.
      (* Downwards close is LRRefl for Box right!? *)
    Abort.

    Global Instance LRInstance : LR SymInstance :=
      fun w0 w1 ω01 ι0 ι1 =>
        (* instpc ι1 pc1 /\ instpc ι0 pc0 /\ *)
        ι0 = inst (wsub ω01) ι1.

    Global Instance LRReflInstance : LRRefl SymInstance.
    Proof.
      constructor. unfold lr, LRInstance.
      intros w0 ι0. unfold wrefl. cbn.
      now rewrite inst_sub_id.
    Qed.

    Definition dcl {A} `{LR A} : ⊢ □A -> PROP :=
      fun w0 a =>
        forall w1 (ω01 : w0 ⊒ w1),
          went ω01 ->
          lr ω01 a (four a ω01).

    Lemma dcl_four {A} `{LR A} {w0} (a : Box A w0) (a_dcl : dcl a) :
      forall w1 (ω01 : w0 ⊒ w1), went ω01 -> dcl (four a ω01).
    Proof.
      unfold dcl, four, lr, LRBox, went in *; cbn.
      intros w1 ω01 Hω01.
      intros w2 ω12 Hω12.
      intros w3 ω23 Hω23.
      unfold wtrans. cbn [wsub].
      rewrite <- sub_comp_assoc.
      apply a_dcl; auto. cbn [wsub].
      rewrite subst_sub_comp.
      transitivity (subst (wco w1) ω12); auto.
      now apply proper_subst_entails.
    Qed.

    (* Lemma dcl_four_wk1 {A} `{LR A} {Σ0} (pc0 : PathCondition Σ0) (a : Box A Σ0) (a_dcl : dcl pc0 a) : *)
    (*   forall (b : 𝑺 * Ty), *)
    (*     dcl (subst pc0 sub_wk1) (four_wk1 pc0 a b). *)
    (* Proof. *)
    (*   unfold dcl, four_wk1, four, lr, LRBox. *)
    (*   intros b. *)
    (*   intros Σ1 ζ01 pc1 Σ2 ζ12 pc2 Hpc23. *)
    (*   rewrite <- ?sub_comp_wk1_tail. *)
    (*   rewrite <- sub_comp_assoc. *)
    (*   apply a_dcl; auto. *)
    (*   now rewrite subst_sub_comp. *)
    (* Qed. *)

    (* Lemma dcl_four_cons {A} `{LR A} {Σ} (pc : PathCondition Σ) *)
    (*   (fml : Formula Σ) (a : Box A Σ) (a_dcl : dcl pc a) : *)
    (*   dcl (cons fml pc) a. *)
    (* Proof. *)
    (*   intros Σ1 ζ01 pc1 Hpc01. cbn in Hpc01. *)
    (*   apply entails_cons in Hpc01. destruct Hpc01. *)
    (*   now apply a_dcl. *)
    (* Qed. *)

    Global Hint Resolve dcl_four : dcl.
    (* Global Hint Resolve dcl_four_wk1 : dcl. *)
    (* Global Hint Resolve dcl_four_cons : dcl. *)

  End LogicalRelation.

  Class Persistent (A : TYPE) (* `{LogicalRelation.LR A} *) : Type :=
    persist     : ⊢ A -> □A.
      (* persist_lr  : forall w0 (a : A w0) w1 (ω01 : w0 ⊒ w1), *)
      (*     LogicalRelation.lr ω01 a (persist a ω01); *)
      (* persist_dcl : *)
      (*   forall w (a : A w), *)
      (*     LogicalRelation.dcl (persist a) *)
  (* Global Arguments Persistent A {_}. *)

  Global Instance persist_subst {A} `{Subst A} : Persistent A :=
    fun w0 x w1 ω01 => subst x ω01.

  Notation persist__term t :=
    (@persist (STerm _) (@persist_subst (fun Σ => Term Σ _) (@SubstTerm _)) _ t).

  Section Obligations.

    Inductive Obligation {Σ} (msg : Message Σ) (fml : Formula Σ) (ι : SymInstance Σ) : Prop :=
    | obligation (p : inst fml ι : Prop).

  End Obligations.

  Section MultiSubs.

    Inductive MultiSub (w : World) : World -> Type :=
    | multisub_id        : MultiSub w w
    | multisub_cons {w' x σ} (xIn : (x::σ) ∈ w) (t : Term (wctx w - (x::σ)) σ)
                    (ν : MultiSub (wsubst w x t) w')
                    : MultiSub w w'.

    Global Arguments multisub_id {_}.
    Global Arguments multisub_cons {_ _} x {_ _} t ν.

    Fixpoint wmultisub_sup {w1 w2} (ν : MultiSub w1 w2) : w1 ⊒ w2 :=
      match ν with
      | multisub_id         => wrefl
      | multisub_cons _ _ ν => wtrans wsubst_sup (wmultisub_sup ν)
      end.

    Fixpoint sub_multishift {w1 w2} (ζ : MultiSub w1 w2) : Sub w2 w1 :=
      match ζ with
      | multisub_id         => sub_id _
      | multisub_cons x t ζ => subst (sub_multishift ζ) (sub_shift _)
      end.

    Fixpoint inst_multisub {w0 w1} (ζ : MultiSub w0 w1) (ι : SymInstance w0) : Prop :=
      match ζ with
      | multisub_id => True
      | @multisub_cons _ Σ' x σ xIn t ζ0 =>
        let ι' := env_remove' (x :: σ) ι xIn in
        env_lookup ι xIn = inst t ι' /\ inst_multisub ζ0 ι'
      end.

    Lemma inst_multi {w1 w2 : World} (ι1 : SymInstance w1) (ζ : MultiSub w1 w2) :
      inst_multisub ζ ι1 ->
      inst (wsub (wmultisub_sup ζ)) (inst (sub_multishift ζ) ι1) = ι1.
    Proof.
      intros Hζ. induction ζ; cbn - [subst].
      - now rewrite ?inst_sub_id.
      - cbn in Hζ. destruct Hζ as [? Hζ]. rewrite <- inst_sub_shift in Hζ.
        rewrite ?inst_subst.
        rewrite IHζ; auto. rewrite inst_sub_shift.
        now rewrite inst_sub_single.
    Qed.

  End MultiSubs.

  Section Solver.

    Definition try_solve_eq {Σ σ} (t1 t2 : Term Σ σ) : option bool :=
      if Term_eqb t1 t2
      then Some true
      else
        (* If the terms are literals, we can trust the negative result. *)
        match t1 , t2 with
        | term_lit _ _ , term_lit _ _ => Some false
        | term_inr _   , term_inl _   => Some false
        | term_inl _   , term_inr _   => Some false
        | _            , _            => None
        end.

    Lemma try_solve_eq_spec {Σ σ} (t1 t2 : Term Σ σ) :
      OptionSpec
        (fun b => forall ι, inst t1 ι = inst t2 ι <-> is_true b)
        True
        (try_solve_eq t1 t2).
    Proof.
      unfold try_solve_eq.
      destruct (Term_eqb_spec t1 t2).
      - constructor. intros. apply reflect_iff.
        constructor. congruence.
      - destruct t1; dependent elimination t2; constructor; auto;
        intros; apply reflect_iff; constructor; cbn; congruence.
    Qed.

    (* Check if the given formula is always true or always false for any
       assignments of the logic variables. *)
    Definition try_solve_formula {Σ} (fml : Formula Σ) : option bool :=
      match fml with
      | formula_bool t =>
        match t in Term _ σ return option (Lit σ)
        with
        | term_lit _ b => Some b
        | _            => None
        end
      | formula_prop _ _ => None
      | formula_eq t1 t2 => try_solve_eq t1 t2
        (* else Term_eqvb t1 t2 *)
      | formula_neq t1 t2 => option_map negb (try_solve_eq t1 t2)
        (* else option_map negb (Term_eqvb t1 t2) *)
      end.

    Lemma try_solve_formula_spec {Σ} (fml : Formula Σ) :
      OptionSpec
        (fun b => forall ι, inst fml ι <-> is_true b)
        True
        (try_solve_formula fml).
    Proof.
      destruct fml; cbn.
      - dependent elimination t; constructor; auto.
      - constructor; auto.
      - destruct (try_solve_eq_spec t1 t2); now constructor.
      - destruct (try_solve_eq_spec t1 t2); constructor; auto.
        intros ι. specialize (H ι). destruct a; intuition.
    Qed.

    (* Poor man's unification *)
    Definition try_unify {w : World} {σ} (t1 t2 : Term w σ) :
      option { w' & MultiSub w w' } :=
      match t1 with
      | @term_var _ ς σ ςInΣ =>
        fun t2 : Term w σ =>
          match occurs_check ςInΣ t2 with
          | Some t => Some (existT _ (multisub_cons ς t multisub_id))
          | None => None
          end
      | _ => fun _ => None
      end t2.

    Definition try_propagate {w : World} (fml : Formula w) :
      option { w' & MultiSub w w' } :=
      match fml with
      | formula_eq t1 t2 =>
        match try_unify t1 t2 with
        | Some r => Some r
        | None => try_unify t2 t1
        end
      | _ => None
      end.

    Lemma try_unify_spec {w : World} {σ} (t1 t2 : Term w σ) :
      OptionSpec (fun '(existT w' ν) => forall ι, inst t1 ι = inst t2 ι <-> inst_multisub ν ι) True (try_unify t1 t2).
    Proof.
      unfold try_unify. destruct t1; cbn; try (constructor; auto; fail).
      destruct (occurs_check ςInΣ t2) eqn:Heq; constructor; auto.
      apply (occurs_check_sound (T := fun Σ => Term Σ _)) in Heq. subst.
      intros ι. rewrite inst_subst, inst_sub_shift.
      cbn. intuition.
    Qed.

    Lemma try_propagate_spec {w : World} (fml : Formula w) :
      OptionSpec (fun '(existT w' ν) => forall ι, (inst fml ι : Prop) <-> inst_multisub ν ι) True (try_propagate fml).
    Proof.
      unfold try_propagate; destruct fml; cbn; try (constructor; auto; fail).
      destruct (try_unify_spec t1 t2) as [[w' ν] HYP|_]. constructor. auto.
      destruct (try_unify_spec t2 t1) as [[w' ν] HYP|_]. constructor.
      intros ι. specialize (HYP ι). intuition.
      now constructor.
    Qed.

    Open Scope lazy_bool_scope.
    Equations(noind) formula_eqb {Σ} (f1 f2 : Formula Σ) : bool :=
      formula_eqb (formula_bool t1) (formula_bool t2) := Term_eqb t1 t2;
      formula_eqb (@formula_eq _ σ t11 t12) (@formula_eq _ τ t21 t22) with eq_dec σ τ => {
        formula_eqb (@formula_eq _ σ t11 t12) (@formula_eq _ ?(σ) t21 t22) (left eq_refl) :=
          Term_eqb t11 t21 &&& Term_eqb t12 t22;
       formula_eqb (@formula_eq _ σ t11 t12) (@formula_eq _ τ t21 t22) (right _) := false
      };
      formula_eqb (@formula_neq _ σ t11 t12) (@formula_neq _ τ t21 t22) with eq_dec σ τ => {
        formula_eqb (@formula_neq _ σ t11 t12) (@formula_neq _ ?(σ) t21 t22) (left eq_refl) :=
          Term_eqb t11 t21 &&& Term_eqb t12 t22;
        formula_eqb (@formula_neq _ σ t11 t12) (@formula_neq _ τ t21 t22) (right _) := false
      };
      formula_eqb _ _ := false.

    Lemma formula_eqb_spec {Σ} (f1 f2 : Formula Σ) :
      BoolSpec (f1 = f2) True (formula_eqb f1 f2).
    Proof.
      induction f1; dependent elimination f2;
        simp formula_eqb;
        try (constructor; auto; fail).
      - destruct (Term_eqb_spec t t0); constructor; intuition.
      - destruct (eq_dec σ σ0); cbn.
        + destruct e.
          repeat
            match goal with
            | |- context[Term_eqb ?t1 ?t2] =>
              destruct (Term_eqb_spec t1 t2); cbn;
                try (constructor; intuition; fail)
            end.
        + constructor; auto.
      - destruct (eq_dec σ σ1); cbn.
        + destruct e.
          repeat
            match goal with
            | |- context[Term_eqb ?t1 ?t2] =>
              destruct (Term_eqb_spec t1 t2); cbn;
                try (constructor; intuition; fail)
            end.
        + constructor; auto.
    Qed.

    Fixpoint try_assumption {Σ} (pc : PathCondition Σ) (fml : Formula Σ) {struct pc} : bool :=
      match pc with
      | nil       => false
      | cons f pc => formula_eqb f fml ||| try_assumption pc fml
      end.

    Lemma try_assumption_spec {Σ} (pc : PathCondition Σ) (fml : Formula Σ) :
      BoolSpec (forall ι, instpc pc ι -> inst (A := Prop) fml ι) True (try_assumption pc fml).
    Proof.
      induction pc; cbn.
      - constructor; auto.
      - destruct (formula_eqb_spec a fml).
        + subst a. constructor. intros ι.
          rewrite inst_pathcondition_cons.
          intuition.
        + destruct IHpc.
          * constructor. intros ι.
            rewrite inst_pathcondition_cons.
            intuition.
          * constructor; auto.
    Qed.

    Definition solver {w0 : World} (fml : Formula w0) :
      option { w1 & MultiSub w0 w1 * List Formula w1 }%type :=
      match try_propagate fml with
      | Some (existT Σ1 vareqs) => Some (existT Σ1 (vareqs , nil))
      | None =>
        match try_solve_formula fml with
        | Some true => Some (existT w0 (multisub_id , nil))
        | Some false => None
        | None =>
          if try_assumption (wco w0) fml
          then Some (existT w0 (multisub_id , nil))
          else Some (existT w0 (multisub_id , (cons fml nil)))
        end
      end.

    Lemma inst_multisub_inst_sub_multi {w0 w1} (ζ01 : MultiSub w0 w1) (ι1 : SymInstance w1) :
      inst_multisub ζ01 (inst (wsub (wmultisub_sup ζ01)) ι1).
    Proof.
        induction ζ01; cbn - [subst]; auto.
        rewrite <- inst_sub_shift.
        rewrite <- ?inst_subst.
        rewrite <- inst_lookup.
        rewrite lookup_sub_comp.
        rewrite lookup_sub_single_eq.
        rewrite <- subst_sub_comp.
        rewrite <- sub_comp_assoc.
        rewrite sub_comp_shift_single.
        rewrite sub_comp_id_left.
        split; auto.
    Qed.

    Lemma solver_spec {w0 : World} (fml : Formula w0) :
      OptionSpec
        (fun '(existT Σ1 (ζ, fmls)) =>
           forall ι0,
             instpc (wco w0) ι0 ->
             (inst (A:= Prop) fml ι0 -> inst_multisub ζ ι0) /\
             (forall ι1,
                 ι0 = inst (wsub (wmultisub_sup ζ)) ι1 ->
                 inst fml ι0 <-> inst fmls ι1))
        (forall ι, instpc (wco w0) ι -> inst (A := Prop) fml ι -> False)
        (solver fml).
    Proof.
      unfold solver.
      destruct (try_propagate_spec fml) as [[Σ1 ζ01]|].
      { constructor. intros ι0 Hpc. specialize (H ι0).
        split. intuition. intros ι1 ->.
        intuition. constructor. clear H. apply H1.
        apply inst_multisub_inst_sub_multi.
      }
      clear H.
      destruct (try_solve_formula_spec fml) as [b|].
      { destruct b.
        - constructor. intros ι0 Hpc. cbn. split; auto.
          intros ? Hι. rewrite inst_sub_id in Hι. subst ι1.
          specialize (H ι0). intuition. constructor.
        - constructor. unfold is_true in H. intuition.
      }
      clear H.
      destruct (try_assumption_spec (wco w0) fml).
      { constructor. intros ι0 Hpc. specialize (H ι0).
        cbn. split; auto. intros ι1 ->.
        rewrite inst_sub_id in *. intuition.
        constructor.
      }
      clear H.
      { constructor. intros ι0 Hpc. split.
        cbn; auto. intros ι1 ->.
        rewrite inst_pathcondition_cons.
        cbn. rewrite inst_sub_id.
        intuition. constructor.
      }
    Qed.

  End Solver.

  Module Path.

    Inductive SPath (A : TYPE) (w : World) : Type :=
    | pure (a: A w)
    | angelic_binary (o1 o2 : SPath A w)
    | demonic_binary (o1 o2 : SPath A w)
    | error (msg : Message w)
    | block
    | assertk (fml : Formula w) (msg : Message w) (k : SPath A (wformula w fml))
    | assumek (fml : Formula w) (k : SPath A (wformula w fml))
    (* Don't use these two directly. Instead, use the HOAS versions 'angelic' *)
    (* and 'demonic' that will freshen names. *)
    | angelicv b (k : SPath A (wsnoc w b))
    | demonicv b (k : SPath A (wsnoc w b))
    | assert_vareq
        x σ (xIn : x::σ ∈ w)
        (t : Term (w - (x::σ)) σ)
        (msg : Message (w - (x::σ)))
        (k : SPath A (wsubst w x t))
    | assume_vareq
        x σ (xIn : (x,σ) ∈ w)
        (t : Term (w - (x,σ)) σ)
        (k : SPath A (wsubst w x t))
    | debug
        {BT B} {subB : Subst BT}
        {instB : Inst BT B}
        {occB: OccursCheck BT}
        (b : BT w) (k : SPath A w).

    Global Arguments pure {_ _} _.
    Global Arguments error {_ _} _.
    Global Arguments block {_ _}.
    Global Arguments assertk {_ _} fml msg k.
    Global Arguments assumek {_ _} fml k.
    Global Arguments angelicv {_ _} _ _.
    Global Arguments demonicv {_ _} _ _.
    Global Arguments assert_vareq {_ _} x {_ _} t msg k.
    Global Arguments assume_vareq {_ _} x {_ _} t k.

    Definition demonic_close {A} :
      forall Σ, SPath A {| wctx := Σ; wco := nil |} -> SPath A wnil :=
      fix close Σ :=
        match Σ with
        | ctx_nil      => fun k => k
        | ctx_snoc Σ b => fun k => close Σ (@demonicv A (@MkWorld Σ []) b k)
        end.

    Global Instance persistent_spath {A} `{Persistent A} : Persistent (SPath A) :=
      (* ⊢ SPath A -> □(SPath A) := *)
       fix pers {w0} p {w1} ω01 {struct p} : SPath A w1 :=
         match p with
         | pure a               => pure (persist a ω01)
         | angelic_binary p1 p2 => angelic_binary (pers p1 ω01) (pers p2 ω01)
         | demonic_binary p1 p2 => demonic_binary (pers p1 ω01) (pers p2 ω01)
         | error msg            => error (subst msg (wsub ω01))
         | block                => block
         | assertk fml msg p0   =>
             assertk (subst fml (wsub ω01)) (subst msg (wsub ω01))
               (pers p0 (wacc_formula ω01 fml))
         | assumek fml p        =>
             assumek (subst fml (wsub ω01))
               (pers p (wacc_formula ω01 fml))
         | angelicv b p0        => angelicv b (pers p0 (wacc_snoc ω01 b))
         | demonicv b p0        => demonicv b (pers p0 (wacc_snoc ω01 b))
         | assert_vareq x t msg p =>
           let ζ := subst (sub_shift _) (wsub ω01) in
           assertk
             (formula_eq (env_lookup (wsub ω01) _) (subst t ζ))
             (subst msg ζ)
             (pers p
                (MkAcc (MkWorld (subst (wco w0) (sub_single _ t)))
                   (MkWorld
                      (cons (formula_eq (env_lookup (wsub ω01) _) (subst t ζ))
                         (wco w1))) ζ))
         | @assume_vareq _ _ x σ xIn t p =>
           let ζ := subst (sub_shift _) (wsub ω01) in
           assumek
             (formula_eq (env_lookup (wsub ω01) xIn) (subst t ζ))
             (pers p
                (MkAcc (MkWorld (subst (wco w0) (sub_single xIn t)))
                   (MkWorld
                      (cons (formula_eq (env_lookup (wsub ω01) xIn) (subst t ζ))
                         (wco w1))) ζ))
         | debug d p => debug (subst d (wsub ω01)) (pers p ω01)
         end.

    (* Fixpoint occurs_check_spath {A} `{OccursCheck A} {w : World} {x} (xIn : x ∈ w) (o : SPath A w) : *)
    (*   option (SPath A (w - x)) := *)
    (*   match o with *)
    (*   | pure a => option_map pure (occurs_check xIn a) *)
    (*   | angelic_binary o1 o2 => *)
    (*     option_ap (option_map (angelic_binary (Σ := Σ - x)) (occurs_check_spath xIn o1)) (occurs_check_spath xIn o2) *)
    (*   | demonic_binary o1 o2 => *)
    (*     option_ap (option_map (demonic_binary (Σ := Σ - x)) (occurs_check_spath xIn o1)) (occurs_check_spath xIn o2) *)
    (*   | error msg => option_map error (occurs_check xIn msg) *)
    (*   | block => Some block *)
    (*   | assertk P msg o => *)
    (*     option_ap (option_ap (option_map (assertk (Σ := Σ - x)) (occurs_check xIn P)) (occurs_check xIn msg)) (occurs_check_spath xIn o) *)
    (*   | assumek P o => option_ap (option_map (assumek (Σ := Σ - x)) (occurs_check xIn P)) (occurs_check_spath xIn o) *)
    (*   | angelicv b o => option_map (angelicv b) (occurs_check_spath (inctx_succ xIn) o) *)
    (*   | demonicv b o => option_map (demonicv b) (occurs_check_spath (inctx_succ xIn) o) *)
    (*   | @assert_vareq _ _ y σ yIn t msg o => *)
    (*     match occurs_check_view yIn xIn with *)
    (*     | Same _ => None *)
    (*     | @Diff _ _ _ _ x xIn => *)
    (*       option_ap *)
    (*         (option_ap *)
    (*            (option_map *)
    (*               (fun (t' : Term (Σ - (y :: σ) - x) σ) (msg' : Message (Σ - (y :: σ) - x)) (o' : SPath A (Σ - (y :: σ) - x)) => *)
    (*                  let e := swap_remove yIn xIn in *)
    (*                  assert_vareq *)
    (*                    y *)
    (*                    (eq_rect (Σ - (y :: σ) - x) (fun Σ => Term Σ σ) t' (Σ - x - (y :: σ)) e) *)
    (*                    (eq_rect (Σ - (y :: σ) - x) Message msg' (Σ - x - (y :: σ)) e) *)
    (*                    (eq_rect (Σ - (y :: σ) - x) (SPath A) o' (Σ - x - (y :: σ)) e)) *)
    (*               (occurs_check xIn t)) *)
    (*            (occurs_check xIn msg)) *)
    (*         (occurs_check_spath xIn o) *)
    (*     end *)
    (*   | @assume_vareq _ _ y σ yIn t o => *)
    (*     match occurs_check_view yIn xIn with *)
    (*     | Same _ => Some o *)
    (*     | @Diff _ _ _ _ x xIn => *)
    (*       option_ap *)
    (*         (option_map *)
    (*            (fun (t' : Term (Σ - (y :: σ) - x) σ) (o' : SPath A (Σ - (y :: σ) - x)) => *)
    (*               let e := swap_remove yIn xIn in *)
    (*               assume_vareq *)
    (*                 y *)
    (*                 (eq_rect (Σ - (y :: σ) - x) (fun Σ => Term Σ σ) t' (Σ - x - (y :: σ)) e) *)
    (*                 (eq_rect (Σ - (y :: σ) - x) (SPath A) o' (Σ - x - (y :: σ)) e)) *)
    (*            (occurs_check xIn t)) *)
    (*         (occurs_check_spath xIn o) *)
    (*     end *)
    (*   | debug b o => option_ap (option_map (debug (Σ := Σ - x)) (occurs_check xIn b)) (occurs_check_spath xIn o) *)
    (*   end. *)

    Fixpoint inst_spath {AT A} `{Inst AT A} {w} (o : SPath AT w) (ι : SymInstance w) : Outcome A :=
      match o with
      | pure a               => outcome_pure (inst a ι)
      | angelic_binary o1 o2 => outcome_angelic_binary (inst_spath o1 ι) (inst_spath o2 ι)
      | demonic_binary o1 o2 => outcome_demonic_binary (inst_spath o1 ι) (inst_spath o2 ι)
      | error msg            => outcome_fail msg
      | block                => outcome_block
      | assertk fml msg o    => outcome_assertk
                                  (Obligation msg fml ι)
                                  (inst_spath o ι)
      | assumek fml o        => outcome_assumek (inst fml ι) (inst_spath o ι)
      | angelicv b k         => outcome_angelic (fun v : Lit (snd b) => inst_spath k (env_snoc ι b v))
      | demonicv b k         => outcome_demonic (fun v : Lit (snd b) => inst_spath k (env_snoc ι b v))
      | @assert_vareq _ _ x σ xIn t msg k =>
        let ι' := env_remove' _ ι xIn in
        outcome_assertk
          (env_lookup ι xIn = inst t ι')
          (inst_spath k ι')
      | @assume_vareq _ _ x σ xIn t k =>
        let ι' := env_remove' _ ι xIn in
        outcome_assumek
          (env_lookup ι xIn = inst t ι')
          (inst_spath k ι')
      | debug d k            => outcome_debug (inst d ι) (inst_spath k ι)
      end.

    Definition mapping AT BT : TYPE :=
      □(AT -> BT).
    Definition arrow AT BT : TYPE :=
      □(AT -> SPath BT).

    (* Definition arrow_dcl {ET E AT A BT B} `{Subst ET, Subst BT, Inst ET E, Inst AT A, Inst BT B} {Σ} (f : arrow ET AT BT Σ) : Prop := *)
    (*   forall Σ1 Σ2 ζ1 ζ2 ζ12 a1 a2, *)
    (*     (forall ι1 ι2, ι1 = inst ι2 ζ12 -> inst ι1 a1 = inst ι2 a2) -> *)
    (*     geq (subst ζ12 (f Σ1 ζ1 a1)) (f Σ2 ζ2 a2). *)

    Definition angelic {AT} (x : option 𝑺) σ :
      ⊢ □(STerm σ -> SPath AT) -> SPath AT :=
      fun w k =>
        let y := fresh w x in
        angelicv
          (y :: σ) (k (wsnoc w (y :: σ)) wsnoc_sup (@term_var _ y σ inctx_zero)).
    Global Arguments angelic {_} x σ [w] k.

    Definition demonic {AT} (x : option 𝑺) σ :
      ⊢ □(STerm σ -> SPath AT) -> SPath AT :=
      fun w k =>
        let y := fresh w x in
        demonicv
          (y :: σ) (k (wsnoc w (y :: σ)) wsnoc_sup (@term_var _ y σ inctx_zero)).
    Global Arguments demonic {_} x σ [w] k.

    Definition angelic_freshen_ctx {AT} {N : Set} (n : N -> 𝑺) :
      ⊢ ∀ Δ : NCtx N Ty, □((fun w => NamedEnv (Term w) Δ) -> SPath AT) -> SPath AT :=
      fix freshen {w} Δ {struct Δ} :=
        match Δ with
        | ctx_nil             => fun k => T k env_nil
        | ctx_snoc Δ (x :: σ) =>
          fun k =>
            angelic (Some (n x)) σ (fun w1 ω01 t =>
              freshen Δ (fun w2 ω12 EΔ =>
                k w2 (wtrans ω01 ω12) (EΔ ► (x :: σ ↦ subst t ω12))))
        end.
    Global Arguments angelic_freshen_ctx {_ _} n [w] Δ : rename.

    Definition demonic_freshen_ctx {AT} {N : Set} (n : N -> 𝑺) :
      ⊢ ∀ Δ : NCtx N Ty, □((fun w => NamedEnv (Term w) Δ) -> SPath AT) -> SPath AT :=
      fix freshen {w} Δ {struct Δ} :=
        match Δ with
        | ctx_nil             => fun k => T k env_nil
        | ctx_snoc Δ (x :: σ) =>
          fun k =>
            demonic (Some (n x)) σ (fun w1 ω01 t =>
              freshen Δ (fun w2 ω12 EΔ =>
                k w2 (wtrans ω01 ω12) (EΔ ► (x :: σ ↦ subst t ω12))))
        end.
    Global Arguments demonic_freshen_ctx {_ _} n [w] Δ : rename.

    Definition map {A B} :
      ⊢ □(A -> B) -> SPath A -> SPath B :=
      fix map {w} f p :=
        match p with
        | pure a                 => pure (T f a)
        | angelic_binary p1 p2   => angelic_binary (map f p1) (map f p2)
        | demonic_binary p1 p2   => demonic_binary (map f p1) (map f p2)
        | error msg              => error msg
        | block                  => block
        | assertk fml msg p      => assertk fml msg (map (four f wformula_sup) p)
        | assumek fml p          => assumek fml (map (four f wformula_sup) p)
        | angelicv b p           => angelicv b (map (four f wsnoc_sup) p)
        | demonicv b p           => demonicv b (map (four f wsnoc_sup) p)
        | assert_vareq x t msg p => assert_vareq x t msg (map (four f wsubst_sup) p)
        | assume_vareq x t p     => assume_vareq x t (map (four f wsubst_sup) p)
        | debug d p              => debug d (map f p)
        end.

    Definition bind {A B} :
      ⊢ SPath A -> □(A -> SPath B) -> SPath B :=
      fix bind {w} ma f :=
        match ma with
        | pure a                 => T f a
        | angelic_binary p1 p2   => angelic_binary (bind p1 f) (bind p2 f)
        | demonic_binary p1 p2   => demonic_binary (bind p1 f) (bind p2 f)
        | error msg              => error msg
        | block                  => block
        | assertk fml msg p      => assertk fml msg (bind p (four f wformula_sup))
        | assumek fml p          => assumek fml (bind p (four f wformula_sup))
        | angelicv b p           => angelicv b (bind p (four f wsnoc_sup))
        | demonicv b p           => demonicv b (bind p (four f wsnoc_sup))
        | assert_vareq x t msg p => assert_vareq x t msg (bind p (four f wsubst_sup))
        | assume_vareq x t p     => assume_vareq x t (bind p (four f wsubst_sup))
        | debug d p              => debug d (bind p f)
        end.

    Definition assume_formulas_without_solver {A} {w : World} :
      forall (fmls : List Formula w), SPath A (wformulas w fmls) -> SPath A w :=
      match w with
      | @MkWorld Σ pc =>
        (fix assumes pc (fmls : List Formula Σ) {struct fmls} :
           SPath A {| wctx := Σ; wco := app fmls pc |} ->
           SPath A {| wctx := Σ; wco := pc |} :=
           match fmls with
           | nil => fun p => p
           | cons fml fmls =>
             fun p =>
               assumes pc fmls
                 (assumek (w:= {| wctx := Σ; wco := app fmls pc |}) fml p)
           end) pc
      end.
    Global Arguments assume_formulas_without_solver {_ _} fmls p.

    Definition assert_formulas_without_solver {A} :
      ⊢ Message -> List Formula -> □(SPath A) -> SPath A :=
      fix asserts w msg fmls k :=
        match fmls with
        | nil           => T k
        | cons fml fmls =>
          assertk fml msg (asserts (wformula w fml) msg fmls (four k wformula_sup))
        end.

    Fixpoint assume_multisub {AT w1 w2} (ν : MultiSub w1 w2) :
      SPath AT w2 -> SPath AT w1.
    Proof.
      destruct ν; intros o; cbn in o.
      - exact o.
      - apply (@assume_vareq AT w1 x σ xIn t).
        eapply assume_multisub.
        apply ν.
        apply o.
    Defined.

    Fixpoint assert_multisub {AT} {w1 w2 : World} (msg : Message w1) (ζ : MultiSub w1 w2) : (Message w2 -> SPath AT w2) -> SPath AT w1.
    Proof.
      destruct ζ; intros o; cbn in o.
      - apply o. apply msg.
      - apply (@assert_vareq AT w1 x σ xIn t).
        apply (subst msg (sub_single xIn t)).
        refine (assert_multisub AT (wsubst w1 x t) _ (subst msg (sub_single xIn t)) ζ o).
    Defined.

    Definition assume_formulak {A} :
      ⊢ Formula -> □(SPath A) -> SPath A :=
      fun w0 fml k =>
        match solver fml with
        | Some (existT w1 (ν , fmls)) =>
          (* Assume variable equalities and the residual constraints *)
          assume_multisub ν
            (assume_formulas_without_solver fmls
               (four k (wmultisub_sup ν) (wformulas_sup w1 fmls)))
        | None =>
          (* The formula is inconsistent with the path constraints. *)
          block
        end.

    Definition assert_formulak {A} :
      ⊢ Message -> Formula -> □(SPath A) -> SPath A :=
      fun w0 msg fml k =>
        match solver fml with
        | Some (existT w1 (ν , fmls)) =>
          (* Assert variable equalities and the residual constraints *)
          assert_multisub msg ν
            (fun msg' => assert_formulas_without_solver msg' fmls (four k (wmultisub_sup ν)))
        | None =>
          (* The formula is inconsistent. *)
          error msg
        end.

    Definition assume_formula :
      ⊢ Formula -> SPath Unit :=
      fun w fml =>
        assume_formulak fml (fun _ _ => pure tt).

    Definition assume_formulas :
      ⊢ List Formula -> SPath Unit :=
      fix assume_formulas {w0} fmls {struct fmls} :=
        match fmls with
        | nil => pure tt
        | cons fml fmls =>
          bind
            (assume_formulas fmls)
            (fun w1 ω01 _ => assume_formula (subst fml ω01))
        end.

    Definition assume_formulask {A} :
      ⊢ List Formula -> □(SPath A) -> □(SPath A) :=
      fun w0 =>
        fix assumes fmls k :=
        match fmls with
        | nil           => k
        | cons fml fmls =>
          fun w1 ω01 =>
            assume_formulak
              (subst fml ω01)
              (four (assumes fmls k) ω01)
        end.

    Definition assert_formula :
      ⊢ Message -> Formula -> SPath Unit :=
      fun w msg fml =>
        assert_formulak msg fml (fun _ _ => pure tt).

    Definition assert_formulas :
      ⊢ Message -> List Formula -> SPath Unit :=
      fix assert_formulas {w0} msg fmls {struct fmls} :=
        match fmls with
        | nil => pure tt
        | cons fml fmls =>
          bind
            (assert_formulas msg fmls)
            (fun w1 ω01 _ => assert_formula (subst msg ω01) (subst fml ω01))
        end.

    Definition assert_formulask {A} :
      ⊢ Message -> List Formula -> □(SPath A) -> □(SPath A) :=
      fun w0 msg =>
        fix asserts fmls k :=
        match fmls with
        | nil           => k
        | cons fml fmls =>
          fun w1 ω01 =>
            assert_formulak
              (subst msg ω01)
              (subst fml ω01)
              (four (asserts fmls k) ω01)
        end.

    Definition angelic_list {A} :
      ⊢ Message -> List A -> SPath A :=
      fun w msg =>
        fix rec xs :=
        match xs with
        | nil        => error msg
        | cons x nil => pure x
        | cons x xs  => angelic_binary (pure x) (rec xs)
        end.

    Definition angelic_listk {A B : TYPE} :
      ⊢ Message -> (A -> SPath B) -> WList A -> SPath B :=
      fun w msg k =>
        fix rec xs :=
        match xs with
        | nil        => error msg
        | cons x nil => k x
        | cons x xs  => angelic_binary (k x) (rec xs)
        end.

    Definition demonic_list {A} :
      ⊢ WList A -> SPath A :=
      fun w =>
        fix rec xs :=
        match xs with
        | nil        => block
        | cons x nil => pure x
        | cons x xs  => demonic_binary (pure x) (rec xs)
        end.

    Definition demonic_listk {A B} :
      ⊢ (A -> SPath B) -> WList A -> SPath B :=
      fun w k =>
        fix rec xs :=
        match xs with
        | nil        => block
        | cons x nil => k x
        | cons x xs  => demonic_binary (k x) (rec xs)
        end.

    Definition angelic_finite {A} F `{finite.Finite F} :
      ⊢ Message -> (⌜F⌝ -> SPath A) -> SPath A :=
      fun w msg k => angelic_listk msg k (finite.enum F).

    Definition demonic_finite {A} F `{finite.Finite F} :
      ⊢ (⌜F⌝ -> SPath A) -> SPath A :=
      fun w k => demonic_listk k (finite.enum F).

    Definition angelic_match_bool {A} :
      ⊢ Message -> STerm ty_bool -> □(SPath A) -> □(SPath A) -> SPath A :=
      fun w0 msg t pt pf =>
        match term_get_lit t with
        | Some true => T pt
        | Some false => T pf
        | None =>
          angelic_binary
            (bind
               (assert_formula msg (formula_bool t))
               (fun w1 ω01 _ => pt w1 ω01))
            (bind
               (assert_formula msg (formula_bool (term_not t)))
               (fun w1 ω01 _ => pf w1 ω01))
        end.

    Definition demonic_match_bool {A} :
      ⊢ STerm ty_bool -> □(SPath A) -> □(SPath A) -> SPath A :=
      fun w0 t pt pf =>
        match term_get_lit t with
        | Some true => T pt
        | Some false => T pf
        | None =>
          demonic_binary
            (assume_formulak (formula_bool t) pt)
            (assume_formulak (formula_bool (term_not t)) pf)
        end.

    Definition angelic_match_enum {AT E} :
      ⊢ Message -> STerm (ty_enum E) -> (⌜Lit (ty_enum E)⌝ -> □(SPath AT)) -> SPath AT :=
      fun w msg t k =>
        match term_get_lit t with
        | Some v => T (k v)
        | None => angelic_finite
                    msg (fun v => assert_formulak msg (formula_eq t (term_enum E v)) (k v))
        end.

    Definition demonic_match_enum {AT E} :
      ⊢ STerm (ty_enum E) -> (⌜Lit (ty_enum E)⌝ -> □(SPath AT)) -> SPath AT :=
      fun w t k =>
        match term_get_lit t with
        | Some v => T (k v)
        | None => demonic_finite
                    (fun v => assume_formulak (formula_eq t (term_enum E v)) (k v))
        end.

    Definition angelic_match_list {AT} (x y : option 𝑺) (σ : Ty) :
      ⊢ Message -> STerm (ty_list σ) -> □(SPath AT) -> □(STerm σ -> STerm (ty_list σ) -> SPath AT) -> SPath AT :=
      fun w0 msg t knil kcons =>
        angelic_binary (assert_formulak msg (formula_eq (term_lit (ty_list σ) []) t) knil)
          (angelic x σ
             (fun w1 ω01 (th : Term w1 σ) =>
              angelic y (ty_list σ)
                (fun w2 ω12 (tt : Term w2 (ty_list σ)) =>
                 assert_formulak (subst msg (wtrans ω01 ω12))
                   (formula_eq (term_binop binop_cons (subst th ω12) tt) (subst t (wtrans ω01 ω12)))
                   (fun w3 ω23 =>
                    four kcons (wtrans ω01 ω12) ω23 (subst th (wtrans ω12 ω23)) (subst tt ω23))))).

    Definition demonic_match_list {AT} (x y : option 𝑺) (σ : Ty) :
      ⊢ STerm (ty_list σ) -> □(SPath AT) -> □(STerm σ -> STerm (ty_list σ) -> SPath AT) -> SPath AT :=
      fun w0 t knil kcons =>
        demonic_binary (assume_formulak (formula_eq (term_lit (ty_list σ) []) t) knil)
          (demonic x σ
             (fun w1 ω01 (th : Term w1 σ) =>
              demonic y (ty_list σ)
                (fun w2 ω12 (tt : Term w2 (ty_list σ)) =>
                 assume_formulak
                   (formula_eq (term_binop binop_cons (subst th ω12) tt) (subst t (wtrans ω01 ω12)))
                   (fun w3 ω23 =>
                    four kcons (wtrans ω01 ω12) ω23 (subst th (wtrans ω12 ω23)) (subst tt ω23))))).

    Definition angelic_match_sum' {AT} (x : option 𝑺) (σ : Ty) (y : option 𝑺) (τ : Ty) :
      ⊢ Message -> STerm (ty_sum σ τ) -> □(STerm σ -> SPath AT) -> □(STerm τ -> SPath AT) -> SPath AT :=
      fun w0 msg t kinl kinr =>
        angelic_binary
          (angelic x σ
             (fun w1 ω01 (tσ : Term w1 σ) =>
              assert_formulak (subst msg ω01) (formula_eq (term_inl tσ) (subst t ω01))
                (fun w2 ω12 =>
                   four kinl ω01 ω12 (subst tσ ω12))))
          (angelic y τ
             (fun w1 ω01 (tτ : Term w1 τ) =>
              assert_formulak (subst msg ω01) (formula_eq (term_inr tτ) (subst t ω01))
                (fun w2 ω12 =>
                   four kinr ω01 ω12 (subst tτ ω12)))).

    Definition angelic_match_sum {AT} (x : option 𝑺) (σ : Ty) (y : option 𝑺) (τ : Ty) :
      ⊢ Message -> STerm (ty_sum σ τ) -> □(STerm σ -> SPath AT) -> □(STerm τ -> SPath AT) -> SPath AT :=
      fun w0 msg t kinl kinr =>
        match term_get_sum t with
        | Some (inl tσ) => T kinl tσ
        | Some (inr tτ) => T kinr tτ
        | None => angelic_match_sum' x y msg t kinl kinr
        end.

    Definition demonic_match_sum' {AT} (x : option 𝑺) (σ : Ty) (y : option 𝑺) (τ : Ty) :
      ⊢ STerm (ty_sum σ τ) -> □(STerm σ -> SPath AT) -> □(STerm τ -> SPath AT) -> SPath AT :=
      fun w0 t kinl kinr =>
        demonic_binary
          (demonic x σ
             (fun w1 ω01 (tσ : Term w1 σ) =>
              assume_formulak (formula_eq (term_inl tσ) (subst t ω01))
                (fun w2 ω12 =>
                   four kinl ω01 ω12 (subst tσ ω12))))
          (demonic y τ
             (fun w1 ω01 (tτ : Term w1 τ) =>
              assume_formulak (formula_eq (term_inr tτ) (subst t ω01))
                (fun w2 ω12 =>
                   four kinr ω01 ω12 (subst tτ ω12)))).

    Definition demonic_match_sum {AT} (x : option 𝑺) (σ : Ty) (y : option 𝑺) (τ : Ty) :
      ⊢ STerm (ty_sum σ τ) -> □(STerm σ -> SPath AT) -> □(STerm τ -> SPath AT) -> SPath AT :=
      fun w0 t kinl kinr =>
        match term_get_sum t with
        | Some (inl tσ) => T kinl tσ
        | Some (inr tτ) => T kinr tτ
        | None => demonic_match_sum' x y t kinl kinr
        end.

    Definition angelic_match_pair' {AT} (x : option 𝑺) (σ : Ty) (y : option 𝑺) (τ : Ty) :
      ⊢ Message -> STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> SPath AT) -> SPath AT :=
      fun w0 msg t k =>
        angelic x σ
          (fun w1 ω01 (tσ : Term w1 σ) =>
           angelic y τ
             (fun w2 ω12 (tτ : Term w2 τ) =>
              assert_formulak (subst msg (wtrans ω01 ω12)) (formula_eq (term_binop binop_pair (subst tσ ω12) tτ) (subst t (wtrans ω01 ω12)))
                (fun w3 ω23 =>
                 four k (wtrans ω01 ω12) ω23 (subst tσ (wtrans ω12 ω23)) (subst tτ ω23)))).

    Definition angelic_match_pair {AT} (x : option 𝑺) (σ : Ty) (y : option 𝑺) (τ : Ty) :
      ⊢ Message -> STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> SPath AT) -> SPath AT :=
      fun w0 msg t k =>
        match term_get_pair t with
        | Some (tσ,tτ) => T k tσ tτ
        | None => angelic_match_pair' x y msg t k
        end.

    Definition demonic_match_pair' {AT} (x : option 𝑺) (σ : Ty) (y : option 𝑺) (τ : Ty) :
      ⊢ STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> SPath AT) -> SPath AT :=
      fun w0 t k =>
        demonic x σ
          (fun w1 ω01 (tσ : Term w1 σ) =>
           demonic y τ
             (fun w2 ω12 (tτ : Term w2 τ) =>
              assume_formulak (formula_eq (term_binop binop_pair (subst tσ ω12) tτ) (subst t (wtrans ω01 ω12)))
                (fun w3 ω23 =>
                 four k (wtrans ω01 ω12) ω23 (subst tσ (wtrans ω12 ω23)) (subst tτ ω23)))).

    Definition demonic_match_pair {AT} (x : option 𝑺) (σ : Ty) (y : option 𝑺) (τ : Ty) :
      ⊢ STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> SPath AT) -> SPath AT :=
      fun w0 t k =>
        match term_get_pair t with
        | Some (tσ,tτ) => T k tσ tτ
        | None => demonic_match_pair' x y t k
        end.

    Definition angelic_match_record' {N : Set} (n : N -> 𝑺) {AT R} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) :
      ⊢ Message -> STerm (ty_record R) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> SPath AT) -> SPath AT.
    Proof.
      intros w0 msg t k.
      apply (angelic_freshen_ctx n Δ).
      intros w1 ω01 ts.
      apply assert_formulak.
      apply (subst msg ω01).
      apply (formula_eq (subst t ω01)).
      apply (term_record R (record_pattern_match_env_reverse p ts)).
      intros w2 ω12.
      apply (k w2 (wtrans ω01 ω12) (subst ts ω12)).
    Defined.

    Definition angelic_match_record {N : Set} (n : N -> 𝑺) {AT R} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) :
      ⊢ Message -> STerm (ty_record R) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> SPath AT) -> SPath AT.
    Proof.
      intros w0 msg t k.
      destruct (term_get_record t).
      - apply (T k).
        apply (record_pattern_match_env p n0).
      - apply (angelic_match_record' n p msg t k).
    Defined.

    Definition demonic_match_record' {N : Set} (n : N -> 𝑺) {AT R} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) :
      ⊢ STerm (ty_record R) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> SPath AT) -> SPath AT.
    Proof.
      intros w0 t k.
      apply (demonic_freshen_ctx n Δ).
      intros w1 ω01 ts.
      apply assume_formulak.
      apply (formula_eq (subst t ω01)).
      apply (term_record R (record_pattern_match_env_reverse p ts)).
      intros w2 ω12.
      apply (k w2 (wtrans ω01 ω12) (subst ts ω12)).
    Defined.

    Definition demonic_match_record {N : Set} (n : N -> 𝑺) {AT R} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) :
      ⊢ STerm (ty_record R) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> SPath AT) -> SPath AT.
    Proof.
      intros w0 t k.
      destruct (term_get_record t).
      - apply (T k).
        apply (record_pattern_match_env p n0).
      - apply (demonic_match_record' n p t k).
    Defined.

    Definition angelic_match_tuple' {N : Set} (n : N -> 𝑺) {AT σs} {Δ : NCtx N Ty} (p : TuplePat σs Δ) :
      ⊢ Message -> STerm (ty_tuple σs) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> SPath AT) -> SPath AT.
    Proof.
      intros w0 msg t k.
      apply (angelic_freshen_ctx n Δ).
      intros w1 ω01 ts.
      apply assert_formulak.
      apply (subst msg ω01).
      apply (formula_eq (subst t ω01)).
      apply (term_tuple (tuple_pattern_match_env_reverse p ts)).
      intros w2 ω12.
      apply (k w2 (wtrans ω01 ω12) (subst ts ω12)).
    Defined.

    Definition angelic_match_tuple {N : Set} (n : N -> 𝑺) {AT σs} {Δ : NCtx N Ty} (p : TuplePat σs Δ) :
      ⊢ Message -> STerm (ty_tuple σs) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> SPath AT) -> SPath AT.
    Proof.
      intros w0 msg t k.
      destruct (term_get_tuple t).
      - apply (T k).
        apply (tuple_pattern_match_env p e).
      - apply (angelic_match_tuple' n p msg t k).
    Defined.

    Definition demonic_match_tuple' {N : Set} (n : N -> 𝑺) {AT σs} {Δ : NCtx N Ty} (p : TuplePat σs Δ) :
      ⊢ STerm (ty_tuple σs) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> SPath AT) -> SPath AT.
    Proof.
      intros w0 t k.
      apply (demonic_freshen_ctx n Δ).
      intros w1 ω01 ts.
      apply assume_formulak.
      apply (formula_eq (subst t ω01)).
      apply (term_tuple (tuple_pattern_match_env_reverse p ts)).
      intros w2 ω12.
      apply (k w2 (wtrans ω01 ω12) (subst ts ω12)).
    Defined.

    Definition demonic_match_tuple {N : Set} (n : N -> 𝑺) {AT σs} {Δ : NCtx N Ty} (p : TuplePat σs Δ) :
      ⊢ STerm (ty_tuple σs) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> SPath AT) -> SPath AT.
    Proof.
      intros w0 t k.
      destruct (term_get_tuple t).
      - apply (T k).
        apply (tuple_pattern_match_env p e).
      - apply (demonic_match_tuple' n p t k).
    Defined.

    (* TODO: move to Syntax *)
    Definition pattern_match_env_reverse {N : Set} {Σ : LCtx} {σ : Ty} {Δ : NCtx N Ty} (p : Pattern Δ σ) :
      NamedEnv (Term Σ) Δ -> Term Σ σ :=
      match p with
      | pat_var x    => fun Ex => match snocView Ex with isSnoc _ t => t end
      | pat_unit     => fun _ => term_lit ty_unit tt
      | pat_pair x y => fun Exy => match snocView Exy with
                                     isSnoc Ex ty =>
                                     match snocView Ex with
                                       isSnoc _ tx => term_binop binop_pair tx ty
                                     end
                                   end
      | pat_tuple p  => fun EΔ => term_tuple (tuple_pattern_match_env_reverse p EΔ)
      | pat_record p => fun EΔ => term_record _ (record_pattern_match_env_reverse p EΔ)
      end.

    Definition angelic_match_pattern {N : Set} (n : N -> 𝑺) {AT σ} {Δ : NCtx N Ty} (p : Pattern Δ σ) :
      ⊢ Message -> STerm σ -> □((fun Σ => NamedEnv (Term Σ) Δ) -> SPath AT) -> SPath AT :=
      fun w0 msg t k =>
        angelic_freshen_ctx n Δ
          (fun w1 ω01 (ts : (fun Σ : LCtx => NamedEnv (Term Σ) Δ) w1) =>
           assert_formulak (subst msg ω01) (formula_eq (subst t ω01) (pattern_match_env_reverse p ts))
             (fun w2 ω12 => k w2 (wtrans ω01 ω12) (subst ts ω12))).

    Definition demonic_match_pattern {N : Set} (n : N -> 𝑺) {AT σ} {Δ : NCtx N Ty} (p : Pattern Δ σ) :
      ⊢ STerm σ -> □((fun Σ => NamedEnv (Term Σ) Δ) -> SPath AT) -> SPath AT :=
      fun w0 t k =>
        demonic_freshen_ctx n Δ
          (fun w1 ω01 (ts : (fun Σ : LCtx => NamedEnv (Term Σ) Δ) w1) =>
           assume_formulak (formula_eq (subst t ω01) (pattern_match_env_reverse p ts))
             (fun w2 ω12 => k w2 (wtrans ω01 ω12) (subst ts ω12))).

    Definition angelic_match_union' {N : Set} (n : N -> 𝑺) {AT U} {Δ : 𝑼𝑲 U -> NCtx N Ty}
      (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) :
      ⊢ Message -> STerm (ty_union U) -> (∀ K, □((fun Σ => NamedEnv (Term Σ) (Δ K)) -> SPath AT)) -> SPath AT :=
      fun w0 msg t k =>
        angelic_finite msg
          (fun K : 𝑼𝑲 U =>
           angelic None (𝑼𝑲_Ty K)
             (fun w1 ω01 (t__field : Term w1 (𝑼𝑲_Ty K)) =>
              assert_formulak (subst msg ω01) (formula_eq (term_union U K t__field) (subst t ω01))
                (fun w2 ω12 =>
                 let ω02 := wtrans ω01 ω12 in
                 angelic_match_pattern n (p K) (subst msg ω02) (subst t__field ω12) (four (k K) ω02)))).

    Definition angelic_match_union {N : Set} (n : N -> 𝑺) {AT U} {Δ : 𝑼𝑲 U -> NCtx N Ty}
      (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) :
      ⊢ Message -> STerm (ty_union U) -> (∀ K, □((fun Σ => NamedEnv (Term Σ) (Δ K)) -> SPath AT)) -> SPath AT :=
      fun w0 msg t k =>
        match term_get_union t with
        | Some (existT K t__field) => angelic_match_pattern n (p K) msg t__field (k K)
        | None => angelic_match_union' n p msg t k
        end.

    Definition demonic_match_union' {N : Set} (n : N -> 𝑺) {AT U} {Δ : 𝑼𝑲 U -> NCtx N Ty}
      (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) :
      ⊢ STerm (ty_union U) -> (∀ K, □((fun Σ => NamedEnv (Term Σ) (Δ K)) -> SPath AT)) -> SPath AT :=
      fun w0 t k =>
        demonic_finite
          (fun K : 𝑼𝑲 U =>
           demonic None (𝑼𝑲_Ty K)
             (fun w1 ω01 (t__field : Term w1 (𝑼𝑲_Ty K)) =>
              assume_formulak (formula_eq (term_union U K t__field) (subst t ω01))
                (fun w2 ω12 =>
                 demonic_match_pattern n (p K) (subst t__field ω12) (four (k K) (wtrans ω01 ω12))))).

    Definition demonic_match_union {N : Set} (n : N -> 𝑺) {AT U} {Δ : 𝑼𝑲 U -> NCtx N Ty}
      (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) :
      ⊢ STerm (ty_union U) -> (∀ K, □((fun Σ => NamedEnv (Term Σ) (Δ K)) -> SPath AT)) -> SPath AT :=
      fun w0 t k =>
        match term_get_union t with
        | Some (existT K t__field) => demonic_match_pattern n (p K) t__field (k K)
        | None => demonic_match_union' n p t k
        end.

    Definition wp {AT A} `{Inst AT A} :
      (* ⊢ SPath AT -> ⌜A -> Prop⌝ -> SymInstance -> PROP *)
      forall w (o : SPath AT w) (POST : A -> Prop) (ι : SymInstance w), Prop :=
      fix wp {w} o POST ι : Prop :=
      match o return Prop with
      | pure a                            => POST (inst a ι)
      | angelic_binary o1 o2              => (wp o1 POST ι) \/ (wp o2 POST ι)
      | demonic_binary o1 o2              => (wp o1 POST ι) /\ (wp o2 POST ι)
      | error msg                         => Error msg
      | block                             => True
      | assertk fml msg o                 => inst fml ι /\ wp o POST ι
      | assumek fml o                     => inst (A := Prop) fml ι -> wp o POST ι
      | angelicv b k                      => exists (v : Lit (snd b)),
                                             wp k POST (env_snoc ι b v)
      | demonicv b k                      => forall (v : Lit (snd b)),
                                             wp k POST (env_snoc ι b v)
      | @assert_vareq _ _ x σ xIn t msg k => let ι' := env_remove' _ ι xIn in
                                             env_lookup ι xIn = inst t ι' /\
                                             wp k POST ι'
      | @assume_vareq _ _ x σ xIn t k     => let ι' := env_remove' _ ι xIn in
                                             env_lookup ι xIn = inst t ι' ->
                                             wp k POST ι'
      | debug d k                         => Debug (inst d ι) (wp k POST ι)
      end%type.

    Definition wp' {AT A} `{Inst AT A} :
      ⊢ SPath AT -> ⌜A -> Prop⌝ -> SymInstance -> PROP :=
      fun w o POST ι => outcome_satisfy (inst_spath o ι) POST.

    Lemma wp_wp' {AT A} `{Inst AT A} {w}
      (o : SPath AT w) (POST : A -> Prop) (ι : SymInstance w) :
      wp o POST ι <-> wp' o POST ι.
    Proof.
      unfold wp'.
      induction o; cbn; auto.
      - specialize (IHo1 ι). specialize (IHo2 ι). intuition.
      - specialize (IHo1 ι). specialize (IHo2 ι). intuition.
      - split; intros [].
      - specialize (IHo ι). intuition.
        constructor; auto.
      - specialize (IHo ι). intuition.
      - split; intros [v HYP]; exists v;
          specialize (IHo (env_snoc ι b v)); intuition.
      - split; intros HYP v; specialize (HYP v);
          specialize (IHo (env_snoc ι b v)); intuition.
      - specialize (IHo (env_remove' (x :: σ) ι xIn)).
        intuition.
      - specialize (IHo (env_remove' (x :: σ) ι xIn)).
        intuition.
      - split; intros [HYP]; constructor; revert HYP; apply IHo.
    Qed.

    Lemma wp_monotonic {AT A} `{Inst AT A} {w}
      (o : SPath AT w) (P Q : A -> Prop) (PQ : forall a, P a -> Q a)
      (ι : SymInstance w) :
      wp o P ι ->
      wp o Q ι.
    Proof.
      intros HP. rewrite wp_wp' in *.
      unfold wp' in *. revert HP.
      now apply outcome_satisfy_monotonic.
    Qed.

    Lemma wp_equiv {AT A} `{Inst AT A} {w}
      (o : SPath AT w) (P Q : A -> Prop) (PQ : forall a, P a <-> Q a)
      (ι : SymInstance w) :
      wp o P ι <->
      wp o Q ι.
    Proof. split; apply wp_monotonic; intuition. Qed.

    Global Instance proper_wp {AT A} `{Inst AT A} {w} (o : SPath AT w) :
      Proper
        (pointwise_relation A iff ==> eq ==> iff)
        (wp o).
    Proof.
      unfold Proper, respectful, pointwise_relation, Basics.impl.
      intros P Q PQ ι1 ι2 ->; split; apply wp_monotonic; intuition.
    Qed.

    Notation instpc ι pc := (@inst _ _ instantiate_pathcondition _ ι pc).

    Definition mapping_dcl {AT A BT B} `{Inst AT A, Inst BT B} :
      ⊢ mapping AT BT -> PROP :=
      fun w0 f =>
        forall w1 (ω01 : w0 ⊒ w1)
               w2 (ω02 : w0 ⊒ w2)
               (ω12 : w1 ⊒ w2) (a1 : AT w1) (a2 : AT w2) ,
        forall ι1 ι2,
          ι1 = inst (T := Sub _) ω12 ι2 ->
          inst (T := Sub _) ω01 ι1 = inst (T := Sub _) ω02 ι2 ->
          inst a1 ι1 = inst a2 ι2 ->
          inst (f w1 ω01 a1) ι1 = inst (f w2 ω02 a2) ι2.

    Lemma mapping_dcl_four {AT A BT B} `{Inst AT A, Inst BT B} {w0}
      (f : mapping AT BT w0) (f_dcl : mapping_dcl f) :
      forall w1 (ω01 : w0 ⊒ w1),
        mapping_dcl (four f ω01).
    Proof.
      unfold mapping_dcl. intros * Hι Hζ Ha.
      eapply f_dcl; eauto. unfold wtrans; cbn.
      rewrite ?inst_subst. intuition.
    Qed.

    (* Lemma mapping_dcl_four_wk1 {AT A BT B} `{Inst AT A, Inst BT B} {Σ0} pc0 (b : 𝑺 * Ty) *)
    (*   (f : mapping AT BT Σ0) (f_dcl : mapping_dcl pc0 f) : *)
    (*   mapping_dcl (subst pc0 sub_wk1) (four_wk1 pc0 f b). *)
    (* Proof. *)
    (*   unfold mapping_dcl. intros * Hι Hζ Ha. *)
    (*   unfold four_wk1. rewrite <- ?sub_comp_wk1_tail. *)
    (*   eapply f_dcl; eauto. rewrite ?inst_subst. *)
    (*   intuition. *)
    (* Qed. *)

    Definition dcl {AT A} `{Inst AT A} :
      ⊢ □(SPath AT) -> PROP :=
      fun w0 p =>
        forall
          (P Q : A -> Prop) (PQ : forall a, P a -> Q a)
          w1 (ω01 : w0 ⊒ w1)
          w2 (ω02 : w0 ⊒ w2)
          (ω12 : w1 ⊒ w2),
        forall ι1 ι2,
          ι1 = inst (T := Sub _) ω12 ι2 ->
          instpc (wco w1) ι1 ->
          instpc (wco w2) ι2 ->
          inst (T := Sub _) ω01 ι1 = inst (T := Sub _) ω02 ι2 ->
          wp (p w1 ω01) P ι1 ->
          wp (p w2 ω02) Q ι2.

    Definition arrow_dcl {AT A BT B} `{Inst AT A, Inst BT B} {w0} (f : arrow AT BT w0) : Prop :=
      forall
        w1 (ω01 : w0 ⊒ w1)
        w2 (ω02 : w0 ⊒ w2)
        (ω12 : w1 ⊒ w2) (a1 : AT w1) (a2 : AT w2)
        (P Q : B -> Prop) (PQ : forall b, P b -> Q b),
       forall (ι1 : SymInstance w1) (ι2 : SymInstance w2),
         ι1 = inst (T := Sub _) ω12 ι2 ->
         instpc (wco w1) ι1 ->
         instpc (wco w2) ι2 ->
         inst (T := Sub _) ω01 ι1 = inst (T := Sub _) ω02 ι2 ->
         inst a1 ι1 = inst a2 ι2 ->
         wp (f w1 ω01 a1) P ι1 ->
         wp (f w2 ω02 a2) Q ι2.

    Lemma arrow_dcl_equiv {AT A BT B} `{Inst AT A, Inst BT B} {w0} (f : arrow AT BT w0) (f_dcl : arrow_dcl f) :
      forall
        w1 (ω01 : w0 ⊒ w1)
        w2 (ω02 : w0 ⊒ w2)
        (ω12 : w1 ⊒ w2) (ω21 : w2 ⊒ w1)
        (a1 : AT w1) (a2 : AT w2)
        (P Q : B -> Prop) (PQ : forall b, P b <-> Q b),
       forall (ι1 : SymInstance w1) (ι2 : SymInstance w2),
         ι1 = inst (T := Sub _) ω12 ι2 ->
         ι2 = inst (T := Sub _) ω21 ι1 ->
         instpc (wco w1) ι1 ->
         instpc (wco w2) ι2 ->
         inst (T := Sub _) ω01 ι1 = inst (T := Sub _) ω02 ι2 ->
         inst a1 ι1 = inst a2 ι2 ->
         wp (f w1 ω01 a1) P ι1 <->
         wp (f w2 ω02 a2) Q ι2.
    Proof.
      intros; split; eapply f_dcl; eauto; intuition.
    Qed.

    Lemma arrow_dcl_four {AT A BT B} `{Inst AT A, Inst BT B} {w0} (f : arrow AT BT w0) (f_dcl : arrow_dcl f) :
      forall w1 (ω01 : w0 ⊒ w1),
        arrow_dcl (four f ω01).
    Proof.
      unfold arrow_dcl. intros * PQ * Hι Hpc1 Hpc2 Hζ Ha.
      eapply f_dcl; eauto. unfold wtrans; cbn.
      rewrite ?inst_subst. intuition.
    Qed.

    (* Lemma arrow_dcl_four_wk1 {AT A BT B} `{Inst AT A, Inst BT B} {Σ0} pc0 (f : arrow AT BT Σ0) (f_dcl : arrow_dcl pc0 f) : *)
    (*   forall (b : 𝑺 * Ty), *)
    (*     arrow_dcl (subst pc0 sub_wk1) (four_wk1 pc0 f b). *)
    (* Proof. *)
    (*   unfold arrow_dcl. intros * PQ * Hι Hpc1 Hpc2 Hζ Ha. *)
    (*   unfold four_wk1. rewrite <- ?sub_comp_wk1_tail. *)
    (*   eapply f_dcl; eauto. rewrite ?inst_subst. *)
    (*   intuition. *)
    (* Qed. *)

    Hint Resolve mapping_dcl_four : dcl.
    (* Hint Resolve mapping_dcl_four_wk1 : dcl. *)
    Hint Resolve arrow_dcl_four : dcl.
    (* Hint Resolve arrow_dcl_four_wk1 : dcl. *)

    Lemma wp_persist {AT A} `{InstLaws AT A} {w1 w2 : World} (ω12 : w1 ⊒ w2)
          (o : SPath AT w1) (POST : A -> Prop) (ι2 : SymInstance w2) :
      wp (persist (A := SPath AT) o ω12) POST ι2 <->
      wp o POST (inst (T := Sub _) ω12 ι2).
    Proof.
      revert w2 ω12 ι2.
      induction o; cbn; intros.
      - unfold persist, persist_subst.
        now rewrite inst_subst.
      - now rewrite IHo1, IHo2.
      - now rewrite IHo1, IHo2.
      - split; intros [].
      - reflexivity.
      - now rewrite IHo, inst_subst.
      - now rewrite IHo, inst_subst.
      - split; intros [v HYP]; exists v; revert HYP;
          rewrite IHo; unfold wacc_snoc, wsnoc;
            cbn [wctx wsub]; now rewrite inst_sub_up1.
      - split; intros HYP v; specialize (HYP v); revert HYP;
          rewrite IHo; unfold wacc_snoc, wsnoc;
            cbn [wctx wsub]; now rewrite inst_sub_up1.
      - rewrite IHo; unfold wsubst; cbn [wctx wsub].
        now rewrite ?inst_subst, ?inst_sub_shift, <- inst_lookup.
      - rewrite IHo; unfold wsubst; cbn [wctx wsub].
        now rewrite ?inst_subst, ?inst_sub_shift, <- inst_lookup.
      - split; intros [HYP]; constructor; revert HYP; apply IHo.
    Qed.

    Definition safe {AT} :
      (* ⊢ SPath AT -> SymInstance -> PROP := *)
      forall w (o : SPath AT w) (ι : SymInstance w), Prop :=
      fix safe {w} o ι :=
        match o with
        | pure a => True
        | angelic_binary o1 o2 => safe o1 ι \/ safe o2 ι
        | demonic_binary o1 o2 => safe o1 ι /\ safe o2 ι
        | error msg => False
        | block => True
        | assertk fml msg o =>
          Obligation msg fml ι /\ safe o ι
        | assumek fml o => (inst fml ι : Prop) -> safe o ι
        | angelicv b k => exists v, safe k (env_snoc ι b v)
        | demonicv b k => forall v, safe k (env_snoc ι b v)
        | @assert_vareq _ _ x σ xIn t msg k =>
          (let ζ := sub_shift xIn in
          Obligation (subst msg ζ) (formula_eq (term_var x) (subst t ζ))) ι /\
          (let ι' := env_remove (x,σ) ι xIn in
          safe k ι')
        | @assume_vareq _ _ x σ xIn t k =>
          let ι' := env_remove (x,σ) ι xIn in
          env_lookup ι xIn = inst t ι' ->
          safe k ι'
        | debug d k => Debug (inst d ι) (safe k ι)
        end%type.
    Global Arguments safe {_ w} o ι.

    Lemma and_iff_compat_l' (A B C : Prop) :
      (A -> B <-> C) <-> (A /\ B <-> A /\ C).
    Proof. intuition. Qed.

    Lemma imp_iff_compat_l' (A B C : Prop) :
      (A -> B <-> C) <-> ((A -> B) <-> (A -> C)).
    Proof. intuition. Qed.

    Global Instance proper_debug {B} : Proper (eq ==> iff ==> iff) (@Debug B).
    Proof.
      unfold Proper, respectful.
      intros ? ? -> P Q PQ.
      split; intros []; constructor; intuition.
    Qed.

    Ltac wsimpl :=
      repeat
        (try change (wctx (wsnoc ?w ?b)) with (ctx_snoc (wctx w) b);
         try change (wsub (@wred_sup ?w ?b ?t)) with (sub_snoc (sub_id (wctx w)) b t);
         try change (wco (wsnoc ?w ?b)) with (subst (wco w) (sub_wk1 (b:=b)));
         try change (wsub (@wrefl ?w)) with (sub_id (wctx w));
         try change (wsub (@wsnoc_sup ?w ?b)) with (@sub_wk1 (wctx w) b);
         try change (wctx (wformula ?w ?fml)) with (wctx w);
         try change (wsub (wtrans ?ω1 ?ω2)) with (subst (wsub ω1) (wsub ω2));
         try change (wsub (@wformula_sup ?w ?fml)) with (sub_id (wctx w));
         try change (wco (wformula ?w ?fml)) with (cons fml (wco w));
         try change (wco (@wsubst ?w _ _ ?xIn ?t)) with (subst (wco w) (sub_single xIn t));
         try change (wctx (@wsubst ?w _ _ ?xIn ?t)) with (ctx_remove xIn);
         try change (wsub (@wsubst_sup ?w _ _ ?xIn ?t)) with (sub_single xIn t);
         rewrite <- ?sub_comp_wk1_tail, ?inst_subst, ?subst_sub_id,
           ?inst_sub_id, ?inst_sub_wk1, ?inst_sub_snoc,
           ?inst_lift, ?inst_sub_single, ?inst_pathcondition_cons;
         repeat
           match goal with
           | |- Debug _ _ <-> Debug _ _ => apply proper_debug
           | |- (?A /\ ?B) <-> (?A /\ ?C) => apply and_iff_compat_l'; intro
           | |- (?A -> ?B) <-> (?A -> ?C) => apply imp_iff_compat_l'; intro
           | |- (exists x : ?X, _) <-> (exists y : ?X, _) => apply base.exist_proper; intro
           | |- (forall x : ?X, _) <-> (forall y : ?X, _) => apply base.forall_proper; intro
           | |- wp ?m _ ?ι -> wp ?m _ ?ι => apply wp_monotonic; intro
           | |- wp ?m _ ?ι <-> wp ?m _ ?ι => apply wp_equiv; intro
           | |- ?w ⊒ ?w => apply wrefl
           | |- ?POST (@inst _ _ _ ?Σ1 ?x1 ?ι1) <-> ?POST (@inst _ _ _ ?Σ2 ?x2 ?ι2) =>
             assert (@inst _ _ _ Σ1 x1 ι1 = @inst _ _ _ Σ2 x2 ι2) as ->; auto
           | |- ?POST (?inst _ _ _ ?Σ1 ?x1 ?ι1) -> ?POST (@inst _ _ _ ?Σ2 ?x2 ?ι2) =>
             assert (@inst _ _ _ Σ1 x1 ι1 = @inst _ _ _ Σ2 x2 ι2) as ->; auto
           | Hdcl : mapping_dcl ?f |-
             inst (?f ?w ?ω _) _ = inst (?f ?w ?ω _) _ =>
             apply (Hdcl w ω w ω wrefl)
           | Hdcl : mapping_dcl ?f |-
             inst (?f ?w0 wrefl _) _ = inst (?f ?w1 ?ω01 _) _ =>
             apply (Hdcl w0 wrefl w1 ω01 ω01)
           | Hdcl : mapping_dcl ?f |-
             inst (?f ?w1 ?ω01 _) _ = inst (?f ?w0 wrefl _) _ =>
             symmetry; apply (Hdcl w0 wrefl w1 ω01 ω01)
           | Hdcl : arrow_dcl ?f |-
             wp (?f ?w ?ω _) _ _ -> wp (?f ?w ?ω _) _ _  =>
             apply (Hdcl w ω w ω wrefl)
           end).

    Lemma wp_angelic {AT A} `{InstLaws AT A} {w0} {x : option 𝑺} {σ : Ty}
          (k : arrow (STerm σ) AT w0) (k_dcl : arrow_dcl k)
          (POST : A -> Prop) (ι0 : SymInstance w0) :
      instpc (wco w0) ι0 ->
      wp (angelic x σ k) POST ι0 <->
      exists v : Lit σ, wp (k _ wrefl (lift v)) POST ι0.
    Proof.
      cbn. split; intros [v Hwp]; exists v; revert Hwp.
      - apply k_dcl with (wred_sup (fresh w0 x :: σ) (lift v)); wsimpl; auto.
      - apply k_dcl with wsnoc_sup; wsimpl; auto.
    Qed.

    Lemma wp_map {AT A BT B} `{InstLaws AT A, Inst BT B} {w0} (ma : SPath AT w0)
      (f : mapping AT BT w0) (f_dcl : mapping_dcl f) :
      forall POST (ι : SymInstance w0) (Hpc : instpc (wco w0) ι),
        wp (map f ma) POST ι <->
        wp ma (fun a => POST (inst (T f (lift a)) ι)) ι.
    Proof with wsimpl; auto with dcl; unfold four; wsimpl; auto.
      intros POST ι Hpc. unfold T.
      induction ma; cbn; wsimpl; auto.
      - unfold T. wsimpl; auto.
      - rewrite IHma1, IHma2...
      - rewrite IHma1, IHma2...
      - rewrite IHma...
      - rewrite IHma...
      - rewrite IHma...
      - rewrite IHma...
      - rewrite IHma...
      - rewrite IHma...
    Qed.

    Lemma wp_bind {AT A BT B} `{InstLaws AT A, Inst BT B} {w0} (ma : SPath AT w0)
      (f : arrow AT BT w0) (f_dcl : arrow_dcl f) :
      forall POST (ι : SymInstance w0) (Hpc : instpc (wco w0) ι),
        wp (bind ma f) POST ι <->
        wp ma (fun a => wp (T f (lift a)) POST ι) ι.
    Proof with wsimpl; auto with dcl; unfold four; wsimpl; auto.
      intros POST ι Hpc. unfold T.
      induction ma; cbn; wsimpl; auto.
      - unfold T. split; wsimpl; auto.
      - rewrite IHma1, IHma2...
      - rewrite IHma1, IHma2...
      - rewrite IHma...
        eapply arrow_dcl_equiv; wsimpl; auto.
        Unshelve.
        3: apply wformula_sub.
        3: apply wformula_sup.
        unfold wformula_sub. cbn. wsimpl; auto.
        unfold wformula_sup. cbn. wsimpl; auto.
      - rewrite IHma...
        eapply arrow_dcl_equiv; wsimpl; auto.
        Unshelve.
        3: apply wformula_sub.
        3: apply wformula_sup.
        unfold wformula_sub. cbn. wsimpl; auto.
        unfold wformula_sup. cbn. wsimpl; auto.
    Admitted.

    Lemma wp_assume_multisub {AT A} `{InstLaws AT A} {w0 w1} (ζ : MultiSub w0 w1)
      (o : SPath AT w1) (P : A -> Prop) (ι0 : SymInstance w0) :
      wp (assume_multisub ζ o) P ι0 <->
      (inst_multisub ζ ι0 -> wp o P (inst (sub_multishift ζ) ι0)).
    Proof.
      induction ζ; cbn in *.
      - rewrite inst_sub_id. intuition.
      - rewrite IHζ. clear IHζ.
        rewrite <- inst_sub_shift.
        rewrite inst_subst.
        intuition.
    Qed.

    Lemma wp_assume_formulas_without_solver {AT A} `{InstLaws AT A} {w0 : World}
      (fmls : List Formula w0) (o : SPath AT (wformulas w0 fmls))
      (P : A -> Prop) (ι0 : SymInstance w0) :
      wp (assume_formulas_without_solver fmls o) P ι0 <->
      (instpc fmls ι0 -> wp o P ι0).
    Proof.
      destruct w0. unfold assume_formulas_without_solver. cbn in fmls.
      induction fmls; unfold wformulas; cbn in *.
      - split; auto. intros HYP. apply HYP. constructor.
      - rewrite IHfmls, inst_pathcondition_cons. cbn.
        intuition.
    Qed.

    Definition angelic_binary_prune {AT} :
      ⊢ SPath AT -> SPath AT -> SPath AT :=
      fun w o1 o2 =>
        match o1 , o2 with
        | block   , _       => block
        | _       , block   => block
        | error _ , _       => o2
        | _       , error _ => o1
        | _       , _       => angelic_binary o1 o2
        end.

    Definition demonic_binary_prune {AT} :
      ⊢ SPath AT -> SPath AT -> SPath AT :=
      fun w o1 o2 =>
        match o1 , o2 with
        | block   , _       => o2
        | _       , block   => o1
        | error s , _       => error s
        | _       , error s => error s
        | _       , _       => demonic_binary o1 o2
        end.

    Definition assertk_prune {AT} :
      (* ⊢ Formula -> Message -> SPath AT -> SPath AT. *)
      forall {w : World} (fml : Formula w), Message w -> SPath AT (wformula w fml) -> SPath AT w :=
      fun w fml msg o =>
        match o with
        | error s => @error AT w s
        | _       => assertk fml msg o
        end.
    Global Arguments assertk_prune {AT w} fml msg p.

    Definition assumek_prune {AT} :
      (* ⊢ Formula -> SPath AT -> SPath AT := *)
      forall {w : World} (fml : Formula w), SPath AT (wformula w fml) -> SPath AT w :=
      fun w fml o =>
        match o with
        | block => block
        | _     => assumek fml o
        end.
    Global Arguments assumek_prune {AT w} fml p.

    Definition angelicv_prune {AT} (* `{OccursCheck AT} *) b :
      ⊢ Snoc (SPath AT) b -> SPath AT :=
      fun w o => angelicv b o.
        (* This is not good *)
        (* match o with *)
        (* | fail s => fail s *)
        (* | _           => angelicv b o *)
        (* end. *)

    Definition demonicv_prune {AT} `{OccursCheck AT} b :
      ⊢ Snoc (SPath AT) b -> SPath AT :=
      fun w o => demonicv b o.
        (* match @occurs_check_spath AT _ (Σ ▻ b) b inctx_zero o with *)
        (* | Some o => o *)
        (* | None   => demonicv b o *)
        (* end. *)

    Definition assert_vareq_prune {AT w}
      {x σ} {xIn : (x,σ) ∈ wctx w} (t : Term (w - (x,σ)) σ)
      (msg : Message (w - (x,σ))) (k : SPath AT (wsubst w x t)) : SPath AT w :=
      match k with
      (* | fail s => fail s *)
      | _          => assert_vareq x t msg k
      end.
    Global Arguments assert_vareq_prune {AT w} x {σ xIn} t msg k.

    Definition assume_vareq_prune {AT w}
      {x σ} {xIn : (x,σ) ∈ wctx w} (t : Term (w - (x,σ)) σ) (k : SPath AT (wsubst w x t)) : SPath AT w :=
      match k with
      | block => block
      | _          => assume_vareq x t k
      end.
    Global Arguments assume_vareq_prune {AT w} x {σ xIn} t k.

    Definition prune {AT} `{OccursCheck AT} :
      ⊢ SPath AT -> SPath AT :=
      fix prune {w} o :=
        match o with
        | pure a => pure a
        | error msg => error msg
        | block => block
        | angelic_binary o1 o2 =>
          angelic_binary_prune (prune o1) (prune o2)
        | demonic_binary o1 o2 =>
          demonic_binary_prune (prune o1) (prune o2)
        | assertk fml msg o =>
          assertk_prune fml msg (prune o)
        | assumek fml o =>
          assumek_prune fml (prune o)
        | angelicv b o =>
          angelicv_prune (prune o)
        | demonicv b o =>
          demonicv_prune (prune o)
        | assert_vareq x t msg k =>
          assert_vareq_prune x t msg (prune k)
        | assume_vareq x t k =>
          assume_vareq_prune x t (prune k)
        | debug d k =>
          debug d (prune k)
        end.

    Definition ok {AT} `{OccursCheck AT} :
      ⊢ SPath AT -> ⌜bool⌝ :=
      fun w o =>
        match prune o with
        | block => true
        | _     => false
        end.

    Definition run {AT A} `{OccursCheck AT, Inst AT A} :
      ⊢ SPath AT -> SymInstance -> ⌜option A⌝ :=
      fun w o ι =>
        match prune o with
        | pure a => Some (inst a ι)
        | _      => None
        end.

  End Path.

  Import Path.

  Section VerificationConditions.

    Inductive VerificationCondition {AT} (p : SPath AT wnil) : Prop :=
    | vc (P : safe p env_nil).

  End VerificationConditions.

  Section SMutatorResult.

    (* Local Set Primitive Projections. *)
    Local Set Maximal Implicit Insertion.

    Record SMutResult (Γ : PCtx) (A : TYPE) (w : World) : Type :=
      MkSMutResult {
          smutres_value : A w;
          smutres_store : SStore Γ w;
          smutres_heap  : SHeap w;
        }.

    Global Arguments MkSMutResult {_ _ _} _ _ _.

   (*  Global Instance SubstSMutResult {Γ A} `{Subst A} : Subst (SMutResult Γ A). *)
   (*  Proof. *)
   (*    intros Σ1 [a δ h] Σ2 ζ. *)
   (*    constructor. *)
   (*    apply (subst a ζ). *)
   (*    apply (subst δ ζ). *)
   (*    apply (subst h ζ). *)
   (* Defined. *)

   (*  Global Instance SubstLawsSMutResult {Γ A} `{SubstLaws A} : SubstLaws (SMutResult Γ A). *)
   (*  Proof. *)
   (*    constructor. *)
   (*    - intros ? []; cbn; now rewrite ?subst_sub_id. *)
   (*    - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp. *)
   (*  Qed. *)

  End SMutatorResult.

  Section Configuration.

    Record Config : Type :=
      MkConfig
        { config_debug_function : forall Δ τ, 𝑭 Δ τ -> bool;
        }.

    Definition default_config : Config :=
      {| config_debug_function _ _ f := false;
      |}.

  End Configuration.

  Section SMutator.

    Definition SMut (Γ1 Γ2 : PCtx) (A : TYPE) : TYPE :=
      SStore Γ1 -> SHeap -> SPath (SMutResult Γ2 A).
    Bind Scope smut_scope with SMut.

    Definition smut_pure {Γ} {A : TYPE} :
      ⊢ A -> SMut Γ Γ A.
      intros w0 a δ h.
      apply Path.pure.
      constructor.
      apply a.
      apply δ.
      apply h.
    Defined.

    Definition smut_bpure {Γ} {A : TYPE}  :
      ⊢ □(A -> SMut Γ Γ A).
      intros w0 w1 ω01 a δ h.
      apply Path.pure.
      constructor.
      apply a.
      apply δ.
      apply h.
    Defined.
    Global Arguments smut_bpure {_ _ _}.

    Definition smut_bind {Γ1 Γ2 Γ3 A B} :
      ⊢ SMut Γ1 Γ2 A -> □(A -> SMut Γ2 Γ3 B) -> SMut Γ1 Γ3 B :=
      fun w0 ma f δ1 h1 =>
        bind (ma δ1 h1)
          (fun w1 ω01 '(MkSMutResult a1 δ1 h1) =>
             f w1 ω01 a1 δ1 h1).

    Definition smut_bbind {Γ1 Γ2 Γ3 A B} :
      ⊢ □(SMut Γ1 Γ2 A) -> □(A -> SMut Γ2 Γ3 B) -> □(SMut Γ1 Γ3 B).
      intros w0 ma f w1 ω01 δ1 h1.
      apply (bind (ma w1 ω01 δ1 h1)).
      intros w2 ω12 [a2 δ2 h2].
      apply (four f ω01). auto. auto. auto. auto.
    Defined.

    (* Definition smut_strength {Γ1 Γ2 A B Σ} `{Subst A, Subst B} (ma : SMut Γ1 Γ2 A Σ) (b : B Σ) : *)
    (*   SMut Γ1 Γ2 (fun Σ => A Σ * B Σ)%type Σ := *)
    (*   smut_bind ma (fun _ ζ a => smut_pure (a, subst b ζ)). *)

    Definition smut_bind_right {Γ1 Γ2 Γ3 A B} :
      ⊢ □(SMut Γ1 Γ2 A) -> □(SMut Γ2 Γ3 B) -> □(SMut Γ1 Γ3 B).
      refine (fun w0 ma mb w1 ω01 => smut_bind (ma w1 ω01) _).
      refine (fun w2 ω12 _ => mb w2 (wtrans ω01 ω12)).
    Defined.

    Definition smut_bind_left {Γ1 Γ2 Γ3 A B} `{Subst A} :
      ⊢ □(SMut Γ1 Γ2 A) -> □(SMut Γ2 Γ3 B) -> □(SMut Γ1 Γ3 A).
    Proof.
      intros w0 ma mb.
      apply (smut_bbind ma).
      intros w1 ω01 a1 δ1 h1.
      apply (bind (mb w1 ω01 δ1 h1)).
      intros w2 ω12 [_ δ2 h2].
      apply (smut_pure).
      apply (subst a1 ω12).
      auto.
      auto.
    Defined.

    (* Definition smut_map {Γ1 Γ2 A B} `{Subst A, Subst B} : *)
    (*   ⊢ □(SMut Γ1 Γ2 A) -> □(A -> B) -> □(SMut Γ1 Γ2 B) := *)
    (*   fun w0 ma f Σ1 ζ01 pc1 δ1 h1 => *)
    (*     map pc1 *)
    (*       (fun Σ2 ζ12 pc2 '(MkSMutResult a2 δ2 h2) => *)
    (*          MkSMutResult (f Σ2 (subst ζ01 ζ12) pc2 a2) δ2 h2) *)
    (*        (ma Σ1 ζ01 pc1 δ1 h1). *)

    Definition smut_error {Γ1 Γ2 A D} (func : string) (msg : string) (data:D) :
      ⊢ SMut Γ1 Γ2 A.
    Proof.
      intros w δ h.
      apply error.
      apply (@MkMessage _ func msg Γ1); auto.
      apply (wco w).
    Defined.
    Global Arguments smut_error {_ _ _ _} func msg data {w} _ _.

    Definition smut_block {Γ1 Γ2 A} :
      ⊢ SMut Γ1 Γ2 A :=
      fun w δ h => block.

    Definition smut_angelic_binary {Γ1 Γ2 A} :
      ⊢ □(SMut Γ1 Γ2 A) -> □(SMut Γ1 Γ2 A) -> □(SMut Γ1 Γ2 A) :=
      fun w0 m1 m2 w1 ω01 δ1 h1 =>
      angelic_binary (m1 w1 ω01 δ1 h1) (m2 w1 ω01 δ1 h1).
    Definition smut_demonic_binary {Γ1 Γ2 A} :
      ⊢ □(SMut Γ1 Γ2 A) -> □(SMut Γ1 Γ2 A) -> □(SMut Γ1 Γ2 A) :=
      fun w0 m1 m2 w1 ω01 δ1 h1 =>
        demonic_binary (m1 w1 ω01 δ1 h1) (m2 w1 ω01 δ1 h1).

    Definition smut_angelic {AT Γ1 Γ2} (x : option 𝑺) σ :
      ⊢ □(STerm σ -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT :=
      fun w0 k δ0 h0 =>
        angelic x σ
          (fun w1 ω01 t =>
           k w1 ω01 t (subst δ0 ω01) (subst h0 ω01)).
    Global Arguments smut_angelic {_ _ _} x σ {w} k.

    Definition smut_demonic {AT Γ1 Γ2} (x : option 𝑺) σ :
      ⊢ □(STerm σ -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT :=
      fun w0 k δ0 h0 =>
        demonic x σ
          (fun w1 ω01 t =>
           k w1 ω01 t (subst δ0 ω01) (subst h0 ω01)).
    Global Arguments smut_demonic {_ _ _} x σ {w} k.

    Definition smut_debug {AT DT D} `{Subst DT, Inst DT D, OccursCheck DT} {Γ1 Γ2} :
      ⊢ (SStore Γ1 -> SHeap -> DT) -> (SMut Γ1 Γ2 AT) -> (SMut Γ1 Γ2 AT) :=
      fun w0 d m δ1 h1 =>
        debug (d δ1 h1) (m δ1 h1).

  End SMutator.
  Bind Scope smut_scope with SMut.

  Module SMutatorNotations.

    (* Notation "'⨂' x .. y => F" := *)
    (*   (smut_demonic (fun x => .. (smut_demonic (fun y => F)) .. )) : smut_scope. *)

    (* Notation "'⨁' x .. y => F" := *)
    (*   (smut_angelic (fun x => .. (smut_angelic (fun y => F)) .. )) : smut_scope. *)

    Infix "⊗" := smut_demonic_binary (at level 40, left associativity) : smut_scope.
    Infix "⊕" := smut_angelic_binary (at level 50, left associativity) : smut_scope.

    Notation "x <- ma ;; mb" := (smut_bind ma (fun _ _ x => mb)) (at level 80, ma at level 90, mb at level 200, right associativity) : smut_scope.
    Notation "ma >>= f" := (smut_bind ma f) (at level 50, left associativity) : smut_scope.
    (* Notation "m1 ;; m2" := (smut_bind_right m1 m2) : smut_scope. *)

  End SMutatorNotations.
  Import SMutatorNotations.
  Local Open Scope smut_scope.

  (* Fixpoint smut_demonic_freshen_ctx {N : Set} {Γ Σ0} (n : N -> 𝑺) (Δ : NCtx N Ty) : *)
  (*   SMut Γ Γ (fun Σ => NamedEnv (Term Σ) Δ) Σ0 := *)
  (*  match Δ  with *)
  (*  | ε            => smut_pure env_nil *)
  (*  | Δ ▻ (x :: σ) => *)
  (*      smut_demonic_freshen_ctx n Δ        >>= fun _ _ δΔ => *)
  (*      smut_demonic_termvar (Some (n x)) σ >>= fun _ ζ12 t => *)
  (*      smut_pure (subst δΔ ζ12 ► (x :: σ ↦ t)) *)
  (*  end. *)

  (* Add the provided formula to the path condition. *)
  Definition smut_assume_formula {Γ} :
    ⊢ Formula -> SMut Γ Γ Unit :=
    fun w fml δ h =>
      assume_formulak fml (smut_bpure <*> persist tt <*> persist δ <*> persist h).

  Definition smut_box_assume_formula {Γ} :
    ⊢ Formula -> □(SMut Γ Γ Unit).
  Proof.
    intros w0 fml w1 ω01.
    apply smut_assume_formula.
    apply (subst fml ω01).
  Defined.

  Definition smutk_assume_formula {A Γ1 Γ2} :
    ⊢ Formula -> □(SMut Γ1 Γ2 A) -> SMut Γ1 Γ2 A :=
    fun w0 fml m δ0 h0 =>
      assume_formulak fml (m <*> persist δ0 <*> persist h0).

  Definition smut_assert_formula {Γ} :
    ⊢ Formula -> SMut Γ Γ Unit :=
    fun w fml δ h =>
      assert_formulak
        {| msg_function        := "smut_assert_formula";
           msg_message         := "Proof obligation";
           msg_program_context := Γ;
           msg_pathcondition   := wco w;
           msg_localstore      := δ;
           msg_heap            := h;
        |}
        fml
        (smut_bpure <*> persist tt <*> persist δ <*> persist h).

  Definition smutk_assert_formula {A Γ1 Γ2} :
    ⊢ Formula -> □(SMut Γ1 Γ2 A) -> SMut Γ1 Γ2 A :=
    fun w0 fml m δ0 h0 =>
      assert_formulak
        {| msg_function        := "smutk_assert_formula";
           msg_message         := "Proof obligation";
           msg_program_context := Γ1;
           msg_pathcondition   := wco w0;
           msg_localstore      := δ0;
           msg_heap            := h0;
        |}
        fml
        (m <*> persist δ0 <*> persist h0).

  Definition smut_box_assert_formula {Γ} :
    ⊢ Formula -> □(SMut Γ Γ Unit).
  Proof.
    intros w0 fml w1 ω01.
    apply smut_assert_formula.
    apply (subst fml ω01).
  Defined.

  Section PatternMatching.

    Definition smut_angelic_match_bool {AT} {Γ1 Γ2} :
      ⊢ STerm ty_bool -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
      fun w0 t kt kf w1 ω01 δ1 h1 =>
        angelic_match_bool
          {| msg_function        := "smut_angelic_match_bool";
             msg_message         := "pattern match assertion";
             msg_program_context := Γ1;
             msg_localstore      := δ1;
             msg_heap            := h1;
             msg_pathcondition   := wco w1;
          |}
          (subst t ω01)
          (four kt ω01 <*> persist δ1 <*> persist h1)
          (four kf ω01 <*> persist δ1 <*> persist h1).

    Definition smut_demonic_match_bool {AT} {Γ1 Γ2} :
      ⊢ STerm ty_bool -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT :=
      fun w0 t kt kf δ0 h0 =>
        demonic_match_bool t
          (kt <*> persist δ0 <*> persist h0)
          (kf <*> persist δ0 <*> persist h0).

    Definition smutb_demonic_match_bool {AT} {Γ1 Γ2} :
      ⊢ STerm ty_bool -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
      fun w0 t kt kf =>
        smut_demonic_match_bool <$> persist__term t <*> four kt <*> four kf.

    Definition smut_angelic_match_enum {AT E} {Γ1 Γ2} :
      ⊢ STerm (ty_enum E) -> (⌜𝑬𝑲 E⌝ -> □(SMut Γ1 Γ2 AT)) -> □(SMut Γ1 Γ2 AT) :=
      fun w0 t k w1 ω01 δ1 h1 =>
        angelic_match_enum
          {| msg_function        := "smut_angelic_match_enum";
             msg_message         := "pattern match assertion";
             msg_program_context := Γ1;
             msg_localstore      := δ1;
             msg_heap            := h1;
             msg_pathcondition   := wco w1;
          |}
          (subst t ω01)
          (fun v => four (k v) ω01 <*> persist δ1 <*> persist h1).

    Definition smut_demonic_match_enum {AT E} {Γ1 Γ2} :
      ⊢ STerm (ty_enum E) -> (⌜𝑬𝑲 E⌝ -> □(SMut Γ1 Γ2 AT)) -> SMut Γ1 Γ2 AT :=
      fun w0 t k δ1 h1 =>
        demonic_match_enum t (fun v => k v <*> persist δ1 <*> persist h1).

    Definition smutb_demonic_match_enum {AT E} {Γ1 Γ2} :
      ⊢ STerm (ty_enum E) -> (⌜𝑬𝑲 E⌝ -> □(SMut Γ1 Γ2 AT)) -> □(SMut Γ1 Γ2 AT) :=
      fun w0 t k =>
        smut_demonic_match_enum
          <$> persist__term t
          <*> (fun (w1 : World) (ω01 : w0 ⊒ w1) (EK : 𝑬𝑲 E) => four (k EK) ω01).

    Definition smut_angelic_match_sum {AT Γ1 Γ2} (x y : 𝑺) {σ τ} :
      ⊢ STerm (ty_sum σ τ) -> □(STerm σ -> SMut Γ1 Γ2 AT) -> □(STerm τ -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
      fun w0 t kinl kinr w1 ω01 δ1 h1 =>
        Path.angelic_match_sum
          (Some x) (Some y)
          {| msg_function        := "smut_angelic_match_sum";
             msg_message         := "pattern match assertion";
             msg_program_context := Γ1;
             msg_localstore      := δ1;
             msg_heap            := h1;
             msg_pathcondition   := wco w1;
          |}
          (subst t ω01)
          (fun w2 ω12 t' =>
             four kinl ω01 ω12 t' (subst δ1 ω12) (subst h1 ω12))
          (fun w2 ω12 t' =>
             four kinr ω01 ω12 t' (subst δ1 ω12) (subst h1 ω12)).

    Definition smut_demonic_match_sum {AT Γ1 Γ2} (x y : 𝑺) {σ τ} :
      ⊢ STerm (ty_sum σ τ) -> □(STerm σ -> SMut Γ1 Γ2 AT) -> □(STerm τ -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
    Proof.
      refine (fun w0 t kinl kinr δ0 h0 => _).
      apply (Path.demonic_match_sum (Some x) (Some y) t).
      - intros w1 ω01 t'. apply kinl; auto.
        apply (persist δ0 ω01).
        apply (persist h0 ω01).
      - intros w1 ω01 t'.
        apply kinr; auto.
        apply (persist δ0 ω01).
        apply (persist h0 ω01).
    Defined.

    Definition smutb_demonic_match_sum {AT Γ1 Γ2} (x y : 𝑺) {σ τ} :
      ⊢ STerm (ty_sum σ τ) -> □(STerm σ -> SMut Γ1 Γ2 AT) -> □(STerm τ -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
      fun w0 t kinl kinr w1 ω01 δ1 h1 =>
        Path.demonic_match_sum
          (Some x) (Some y) (subst t ω01)
          (fun w2 ω12 t' =>
             four kinl ω01 ω12 t' (subst δ1 ω12) (subst h1 ω12))
          (fun w2 ω12 t' =>
             four kinr ω01 ω12 t' (subst δ1 ω12) (subst h1 ω12)).

    Definition smut_angelic_match_list {AT Γ1 Γ2} (x y : 𝑺) {σ} :
      ⊢ STerm (ty_list σ) -> □(SMut Γ1 Γ2 AT) -> □(STerm σ -> STerm (ty_list σ) -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
      fun w0 t knil kcons w1 ω01 δ1 h1 =>
        angelic_match_list
          (Some x) (Some y)
          {| msg_function        := "smut_angelic_match_list";
             msg_message         := "pattern match assertion";
             msg_program_context := Γ1;
             msg_localstore      := δ1;
             msg_heap            := h1;
             msg_pathcondition   := wco w1;
          |}
          (subst t ω01)
          (fun (w2 : World) (ω12 : w1 ⊒ w2) => four knil ω01 ω12 (subst δ1 ω12) (subst h1 ω12))
          (fun (w2 : World) (ω12 : w1 ⊒ w2) (th : Term w2 σ) (tt : Term w2 (ty_list σ)) =>
             four kcons ω01 ω12 th tt (subst δ1 ω12) (subst h1 ω12)).

    Definition smut_demonic_match_list {AT Γ1 Γ2} (x y : 𝑺) {σ} :
      ⊢ STerm (ty_list σ) -> □(SMut Γ1 Γ2 AT) -> □(STerm σ -> STerm (ty_list σ) -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
      fun w0 t knil kcons w1 ω01 δ1 h1 =>
        demonic_match_list
          (Some x) (Some y) (subst t ω01)
          (fun (w2 : World) (ω12 : w1 ⊒ w2) => four knil ω01 ω12 (subst δ1 ω12) (subst h1 ω12))
          (fun (w2 : World) (ω12 : w1 ⊒ w2) (th : Term w2 σ) (tt : Term w2 (ty_list σ)) =>
             four kcons ω01 ω12 th tt (subst δ1 ω12) (subst h1 ω12)).

    Definition smut_angelic_match_pair {AT} {Γ1 Γ2} (x y : 𝑺) {σ τ} :
      ⊢ STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
      fun w0 t k w1 ω01 δ1 h1 =>
        angelic_match_pair
          (Some x) (Some y)
          {| msg_function        := "smut_angelic_match_pair";
             msg_message         := "pattern match assertion";
             msg_program_context := Γ1;
             msg_localstore      := δ1;
             msg_heap            := h1;
             msg_pathcondition   := wco w1;
          |}
          (subst t ω01)
          (fun (w2 : World) (ω12 : w1 ⊒ w2) (tl : Term w2 σ) (tr : Term w2 τ) =>
             four k ω01 ω12 tl tr (subst δ1 ω12) (subst h1 ω12)).

    Definition smutb_demonic_match_pair {AT} {Γ1 Γ2} (x y : 𝑺) {σ τ} :
      ⊢ STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
      fun w0 t k w1 ω01 δ1 h1 =>
        demonic_match_pair
          (Some x) (Some y) (subst t ω01)
          (fun (w2 : World) (ω12 : w1 ⊒ w2) (tl : Term w2 σ) (tr : Term w2 τ) =>
             four k ω01 ω12 tl tr (subst δ1 ω12) (subst h1 ω12)).

    Definition smut_angelic_match_record {N : Set} (n : N -> 𝑺) {AT R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) :
      ⊢ STerm (ty_record R) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
      fun w0 t k w1 ω01 δ1 h1 =>
        angelic_match_record
          n p
          {| msg_function        := "smut_angelic_match_record";
             msg_message         := "pattern match assertion";
             msg_program_context := Γ1;
             msg_localstore      := δ1;
             msg_heap            := h1;
             msg_pathcondition   := wco w1;
          |}
          (subst t ω01)
          (fun (w2 : World) (ω12 : w1 ⊒ w2) (ts : NamedEnv (Term w2) Δ) =>
             four k ω01 ω12 ts (subst δ1 ω12) (subst h1 ω12)).

    Definition smut_demonic_match_record {N : Set} (n : N -> 𝑺) {AT R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) :
      ⊢ STerm (ty_record R) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
      fun w0 t k w1 ω01 δ1 h1 =>
        demonic_match_record
          n p (subst t ω01)
          (fun (w2 : World) (ω12 : w1 ⊒ w2) (ts : NamedEnv (Term w2) Δ) =>
             four k ω01 ω12 ts (subst δ1 ω12) (subst h1 ω12)).

    Definition smut_angelic_match_tuple {N : Set} (n : N -> 𝑺) {AT σs Γ1 Γ2} {Δ : NCtx N Ty} (p : TuplePat σs Δ) :
      ⊢ STerm (ty_tuple σs) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
      fun w0 t k w1 ω01 δ1 h1 =>
        angelic_match_tuple
          n p
          {| msg_function        := "smut_angelic_match_tuple";
             msg_message         := "pattern match assertion";
             msg_program_context := Γ1;
             msg_localstore      := δ1;
             msg_heap            := h1;
             msg_pathcondition   := wco w1;
          |}
          (subst t ω01)
          (fun (w2 : World) (ω12 : w1 ⊒ w2) (ts : NamedEnv (Term w2) Δ) =>
             four k ω01 ω12 ts (subst δ1 ω12) (subst h1 ω12)).

    Definition smut_demonic_match_tuple {N : Set} (n : N -> 𝑺) {AT σs Γ1 Γ2} {Δ : NCtx N Ty} (p : TuplePat σs Δ) :
      ⊢ STerm (ty_tuple σs) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
      fun w0 t k w1 ω01 δ1 h1 =>
        demonic_match_tuple
          n p (subst t ω01)
          (fun (w2 : World) (ω12 : w1 ⊒ w2) (ts : NamedEnv (Term w2) Δ) =>
             four k ω01 ω12 ts (subst δ1 ω12) (subst h1 ω12)).

    Definition smut_angelic_match_union {N : Set} (n : N -> 𝑺) {AT Γ1 Γ2 U}
      {Δ : 𝑼𝑲 U -> NCtx N Ty} (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) :
      ⊢ STerm (ty_union U) -> (∀ K, □((fun w => NamedEnv (Term w) (Δ K)) -> SMut Γ1 Γ2 AT)) -> □(SMut Γ1 Γ2 AT) :=
      fun w0 t k w1 ω01 δ1 h1 =>
        angelic_match_union
          n p
          {| msg_function        := "smut_angelic_match_union";
             msg_message         := "pattern match assertion";
             msg_program_context := Γ1;
             msg_localstore      := δ1;
             msg_heap            := h1;
             msg_pathcondition   := wco w1;
          |}
          (subst t ω01)
          (fun (K : 𝑼𝑲 U) (w2 : World) (ω12 : w1 ⊒ w2) (ts : NamedEnv (Term w2) (Δ K)) =>
             four (k K) ω01 ω12 ts (subst δ1 ω12) (subst h1 ω12)).

    Definition smut_demonic_match_union {N : Set} (n : N -> 𝑺) {AT Γ1 Γ2 U}
      {Δ : 𝑼𝑲 U -> NCtx N Ty} (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) :
      ⊢ STerm (ty_union U) -> (∀ K, □((fun w => NamedEnv (Term w) (Δ K)) -> SMut Γ1 Γ2 AT)) -> □(SMut Γ1 Γ2 AT) :=
      fun w0 t k w1 ω01 δ1 h1 =>
        demonic_match_union
          n p (subst t ω01)
          (fun (K : 𝑼𝑲 U) (w2 : World) (ω12 : w1 ⊒ w2) (ts : NamedEnv (Term w2) (Δ K)) =>
             four (k K) ω01 ω12 ts (subst δ1 ω12) (subst h1 ω12)).

  End PatternMatching.

  Section State.

    Definition smut_state {Γ1 Γ2 A} :
      ⊢ (SStore Γ1 -> SHeap -> SMutResult Γ2 A) -> SMut Γ1 Γ2 A :=
      fun w0 f δ0 h0 =>
       pure (f δ0 h0).

    Definition smut_bstate {Γ1 Γ2 A} :
      ⊢ □(SStore Γ1 -> SHeap -> SMutResult Γ2 A) -> □(SMut Γ1 Γ2 A) :=
      fun w0 f w1 ω01 δ1 h1 =>
       pure (f w1 ω01 δ1 h1).

    Definition smut_get_local {Γ} : ⊢ □(SMut Γ Γ (SStore Γ)) :=
      fun w0 =>
        smut_bstate (fun w1 ω01 δ1 h1 => MkSMutResult δ1 δ1 h1).
    (* Definition smut_put_local {Γ Γ' Σ} (δ' : SStore Γ' Σ) : SMut Γ Γ' Unit Σ := *)
    (*   smut_state (fun _ ζ _ h => MkSMutResult tt (subst δ' ζ) h). *)

    Definition smutk_pop_local {A Γ1 Γ2 b} :
      ⊢ SMut Γ1 Γ2 A -> SMut (Γ1 ▻ b) Γ2 A.
    Proof.
      intros w k δ h.
      apply k.
      apply (env_tail δ).
      auto.
    Defined.

    Definition smutk_pops_local {A Γ1 Γ2 Δ} :
      ⊢ SMut Γ1 Γ2 A -> SMut (Γ1 ▻▻ Δ) Γ2 A.
    Proof.
      intros w k δ h.
      apply k.
      apply (env_drop Δ δ).
      auto.
    Defined.

    Definition smutk_push_local {A Γ1 Γ2 x σ} :
      ⊢ STerm σ -> SMut (Γ1 ▻ (x :: σ)) Γ2 A -> SMut Γ1 Γ2 A.
    Proof.
      intros w t k δ h.
      apply k.
      apply (env_snoc δ (x :: σ) t).
      auto.
    Defined.

    Definition smutk_pushs_local {A Γ1 Γ2 Δ} :
      ⊢ SStore Δ -> SMut (Γ1 ▻▻ Δ) Γ2 A -> SMut Γ1 Γ2 A.
    Proof.
      intros w δΔ k δ h.
      apply k.
      apply (env_cat δ δΔ).
      auto.
    Defined.

    (* Definition smut_pushpop {AT} `{Subst AT} {Γ1 Γ2 x σ Σ} (t : Term Σ σ) (d : SMut (Γ1 ▻ (x :: σ)) (Γ2 ▻ (x :: σ)) AT Σ) : *)
    (*   SMut Γ1 Γ2 AT Σ := *)
    (*   smut_push_local t ;; smut_bind_left d smut_pop_local. *)
    Definition smut_pushspops {AT} `{Subst AT} {Γ1 Γ2 Δ} :
      ⊢ SStore Δ -> SMut (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) AT -> SMut Γ1 Γ2 AT.
      intros w0 δΔ k.
      intros δ0 h0.
      apply (bind (k (env_cat δ0 δΔ) h0)).
      intros w1 ω01 [a1 δ1 h1].
      apply smut_pure.
      apply a1.
      apply (env_drop Δ δ1).
      apply h1.
    Defined.
    (* Definition smut_get_heap {Γ Σ} : SMut Γ Γ SHeap Σ := *)
    (*   smut_state (fun _ _ δ h => MkSMutResult h δ h). *)
    (* Definition smut_put_heap {Γ Σ} (h : SHeap Σ) : SMut Γ Γ Unit Σ := *)
    (*   smut_state (fun _ ζ δ _ => MkSMutResult tt δ (subst h ζ)). *)
    Definition smut_eval_exp {Γ σ} (e : Exp Γ σ) :
      ⊢ SMut Γ Γ (STerm σ).
      intros w δ h.
      apply smut_pure.
      apply (seval_exp δ e).
      auto.
      auto.
    Defined.
    Definition smut_eval_exps {Γ} {σs : PCtx} (es : NamedEnv (Exp Γ) σs) :
      ⊢ SMut Γ Γ (SStore σs).
      intros w δ h.
      apply smut_pure.
      refine (env_map _ es).
      intros b. apply (seval_exp δ).
      auto.
      auto.
    Defined.

    Definition smutk_eval_exp {A Γ1 Γ2 σ} (e : Exp Γ1 σ) :
      ⊢ (STerm σ -> SMut Γ1 Γ2 A) -> SMut Γ1 Γ2 A.
    Proof.
      intros w k δ h.
      apply k.
      apply (seval_exp δ e).
      auto.
      auto.
    Defined.

    Definition smutk_eval_exps {A Γ1 Γ2} {σs : PCtx} (es : NamedEnv (Exp Γ1) σs) :
      ⊢ (SStore σs -> SMut Γ1 Γ2 A) -> SMut Γ1 Γ2 A.
    Proof.
      intros w k δ h.
      apply k.
      refine (env_map _ es).
      intros b. apply (seval_exp δ).
      auto.
      auto.
    Defined.

  End State.

  (* Definition smut_assert_formulas {Γ Σ} (fmls : list (Formula Σ)) : SMut Γ Γ Unit Σ := *)
  (*   fold_right (fun fml => smut_bind_right (smut_assert_formula fml)) (smut_pure tt) fmls. *)
  Definition smut_produce_chunk {Γ} :
    ⊢ Chunk -> SMut Γ Γ Unit.
  Proof.
    intros w0 c δ h. apply smut_pure.
    constructor. apply δ.
    apply (cons c h).
  Defined.

  Definition smutk_produce_chunk {Γ1 Γ2 A} :
    ⊢ Chunk -> SMut Γ1 Γ2 A -> SMut Γ1 Γ2 A.
  Proof.
    intros w0 c k δ h. apply k.
    apply δ.
    apply (cons c h).
  Defined.

  Definition smut_consume_chunk {Γ} :
    ⊢ Chunk -> □(SMut Γ Γ Unit) :=
    fun w0 c w1 ω01 δ1 h1 =>
      angelic_listk
        (A := fun w => Pair PathCondition SHeap w)
        {| msg_function := "smut_consume_chunk";
           msg_message := "Empty extraction";
           msg_program_context := Γ;
           msg_localstore := δ1;
           msg_heap := h1;
           msg_pathcondition := wco w1
        |}
        (fun '(Δpc,h1') =>
           assert_formulask
             (A := (fun Σ : World => SMutResult Γ Unit Σ))
             {| msg_function := "smut_consume_chunk";
                msg_message := "Proof Obligation";
                msg_program_context := Γ;
                msg_localstore := δ1;
                msg_heap := h1';
                msg_pathcondition := wco w1
             |}
             Δpc
             (fun w2 ω12 => smut_pure tt (subst δ1 ω12) (subst h1' ω12))
             wrefl)
        (extract_chunk_eqb (subst c ω01) h1).

  (* Definition smut_assert_formulak {A Γ1 Γ2 Σ} (fml : Formula Σ) (k : SMut Γ1 Γ2 A Σ) : SMut Γ1 Γ2 A Σ := *)
  (*   smut_bind_right (smut_assert_formula fml) k. *)
  (* Definition smut_assert_formulask {A Γ1 Γ2 Σ} (fmls : list (Formula Σ)) (k: SMut Γ1 Γ2 A Σ) : SMut Γ1 Γ2 A Σ := *)
  (*   fold_right smut_assert_formulak k fmls. *)

  (* Definition smut_leakcheck {Γ Σ} : SMut Γ Γ Unit Σ := *)
  (*   smut_get_heap >>= fun _ _ h => *)
  (*   match h with *)
  (*   | nil => smut_pure tt *)
  (*   | _   => smut_error "smut_leakcheck" "Heap leak" h *)
  (*   end. *)

  (* Definition smut_make_message {Γ} (func msg : string) {Σ0} : SMut Γ Γ Message Σ0 := *)
  (*   fun w1 ω01 δ1 h1 => *)
  (*     pure *)
  (*       (MkSMutResult *)
  (*          {| msg_function        := func; *)
  (*             msg_message         := msg; *)
  (*             msg_program_context := Γ; *)
  (*             msg_localstore      := δ1; *)
  (*             msg_heap            := h1; *)
  (*             msg_pathcondition   := pc1 *)
  (*          |} δ1 h1). *)

  Definition smut_produce {Γ} :
    ⊢ Assertion -> □(SMut Γ Γ Unit) :=
    fix produce w asn {struct asn} :=
      match asn with
      | asn_formula fml => smut_box_assume_formula fml
      | asn_chunk c => valid_box smut_produce_chunk <*> persist c
      | asn_if b asn1 asn2 => smutb_demonic_match_bool b (produce w asn1) (produce w asn2)
      | asn_match_enum E k alts => smutb_demonic_match_enum k (fun K : 𝑬𝑲 E => produce w (alts K))
      | asn_match_sum σ τ s xl asn1 xr asn2 =>
          smutb_demonic_match_sum xl xr s
            (fun (w1 : World) (ω01 : w ⊒ w1) (tl : (fun w0 : World => Term w0 σ) w1) =>
             produce (wsnoc w (xl :: σ)) asn1 w1 (wsnoc_sub ω01 (xl :: σ) tl))
            (fun (w1 : World) (ω01 : w ⊒ w1) (tr : (fun w0 : World => Term w0 τ) w1) =>
             produce (wsnoc w (xr :: τ)) asn2 w1 (wsnoc_sub ω01 (xr :: τ) tr))
      | @asn_match_list _ σ s asn1 xh xt asn2 =>
          smut_demonic_match_list xh xt s (produce w asn1)
            (fun (w1 : World) (ω01 : w ⊒ w1) (th : Term w1 σ) (tt : Term w1 (ty_list σ)) =>
             produce (wsnoc (wsnoc w (xh :: σ)) (xt :: ty_list σ)) asn2 w1
               (wsnoc_sub (wsnoc_sub ω01 (xh :: σ) th) (xt :: ty_list σ) tt))
      | @asn_match_pair _ σ1 σ2 s xl xr asn0 =>
          smutb_demonic_match_pair xl xr s
            (fun (w1 : World) (ω01 : w ⊒ w1) (tl : Term w1 σ1) (tr : Term w1 σ2) =>
             produce (wsnoc (wsnoc w (xl :: σ1)) (xr :: σ2)) asn0 w1
               (wsnoc_sub (wsnoc_sub ω01 (xl :: σ1) tl) (xr :: σ2) tr))
      | @asn_match_tuple _ σs Δ s p asn0 =>
          smut_demonic_match_tuple id p s
            (fun (w1 : World) (ω01 : w ⊒ w1) (ts : NamedEnv (Term w1) Δ) =>
             produce (MkWorld (subst (wco w) (sub_cat_left Δ))) asn0 w1
               (MkAcc (MkWorld (subst (wco w) (sub_cat_left Δ))) w1 (wsub ω01 ►► ts)))
      | @asn_match_record _ R Δ s p asn0 =>
          smut_demonic_match_record id p s
            (fun (w1 : World) (ω01 : w ⊒ w1) (ts : NamedEnv (Term w1) Δ) =>
             produce (MkWorld (subst (wco w) (sub_cat_left Δ))) asn0 w1
               (MkAcc (MkWorld (subst (wco w) (sub_cat_left Δ))) w1 (wsub ω01 ►► ts)))
      | asn_match_union U s alt__ctx alt__pat alt__rhs =>
          smut_demonic_match_union id alt__pat s
            (fun (K : 𝑼𝑲 U) (w1 : World) (ω01 : w ⊒ w1) (ts : NamedEnv (Term w1) (alt__ctx K)) =>
             produce (MkWorld (subst (wco w) (sub_cat_left (alt__ctx K)))) (alt__rhs K) w1
               (MkAcc (MkWorld (subst (wco w) (sub_cat_left (alt__ctx K)))) w1 (wsub ω01 ►► ts)))
      | asn_sep asn1 asn2 => smut_bind_right (produce w asn1) (produce w asn2)
      | asn_exist ς τ asn0 =>
        fun (w1 : World) (ω01 : w ⊒ w1) =>
          smut_demonic (Some ς) τ
            (fun (w2 : World) (ω12 : w1 ⊒ w2) (t2 : Term w2 τ) =>
             produce (wsnoc w (ς :: τ)) asn0 w2 (wsnoc_sub (wtrans ω01 ω12) (ς :: τ) t2))
      | asn_debug =>
        fun w1 ω01 =>
          smut_debug (MkSDebugAsn (wco w1)) (smut_pure tt)
      end.

  Definition smut_produce_fail_recursion {A Γ1 Γ2} :
    ⊢ Assertion -> □(SMut Γ1 Γ2 A) -> SMut Γ1 Γ2 A.
  Proof.
    refine
      (fix produce w0 asn k {struct asn} :=
         match asn with
         | asn_sep asn1 asn2 =>
           produce w0 asn1
                   (* Recursive call to produce has principal argument equal  *)
                   (* to "persist asn2 ω01" instead of one of the following *)
                   (* variables: "asn1" "asn2". *)
                   (produce <$> persist asn2 <*> four k)
         | _ => @smut_block _ _ _ _
         end).
  Abort.

  Definition smutbbk_produce {A Γ1 Γ2} :
    ⊢ Assertion -> □(□(SMut Γ1 Γ2 A) -> SMut Γ1 Γ2 A).
  Proof.
    refine (fix produce w0 asn {struct asn} := _).
    destruct asn.
    - apply (smutk_assume_formula <$> persist fml).
    - intros w1 ω01 k.
      apply (smutk_produce_chunk (subst c ω01)).
      apply (T k).
    - intros w1 ω01 k.
      apply smut_demonic_match_bool.
      + apply (persist__term b ω01).
      + apply (four (produce w0 asn1) ω01 <*> four k).
      + apply (four (produce w0 asn2) ω01 <*> four k).
    - intros w1 ω01 cont.
      apply (smut_demonic_match_enum (persist__term k ω01)). intros EK.
      apply (four (produce w0 (alts EK)) ω01 <*> four cont).
    - intros w1 ω01 k.
      apply (smut_demonic_match_sum xl xr (persist__term s ω01)).
      + intros w2 ω12 t.
        eapply (produce (wsnoc w0 (xl :: σ)) asn1).
        apply wsnoc_sub.
        apply (wtrans ω01 ω12). apply t.
        apply (four k ω12).
      + intros w2 ω12 t.
        eapply (produce (wsnoc w0 (xr :: τ)) asn2).
        apply wsnoc_sub.
        apply (wtrans ω01 ω12). apply t.
        apply (four k ω12).
    - intros w1 ω01 k.
      apply (smut_demonic_match_list xh xt (persist__term s ω01)); try apply wrefl.
      + intros w2 ω12.
        eapply (produce _ asn1).
        apply (wtrans ω01 ω12).
        apply (four k ω12).
      + intros w2 ω12 t1 t2.
        eapply (produce (wsnoc (wsnoc w0 (xh :: _)) (xt :: _)) asn2).
        apply wsnoc_sub.
        apply wsnoc_sub.
        apply (wtrans ω01 ω12).
        apply t1.
        apply t2.
        apply (four k ω12).
    - intros w1 ω01 k.
      apply (smutb_demonic_match_pair xl xr (persist__term s ω01)).
      intros w2 ω12 t1 t2.
      eapply (produce (wsnoc (wsnoc w0 (xl :: σ1)) (xr :: σ2)) asn).
      apply wsnoc_sub.
      apply wsnoc_sub.
      apply (wtrans ω01 ω12).
      apply t1.
      apply t2.
      apply (four k ω12).
      apply wrefl.
    - admit.
    - admit.
    - admit.
    - intros w1 ω01 k.
      apply (produce _ asn1).
      auto.
      apply (four (produce _ asn2) ω01 <*> four k).
    - intros w1 ω01 k.
      apply (smut_demonic (Some ς) τ).
      intros w2 ω12 t2.
      apply (produce (wsnoc w0 (ς :: τ)) asn).
      apply wsnoc_sub.
      apply (wtrans ω01 ω12).
      cbn; auto.
      apply (four k).
      auto.
    - intros w1 ω01 k.
      apply smut_debug.
      intros δ h.
      eapply (MkSDebugAsn (wco w1) δ h).
      apply k. apply wrefl.
  Admitted.

  Definition smutbk_consume {A Γ1 Γ2} :
    ⊢ Assertion -> □(SMut Γ1 Γ2 A -> SMut Γ1 Γ2 A).
  Admitted.

  Definition smutbbk_consume {A Γ1 Γ2} :
    ⊢ Assertion -> □(□(SMut Γ1 Γ2 A) -> SMut Γ1 Γ2 A).
  Admitted.

  Definition smutkb_produce {A Γ1 Γ2} :
    ⊢ Assertion -> □(SMut Γ1 Γ2 A) -> □(SMut Γ1 Γ2 A).
  Proof.
    refine (fix produce w0 asn k {struct asn} := _).
    destruct asn.
    - apply (valid_box smutk_assume_formula <*> persist fml <*> four k).
    - apply (valid_box smutk_produce_chunk <*> persist c <*> k).
    - apply (smutb_demonic_match_bool b (produce w0 asn1 k) (produce w0 asn2 k)).
    - apply (smutb_demonic_match_enum k0). intros EK.
      apply (produce w0 (alts EK) k).
    - apply (smutb_demonic_match_sum xl xr s).
      + intros w1 ω01 tl.
        apply (produce (wsnoc w0 (xl :: σ)) asn1).
        apply (four k). apply wsnoc_sup.
        apply (wsnoc_sub ω01). apply tl.
      + intros w1 ω01 tr.
        apply (produce (wsnoc w0 (xr :: τ)) asn2).
        apply (four k). apply wsnoc_sup.
        apply (wsnoc_sub ω01). apply tr.
    - apply (smut_demonic_match_list xh xt s).
      + apply (produce w0 asn1 k).
      + intros w1 ω01 thead ttail.
        apply (produce (wsnoc (wsnoc w0 (xh :: σ)) (xt :: ty_list σ)) asn2).
        apply (four k).
        eapply (wtrans wsnoc_sup wsnoc_sup).
        apply wsnoc_sub; cbn; auto.
        apply wsnoc_sub; cbn; auto.
    - apply (smutb_demonic_match_pair xl xr s).
      intros w1 ω01 tl tr.
      apply (produce (wsnoc (wsnoc w0 (xl :: σ1)) (xr :: σ2)) asn).
      apply (four k).
      eapply (wtrans wsnoc_sup wsnoc_sup).
      apply wsnoc_sub; cbn; auto.
      apply wsnoc_sub; cbn; auto.
    - apply (smut_demonic_match_tuple id p s).
      intros w1 ω01 ts.
      apply (produce (MkWorld (subst (wco w0) (sub_cat_left Δ))) asn).
      apply (four k).
      constructor. cbn. apply sub_cat_left.
      constructor. cbn. apply (wsub ω01 ►► ts).
    - apply (smut_demonic_match_record id p s).
      intros w1 ω01 ts.
      apply (produce (MkWorld (subst (wco w0) (sub_cat_left Δ))) asn).
      apply (four k).
      constructor. cbn. apply sub_cat_left.
      constructor. cbn. apply (wsub ω01 ►► ts).
    - apply (smut_demonic_match_union id alt__pat s).
      intros UK w1 ω01 ts.
      apply (produce (MkWorld (subst (wco w0) (sub_cat_left (alt__ctx UK)))) (alt__rhs UK)).
      apply (four k).
      constructor. cbn. apply sub_cat_left.
      constructor. cbn. apply (wsub ω01 ►► ts).
    - apply (produce w0 asn1).
      apply (produce w0 asn2).
      apply k.
    - intros w1 ω01.
      apply (smut_demonic (Some ς) τ).
      intros w2 ω12 t2.
      apply (produce (wsnoc w0 (ς :: τ)) asn).
      apply (four k).
      apply wsnoc_sup.
      apply wsnoc_sub.
      apply (wtrans ω01 ω12).
      cbn; auto.
    - apply (valid_box
             smut_debug
             <*> (fun w1 _ => MkSDebugAsn (wco w1))
             <*> k).
  Defined.

  Definition smutk_produce {AT Γ1 Γ2} :
    ⊢ Assertion -> □(SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT :=
    fun w0 asn k => smutkb_produce asn k wrefl.

  Definition smut_consume {Γ} :
    ⊢ Assertion -> □(SMut Γ Γ Unit) :=
    fix consume w asn {struct asn} :=
      match asn with
      | asn_formula fml => smut_box_assert_formula fml
      | asn_chunk c => smut_consume_chunk c
      | asn_if b asn1 asn2 => smut_angelic_match_bool b (consume w asn1) (consume w asn2)
      | asn_match_enum E k alts => smut_angelic_match_enum k (fun K : 𝑬𝑲 E => consume w (alts K))
      | asn_match_sum σ τ s xl asn1 xr asn2 =>
          smut_angelic_match_sum xl xr s
            (fun (w1 : World) (ω01 : w ⊒ w1) (tl : (fun w0 : World => Term w0 σ) w1) =>
             consume (wsnoc w (xl :: σ)) asn1 w1 (wsnoc_sub ω01 (xl :: σ) tl))
            (fun (w1 : World) (ω01 : w ⊒ w1) (tr : (fun w0 : World => Term w0 τ) w1) =>
             consume (wsnoc w (xr :: τ)) asn2 w1 (wsnoc_sub ω01 (xr :: τ) tr))
      | @asn_match_list _ σ s asn1 xh xt asn2 =>
          smut_angelic_match_list xh xt s (consume w asn1)
            (fun (w1 : World) (ω01 : w ⊒ w1) (th : Term w1 σ) (tt : Term w1 (ty_list σ)) =>
             consume (wsnoc (wsnoc w (xh :: σ)) (xt :: ty_list σ)) asn2 w1
               (wsnoc_sub (wsnoc_sub ω01 (xh :: σ) th) (xt :: ty_list σ) tt))
      | @asn_match_pair _ σ1 σ2 s xl xr asn0 =>
          smut_angelic_match_pair xl xr s
            (fun (w1 : World) (ω01 : w ⊒ w1) (tl : Term w1 σ1) (tr : Term w1 σ2) =>
             consume (wsnoc (wsnoc w (xl :: σ1)) (xr :: σ2)) asn0 w1
               (wsnoc_sub (wsnoc_sub ω01 (xl :: σ1) tl) (xr :: σ2) tr))
      | @asn_match_tuple _ σs Δ s p asn0 =>
          smut_angelic_match_tuple id p s
            (fun (w1 : World) (ω01 : w ⊒ w1) (ts : NamedEnv (Term w1) Δ) =>
             consume (MkWorld (subst (wco w) (sub_cat_left Δ))) asn0 w1
               (MkAcc (MkWorld (subst (wco w) (sub_cat_left Δ))) w1 (wsub ω01 ►► ts)))
      | @asn_match_record _ R Δ s p asn0 =>
          smut_angelic_match_record id p s
            (fun (w1 : World) (ω01 : w ⊒ w1) (ts : NamedEnv (Term w1) Δ) =>
             consume (MkWorld (subst (wco w) (sub_cat_left Δ))) asn0 w1
               (MkAcc (MkWorld (subst (wco w) (sub_cat_left Δ))) w1 (wsub ω01 ►► ts)))
      | asn_match_union U s alt__ctx alt__pat alt__rhs =>
          smut_angelic_match_union id alt__pat s
            (fun (K : 𝑼𝑲 U) (w1 : World) (ω01 : w ⊒ w1) (ts : NamedEnv (Term w1) (alt__ctx K)) =>
             consume (MkWorld (subst (wco w) (sub_cat_left (alt__ctx K)))) (alt__rhs K) w1
               (MkAcc (MkWorld (subst (wco w) (sub_cat_left (alt__ctx K)))) w1 (wsub ω01 ►► ts)))
      | asn_sep asn1 asn2 => smut_bind_right (consume w asn1) (consume w asn2)
      | asn_exist ς τ asn0 =>
        fun (w1 : World) (ω01 : w ⊒ w1) =>
          smut_angelic (Some ς) τ
            (fun (w2 : World) (ω12 : w1 ⊒ w2) (t2 : Term w2 τ) =>
             consume (wsnoc w (ς :: τ)) asn0 w2 (wsnoc_sub (wtrans ω01 ω12) (ς :: τ) t2))
      | asn_debug =>
        fun w1 ω01 =>
          smut_debug (MkSDebugAsn (wco w1)) (smut_pure tt)
      end.

  Definition smutk_consume {AT Γ1 Γ2} :
    ⊢ Assertion -> □(SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
  Proof.
    intros w0 asn k.
    apply (smut_bind (T (smut_consume asn))).
    intros w1 ω01 _.
    apply k. auto.
  Defined.

  Definition smutkb_consume {AT Γ1 Γ2} :
    ⊢ Assertion -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT).
  Proof.
    intros w0 asn k.
    apply (smut_bbind (smut_consume asn)).
    intros w1 ω01 _.
    apply k. auto.
  Defined.

  Section WithConfig.

    Variable cfg : Config.

    Definition smut_call {Γ Δ τ} (contract : SepContract Δ τ) :
      ⊢ SStore Δ -> SMut Γ Γ (STerm τ).
    Proof.
      refine
        (match contract with
         | MkSepContract _ _ Σe δe req result ens => _
         end).
      intros w0 ts δ0 h0.
      apply (angelic_freshen_ctx id Σe).
      intros w1 ω01 evars.
      apply (assert_formulask
               {|
                 msg_function := "smut_call";
                 msg_message := "argument pattern match";
                 msg_program_context := Γ;
                 msg_localstore := subst δ0 ω01;
                 msg_heap := subst h0 ω01;
                 msg_pathcondition := wco w1;
               |} (formula_eqs (subst δe evars) (subst ts ω01))); try exact wrefl.
      intros w2 ω12.
      eapply bind.
      refine (smut_consume (w := @MkWorld Σe nil) req _ (subst δ0 (wtrans ω01 ω12)) (subst h0 (wtrans ω01 ω12))).
      constructor. cbn.
      apply (subst (T := Sub _) evars ω12).
      intros w3 ω23 [_ δ3 h3].
      apply (demonic (Some result) τ).
      intros w4 ω34 res.
      eapply bind.
      refine (smut_produce
               (w := @MkWorld (Σe ▻ (result::τ)) nil)
               ens
               _
               (subst δ3 ω34) (subst h3 ω34)).
      constructor. cbn.
      apply (sub_snoc (subst (T := Sub _) evars (wtrans ω12 (wtrans ω23 ω34))) (result :: τ) res).
      intros w5 ω45 [_ δ5 h5].
      apply (pure {| smutres_value := subst (T := fun Σ => Term Σ _) res ω45; smutres_store := δ5; smutres_heap := h5 |}).
    Defined.

    Definition smutk_call {Γ1 Γ2 Δ τ AT} (contract : SepContract Δ τ) :
      ⊢ SStore Δ -> □(STerm τ -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
    Proof.
      refine
        (match contract with
         | MkSepContract _ _ Σe δe req result ens => _
         end).
      intros w0 ts k δ0 h0.
      apply (angelic_freshen_ctx id Σe).
      intros w1 ω01 evars.
      apply (assert_formulask
               {|
                 msg_function := "smut_call";
                 msg_message := "argument pattern match";
                 msg_program_context := Γ1;
                 msg_localstore := subst δ0 ω01;
                 msg_heap := subst h0 ω01;
                 msg_pathcondition := wco w1;
               |} (formula_eqs (subst δe evars) (subst ts ω01))); try exact wrefl.
      intros w2 ω12.
      apply (smutk_consume (Γ1 := Γ1) (Γ2 := Γ2) (subst req (subst (T := Sub _) evars ω12))).
      intros w3 ω23 δ3 h3.
      apply (demonic (Some result) τ).
      intros w4 ω34 res.
      apply (smutk_produce (Γ1 := Γ1) (Γ2 := Γ2)).
      apply (subst ens).
      apply sub_snoc.
      apply (subst (T := Sub _) evars (wtrans ω12 (wtrans ω23 ω34))).
      apply res.
      eapply K. 2: apply (persist__term res).
      apply (four k).
      apply (wtrans (wtrans ω01 ω12) (wtrans ω23 ω34)).
      apply (subst δ3 ω34).
      apply (subst h3 ω34).
      apply (subst δ0 (wtrans ω01 ω12)).
      apply (subst h0 (wtrans ω01 ω12)).
    Defined.

    Definition smutbbk_call {Γ1 Γ2 Δ τ AT} (contract : SepContract Δ τ) :
      ⊢ SStore Δ -> □(STerm τ -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
    Proof.
      refine
        (match contract with
         | MkSepContract _ _ Σe δe req result ens => _
         end).
      intros w0 ts k δ0 h0.
      apply (angelic_freshen_ctx id Σe).
      intros w1 ω01 evars.
      apply (assert_formulask
               {|
                 msg_function := "smut_call";
                 msg_message := "argument pattern match";
                 msg_program_context := Γ1;
                 msg_localstore := subst δ0 ω01;
                 msg_heap := subst h0 ω01;
                 msg_pathcondition := wco w1;
               |} (formula_eqs (subst δe evars) (subst ts ω01))); try exact wrefl.
      intros w2 ω12.
      apply (@smutbbk_consume AT Γ1 Γ2 (@MkWorld Σe nil) req).
      refine (wtrans _ ω12).
      constructor. apply evars.
      2: apply (subst δ0 (wtrans ω01 ω12)).
      2: apply (subst h0 (wtrans ω01 ω12)).
      intros w3 ω23 δ3 h3.
      apply (demonic (Some result) τ).
      intros w4 ω34 res.
      apply (smutk_produce (Γ1 := Γ1) (Γ2 := Γ2)).
      apply (subst ens).
      apply sub_snoc.
      apply (subst (T := Sub _) evars (wtrans ω12 (wtrans ω23 ω34))).
      apply res.
      eapply K. 2: apply (persist__term res).
      apply (four k).
      apply (wtrans (wtrans ω01 ω12) (wtrans ω23 ω34)).
      apply (subst δ3 ω34).
      apply (subst h3 ω34).
    Defined.


    Definition smutk_call_debug {Γ1 Γ2 Δ τ AT} (f : 𝑭 Δ τ) (contract : SepContract Δ τ) :
      ⊢ SStore Δ -> □(STerm τ -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT :=
      fun w0 δΔ k =>
        let o := smutk_call contract δΔ k in
        if config_debug_function cfg f
        then
          smut_debug
            (fun δ h => {| sdebug_call_function_parameters := Δ;
                           sdebug_call_function_result_type := τ;
                           sdebug_call_function_name := f;
                           sdebug_call_function_contract := contract;
                           sdebug_call_function_arguments := δΔ;
                           sdebug_call_program_context := Γ1;
                           sdebug_call_pathcondition := wco w0;
                           sdebug_call_localstore := δ;
                           sdebug_call_heap := h|})
            o
        else o.

    Definition smutk_exec {A} `{subA: Subst A} :
      forall {Γ1 Γ2 τ} (s : Stm Γ1 τ),
        (⊢ STerm τ -> SMut Γ1 Γ2 A) ->
        ⊢ SMut Γ1 Γ2 A.
    Proof.
      refine (fix smutk_exec {Γ1 Γ2 τ} s k {struct s} := _).
      destruct s.
      - intros w. apply k. apply (term_lit τ l).
      - intros w δ. apply (k w (seval_exp δ e) δ).
      - apply
          (smutk_exec Γ1 Γ2 σ s1
         (fun (w1 : World) (t1 : Term w1 σ) (δ1 : SStore Γ1 w1) (h1 : SHeap w1) =>
          smutk_exec (Γ1 ▻ (x :: σ)) Γ2 τ s2
            (fun (w2 : World) (t2 : Term w2 τ) (δ2 : SStore (Γ1 ▻ (x :: σ)) w2) => k w2 t2 (env_tail δ2)) w1
            (δ1 ► (x :: σ ↦ t1)) h1)).
    Abort.

    Definition smutk_exec {A} `{subA: Subst A} :
      forall {Γ1 Γ2 τ} (s : Stm Γ1 τ),
      ⊢ □(STerm τ -> SMut Γ1 Γ2 A) -> SMut Γ1 Γ2 A.
    Proof.
      refine (fix smutk_exec {Γ1 Γ2 τ} s {w0} k {struct s} := _).
      destruct s.
      - apply (T k). apply (term_lit τ l).
      - apply (smutk_eval_exp e).
        apply (T k).
      - apply (smutk_exec _ _ _ s1).
        intros w1 ω01 t1.
        eapply (smutk_push_local t1).
        apply (smutk_exec _ _ _ s2).
        intros w2 ω12 t2.
        apply smutk_pop_local.
        apply (four k ω01). auto. auto.
      - apply (smutk_pushs_local (lift δ)).
        apply (smutk_exec _ _ _ s).
        intros w1 ω01 t.
        apply smutk_pops_local.
        apply k. auto. auto.
      - apply (smutk_exec _ _ _ s).
        intros w1 ω01 t δ h.
        apply k. auto. auto.
        apply (δ ⟪ x ↦ t ⟫)%env.
        auto.
      - apply (smutk_eval_exps es).
        intros args.
        destruct (CEnv f) as [c|].
        apply (smutk_call_debug f c args k).
        apply (smut_error "smut_exec" "Function call without contract" (f,args)).
      - rename δ into δΔ. intros δ0 h0.
        apply (smutk_exec _ _ _ s).
        intros w1 ω01 t δΔ' h1.
        apply k. auto. auto. apply (subst δ0 ω01). auto.
        apply (lift δΔ). auto.
      - apply (smutk_eval_exps es).
        intros args.
        apply (smutk_call (CEnvEx f) args k).
      - apply (smutk_eval_exp e). intros t.
        apply (smut_demonic_match_bool t); auto using wrefl.
        + intros w1 ω01.
          apply (smutk_exec _ _ _ s1).
          apply (four k). auto.
        + intros w1 ω01.
          apply (smutk_exec _ _ _ s2).
          apply (four k). auto.
      - apply (smutk_exec _ _ _ s1).
        intros w1 ω01 t1.
        apply (smutk_exec _ _ _ s2).
        apply (four k). auto.
      - apply (smutk_eval_exp e1). intros t.
        apply (smutk_assume_formula (formula_bool t)).
        intros w1 ω01.
        apply (smutk_exec _ _ _ s).
        apply (four k). auto.
      - apply smut_block.
      - apply (smutk_eval_exp e). intros t.
        apply (smut_demonic_match_list (𝑿to𝑺 xh) (𝑿to𝑺 xt) t); auto using wrefl.
        + intros w1 ω01.
          apply (smutk_exec _ _ _ s1).
          apply (four k). auto.
        + intros w1 ω01 thead ttail.
          eapply (smutk_pushs_local (env_snoc (env_snoc env_nil (_,_) thead) (_,_) ttail)).
          apply (smutk_exec _ _ _ s2).
          intros w2 ω12 res.
          apply (smutk_pops_local (Δ := ctx_nil ▻ _ ▻ _)).
          apply (four k ω01); auto.
      - apply (smutk_eval_exp e). intros t.
        apply (smut_demonic_match_sum (𝑿to𝑺 xinl) (𝑿to𝑺 xinr) t); auto using wrefl.
        + intros w1 ω01 tl.
          eapply (smutk_push_local tl).
          apply (smutk_exec _ _ _ s1).
          intros w2 ω12 res.
          apply smutk_pop_local.
          apply (four k ω01); auto.
        + intros w1 ω01 tr.
          eapply (smutk_push_local tr).
          apply (smutk_exec _ _ _ s2).
          intros w2 ω12 res.
          apply smutk_pop_local.
          apply (four k ω01); auto.
      - apply (smutk_eval_exp e). intros t.
        apply (smutb_demonic_match_pair (𝑿to𝑺 xl) (𝑿to𝑺 xr) t); auto using wrefl.
        intros w1 ω01 t1 t2.
        eapply (smutk_pushs_local (env_snoc (env_snoc env_nil (_,_) t1) (_,_) t2)).
        apply (smutk_exec _ _ _ s).
        intros w2 ω12 res.
        apply (smutk_pops_local (Δ := ctx_nil ▻ _ ▻ _)).
        apply (four k ω01); auto.
      - apply (smutk_eval_exp e). intros t.
        apply (smut_demonic_match_enum t); auto using wrefl.
        intros K.
        intros w1 ω01.
        apply (smutk_exec _ _ _ (alts K)).
        apply (four k). auto.
      - apply (smutk_eval_exp e). intros t.
        apply (smut_demonic_match_tuple 𝑿to𝑺 p t); auto using wrefl.
        intros w1 ω01 ts.
        eapply (smutk_pushs_local ts).
        apply (smutk_exec _ _ _ s).
        intros w2 ω12 res.
        apply (smutk_pops_local).
        apply (four k ω01); auto.
      - apply (smutk_eval_exp e). intros t.
        apply (smut_demonic_match_union 𝑿to𝑺 alt__pat t); auto using wrefl.
        intros K w1 ω01 ts.
        eapply (smutk_pushs_local ts).
        apply (smutk_exec _ _ _ (alt__rhs K)).
        intros w2 ω12 res.
        apply (smutk_pops_local).
        apply (four k ω01); auto.
      - apply (smutk_eval_exp e). intros t.
        apply (smut_demonic_match_record 𝑿to𝑺 p t); auto using wrefl.
        intros w1 ω01 ts.
        eapply (smutk_pushs_local ts).
        apply (smutk_exec _ _ _ s).
        intros w2 ω12 res.
        apply (smutk_pops_local).
        apply (four k ω01); auto.
      - eapply (smut_angelic None τ).
        intros w1 ω01 t.
        apply (smutk_consume (asn_chunk (chunk_ptsreg reg t))).
        intros w2 ω12.
        apply (smutk_produce (asn_chunk (chunk_ptsreg reg (subst t ω12)))).
        eapply (K (four k (wtrans ω01 ω12))).
        intros w3 ω23.
        apply (subst (T := STerm _) t (wtrans ω12 ω23)).
      - eapply (smut_angelic None τ).
        intros w1 ω01 told.
        apply (smutk_consume (asn_chunk (chunk_ptsreg reg told))).
        intros w2 ω12.
        apply (smutk_eval_exp e). intros tnew.
        apply (smutk_produce (asn_chunk (chunk_ptsreg reg tnew))).
        eapply (K (four k (wtrans ω01 ω12))).
        intros w3 ω23.
        apply (subst (T := STerm _) tnew ω23).
      - apply (smut_error "smut_exec" "stm_bind not supported" tt).
      - apply smut_debug.
        intros δ0 h0.
        econstructor.
        apply (wco w0).
        apply δ0.
        apply h0.
        apply (smutk_exec _ _ _ s).
        apply k.
    Defined.

    Definition smut_contract {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) :
      let w := @MkWorld (sep_contract_logic_variables c) nil in
      SMut Δ Δ Unit w.
    Proof.
      refine
        (match c with
         | MkSepContract _ _ Σ δ req result ens => _
           (* smut_produce req ;; *)
           (* smut_exec s      >>= fun Σ1 ζ1 t => *)
           (* smut_sub (sub_snoc ζ1 (result,τ) t) (smut_consume ens) ;; *)
           (* (* smut_leakcheck *) *)
           (* smut_block *)
         end).
      intros w0.
      apply (smutk_produce (w:=w0) req).
      intros w1 ω01.
      apply (smutk_exec s).
      intros w2 ω12.
      intros res.
      apply (smutkb_consume (w:=wsnoc w0 (result :: τ)) ens).
      intros w3 ω23.
      apply smut_block.
      apply wsnoc_sub.
      apply (wtrans ω01 ω12).
      apply res.
    Defined.

    Definition smut_contract_outcome {Δ : PCtx} {τ : Ty} (c : SepContract Δ τ) (s : Stm Δ τ) :
      SPath Unit wnil.
      pose (sep_contract_localstore c) as δ.
      pose (smut_contract c s δ nil).
      refine (demonic_close (map _ s0)).
      intros ? ? ?. constructor.
    Defined.

    Definition ValidContractWithConfig {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      VerificationCondition (prune (prune (smut_contract_outcome c body))).

  End WithConfig.

  Definition ValidContract {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
    VerificationCondition (prune (prune (smut_contract_outcome default_config c body))).

  Definition ValidContractReflect {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
    is_true (ok (prune (smut_contract_outcome default_config c body))).

  Lemma dynmutevarreflect_sound {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
    ValidContractReflect c body ->
    ValidContract c body.
  Proof.
    (* intros H. *)
    (* apply (outcome_ok_spec _ (fun _ => True)) in H. *)
    (* now rewrite outcome_satisfy_bind in H. *)
  Admitted.

  Module EvarEnv.

    Definition smut_consume_chunk_evar {Γ Σe} (c : Chunk Σe) :
      ⊢ EvarEnv Σe -> SMut Γ Γ (EvarEnv Σe) :=
      fun w0 L0 δ0 h0 =>
        angelic_listk
          (A := Pair (EvarEnv Σe) SHeap)
          {| msg_function := "smut_consume_chunk_evar";
             msg_message := "Empty extraction";
             msg_program_context := Γ;
             msg_localstore := δ0;
             msg_heap := h0;
             msg_pathcondition := wco w0
          |}
          (fun '(L1, h1) => smut_pure L1 δ0 h1)
          (extract_chunk c h0 L0).

     (* This function tries to assert the equality between the terms `te` from *)
    (*     a callee context and `tr` from the caller context. The callee context *)
    (*     variables are all evars and if possible, it will fill in evars that are *)
    (*     strictly necessary for the assertion to be true. *)
    Definition smut_assert_term_eq_evar {Γ Σe σ} (te : STerm σ Σe) :
      ⊢ STerm σ -> EvarEnv Σe -> SMut Γ Γ (EvarEnv Σe) :=
      fun w0 tr L0 =>
        (* Try to fully match te against tr1, potentially filling in some evars. *)
        match match_term te tr L0 with
        | Some L1 => smut_pure L1
        | None =>
          (* The match failed. See if all evars in te are already known.*)
          match eval_term_evar L0 te with
          | Some te1 =>
            (* All evars are known. So assert the equality between the terms in *)
    (*            the caller context. *)
            smutk_assert_formula
              (formula_eq te1 tr)
              (fun w1 ω01 => smut_pure (subst L0 ω01))
          | None =>
            (* Give up. This is currently missing some corner cases where a *)
    (*            sub-term of te would already constrain all appearing evars, but *)
    (*            which can't be fully unified with tr. match_term could be *)
    (*            augmented to also handle this kind of case. *)
            smut_error
              "smut_assert_term_eq_evar"
              "Uninstantiated evars variable"
              {| evarerror_env := L0;
                 evarerror_data := (te,tr)
              |}
          end
        end.

    Equations(noeqns) smut_assert_namedenv_eq_evar {Γ X Σe σs}
             (te : NamedEnv (X:=X) (Term Σe) σs) {w0 : World}
             (tr : NamedEnv (Term w0) σs)
             (L0 : EvarEnv Σe w0) : SMut Γ Γ (EvarEnv Σe) w0 :=
      smut_assert_namedenv_eq_evar env_nil             env_nil L0 := smut_pure L0;
      smut_assert_namedenv_eq_evar (env_snoc E1 b1 t1) (env_snoc E2 b2 t2) L0 :=
        smut_bind (smut_assert_namedenv_eq_evar E1 E2 L0)
          (fun w1 ω01 L1 =>
             smut_assert_term_eq_evar t1 (subst (T := STerm _) t2 ω01) L1).

    Definition smut_consume_formula_evar {Γ Σe} (fml : Formula Σe) :
      ⊢ EvarEnv Σe -> SMut Γ Γ (EvarEnv Σe) :=
      fun w0 L =>
        match fml with
        | formula_bool t =>
          match eval_term_evar L t with
          | Some t0 => smutk_assert_formula
                         (formula_bool t0)
                         (fun w ω01 => smut_pure (subst L ω01))
          | None => smut_error
                      "smut_consume_formula_evar"
                      "Uninstantiated evars when consuming formula"
                      {| evarerror_env := L; evarerror_data := fml |}
          end
        | formula_prop ζ P =>
          match evarenv_to_option_sub L with
          | Some s => smutk_assert_formula
                        (formula_prop (subst ζ s) P)
                        (fun w1 ω01 => smut_pure (subst L ω01))
          | None => smut_error
                      "smut_consume_formula_evar"
                      "Uninstantiated evars when consuming formula"
                      {| evarerror_env := L; evarerror_data := fml |}
          end
        | formula_eq t1 t2 =>
          match eval_term_evar L t1 , eval_term_evar L t2 with
          | Some t1' , Some t2' => smutk_assert_formula
                                     (formula_eq t1' t2')
                                     (fun w1 ω01 => smut_pure (subst L ω01))
          | Some t1' , None     => smut_assert_term_eq_evar t2 t1' L
          | None     , Some t2' => smut_assert_term_eq_evar t1 t2' L
          | None     , None     => smut_error
                                     "smut_consume_formula_evar"
                                     "Uninstantiated evars when consuming formula"
                                     {| evarerror_env := L; evarerror_data := fml |}
          end
        | @formula_neq _ σ t1 t2 =>
          match eval_term_evar L t1 , eval_term_evar L t2 with
          | Some t1' , Some t2' => smutk_assert_formula
                                     (formula_neq t1' t2')
                                     (fun w1 ω01 => smut_pure (subst L ω01))
          (* | Some t1' , None     => smut_assert_term_eq_evar t2 t1' L *)
          (* | None     , Some t2' => smut_assert_term_eq_evar t1 t2' L *)
          | _        , _        => smut_error
                                     "smut_consume_formula_evar"
                                     "Uninstantiated evars when consuming formula"
                                     {| evarerror_env := L; evarerror_data := fml |}
          end
        end.

  End EvarEnv.

  Module EvarExplanation.

    (* We currently avoid introducing existential variables into the
       underlying symbolic path monad, because this would make the system more
       complicated. Instead we avoid using existential quantification of the
       path monad altogether and deal with it in the mutator instead.

       This is achieved by temporarily creating an [EvarEnv] when needed, i.e.
       when *consuming* the post-condition at the end of a function, or the
       pre-condition of a called function. An [EvarEnv] can be understood as a
       system of equations between existential variables and term in which
       those existentials are fresh (c.f. solved forms for Hindley-Milner
       constraint-based type checking).

       Effectively, we have something like this

           [∀ᾱ∃β̄, (βᵢ = tᵢ) ∧ ..]

       All existential variables β̄ (angelic choice) come after the universal
       variables ᾱ (demonic choice). We also avoid introducing new universals
       during consume to keep this order. In this setting the [EvarEnv] can be
       interpreted as a set of equations between a subset of existential
       variables [βᵢ] and terms [tᵢ] such that [freevars (tᵢ) ⊆ ᾱ`].

       Equations are discovered by semi-unification and added to the EvarEnv.
       See [smut_consume_formula_evar] and [smut_consume_chunk_evar] for
       details.
     *)

    Lemma exists_distr A P Q :
      (exists a : A, P a \/ Q a) <->
      (exists a : A, P a) \/ (exists a, Q a).
    Proof. firstorder. Qed.

    Lemma exists_distr_conj A P Q :
      (exists a : A, P /\ Q a) <->
      P /\ (exists a : A, Q a).
    Proof. firstorder. Qed.

    Lemma if_demonic (b : bool) (P Q : Prop) :
      (if b then P else Q) <->
      (b = true -> P) /\ (b = false -> Q).
    Proof. destruct b; intuition. Qed.

    Lemma if_angelic (b : bool) (P Q : Prop) :
      (if b then P else Q) <->
      (b = true /\ P) \/ (b = false /\ Q).
    Proof. destruct b; intuition. Qed.

  End EvarExplanation.

  Module ModalWP.

    Import LogicalRelation.

    Definition wp {A} :
      (* ⊢ □(A -> SymInstance -> PROP) -> SPath A -> SymInstance -> PROP := *)
      forall w, (Box (A -> SymInstance -> PROP) w) -> SPath A w -> SymInstance w -> Prop :=
      fix WP {w} POST o ι :=
        match o with
        | pure a                            => T POST a ι
        | angelic_binary o1 o2              => (WP POST o1 ι) \/ (WP POST o2 ι)
        | demonic_binary o1 o2              => (WP POST o1 ι) /\ (WP POST o2 ι)
        | error msg                         => Error msg
        | block                             => True
        | assertk fml msg o                 => inst fml ι /\ WP (four POST (wformula_sup)) o ι
        | assumek fml o                     => inst (A := Prop) fml ι -> WP (four POST (wformula_sup)) o ι
        | angelicv b k                      => exists (v : Lit (snd b)),
                                               WP (four POST wsnoc_sup) k (env_snoc ι b v)
        | demonicv b k                      => forall (v : Lit (snd b)),
                                               WP (four POST wsnoc_sup) k (env_snoc ι b v)
        | @assert_vareq _ _ x σ xIn t msg k => let ι'  := env_remove' _ ι xIn in
                                               env_lookup ι xIn = inst t ι' /\ WP (four POST wsubst_sup) k ι'
        | @assume_vareq _ _ x σ xIn t k     => let ι'  := env_remove' _ ι xIn in
                                               env_lookup ι xIn = inst t ι' -> WP (four POST wsubst_sup) k ι'
        | debug d k                         => Debug (inst d ι) (WP POST k ι)
        end%type.

    Definition wpbox {A} :
      ⊢ □(A -> SymInstance -> PROP) -> □(SPath A -> SymInstance -> PROP).
    Proof.
      intros w0 POST.
      refine (K _ (four POST)).
      intros w1 ω01.
      unfold Box, Impl in *.
      apply (@wp A).
    Defined.

    Definition IPROP : TYPE :=
      SymInstance -> PROP.

    Definition Dijkstra (A : TYPE) : TYPE :=
      □(A -> IPROP) -> IPROP.

    Definition wp' {A} :
      ⊢ SPath A -> Dijkstra A :=
      fun w o POST => wp POST o.

    Global Instance LRSPath {A} `{LR A} : LR (SPath A) :=
      fun w0 w1 ω01 o0 o1 =>
        forall
          (POST : Box (A -> SymInstance -> PROP) w0)
          (POST_dcl : dcl POST)
          (ι1 : SymInstance w1),
          wp POST o0 (inst (T := Sub _) ω01 ι1) ->
          wp (four POST ω01) o1 ι1.

    Hint Unfold four : core.

    Lemma wp_monotonic' {A w0} (p : SPath A w0)
      (P Q : Box (A -> SymInstance -> PROP) w0)
      (PQ : forall w1 (ω01 : w0 ⊒ w1) a ι,
          P w1 ω01 a ι ->
          Q w1 ω01 a ι) :
      forall ι0 : SymInstance w0,
        wp P p ι0 ->
        wp Q p ι0.
    Proof.
      induction p; cbn.
      - apply PQ; auto.
      - intros ι0 [Hwp|Hwp]; [left|right]; revert Hwp.
        + now apply IHp1.
        + now apply IHp2.
      - intros ι0 [Hwp1 Hwp2]; split;
          [ revert Hwp1; now apply IHp1
          | revert Hwp2; now apply IHp2].
      - auto.
      - auto.
      - intros ι0 [Hfml Hwp]. split; auto.
        revert Hwp. apply IHp. auto.
      - intros ι0 Hwp Hfml; specialize (Hwp Hfml). revert Hwp.
        apply IHp. auto.
      - intros ι0 [v Hwp]; exists v; revert Hwp.
        apply IHp. intros ? ?. apply PQ.
      - intros ι0 Hwp v; specialize (Hwp v); revert Hwp.
        apply IHp. intros ? ?. apply PQ.
      - intros ι0 [Hfml Hwp]. split; auto.
        revert Hwp. apply IHp. intros ? ?. apply PQ.
      - intros ι0 Hwp Hfml; specialize (Hwp Hfml). revert Hwp.
        apply IHp. intros ? ?. apply PQ.
      - intros ι0 [Hwp]. constructor. revert Hwp.
        apply IHp, PQ.
    Qed.

    Global Instance proper_wp {A : TYPE} {w0 : World} :
      Proper
        (forall_relation
           (fun w1 => eq ==> eq ==> eq ==> iff) ==>
           eq ==> eq ==> iff)
        (@wp A w0).
    Proof.
      unfold Proper, respectful, forall_relation.
      intros P Q PQ o1 o2 <- ι1 ι2 <-.
      split; apply wp_monotonic';
        intros *; now apply PQ.
    Qed.

    Lemma wp_monotonic {A} {lrA : LR A} {persA : Persistent A}
      {lrReflA : LRRefl A}
      {w0} (p : SPath A w0) :
      forall w1 (ω01 : w0 ⊒ w1) (Hω01 : went ω01)
        (P : Box (A -> SymInstance -> PROP) w0) (P_dcl : dcl P)
        (Q : Box (A -> SymInstance -> PROP) w1)
          (PQ : lr ω01 P Q)
          (ι0 : SymInstance w0)
          (ι1 : SymInstance w1)
          (Hι : lr ω01 ι0 ι1),
          wp P p ι0 ->
          wp Q (persistent_spath p ω01) ι1.
    Proof.
      induction p; cbn - [subst]; intros w1 ω01 Hω01 P P_dcl Q PQ ι0 ι1 Hι.
      - unfold T.
        intros HP. eapply PQ.
        apply went_wrefl.
        apply lr_refl.
        reflexivity.
        specialize (P_dcl w wrefl went_wrefl).
        specialize (P_dcl w1 ω01 Hω01).
        specialize (P_dcl a (persist a ω01)).
        (* inster P_dcl by apply persist_lr. *)
        inster P_dcl by admit.
        specialize (P_dcl ι0 ι1 Hι).
        apply P_dcl in HP. revert HP.
        unfold four, wtrans, wrefl.
        cbn - [subst].
        rewrite inst_sub_id.
        rewrite sub_comp_id_left.
        now destruct ω01.
      - intros [Hwp|Hwp]; [left|right]; revert Hwp.
        + now apply IHp1.
        + now apply IHp2.
      - intros [Hwp1 Hwp2]; split;
          [ revert Hwp1; now apply IHp1
          | revert Hwp2; now apply IHp2].
      - intros [].
      - auto.
      - rewrite Hι, inst_subst.
        intros [Hfml Hwp]. split; auto.
        revert Hwp. apply IHp.
        + now apply went_wacc_formula.
        + apply dcl_four; auto.
          apply went_wformula_sup.
        + admit.
        + admit.
      - rewrite Hι, inst_subst.
        intros Hwp Hfml; specialize (Hwp Hfml).
        revert Hwp. apply IHp.
        + now apply went_wacc_formula.
        + apply dcl_four; auto.
          apply went_wformula_sup.
        + admit.
        + admit.
      - intros [v Hwp]; exists v; revert Hwp.
        apply IHp.
        + now apply went_wacc_snoc.
        + apply dcl_four; auto.
          admit.
          (* apply went_snoc_sup. *)
        + admit.
        + admit.
      - intros Hwp v; specialize (Hwp v); revert Hwp.
        apply IHp.
        + admit.
        + admit.
        + admit.
        + admit.
      - rewrite <- inst_sub_shift.
        rewrite Hι, ?inst_subst in *.
        rewrite <- inst_lookup.
        intros [Hfml Hwp]. split; auto.
        revert Hwp. apply IHp.
        + admit.
        + admit.
        + admit.
        + admit.
      - rewrite <- inst_sub_shift.
        rewrite Hι, ?inst_subst in *.
        rewrite <- inst_lookup.
        intros Hwp Hfml; specialize (Hwp Hfml). revert Hwp.
        apply IHp.
        + admit.
        + admit.
        + admit.
        + admit.
      - intros [Hwp]. constructor. revert Hwp.
        apply IHp; auto.
    Admitted.

    Global Instance LRReflSPath {A} `{LR A} : LRRefl (SPath A).
    Proof.
      constructor.
      unfold lr, LRSPath.
      intros * POST_dcl ι0.
      unfold four, wrefl, wtrans. cbn [wsub].
      rewrite inst_sub_id.
      apply wp_monotonic'.
      intros w1 [ζ01] a1 ι1.
      now rewrite sub_comp_id_left.
    Qed.

    Lemma wp_map {A B} {w0} (ma : SPath A w0)
      (f : Box (A -> B) w0)
      (POST : Box (B -> SymInstance -> PROP) w0) (ι : SymInstance w0) :
      wp POST (map f ma) ι <->
      wp (bcomp POST f) ma ι.
    Proof.
      induction ma; cbn.
      - auto.
      - rewrite IHma1, IHma2; auto.
      - rewrite IHma1, IHma2; auto.
      - auto.
      - auto.
      - rewrite IHma; auto.
      - rewrite IHma; auto.
      - setoid_rewrite IHma; auto.
      - setoid_rewrite IHma; auto.
      - rewrite IHma; auto.
      - rewrite IHma; auto.
      - split; intros []; constructor; apply IHma; auto.
    Qed.

    Lemma wp_bind {A B} {w0} (ma : SPath A w0)
      (f : Box (A -> SPath B) w0)
      (POST : Box (B -> SymInstance -> PROP) w0)
      (ι0 : SymInstance w0) (Hpc0 : instpc (wco w0) ι0) :
      wp POST (bind ma f) ι0 <->
      wp (bcomp (wpbox POST) f) ma ι0.
    Proof with unfold wpbox, four, bcomp, K, comp, Basics.compose, valid_box;
          apply wp_monotonic'; intros w1 ω01 a1 ι1;
          apply wp_monotonic'; intros w2 ω02 b2 ι2;
          now rewrite <- subst_sub_comp.
      induction ma; cbn.
      - unfold T, bcomp, wpbox, K, valid_box, comp, Basics.compose.
        split; apply wp_monotonic'; eauto.
        + intros w1 [ζ01] a1 ι1. unfold four, wrefl, wtrans.
          cbn [wsub]. now rewrite sub_comp_id_left.
        + intros w1 [ζ01] a1 ι1. unfold four, wrefl, wtrans.
          cbn [wsub]. now rewrite sub_comp_id_left.
      - rewrite IHma1, IHma2; auto.
      - rewrite IHma1, IHma2; auto.
      - auto.
      - auto.
      - split; intros [Hfml Hwp]; split; auto; revert Hwp;
          rewrite IHma; unfold wformula; cbn [wctx wco];
            rewrite ?inst_pathcondition_cons; auto.
        + apply wp_monotonic'. intros *.
          apply wp_monotonic'. intros *.
          unfold four, wtrans; cbn [wsub].
          now rewrite sub_comp_assoc.
        + apply wp_monotonic'. intros *.
          apply wp_monotonic'. intros *.
          unfold four, wtrans; cbn [wsub].
          now rewrite sub_comp_assoc.
      - split; intros Hwp Hfml; specialize (Hwp Hfml); revert Hwp;
          rewrite IHma; unfold wformula; cbn [wctx wco];
            rewrite ?inst_pathcondition_cons; auto.
        + apply wp_monotonic'. intros *.
          apply wp_monotonic'. intros *.
          unfold four, wtrans; cbn [wsub].
          now rewrite sub_comp_assoc.
        + apply wp_monotonic'. intros *.
          apply wp_monotonic'. intros *.
          unfold four, wtrans; cbn [wsub].
          now rewrite sub_comp_assoc.
      - split; intros [v Hwp]; exists v; revert Hwp;
          rewrite IHma; unfold wsnoc; cbn [wctx wco];
            rewrite ?inst_subst, ?inst_sub_wk1; auto.
        + apply wp_monotonic'. intros *.
          apply wp_monotonic'. intros *.
          unfold four, wtrans; cbn [wctx wsub].
          now rewrite sub_comp_assoc.
        + apply wp_monotonic'. intros *.
          apply wp_monotonic'. intros *.
          unfold four, wtrans; cbn [wctx wsub].
          now rewrite sub_comp_assoc.
      - split; intros Hwp v; specialize (Hwp v); revert Hwp;
          rewrite IHma; unfold wsnoc; cbn [wctx wco];
            rewrite ?inst_subst, ?inst_sub_wk1; auto.
        + apply wp_monotonic'. intros *.
          apply wp_monotonic'. intros *.
          unfold four, wtrans; cbn [wctx wsub].
          now rewrite sub_comp_assoc.
        + apply wp_monotonic'. intros *.
          apply wp_monotonic'. intros *.
          unfold four, wtrans; cbn [wctx wsub].
          now rewrite sub_comp_assoc.
      - split; intros [Hfml Hwp]; split; auto; revert Hwp;
          rewrite IHma; unfold wsubst; cbn [wctx wco];
            rewrite ?inst_subst, ?inst_sub_single; auto.
        + apply wp_monotonic'. intros *.
          apply wp_monotonic'. intros *.
          unfold four, wtrans; cbn [wctx wsub].
          now rewrite sub_comp_assoc.
        + apply wp_monotonic'. intros *.
          apply wp_monotonic'. intros *.
          unfold four, wtrans; cbn [wctx wsub].
          now rewrite sub_comp_assoc.
      - split; intros Hwp Hfml; specialize (Hwp Hfml); revert Hwp;
          rewrite IHma; unfold wsubst; cbn [wctx wco];
            rewrite ?inst_subst, ?inst_sub_single; auto.
        + apply wp_monotonic'. intros *.
          apply wp_monotonic'. intros *.
          unfold four, wtrans; cbn [wctx wsub].
          now rewrite sub_comp_assoc.
        + apply wp_monotonic'. intros *.
          apply wp_monotonic'. intros *.
          unfold four, wtrans; cbn [wctx wsub].
          now rewrite sub_comp_assoc.
      - split; intros []; constructor; apply IHma; auto.
    Qed.

    Lemma wp_angelic {A} `{LR A} {w0} {x : option 𝑺} {σ : Ty}
          (k : Box (STerm σ -> SPath A) w0) (k_dcl : dcl k)
          (POST : Box (A -> SymInstance -> PROP) w0)
          (ι0 : SymInstance w0) :
      wp POST (angelic x σ k) ι0 <->
      exists v : Lit σ, wp POST (T k (lift v)) ι0.
    Proof.
      cbn. split; intros [v Hwp]; exists v; revert Hwp.
      - cbv [lr LRBox dcl LRImpl LRSPath LRInstance LRTerm LRPROP] in k_dcl.
        specialize (k_dcl (wsnoc w0 (fresh w0 x :: σ)) wsnoc_sup went_wsnoc_sup).
        specialize (k_dcl w0).
        pose proof (@wsubst_sup (wsnoc w0 (fresh w0 x :: σ)) (fresh w0 x) σ inctx_zero (lift v)).
        destruct w0 as [Σ0 pc0].
        unfold wsnoc in *. cbn - [subst sub_single sub_wk1] in *.
        unfold wsnoc, wsubst in H0. cbn - [sub_single sub_wk1] in H0.
        rewrite <- subst_sub_comp in H0.
        admit.
      - admit.
    Admitted.

  End ModalWP.

End Mutators.
