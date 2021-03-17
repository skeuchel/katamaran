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
     Classes.Equivalence
     Classes.Morphisms
     Classes.RelationClasses
     Program.Tactics
     List
     Relations
     String.

From Equations Require Import
     Equations.

(* From MicroSail Require Import. *)
(*      Sep.Logic. *)

From stdpp Require
     finite.

Set Implicit Arguments.

Delimit Scope outcome_scope with out.

Inductive Outcome (E A : Type) : Type :=
| outcome_pure (a: A)
| outcome_angelic {I : Type} (R : Prop) (os: I -> Outcome E A)
| outcome_demonic {I : Type} (os: I -> Outcome E A)
| outcome_angelic_binary (o1 o2 : Outcome E A)
| outcome_demonic_binary (o1 o2 : Outcome E A)
| outcome_fail (msg : E)
| outcome_block
| outcome_assertk (P : Prop) (k : Outcome E A)
| outcome_assumek (P : Prop) (k : Outcome E A)
| outcome_debug {B : Type} (b : B) (k : Outcome E A)
.

Arguments outcome_pure {_ _} _.
Arguments outcome_fail {_ _} _.
Arguments outcome_block {_ _}.

Section TransparentObligations.
  Local Set Transparent Obligations.
  Derive NoConfusion for Outcome.
End TransparentObligations.

Bind Scope outcome_scope with Outcome.

Definition outcome_angelick_list {E A B} (msg : E) (xs : list A) (k : A -> Outcome E B) : Outcome E B :=
  (fix outcome_angelic_list (xs : list A) :=
    match xs with
    | nil        => outcome_fail msg
    | cons x xs  => outcome_angelic_binary (k x) (outcome_angelic_list xs)
    end) xs.

Definition outcome_demonick_list {E A B} (xs : list A) (k : A -> Outcome E B) : Outcome E B :=
  (fix outcome_demonic_list (xs : list A) :=
    match xs with
    | nil        => outcome_block
    | cons x xs  => outcome_demonic_binary (k x) (outcome_demonic_list xs)
    end) xs.

Definition outcome_angelic_finite {E A} `{finite.Finite A} (msg : E) : Outcome E A :=
  outcome_angelick_list msg (finite.enum A) (@outcome_pure E A).

Definition outcome_demonic_finite {E A} `{finite.Finite A} : Outcome E A :=
  outcome_demonick_list (finite.enum A) (@outcome_pure E A).

Fixpoint outcome_map {E A B : Type} (f : A -> B) (o : Outcome E A) : Outcome E B :=
  match o with
  | outcome_pure a               => outcome_pure (f a)
  | outcome_angelic R os         => outcome_angelic R (fun i => outcome_map f (os i))
  | outcome_demonic os           => outcome_demonic (fun i => outcome_map f (os i))
  | outcome_angelic_binary o1 o2 => outcome_angelic_binary (outcome_map f o1) (outcome_map f o2)
  | outcome_demonic_binary o1 o2 => outcome_demonic_binary (outcome_map f o1) (outcome_map f o2)
  | outcome_fail e               => outcome_fail e
  | outcome_block                => outcome_block
  | outcome_assertk P k          => outcome_assertk P (outcome_map f k)
  | outcome_assumek P k          => outcome_assumek P (outcome_map f k)
  | outcome_debug b k            => outcome_debug b (outcome_map f k)
  end.

Fixpoint outcome_bimap {E F A B : Type} (f : E -> F) (g : A -> B) (o : Outcome E A) : Outcome F B :=
  match o with
  | outcome_pure a               => outcome_pure (g a)
  | outcome_angelic R os         => outcome_angelic R (fun i => outcome_bimap f g (os i))
  | outcome_demonic os           => outcome_demonic (fun i => outcome_bimap f g (os i))
  | outcome_angelic_binary o1 o2 => outcome_angelic_binary (outcome_bimap f g o1) (outcome_bimap f g o2)
  | outcome_demonic_binary o1 o2 => outcome_demonic_binary (outcome_bimap f g o1) (outcome_bimap f g o2)
  | outcome_fail e               => outcome_fail (f e)
  | outcome_block                => outcome_block
  | outcome_assertk P k          => outcome_assertk P (outcome_bimap f g k)
  | outcome_assumek P k          => outcome_assumek P (outcome_bimap f g k)
  | outcome_debug b k            => outcome_debug b (outcome_bimap f g k)
  end.

Fixpoint outcome_bind {E A B : Type} (o : Outcome E A) (f : A -> Outcome E B) : Outcome E B :=
  match o with
  | outcome_pure a               => f a
  | outcome_angelic R os         => outcome_angelic R (fun i => outcome_bind (os i) f)
  | outcome_demonic os           => outcome_demonic (fun i => outcome_bind (os i) f)
  | outcome_angelic_binary o1 o2 => outcome_angelic_binary (outcome_bind o1 f) (outcome_bind o2 f)
  | outcome_demonic_binary o1 o2 => outcome_demonic_binary (outcome_bind o1 f) (outcome_bind o2 f)
  | outcome_fail e               => outcome_fail e
  | outcome_block                => outcome_block
  | outcome_assertk P k          => outcome_assertk P (outcome_bind k f)
  | outcome_assumek P k          => outcome_assumek P (outcome_bind k f)
  | outcome_debug b k            => outcome_debug b (outcome_bind k f)
  end.

Definition Error {E} (msg : E) : Prop := False.
Arguments Error {E} msg : simpl never.

Inductive Debug {B} (b : B) (P : Prop) : Prop :=
| debug (p : P).

Fixpoint outcome_satisfy {E A : Type} (o : Outcome E A) (F : E -> Prop) (P : A -> Prop) : Prop :=
  match o with
  | outcome_pure a               => P a
  | outcome_angelic R os         => R -> exists i, outcome_satisfy (os i) F P
  | outcome_demonic os           => forall i, outcome_satisfy (os i) F P
  | outcome_angelic_binary o1 o2 => outcome_satisfy o1 F P \/ outcome_satisfy o2 F P
  | outcome_demonic_binary o1 o2 => outcome_satisfy o1 F P /\ outcome_satisfy o2 F P
  | outcome_fail e               => F e
  | outcome_block                => True
  | outcome_assertk Q k          => Q /\ outcome_satisfy k F P
  | outcome_assumek Q k          => Q -> outcome_satisfy k F P
  | outcome_debug b k            => Debug b (outcome_satisfy k F P)
  end.

Definition outcome_safe {E A : Type} (o : Outcome E A) : Prop :=
  outcome_satisfy o (fun _ => False) (fun a => True).

Definition outcome_angelic_binary_prune {E A} (o1 o2 : Outcome E A) : Outcome E A :=
  match o1 , o2 with
  | outcome_block  , _              => outcome_block
  | _              , outcome_block  => outcome_block
  | outcome_fail _ , _              => o2
  | _              , outcome_fail _ => o1
  | _              , _              => outcome_angelic_binary o1 o2
  end.

Definition outcome_demonic_binary_prune {E A} (o1 o2 : Outcome E A) : Outcome E A :=
  match o1 , o2 with
  | outcome_block  , _              => o2
  | _              , outcome_block  => o1
  | outcome_fail s , _              => outcome_fail s
  | _              , outcome_fail s => outcome_fail s
  | _              , _              => outcome_demonic_binary o1 o2
  end.

Definition outcome_assertk_prune {E A} (P : Prop) (o : Outcome E A) : Outcome E A :=
  match o with
  | outcome_fail s => outcome_fail s
  | _              => outcome_assertk P o
  end.

Definition outcome_assumek_prune {E A} (P : Prop) (o : Outcome E A) : Outcome E A :=
  match o with
  | outcome_block => outcome_block
  | _             => outcome_assumek P o
  end.

Fixpoint outcome_prune {E A : Type} (o : Outcome E A) : Outcome E A :=
   match o with
   | outcome_angelic R os =>
     outcome_angelic R (fun i => outcome_prune (os i))
   | outcome_demonic os =>
     outcome_demonic (fun i => outcome_prune (os i))
   | outcome_angelic_binary o1 o2 =>
     outcome_angelic_binary_prune (outcome_prune o1) (outcome_prune o2)
   | outcome_demonic_binary o1 o2 =>
     outcome_demonic_binary_prune (outcome_prune o1) (outcome_prune o2)
   | outcome_assertk P o =>
     outcome_assertk_prune P (outcome_prune o)
   | outcome_assumek P o =>
     outcome_assumek_prune P (outcome_prune o)
   | _ => o
   end.

Fixpoint outcome_ok {E A : Type} (o : Outcome E A) : bool :=
  match o with
  | outcome_block        => true
  | outcome_angelic_binary o1 o2 => outcome_ok o1 || outcome_ok o2
  | outcome_demonic_binary o1 o2 => outcome_ok o1 && outcome_ok o2
  | outcome_assumek P o => outcome_ok o
  | outcome_debug b k => outcome_ok k
  | _ => false
  end.

Lemma outcome_satisfy_map {E A B : Type} (o : Outcome E A) (f : A -> B) F (P : B -> Prop) :
  outcome_satisfy (outcome_map f o) F P <-> outcome_satisfy o F (fun a => P (f a)).
Proof. induction o; firstorder. Qed.

Lemma outcome_satisfy_bind {E A B : Type} (o : Outcome E A) (f : A -> Outcome E B) F (P : B -> Prop) :
  outcome_satisfy (outcome_bind o f) F P <-> outcome_satisfy o F (fun a => outcome_satisfy (f a) F P).
Proof. induction o; firstorder. Qed.

Lemma outcome_satisfy_monotonic {E A F} {P Q : A -> Prop} (o : Outcome E A) (hyp : forall a, P a -> Q a) :
  outcome_satisfy o F P -> outcome_satisfy o F Q.
Proof. induction o; firstorder. Qed.

Lemma outcome_satisfy_angelick_list {E A B} (msg : E) (xs : list A) (k : A -> Outcome E B) (F : E -> Prop) (P : B -> Prop) :
  outcome_satisfy (outcome_angelick_list msg xs k) F P <->
  (exists x, In x xs /\ outcome_satisfy (k x) F P) \/ F msg.
Proof.
  unfold outcome_angelick_list.
  induction xs; cbn.
  - firstorder.
  - rewrite IHxs. firstorder; subst; auto.
Qed.

Lemma outcome_satisfy_angelic_finite {E A} `{finite.Finite A} (msg : E) (F : E -> Prop) (P : A -> Prop) :
  outcome_satisfy (outcome_angelic_finite (A := A) msg) F P <->
  (exists a : A, P a) \/ F msg.
Proof.
  unfold outcome_angelic_finite. rewrite outcome_satisfy_angelick_list. cbn.
  split; (intros [[a ?]|]; [ left; exists a; intuition | right; assumption ]).
  apply base.elem_of_list_In.
  apply finite.elem_of_enum.
Qed.

(* Lemma outcome_satisfy_angelic_binary_prune {E A} (o1 o2 : Outcome E A) (F : E -> Prop) (P : A -> Prop) : *)
(*   outcome_satisfy (outcome_angelic_binary_prune o1 o2) F P <-> *)
(*   outcome_satisfy (outcome_angelic_binary o1 o2) F P. *)
(* Proof. *)
(*   destruct o1, o2; cbn; intuition. *)
(* Qed. *)

(* Lemma outcome_satisfy_demonic_binary_prune {E A} (o1 o2 : Outcome A) (F : E -> Prop) (P : A -> Prop) : *)
(*   outcome_satisfy (outcome_demonic_binary_prune o1 o2) P <-> *)
(*   outcome_satisfy (outcome_demonic_binary o1 o2) P. *)
(* Proof. *)
(*   destruct o1, o2; cbn; unfold Error; intuition. *)
(* Qed. *)

(* Lemma outcome_satisfy_assertk_prune {A} (Q : Prop) (o : Outcome A) (P : A -> Prop) : *)
(*   outcome_satisfy (outcome_assertk_prune Q o) P <-> *)
(*   outcome_satisfy (outcome_assertk Q o) P. *)
(* Proof. *)
(*   destruct o; cbn; unfold Error; intuition. *)
(* Qed. *)

(* Lemma outcome_satisfy_assumek_prune {A} (Q : Prop) (o : Outcome A) (P : A -> Prop) : *)
(*   outcome_satisfy (outcome_assumek_prune Q o) P <-> *)
(*   outcome_satisfy (outcome_assumek Q o) P. *)
(* Proof. *)
(*   destruct o; cbn; unfold Error; intuition. *)
(* Qed. *)

(* Lemma outcome_satisfy_prune {A : Type} (o : Outcome A) (P : A -> Prop) : *)
(*   outcome_satisfy (outcome_prune o) P <-> outcome_satisfy o P. *)
(* Proof. *)
(*   induction o; cbn. *)
(*   - auto. *)
(*   - firstorder. *)
(*   - firstorder. *)
(*   - rewrite outcome_satisfy_angelic_binary_prune; cbn. *)
(*     now rewrite IHo1, IHo2. *)
(*   - rewrite outcome_satisfy_demonic_binary_prune; cbn. *)
(*     now rewrite IHo1, IHo2. *)
(*   - auto. *)
(*   - auto. *)
(*   - rewrite outcome_satisfy_assertk_prune; cbn. *)
(*     now rewrite IHo. *)
(*   - rewrite outcome_satisfy_assumek_prune; cbn. *)
(*     now rewrite IHo. *)
(* Qed. *)

Lemma outcome_ok_spec {E A} (o : Outcome E A) (F : E -> Prop) (P : A -> Prop) :
  is_true (outcome_ok o) -> outcome_satisfy o F P.
Proof.
  induction o; cbn; intuition.
  - destruct (outcome_ok o1); intuition.
  - destruct (outcome_ok o1); intuition.
  - destruct (outcome_ok o1); intuition.
  - constructor; intuition.
Qed.

Instance outcome_satisfy_iff_morphism {E A} (o : Outcome E A) (F : E -> Prop) :
  Proper (pointwise_relation A iff ==> iff) (@outcome_satisfy E A o F).
Proof. split; apply outcome_satisfy_monotonic; firstorder. Qed.

(* Definition outcome_cover {A} : relation (Outcome A) := *)
(*   fun o1 o2 => forall P, outcome_satisfy o1 P -> outcome_satisfy o2 P. *)

(* Instance outcome_cover_preorder {A} : PreOrder (@outcome_cover A). *)
(* Proof. split; firstorder. Qed. *)

(* Inductive outcome_satisfy_ind {A : Type} (P : A -> Prop) : Outcome A -> Prop := *)
(* | outcome_satisfy_pure  a    : *)
(*     P a -> *)
(*     outcome_satisfy_ind P (outcome_pure a) *)
(* | outcome_satisfy_demonic {I os} : *)
(*     (forall i, outcome_satisfy_ind P (os i)) -> *)
(*     outcome_satisfy_ind P (@outcome_demonic _ I os) *)
(* | outcome_satisfy_angelic {I i os} : *)
(*     outcome_satisfy_ind P (os i) -> *)
(*     outcome_satisfy_ind P (@outcome_angelic _ I os). *)

(* Inductive outcome_in {A : Type} (a : A) : Outcome A -> Prop := *)
(* | outcome_in_pure : *)
(*     outcome_in a (outcome_pure a) *)
(* | outcome_in_demonic {I os i} : *)
(*     outcome_in a (os i) -> *)
(*     outcome_in a (@outcome_demonic _ I os) *)
(* | outcome_in_angelic {I os i} : *)
(*     outcome_in a (os i) -> *)
(*     outcome_in a (@outcome_angelic _ I os). *)

Module OutcomeNotations.

  Notation "'⨂' x .. y => F" :=
    (outcome_demonic (fun x => .. (outcome_demonic (fun y => F)) .. ))
    (at level 200, x binder, y binder, right associativity) : outcome_scope.
  Notation "'⨁[' R ']' x .. y => F" :=
    (outcome_angelic R (fun x => .. (outcome_angelic R (fun y => F)) .. ))
    (at level 200, x binder, y binder, right associativity) : outcome_scope.

  Infix "⊗" := outcome_demonic_binary (at level 40, left associativity) : outcome_scope.
  Infix "⊕" := outcome_angelic_binary (at level 50, left associativity) : outcome_scope.

  Notation "ma >>= f" := (outcome_bind ma f) (at level 50, left associativity) : outcome_scope.

End OutcomeNotations.

(* Section Unused. *)

(*   Context `{SLL: ISepLogicLaws L}. *)

(*   Local Open Scope logic. *)

(*   Fixpoint outcome_satisfy_natded {A : Type} (o : Outcome A) *)
(*               (P : A -> L) {struct o} : L := *)
(*     match o with *)
(*     | outcome_pure a => P a *)
(*     | @outcome_angelic _ I0 os => *)
(*       ∃ i : I0, outcome_satisfy_natded (os i) P *)
(*     | @outcome_demonic _ IO os => *)
(*       ∀ i : IO, outcome_satisfy_natded (os i) P *)
(*     | outcome_angelic_binary o1 o2 => *)
(*       outcome_satisfy_natded o1 P ∨ outcome_satisfy_natded o2 P *)
(*     | outcome_demonic_binary o1 o2 => *)
(*       outcome_satisfy_natded o1 P ∧ outcome_satisfy_natded o2 P *)
(*     | outcome_fail s => lfalse *)
(*     | outcome_block => ltrue *)
(*   end. *)

(*   Axiom outcome_satisfy_natded_bind : *)
(*     forall {A B : Type} (o : Outcome A) (f : A -> Outcome B) (P : B -> L), *)
(*       outcome_satisfy_natded (outcome_bind o f) P ⊣⊢s *)
(*       outcome_satisfy_natded o (fun a => outcome_satisfy_natded (f a) P). *)

(*   Lemma outcome_satisfy_natded_monotonic {A : Type} {o : Outcome A} {P Q : A -> L} *)
(*     (hyp : forall a, P a ⊢ Q a) : *)
(*     outcome_satisfy_natded o P ⊢ outcome_satisfy_natded o Q. *)
(*   Proof. *)
(*     induction o; cbn. *)
(*     - apply hyp. *)
(*     - apply lex_left; intro i. *)
(*       apply lex_right with i. *)
(*       apply H. *)
(*     - apply lall_right; intro i. *)
(*       apply lall_left with i. *)
(*       apply H. *)
(*     - apply lor_left. *)
(*       + apply lor_right1. *)
(*         apply IHo1. *)
(*       + apply lor_right2. *)
(*         apply IHo2. *)
(*     - apply land_right. *)
(*       + apply land_left1. *)
(*         apply IHo1. *)
(*       + apply land_left2. *)
(*         apply IHo2. *)
(*     - apply entails_refl. *)
(*     - apply entails_refl. *)
(*   Qed. *)

(* End Unused. *)
