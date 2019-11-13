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
     Logic.EqdepFacts
     Program.Equality
     Program.Tactics
     Strings.String
     ZArith.ZArith.

From MicroSail Require Export
     Context
     Environment
     Notation.

Set Implicit Arguments.

Local Definition Cont (R A : Type) : Type := (A -> R) -> R.

Class Blastable (A : Set) : Type :=
  { blast : A -> Cont Prop A;
    blast_sound:
      forall (a : A) (k : A -> Prop),
        blast a k <-> k a
  } .

Program Instance blastable_bool : Blastable bool :=
  {| blast := fun b k => (b = true -> k true) /\ (b = false -> k false) |}.
Solve All Obligations with destruct a; intuition.

Program Instance blastable_int : Blastable Z :=
  { blast := fun z k => k z }.
Solve All Obligations with intuition.

Program Instance blastable_prod {A B : Set} : Blastable (A * B) :=
  { blast := fun ab k => k (fst ab , snd ab) }.
Solve All Obligations with intuition.

Program Instance blastable_sum {A B : Set} : Blastable (A + B) :=
  { blast := fun ab k =>
               (forall (a : A), ab = inl a -> k (inl a)) /\
               (forall (b : B), ab = inr b -> k (inr b)) }.
Solve All Obligations with destruct a; intuition; congruence.

(******************************************************************************)

Module Type TermKit.

  (* Names of functions. *)
  Parameter Inline 𝑭  : Ctx Set -> Set -> Set.

End TermKit.

Module Terms (termkit : TermKit).
  Export termkit.

  Definition Lit (A : Set) : Set := A.
  Arguments Lit / _.
  Definition LocalStore (Γ : Ctx Set) : Type := Env Lit Γ.

  Section Statements.

    Inductive Stm : Set -> Type :=
    | stm_lit        {σ : Set} (v : σ) : Stm σ
    | stm_app        {Δ σ} (f : 𝑭 Δ σ) (es : Env Lit Δ) : Stm σ
    | stm_if         {τ : Set} (b : bool) (s1 s2 : Stm τ) : Stm τ
    | stm_assert     (b : bool) (e2 : string) : Stm bool
    | stm_exit       (τ : Set) (s : string) : Stm τ
    (* | stm_match      {σ τ : Set} {σMatch : Blastable σ} (s : Stm σ) (k : σ -> Stm τ) : Stm τ *)
    | stm_bind       {σ τ : Set} {σMatch : Blastable σ} (s : Stm σ) (k : σ -> Stm τ) : Stm τ.

    Global Arguments stm_lit _.
    Global Arguments stm_app {_%ctx _} _ _%exp.
    Global Arguments stm_if {_} _ _ _.
    Global Arguments stm_assert _ _.
    Global Arguments stm_exit _ _.

  End Statements.

  Fixpoint abstract (Δ : Ctx Set) (τ : Type) {struct Δ} : Type :=
    match Δ with
    | ctx_nil => τ
    | ctx_snoc Δ σ => abstract Δ (σ -> τ)
    end.

  Fixpoint apply {Δ : Ctx Set} {τ : Type} (f : abstract Δ τ) (δ : Env Lit Δ) {struct Δ} : τ :=
   match Δ return (Env Lit Δ -> abstract Δ τ -> τ) with
   | ctx_nil => fun _ v => v
   | ctx_snoc Δ b => fun δ (f : abstract _ (b -> τ)) => apply f (fst δ) (snd δ)
   end δ f.

  (* Record FunDef (Δ : Ctx (𝑿 * Ty)) (τ : Ty) : Set := *)
  (*   { fun_body : Stm Δ τ }. *)

  Section Contracts.

    Definition Pred (A : Type) : Type := A -> Prop.

    Definition Final {σ} (s : Stm σ) : Prop :=
      match s with
      | stm_lit _  => True
      | stm_exit _ _ => True
      | _ => False
      end.

    (* Version that computes *)
    Definition IsLit {σ} (s : Stm σ) :
      forall (POST : Pred σ), Prop :=
      match s with
      | stm_lit v => fun POST => POST v
      | _ => fun _ => False
      end.

    Lemma IsLit_inversion {σ} (s : Stm σ) (POST : Pred σ) :
      IsLit s POST -> exists v, s = stm_lit v /\ POST v.
    Proof. destruct s; cbn in *; try contradiction; eauto. Qed.

    Inductive Contract (Δ : Ctx Set) (τ : Set) : Type :=
    | ContractWLP (pre : abstract Δ Prop) (post: abstract Δ (τ -> Prop))
    | ContractWP  (pre : abstract Δ Prop) (post: abstract Δ (τ -> Prop))
    | ContractNone.

    Definition ContractEnv : Type :=
      forall Δ τ (f : 𝑭 Δ τ), Contract Δ τ.

  End Contracts.

End Terms.

(******************************************************************************)

Module Type ProgramKit
       (Import termkit : TermKit).
  Module TM := Terms termkit.
  Export TM.

  (* Parameter Inline Pi : forall {Δ τ} (f : 𝑭 Δ τ), FunDef Δ τ. *)
  Parameter Inline Pi : forall {Δ τ} (f : 𝑭 Δ τ), abstract Δ (Stm τ).

End ProgramKit.

Module Type ContractKit
       (Import termkit : TermKit)
       (Import progkit : ProgramKit termkit).

  Parameter Inline CEnv : ContractEnv.

End ContractKit.
