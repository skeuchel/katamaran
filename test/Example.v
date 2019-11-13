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
     Program.Equality
     Program.Tactics
     Strings.String
     ZArith.ZArith
     micromega.Lia
     Bool
     Setoid.

(* Unset SsrRewrite. *)
(* From Coq Require Import ssreflect ssrfun ssrbool. *)
(* Set Implicit Arguments. *)
(* Unset Strict Implicit. *)
(* Unset Printing Implicit Defensive. *)

From MicroSail Require Import
     WLP.Spec
     Syntax.

Set Implicit Arguments.
Import CtxNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope ctx_scope.

Inductive Ordering : Set :=
| LT
| EQ
| GT.

Program Instance blastable_ordering : Blastable Ordering :=
  { blast := fun ord k =>
               (ord = LT -> k LT) /\
               (ord = EQ -> k EQ) /\
               (ord = GT -> k GT) }.
Solve All Obligations with intros []; intuition; congruence.

Notation "[ x ]" := (ctx_snoc ctx_nil x) : ctx_scope.
Notation "[ x , .. , z ]" := (ctx_snoc .. (ctx_snoc ctx_nil x) .. z) : ctx_scope.

Module ExampleTermKit <: TermKit.

  (* Global names and types of functions. *)
  Inductive Fun : Ctx Set -> Set -> Set :=
  | abs        : [ Z ]    --> Z
  | gcd        : [ Z, Z ] --> Z
  | gcdpos     : [ Z, Z ] --> Z
  | gcdcompare : [ Z, Z ] --> Z
  | compare    : [ Z, Z ] --> Ordering
  where "Γ --> σ" := (Fun Γ σ).

  Definition 𝑭  : Ctx Set -> Set -> Set := Fun.

End ExampleTermKit.
Module ExampleTerms := Terms ExampleTermKit.
Import ExampleTerms.

(* Notation "[ x , .. , z ]" := *)
(*   (tuplepat_snoc .. (tuplepat_snoc tuplepat_nil x) .. z) : pat_scope. *)
Notation "[ x , .. , z ]" :=
  (pair .. (pair tt x) .. z) : exp_scope.
Notation "'call' f x .. z" :=
  (stm_app f (pair .. (pair tt x) .. z)) (at level 40, x at next level, z at next level) : exp_scope.

Notation "Γ --> σ" := (Fun Γ σ).
Notation "Γ '-->>' τ" := (abstract Γ τ) (at level 60, right associativity) : type_scope.
Notation "'if' b 'then' t 'else' f" := (stm_if b%bool t f) (at level 200) : exp_scope.


Local Coercion stm_lit_Z := (@stm_lit Z).
Local Coercion stm_lit_Ordering := (@stm_lit Ordering).

Module ExampleProgramKit <: (ProgramKit ExampleTermKit).
  Module TM := ExampleTerms.

  Local Open Scope exp_scope.

  Local Notation "ma >>= f" := (stm_bind ma f) (at level 50, left associativity).
  (* Notation "ma *> mb" := (bindright ma mb) (at level 50, left associativity). *)
  (* Notation "ma <* mb" := (bindleft ma mb) (at level 50, left associativity). *)

  Definition Pi {Δ τ} (f : Δ --> τ) : Δ -->> Stm τ :=
    match f with
    | abs => fun x => if 0 <=? x then x else (- x)
    | gcd => fun p q =>
               stm_app abs [p] >>= fun p' =>
               stm_app abs [q] >>= fun q' =>
               if (0 <? p') && (0 <? q')
               then stm_app gcdpos [p', q']
               else p' + q'
    | gcdpos => fun p q =>
                  if p =? q then
                    p
                  else if p <? q then
                    stm_app gcdpos [p, q - p]
                  else
                    stm_app gcdpos [p - q, q]
    | gcdcompare => fun p q =>
                      stm_app compare [p, q] >>= fun ord =>
                      match ord with
                      | LT => stm_app gcdcompare [p, q - p]
                      | EQ => p
                      | GT => stm_app gcdcompare [p - q, q]
                      end
    | compare => fun x y =>
                   if x <? y then LT else
                   if x =? y then EQ else
                   if x >? y then GT else
                   stm_exit Ordering "compare"
    end.

End ExampleProgramKit.
Import ExampleProgramKit.

(******************************************************************************)

Module ExampleContractKit <: (ContractKit ExampleTermKit ExampleProgramKit).

  Definition CEnv : ContractEnv :=
    fun (σs : Ctx Set) (τ : Set) (f : Fun σs τ) =>
      match f with
      | abs        => ContractWLP [Z] Z
                        (fun _ => True)
                        (fun x r => r = Z.abs x)
      | gcdpos     => ContractWLP [Z, Z] Z
                        (fun p q => p > 0 /\ q > 0)
                        (fun p q r => r = Z.gcd p q)
      | compare    => ContractWLP [Z, Z] Ordering
                        (fun _ _ => True)
                        (fun x y ord =>
                           (x < y <-> ord = LT) /\
                           (x = y <-> ord = EQ) /\
                           (x > y <-> ord = GT)
                           (* match ord with *)
                           (* | LT => x < y *)
                           (* | EQ => x = y *)
                           (* | GT => x > y *)
                           (* end *)
                        )
      | gcd        => ContractWLP [Z, Z] Z
                        (fun _ _ => True)
                        (fun p q r => r = Z.gcd p q)
      | gcdcompare => ContractWLP [Z, Z] Z
                        (fun p q => p > 0 /\ q > 0)
                        (fun p q r => r = Z.gcd p q)
      end.

End ExampleContractKit.
Import ExampleContractKit.

Module ExampleWLP := WLP ExampleTermKit ExampleProgramKit ExampleContractKit.
Import ExampleWLP.

Fixpoint Forall (Δ : Ctx Set) {struct Δ} : (Env Lit Δ -> Prop) -> Prop :=
  match Δ return (Env Lit Δ -> Prop) -> Prop with
  | ctx_nil      => fun P => P tt
  | ctx_snoc Δ b => fun P => Forall Δ (fun δ => forall v, P (δ, v))
  end.

Definition ValidContract {Γ τ} (c : Contract Γ τ) (s : abstract Γ (Stm τ)) : Prop :=
  match c with
  | ContractWLP _ _ pre post => Forall Γ (fun δ => apply pre δ -> WLP (apply s δ) (apply post δ))
  | _ => True
  end.

Definition ValidContractEnv (cenv : ContractEnv) : Prop :=
  forall σs σ (f : 𝑭 σs σ), ValidContract (cenv σs σ f) (Pi f).

Lemma gcd_sub_diag_l (n m : Z) : Z.gcd (n - m) m = Z.gcd n m.
Proof. now rewrite Z.gcd_comm, Z.gcd_sub_diag_r, Z.gcd_comm. Qed.

Lemma abs_le_0 (n : Z) :
  Z.abs n <= 0 <-> n = 0.
Proof. lia. Qed.

Ltac validate_destr :=
  match goal with
  | [ H: True |- _ ] => clear H
  | [ H: False |- _ ] => destruct H
  | [ |- _ -> _ ]  => intro
  | [ |- True ]  => constructor
  end.

Ltac validate_simpl :=
  repeat
    (cbn in *; repeat validate_destr; destruct_conjs; subst; try discriminate;
     rewrite ?andb_true_iff, ?andb_false_iff, ?abs_le_0, ?Z.eqb_eq, ?Z.eqb_neq, ?Z.leb_gt, ?Z.ltb_ge, ?Z.ltb_lt, ?Z.leb_le, ?Z.gtb_ltb,
       ?Z.gcd_diag, ?Z.gcd_abs_l, ?Z.gcd_abs_r, ?Z.gcd_sub_diag_r, ?Z.gcd_0_r, ?Z.gcd_0_l, ?gcd_sub_diag_l in *).

     (* ?andb_false_iff, *)
Ltac validate_case :=
  match goal with
  | [ |- match ?e with _ => _ end _ ] =>
    case_eq e
  | [ |- WLP match ?e with _ => _ end _ ] =>
    case_eq e
  end.

Ltac validate_solve :=
  repeat (validate_simpl; intuition; try lia).

Lemma validCEnv : ValidContractEnv CEnv.
Proof. time (intros σs τ [] δ; validate_solve). Qed.

Print Assumptions validCEnv.
