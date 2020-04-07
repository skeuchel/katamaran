Require Import Coq.Program.Tactics.
Require Import FunctionalExtensionality.

Require Import MicroSail.Syntax.
Require Import MicroSail.Environment.
Require Import MicroSail.Sep.Logic.
Require Import MicroSail.Sep.Spec.

Module ProgramLogic

  (Import typekit : TypeKit)
  (Import termkit : TermKit typekit)
  (Import progkit : ProgramKit typekit termkit)
  (Import assertkit : AssertionKit typekit termkit progkit)
  (Import contractkit : SymbolicContractKit typekit termkit progkit assertkit).
  Module CM := SymbolicContracts typekit termkit progkit assertkit contractkit.
  Export CM.

  (* Program Instance Assertion_NatDed (Σ : Ctx (𝑺 * Ty)) : NatDed (Term Σ ty_bool) := *)
  (* { andp := (fun P Q => term_binop binop_and P Q); *)
  (*   orp := (fun P Q => term_binop binop_or P Q); *)
  (*   exp := _; *)
  (*   allp := _; *)
  (*   imp := _; *)
  (*   prop := _; *)
  (*   derives := _; *)
  (* }. *)

  Import CtxNotations.
  Import EnvNotations.

  Open Scope logic.
  (* Definition ctxprop := Ctx (𝑿 * Ty) -> Prop. *)

  (* Definition ptstoctx {Γ : Ctx (𝑿 * Ty)} {A : Set} (x : 𝑿) (v : A) : ctxprop := *)
  (*   fun _ => True. *)

  (* Program Instance ctxpop_NatDed : NatDed ctxprop. *)
  (* Admit Obligations. *)


  Reserved Notation "Γ ⊢ ⦃ P ⦄ s ⦃ Q ⦄" (at level 75, no associativity).

  Definition is_inl {A B} (x : A + B) :=
    match x with
    | inl _ => true
    | _ => false
    end.

  Definition is_inr {A B} (x : A + B) :=
    match x with
    | inr _ => true
    | _ => false
    end.

  Definition Sub (Γ1 Γ2 : Ctx (𝑿 * Ty)) : Type :=
    Env (fun b => Exp Γ2 (snd b)) Γ1.

  Definition sub_id Γ : Sub Γ Γ :=
    @env_tabulate _ (fun b => Exp _ (snd b)) _
                  (fun '(x , σ) xIn => @exp_var Γ x σ xIn).
  Global Arguments sub_id : clear implicits.

  Section HoareTriples.
    Context {A : Type} {ND : NatDedAxioms A} {SL : SepLogAxioms A}.

    Inductive Triple (Γ : Ctx (𝑿 * Ty)) :
      forall {τ : Ty}
             (pre : LocalStore Γ -> A) (s : Stm Γ τ)
             (post :  LocalStore Γ -> Lit τ -> A), Prop :=
    | rule_stm_lit (τ : Ty) (l : Lit τ) :
        Γ ⊢ ⦃ fun _ => TT ⦄ stm_lit τ l ⦃ fun _ x => !!(l = x) ⦄
    | rule_stm_exp_forwards (τ : Ty) (e : Exp Γ τ) (P : LocalStore Γ -> A) :
        Γ ⊢ ⦃ P ⦄ stm_exp e ⦃ fun δ v => P δ ∧ !!(eval e δ = v) ⦄
    | rule_stm_exp_backwards (τ : Ty) (e : Exp Γ τ) (Q : LocalStore Γ -> Lit τ -> A) :
        Γ ⊢ ⦃ fun δ => Q δ (eval e δ) ⦄ stm_exp e ⦃ Q ⦄
    | rule_stm_let
        (x : 𝑿) (σ τ : Ty) (s : Stm Γ σ) (k : Stm (ctx_snoc Γ (x , σ)) τ)
        (P : LocalStore Γ -> A) (Q : LocalStore Γ -> Lit σ -> A)
        (R : LocalStore Γ -> Lit τ -> A) :
        Γ         ⊢ ⦃ P ⦄ s ⦃ Q ⦄ ->
        Γ ▻ (x,σ) ⊢ ⦃ fun δ => Q (env_tail δ) (env_head δ) ⦄ k ⦃ fun δ => R (env_tail δ) ⦄ ->
        Γ         ⊢ ⦃ P ⦄ let: x := s in k ⦃ R ⦄
    | rule_stm_if (τ : Ty) (e : Exp Γ ty_bool) (s1 s2 : Stm Γ τ)
          (P : LocalStore Γ -> A)
          (Q : LocalStore Γ -> Lit τ -> A) :
          Γ ⊢ ⦃ fun δ => P δ ∧ !!(eval e δ = true) ⦄ s1 ⦃ Q ⦄ ->
          Γ ⊢ ⦃ fun δ => P δ ∧ !!(eval e δ = false) ⦄ s2 ⦃ Q ⦄ ->
          Γ ⊢ ⦃ P ⦄ stm_if e s1 s2 ⦃ Q ⦄
    | rule_stm_seq (τ : Ty) (s1 : Stm Γ τ) (σ : Ty) (s2 : Stm Γ σ)
          (P : LocalStore Γ -> A)
          (Q : LocalStore Γ -> A)
          (R : LocalStore Γ -> Lit σ -> A) :
          Γ ⊢ ⦃ P ⦄ s1 ⦃ fun δ _ => Q δ ⦄ ->
          Γ ⊢ ⦃ Q ⦄ s2 ⦃ R ⦄ ->
          Γ ⊢ ⦃ P ⦄ s1 ;; s2 ⦃ R ⦄
    (* | rule_stm_assert (e1 : Exp Γ ty_bool) (e2 : Exp Γ ty_string) : *)
    (* (* Just a side note: don't we need the assertion string to a literal, *)
    (*    rather than an expression? *) *)
    (*     forall (P : LocalStore Γ -> A) *)
    (*       (Q : LocalStore Γ -> Lit ty_bool -> A), *)
    (*       ⦃ fun δ => P δ ∧ !!(eval e1 δ = true) ⦄ stm_assert e1 e2 ⦃ Q ⦄ *)
    (* | rule_stm_fail (τ : Ty) (s : Lit ty_string) : *)
    (*     forall (Q : LocalStore Γ -> Lit τ -> A), *)
    (*     ⦃ fun _ => FF ⦄ stm_fail τ s ⦃ Q ⦄ *)
    (* (* | rule_stm_match_list {σ τ : Ty} (e : Exp Γ (ty_list σ) (alt_nil : Stm Γ τ) *) *)
    (* (*   (xh xt : 𝑿) (alt_cons : Stm (ctx_snoc (ctx_snoc Γ (xh , σ)) (xt , ty_list σ)) τ) : *) *)
    (* | rule_stm_match_sum (σinl σinr τ : Ty) (e : Exp Γ (ty_sum σinl σinr)) *)
    (*   (xinl : 𝑿) (alt_inl : Stm (ctx_snoc Γ (xinl , σinl)) τ) *)
    (*   (xinr : 𝑿) (alt_inr : Stm (ctx_snoc Γ (xinr , σinr)) τ) *)
    (*       (P : LocalStore Γ -> A) *)
    (*       (Q : LocalStore Γ -> Lit τ -> A) : *)
    (*       Γ ▻ (xinl, σinl) ⊢ ⦃ fun δ => P (env_tail δ) ∧ !!(is_inl (@eval  Γ _ e δ)) *)
    (*                           ⦄ alt_inl *)
    (*                           ⦃ fun δ => Q (env_tail δ) ⦄ -> *)
          (* Γ ▻ (xinr, σinr) ⊢ ⦃ fun δ => P δ ∧ !!(is_inr (eval e δ))⦄ alt_inr ⦃ Q ⦄ -> *)
          (* Γ ⊢ ⦃ P ⦄ stm_match_sum e xinl alt_inl xinr alt_inr ⦃ Q ⦄ *)
    where "Γ ⊢ ⦃ P ⦄ s ⦃ Q ⦄" := (Triple Γ P s Q).

  End HoareTriples.

End ProgramLogic.

(* (x : 𝑿) (τ : Ty) (s : Stm Γ τ) {τ : Ty} (k : Stm (ctx_snoc Γ (x , τ)) τ) : Stm Γ τ *)
(*       | rule_stm_exp *)
(*         TT (stm_exp ) FF. *)
(*       (γ : RegStore) (μ : Memory) (δ : LocalStore Γ) (τ : Ty) (e : Exp Γ τ) : *)
(*       ⟨ γ , μ , δ , (stm_exp e) ⟩ ---> ⟨ γ , μ , δ , stm_lit τ (eval e δ) ⟩ *)