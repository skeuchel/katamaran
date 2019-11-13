Require Import Coq.Program.Equality.
Require Import MicroSail.Context.
Require Import MicroSail.Notation.

Set Implicit Arguments.

Section WithBinding.
  Context {B : Type}.

  Fixpoint Env (D : B -> Type) (Γ : Ctx B) : Type :=
    match Γ with
    | ctx_nil => unit
    | ctx_snoc Γ x => prod (Env D Γ) (D x)
    end.
  (* Global Arguments env_nil {_}. *)
  Bind Scope env_scope with Env.

  Fixpoint Env_ind (D : B -> Type) (P : forall Γ, Env D Γ -> Prop)
    (en : P ctx_nil tt)
    (ec : forall Γ E, P Γ E -> forall x (d : D x), P (ctx_snoc Γ x) (E , d))
    (Γ : Ctx B) {struct Γ} : forall (E : Env D Γ), P Γ E :=
    match Γ with
    | ctx_nil => fun E => match E with | tt => en end
    | ctx_snoc Γ b =>
      fun EΓb =>
        match EΓb with
        | (EΓ , db) => ec Γ EΓ (Env_ind D P en ec Γ EΓ) b db
        end
    end.

  (* Inductive Env (D : B -> Type) : Ctx B -> Type := *)
  (* | env_nil : Env D ctx_nil *)
  (* | env_snoc {Γ} (E : Env D Γ) (b : B) (db : D b) : *)
  (*     Env D (ctx_snoc Γ b). *)

  (* Global Arguments env_nil {_}. *)
  (* Bind Scope env_scope with Env. *)

  Fixpoint env_cat {D : B -> Type} {Γ Δ : Ctx B} (EΓ : Env D Γ) {struct Δ} :
    Env D Δ -> Env D (ctx_cat Γ Δ) :=
    match Δ with
    | ctx_nil => fun EΔ => EΓ
    | ctx_snoc Δ b => fun EΔ => (env_cat EΓ (fst EΔ), snd EΔ)
    end.

  (* Fixpoint env_map {D₁ D₂ : B -> Type} {Γ : Ctx B} *)
  (*          (f : forall x, D₁ x -> D₂ x) {struct Γ} : Env D₁ Γ -> Env D₂ Γ := *)
  (*   match Γ as c return (Env D₁ c -> Env D₂ c) with *)
  (*   | ctx_nil => fun E => E *)
  (*   | ctx_snoc Γ b => fun EΓb => (env_map f (fst EΓb), f b (snd EΓb)) *)
  (*   end. *)

  (* Fixpoint env_lookup {D : B -> Type} {Γ : Ctx B} *)
  (*   (E : Env D Γ) : forall (b : B) (bIn : InCtx b Γ), D b := *)
  (*   match E with *)
  (*   | env_nil => fun _ => inctx_case_nil *)
  (*   | env_snoc E b db => inctx_case_snoc D db (env_lookup E) *)
  (*   end. *)

  (* Global Arguments env_lookup {_ _} _ [_] _. *)

  (* Fixpoint env_update {D : B -> Type} {Γ : Ctx B} (E : Env D Γ) {struct E} : *)
  (*   forall {b0 : B} (bIn0 : InCtx b0 Γ) (new : D b0), Env D Γ := *)
  (*   match E with *)
  (*   | env_nil => fun _ => inctx_case_nil *)
  (*   | @env_snoc _ Γ E b bold => *)
  (*     inctx_case_snoc *)
  (*       (fun z => D z -> Env D (ctx_snoc Γ b)) *)
  (*       (fun new => env_snoc E b new) *)
  (*       (fun b0' bIn0' new => env_snoc (env_update E bIn0' new) b bold) *)
  (*   end. *)

  (* Definition env_tail {D : B -> Type} {Γ : Ctx B} *)
  (*   {b : B} (E : Env D (ctx_snoc Γ b)) : Env D Γ := *)
  (*   match E in Env _ Γb *)
  (*   return match Γb with *)
  (*          | ctx_nil => unit *)
  (*          | ctx_snoc Γ _ => Env D Γ *)
  (*          end *)
  (*   with *)
  (*     | env_nil => tt *)
  (*     | env_snoc E _ _ => E *)
  (*   end. *)

  (* Global Arguments env_tail {_ _ _} / _. *)

  (* Fixpoint env_drop {D : B -> Type} {Γ : Ctx B} Δ {struct Δ} : *)
  (*   forall (E : Env D (ctx_cat Γ Δ)), Env D Γ := *)
  (*   match Δ with *)
  (*   | ctx_nil => fun E => E *)
  (*   | ctx_snoc Δ _ => fun E => env_drop Δ (env_tail E) *)
  (*   end. *)

  (* Fixpoint env_split {D : B -> Type} {Γ : Ctx B} Δ {struct Δ} : *)
  (*   forall (E : Env D (ctx_cat Γ Δ)), Env D Γ * Env D Δ := *)
  (*   match Δ with *)
  (*   | ctx_nil => fun E => (E , env_nil) *)
  (*   | ctx_snoc Δ b => *)
  (*     fun E => *)
  (*       match E in (Env _ ΓΔb) *)
  (*       return match ΓΔb with *)
  (*              | ctx_nil => unit *)
  (*              | ctx_snoc ΓΔ b => (Env D ΓΔ -> Env D Γ * Env D Δ) -> *)
  (*                                 Env D Γ * Env D (ctx_snoc Δ b) *)
  (*              end *)
  (*       with *)
  (*       | env_nil => tt *)
  (*       | env_snoc EΓΔ b db => *)
  (*         fun split => let (EΓ, EΔ) := split EΓΔ in (EΓ, env_snoc EΔ b db) *)
  (*       end (env_split Δ) *)
  (*   end. *)

  (* Lemma env_lookup_update {D : B -> Type} {Γ : Ctx B} (E : Env D Γ) : *)
  (*   forall {b : B} (bInΓ : InCtx b Γ) (db : D b), *)
  (*     env_lookup (env_update E bInΓ db) bInΓ = db. *)
  (* Proof. *)
  (*   induction E; intros ? [n e]; try destruct e; *)
  (*     destruct n; cbn in *; subst; auto. *)
  (* Qed. *)

  (* Lemma env_split_cat {D : B -> Type} {Γ Δ : Ctx B} : *)
  (*   forall (EΓ : Env D Γ) (EΔ : Env D Δ), *)
  (*     env_split Δ (env_cat EΓ EΔ) = (EΓ , EΔ). *)
  (* Proof. induction EΔ using Env_ind; cbn; now try rewrite IHEΔ. Qed. *)

  (* Lemma env_cat_split' {D : B -> Type} {Γ Δ : Ctx B} : *)
  (*   forall (EΓΔ : Env D (ctx_cat Γ Δ)), *)
  (*     let (EΓ,EΔ) := env_split _ EΓΔ in *)
  (*     EΓΔ = env_cat EΓ EΔ. *)
  (* Proof. *)
  (*   induction Δ; intros; cbn in *. *)
  (*   - reflexivity. *)
  (*   - dependent destruction EΓΔ. *)
  (*     specialize (IHΔ EΓΔ); cbn in *. *)
  (*     destruct (env_split Δ EΓΔ); now subst. *)
  (* Qed. *)

  (* Lemma env_cat_split {D : B -> Type} {Γ Δ : Ctx B} (EΓΔ : Env D (ctx_cat Γ Δ)) : *)
  (*   EΓΔ = env_cat (fst (env_split _ EΓΔ)) (snd (env_split _ EΓΔ)). *)
  (* Proof. *)
  (*   generalize (env_cat_split' EΓΔ). *)
  (*   now destruct (env_split Δ EΓΔ). *)
  (* Qed. *)

  (* Lemma env_drop_cat {D : B -> Type} {Γ Δ : Ctx B} : *)
  (*   forall (δΔ : Env D Δ) (δΓ : Env D Γ), *)
  (*     env_drop Δ (env_cat δΓ δΔ) = δΓ. *)
  (* Proof. induction δΔ; cbn; auto. Qed. *)

End WithBinding.

(* Definition Env' {X T : Set} (D : T -> Type) (Γ : Ctx (X * T)) : Type := *)
(*   Env (fun xt => D (snd xt)) Γ. *)
Bind Scope env_scope with Env.
(* Bind Scope env_scope with Env'. *)

(* Module EnvNotations. *)

(*   Notation "δ '►' b '↦' d" := (env_snoc δ b d). *)
(*   Notation "δ1 '►►' δ2" := (env_cat δ1 δ2). *)
(*   Notation "δ [ x ↦ v ]" := (@env_update _ _ _ δ (x , _) _ v). *)
(*   Notation "δ ! x" := (@env_lookup _ _ _ δ (x , _) _). *)

(* End EnvNotations. *)
