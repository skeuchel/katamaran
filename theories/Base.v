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

From Stdlib Require Export
     Numbers.BinNums.
From Stdlib Require Import
     Program.Tactics.
From Katamaran Require Export
     Context
     Environment
     Prelude
     Syntax.BinOps
     Syntax.Expressions
     Syntax.Registers
     Syntax.TypeDecl
     Syntax.UnOps
     Syntax.Variables
     Tactics.
From Katamaran Require Import
     Syntax.Messages
     Syntax.Patterns
     Syntax.Terms
     Symbolic.Instantiation
     Symbolic.OccursCheck
     Symbolic.GenOccursCheck.

(* Preciseness for spatial predicates. This does not depend on the [Base], so
   it is defined outside of it, which keeps the [Base] signature smaller. *)
Record Precise {T P : Set} (F : P -> Ctx T) (p : P) : Set :=
  MkPrecise
    { prec_input  : Ctx T;
      prec_output : Ctx T;
      prec_inout  : F p = ctx.cat prec_input prec_output;
    }.
Arguments MkPrecise {_ _ _ _} & _ _ _.

Module Type BaseMixin (Import TY : Types).
  Include
    TermsOn TY <+ PatternsOn TY <+
    OccursCheckOn TY <+ GenOccursCheckOn TY <+ InstantiationOn TY <+
    MessagesOn TY.

  Abbreviation Ty := (@ty.Ty typedeclkit).
  Abbreviation LVar := (@Variables.LVar varkit).
  Abbreviation PVar := (@Variables.PVar varkit).
  Abbreviation PCtx := (NCtx PVar Ty).
  Abbreviation LCtx := (NCtx LVar Ty).
  Abbreviation Val := (@ty.Val typedeclkit typedenotekit).

  Abbreviation Valuation Σ :=
    (@Env (Binding LVar Ty)
       (fun xt : Binding LVar Ty =>
          Val (@type _ _ xt)) Σ).

  Abbreviation CStore := (@NamedEnv PVar Ty Val).

  Definition SMatchResult {N σ} (pat : Pattern (N:=N) σ) (Σ : LCtx) : Type :=
    { pc : PatternCase pat & NamedEnv (Term Σ) (PatternCaseCtx pc) }.

  Section PatternMatching.
    Context {N : Set}.

    Lemma inst_tuple_pattern_match {Σ : LCtx} {σs : Ctx Ty} {Δ : NCtx N Ty}
      (ι : Valuation Σ) (p : TuplePat σs Δ) (ts : Env (Term Σ) σs) :
      inst (tuple_pattern_match_env p ts) ι =
      tuple_pattern_match_env p (inst (T := fun Σ => Env (Term Σ) σs) ts ι).
    Proof.
      unfold inst at 1; cbn.
      induction p; cbn.
      - reflexivity.
      - destruct (env.view ts); cbn.
        f_equal. apply IHp.
    Qed.

    Lemma inst_tuple_pattern_match_reverse {Σ : LCtx} {σs : Ctx Ty} {Δ : NCtx N Ty}
      (ι : Valuation Σ) (p : TuplePat σs Δ) (ts : NamedEnv (Term Σ) Δ) :
      inst (tuple_pattern_match_env_reverse p ts) ι =
      tuple_pattern_match_env_reverse p (inst (T := fun Σ => NamedEnv (Term Σ) Δ) ts ι).
    Proof.
      unfold inst at 1; cbn.
      induction p; cbn.
      - reflexivity.
      - destruct (env.view ts); cbn.
        f_equal. apply IHp.
    Qed.

    Lemma inst_record_pattern_match {Δ__R : NCtx recordf Ty} {Σ : LCtx} {Δ : NCtx N Ty}
      (ι : Valuation Σ) (p : RecordPat Δ__R Δ) (ts : NamedEnv (Term Σ) Δ__R) :
      inst (T := fun Σ => NamedEnv (Term Σ) Δ) (record_pattern_match_env p ts) ι =
      record_pattern_match_env p (inst ts ι).
    Proof.
      unfold inst at 1; cbn.
      induction p; cbn.
      - reflexivity.
      - destruct (env.view ts); cbn.
        f_equal. apply IHp.
    Qed.

    Lemma inst_record_pattern_match_reverse {Δ__R : NCtx recordf Ty} {Σ : LCtx} {Δ : NCtx N Ty}
      (ι : Valuation Σ) (p : RecordPat Δ__R Δ) (ts : NamedEnv (Term Σ) Δ) :
      inst (record_pattern_match_env_reverse p ts) ι =
      record_pattern_match_env_reverse p (inst (T := fun Σ => NamedEnv (Term Σ) Δ) ts ι).
    Proof.
      unfold inst at 1; cbn.
      induction p; cbn.
      - reflexivity.
      - destruct (env.view ts); cbn.
        f_equal. apply IHp.
    Qed.

    Fixpoint pattern_match_term_reverse {Σ σ} (pat : Pattern (N:=N) σ) :
      forall (pc : PatternCase pat), NamedEnv (Term Σ) (PatternCaseCtx pc) -> Term Σ σ :=
      match pat with
      | pat_var x =>
          fun _ ts => env.head ts
      | pat_bool =>
          fun b _ => term_val ty.bool b
      | pat_list σ x y =>
          fun b =>
            match b with
            | true => fun _ => term_val (ty.list σ) nil
            | false => fun Eht =>
                         let (Eh,t) := env.view Eht in
                         let (E,h)  := env.view Eh in
                         term_binop bop.cons h t
            end
      | pat_pair x y =>
          fun _ Exy =>
            let (Ex,vτ) := env.view Exy in
            let (E,vσ)  := env.view Ex in
            term_binop bop.pair vσ vτ
      | pat_sum σ0 τ x y =>
          fun b =>
            match b with
            | true => fun ts => term_unop uop.inl (env.head ts)
            | false => fun ts => term_unop uop.inr (env.head ts)
            end
      | pat_unit =>
          fun pc _ => term_val ty.unit pc
      | pat_enum E =>
          fun v _ => term_val (ty.enum E) v
      | pat_bvec_split m n x y =>
          fun _ Exy =>
            let (Ex,vr) := env.view Exy in
            let (E,vl)  := env.view Ex in
            term_binop bop.bvapp vl vr
      | pat_bvec_exhaustive m =>
          fun v _ => term_val (ty.bvec m) v
      | pat_tuple p =>
          fun _ ts => term_tuple (tuple_pattern_match_env_reverse p ts)
      | pat_record R Δ p =>
          fun _ ts => term_record R (record_pattern_match_env_reverse p ts)
      | pat_union U x =>
          fun '(existT K pc) ts => term_union U K (pattern_match_term_reverse (x K) pc ts)
      end.

    Lemma inst_pattern_match_term_reverse {Σ σ} (ι : Valuation Σ) (pat : Pattern (N:=N) σ) :
      forall (pc : PatternCase pat) (ts : NamedEnv (Term Σ) (PatternCaseCtx pc)),
        inst (pattern_match_term_reverse pat pc ts) ι =
        pattern_match_val_reverse pat pc (inst (T := fun Σ => NamedEnv (Term Σ) _) ts ι).
    Proof.
      induction pat; cbn.
      - intros _ ts. now env.destroy ts.
      - reflexivity.
      - intros [] ts.
        + reflexivity.
        + now env.destroy ts.
      - intros _ ts. now env.destroy ts.
      - intros [] ts; now env.destroy ts.
      - intros [] ts. reflexivity.
      - reflexivity.
      - intros _ ts. now env.destroy ts.
      - reflexivity.
      - intros _ ts.
        now rewrite <- inst_tuple_pattern_match_reverse.
      - intros _ ts. f_equal.
        apply inst_record_pattern_match_reverse.
      - intros [] ts. cbn. f_equal. f_equal. apply H.
    Qed.

    Lemma inst_unfreshen_namedenv (n : N -> LVar) {Σ Σ' Δ}
      (ζ : Sub (freshen_ctx n Σ Δ) Σ') (ι : Valuation Σ') :
      inst (unfreshen_namedenv n ζ) ι = unfreshen_namedenv n (inst ζ ι).
    Proof. induction Δ; cbn in ζ; env.destroy ζ; cbn; f_equal; apply IHΔ. Qed.

    Lemma inst_unfreshen_patterncaseenv (n : N -> LVar) {Σ Σ' σ} (pat : Pattern (N:=N) σ)
      (pc : PatternCase (freshen_pattern n Σ pat))
      (ζ : Sub (PatternCaseCtx pc) Σ')
      (ι : Valuation Σ') :
      inst (unfreshen_patterncaseenv n pat pc ζ) ι =
      unfreshen_patterncaseenv n pat pc (inst ζ ι).
    Proof.
      induction pat; cbn in pc; try destruct pc; cbn in ζ, ι; env.destroy ζ;
        env.destroy ι; cbn; auto using inst_unfreshen_namedenv.
    Qed.

  End PatternMatching.

  Import env.notations.

  Definition seval_exp {Γ Σ} (δ : SStore Γ Σ) :
    forall {σ} (e : Exp Γ σ), Term Σ σ :=
    fix seval_exp {σ} (e : Exp Γ σ) : Term Σ σ :=
      match e with
      | exp_var ς          => δ.[??ς]
      | exp_val σ v        => term_val σ v
      | exp_binop op e1 e2 => term_binop op (seval_exp e1) (seval_exp e2)
      | exp_unop op e      => term_unop op (seval_exp e)
      | exp_list es        => term_list (List.map seval_exp es)
      | exp_bvec es        => term_bvec (Vector.map seval_exp es)
      | exp_tuple es       => term_tuple (env.map (@seval_exp) es)
      | exp_union E K e    => term_union E K (seval_exp e)
      | exp_record R es    => term_record R (env.map (fun _ => seval_exp) es)
      end%exp.

  Lemma eval_exp_inst {Γ Σ τ} (ι : Valuation Σ) (δΓΣ : SStore Γ Σ) (e : Exp Γ τ) :
    eval e (inst δΓΣ ι) = inst (seval_exp δΓΣ e) ι.
  Proof.
    induction e; cbn; repeat f_equal; auto.
    { unfold inst, inst_store, inst_env at 1; cbn.
      now rewrite env.lookup_map.
    }
    2: {
      induction es as [|eb n es IHes]; cbn in *.
      { reflexivity. }
      { destruct X as [-> Heqs].
        change (inst_term ?ι ?t) with (inst ι t).
        destruct (inst (seval_exp δΓΣ eb) ι);
          cbn; f_equal; auto.
      }
    }
    all: induction es; cbn in *; destruct_conjs; f_equal; auto.
  Qed.

  Lemma subst_seval {Γ τ Σ Σ'} (e : Exp Γ τ) (ζ : Sub Σ Σ') (δ : SStore Γ Σ) :
    subst (T := fun Σ => Term Σ _) (seval_exp δ e) ζ = seval_exp (subst δ ζ) e.
  Proof.
    induction e; cbn; f_equal; auto.
    { now rewrite (subst_lookup xInΓ). }
    all: induction es; cbn in *; destruct_conjs; f_equal; auto.
  Qed.

End BaseMixin.

Module Type OperationalModel.

  (* Memory model *)
  Parameter Memory : Type.
  
End OperationalModel.


(* The part of [Base] without the mixin. Functors that only need these
   declarations should take a [BaseKit] instead of a [Base] parameter: every
   functor parameter stores a full copy of its signature, and [Base] is large. *)
Module Type BaseKit := Types <+ RegDeclKit <+ OperationalModel.

Module Type Base := Types <+ RegDeclKit <+ OperationalModel <+ BaseMixin.
