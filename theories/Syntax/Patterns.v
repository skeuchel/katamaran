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

From Katamaran Require Import
     Prelude
     Context
     Environment
     Bitvector
     Syntax.TypeDecl
     Syntax.Variables.

Import ctx.notations.
Import env.notations.

Module Type PatternsOn (Import TY : Types).

  Section Patterns.

    (* These patterns are used in program and logic contexts for pattern
       matching in statements and in assertions. We abstract over the type of
       variables here. *)
    Context {N : Set}.

    Inductive TuplePat : Ctx Ty -> NCtx N Ty -> Set :=
    | tuplepat_nil  : TuplePat [] []
    | tuplepat_snoc
        {σs : Ctx Ty} {Δ : NCtx N Ty}
        (pat : TuplePat σs Δ) {σ : Ty} (x : N) :
        TuplePat (σs ▻ σ) (Δ ▻ x∷σ).

    Inductive RecordPat : NCtx recordf Ty -> NCtx N Ty -> Set :=
    | recordpat_nil  : RecordPat [] []
    | recordpat_snoc
        {rfs : NCtx recordf Ty} {Δ : NCtx N Ty}
        (pat : RecordPat rfs Δ) (rf : recordf) {τ : Ty} (x : N) :
        RecordPat (rfs ▻ rf∷τ) (Δ ▻ x∷τ).

    Definition tuple_pattern_match_env {T : Ty -> Set} :
      forall {σs : Ctx Ty} {Δ : NCtx N Ty},
        TuplePat σs Δ -> Env T σs -> NamedEnv T Δ :=
      fix pattern_match {σs} {Δ} p {struct p} :=
        match p with
        | tuplepat_nil => fun _ => []
        | tuplepat_snoc p x =>
            fun EΔ => let (E,v) := env.view EΔ in
                      (pattern_match p E) ► (_ ↦ v)
        end.

    Definition tuple_pattern_match_env_reverse {T : Ty -> Set} :
      forall {σs : Ctx Ty} {Δ : NCtx N Ty},
        TuplePat σs Δ -> NamedEnv T Δ -> Env T σs :=
      fix pattern_match {σs} {Δ} p {struct p} :=
        match p with
        | tuplepat_nil => fun _ => env.nil
        | tuplepat_snoc p x =>
          fun EΔ => let (E,v) := nenv.view EΔ in
                    env.snoc (pattern_match p E) _ v
        end.

    Definition tuple_pattern_match_val {σs : Ctx Ty} {Δ : NCtx N Ty}
             (p : TuplePat σs Δ) : Val (ty.tuple σs) -> NamedEnv Val Δ :=
      fun lit => tuple_pattern_match_env p (@envrec.to_env Ty Val σs lit).

    Fixpoint record_pattern_match_env {V : Ty -> Set} {rfs : NCtx recordf Ty} {Δ : NCtx N Ty}
             (p : RecordPat rfs Δ) {struct p} : NamedEnv V rfs -> NamedEnv V Δ :=
      match p with
      | recordpat_nil => fun _ => []
      | recordpat_snoc p rf x =>
        fun E =>
          nenv.snoc
            (record_pattern_match_env p (nenv.tail E)) (x∷_)
            (nenv.lookup E ctx.in_zero)
      end.

    Fixpoint record_pattern_match_env_reverse {V : Ty -> Set} {rfs : NCtx recordf Ty} {Δ : NCtx N Ty}
             (p : RecordPat rfs Δ) {struct p} :  NamedEnv V Δ -> NamedEnv V rfs :=
      match p with
      | recordpat_nil => fun _ => nenv.nil
      | recordpat_snoc p rf x =>
        fun E =>
          nenv.snoc
            (record_pattern_match_env_reverse p (nenv.tail E)) (rf∷_)
            (nenv.lookup E ctx.in_zero)
      end.

    Lemma record_pattern_match_env_inverse_right {V : Ty -> Set} {rfs : NCtx recordf Ty} {Δ : NCtx N Ty}
          (p : RecordPat rfs Δ) (vs : NamedEnv V Δ) :
      record_pattern_match_env p (record_pattern_match_env_reverse p vs) = vs.
    Proof. induction p; env.destroy vs; cbn; now f_equal. Qed.

    Lemma record_pattern_match_env_inverse_left {V : Ty -> Set} {rfs : NCtx recordf Ty} {Δ : NCtx N Ty}
          (p : RecordPat rfs Δ) (vs : NamedEnv V rfs) :
      record_pattern_match_env_reverse p (record_pattern_match_env p vs) = vs.
    Proof. induction p; env.destroy vs; cbn; now f_equal. Qed.

    Lemma tuple_pattern_match_env_inverse_right {T : Ty -> Set}
      {σs : Ctx Ty} {Δ : NCtx N Ty} (p : TuplePat σs Δ) (ts : NamedEnv T Δ) :
      tuple_pattern_match_env p (tuple_pattern_match_env_reverse p ts) = ts.
    Proof. induction p; env.destroy ts; cbn; now f_equal. Qed.

    Lemma tuple_pattern_match_env_inverse_left {T : Ty -> Set}
          {σs : Ctx Ty} {Δ : NCtx N Ty} (p : TuplePat σs Δ) (ts : Env T σs) :
      tuple_pattern_match_env_reverse p (tuple_pattern_match_env p ts) = ts.
    Proof. induction p; env.destroy ts; cbn; now f_equal. Qed.

    Definition record_pattern_match_val {R} {Δ : NCtx N Ty}
      (p : RecordPat (recordf_ty R) Δ) : Val (ty.record R) -> NamedEnv Val Δ :=
      fun v => record_pattern_match_env p (recordv_unfold R v).

    (* A [Pattern] describes the different pattern matching possibilities.
       Not every type can be matched on, and some types can be matched on in
       different ways, e.g. bitvectors. The [Pattern], as opposed to the
       [PatternCase] below, is a value that is provided by the user in the
       program and therefore includes all the names ((program or logic
       variables) for all alternatives of that match. For example
       [pat_shape_sum] contains the names [x] and [y] for the [inl] and [inr]
       cases. *)
    Inductive Pattern : Ty -> Set :=
    | pat_var (x : N) {σ}                             : Pattern σ
    | pat_bool                                        : Pattern ty.bool
    | pat_list σ (x y : N)                            : Pattern (ty.list σ)
    | pat_pair (x y : N) {σ τ}                        : Pattern (ty.prod σ τ)
    | pat_sum σ τ (x y : N)                           : Pattern (ty.sum σ τ)
    | pat_unit                                        : Pattern ty.unit
    | pat_enum E                                      : Pattern (ty.enum E)
    | pat_bvec_split m n (x y : N)                    : Pattern (ty.bvec (m+n))
    | pat_bvec_exhaustive m                           : Pattern (ty.bvec m)
    | pat_tuple {σs Δ} (p : TuplePat σs Δ)            : Pattern (ty.tuple σs)
    | pat_record R Δ (p : RecordPat (recordf_ty R) Δ) : Pattern (ty.record R)
    | pat_union U
        (p : forall K, Pattern (unionk_ty U K))       : Pattern (ty.union U).

    (* This describes the different cases/alternatives for a single pattern
       match of a particular shape. It can be seen as a representation of the
       arity of a match. *)
    Fixpoint PatternCase {σ} (pat : Pattern σ) : Set :=
      match pat with
      | pat_var x              => unit
      | pat_bool               => bool
      | pat_list σ x y         => bool
      | pat_pair x y           => unit
      | pat_sum σ τ x y        => bool
      | pat_unit               => unit
      | pat_enum E             => enumt E
      | pat_bvec_split m n x y => unit
      | pat_bvec_exhaustive m  => bv m
      | pat_tuple p            => unit
      | pat_record R Δ p       => unit
      | pat_union U p          => { K : unionk U & PatternCase (p K) }
      end.

    #[export] Instance EqDec_PatternCase :
      forall {σ} (pat : Pattern σ), Classes.EqDec (PatternCase pat) :=
      fix eqd {σ} pat :=
        match pat return Classes.EqDec (PatternCase pat) with
        | pat_var _              => EqDecInstances.unit_EqDec
        | pat_bool               => EqDecInstances.bool_EqDec
        | pat_list _ _ _         => EqDecInstances.bool_EqDec
        | pat_pair _ _           => EqDecInstances.unit_EqDec
        | pat_sum _ _ _ _        => EqDecInstances.bool_EqDec
        | pat_unit               => EqDecInstances.unit_EqDec
        | pat_enum E             => enumt_eqdec E
        | pat_bvec_split _ _ _ _ => EqDecInstances.unit_EqDec
        | pat_bvec_exhaustive m  => bv.eqdec_bv
        | pat_tuple _            => EqDecInstances.unit_EqDec
        | pat_record _ _ _       => EqDecInstances.unit_EqDec
        | pat_union U p          => EqDecInstances.sigma_eqdec
                                      (unionk_eqdec U)
                                      (fun K => eqd (p K))
        end.

    #[export] Instance Finite_PatternCase :
      forall {σ} (pat : Pattern σ),
        finite.Finite (PatternCase pat) :=
      fix fin {σ} pat :=
        match pat as pat return finite.Finite (PatternCase pat) with
        | pat_var _              => finite.unit_finite
        | pat_bool               => Finite_bool
        | pat_list _ _ _         => Finite_bool
        | pat_pair _ _           => finite.unit_finite
        | pat_sum _ _ _ _        => Finite_bool
        | pat_unit               => finite.unit_finite
        | pat_enum E             => enumt_finite E
        | pat_bvec_split _ _ _ _ => finite.unit_finite
        | pat_bvec_exhaustive m  => bv.finite.finite_bv
        | pat_tuple _            => finite.unit_finite
        | pat_record _ _ _       => finite.unit_finite
        | pat_union U p          =>
            @Finite_sigT (unionk U) _ _
              (fun K => PatternCase (p K))
              (fun K => EqDec_PatternCase (p K))
              (fun K => fin (p K))
        end.

    (* For each [Pattern] and each [PatternCase] for that shape, calculate
       the context that represents the variables bound in that case. *)
    Fixpoint PatternCaseCtx {σ} {p : Pattern σ} : PatternCase p -> NCtx N Ty :=
      match p with
      | @pat_var x σ           => fun _ => [x∷σ]
      | pat_bool               => fun _ => [ctx]
      | pat_list σ x y         => fun b => if b then [ctx] else [x∷σ; y∷ty.list σ]
      | @pat_pair x y σ τ      => fun _ => [x∷σ; y∷τ]
      | pat_sum σ τ x y        => fun b => if b then [x∷σ] else [y∷τ]
      | pat_unit               => fun _ => [ctx]
      | pat_enum _             => fun _ => [ctx]
      | pat_bvec_split m n x y => fun _ => [x∷ty.bvec m; y∷ty.bvec n]
      | pat_bvec_exhaustive m  => fun _ => [ctx]
      | @pat_tuple _ Δ _       => fun _ => Δ
      | pat_record _ Δ _       => fun _ => Δ
      | pat_union U p          => fun '(existT K pc) => PatternCaseCtx pc
      end%ctx.

    Definition MatchResult {σ} (pat : Pattern σ) : Type :=
      { c : PatternCase pat & NamedEnv Val (PatternCaseCtx c) }.
    #[global] Arguments MatchResult {σ} !pat /.

    (* Pattern match on a value. The result is a [PatternCase] that represents
       the alternative corresponding to the value, together with an environment
       that maps the variables of the pattern to values. *)
    Fixpoint pattern_match_val {σ} (p : Pattern σ) : Val σ -> MatchResult p :=
      match p with
      | pat_var x =>
          fun v => existT tt [env].[x∷_ ↦ v]
      | pat_bool       =>
          fun b => existT b [env]
      | pat_list σ x y =>
          fun v : Val (ty.list σ) =>
            match v with
            | nil       => existT true [env]
            | cons v vs => existT false [env].[x∷σ ↦ v].[y∷ty.list σ ↦ vs]
            end
      | pat_pair x y =>
          fun '(a, b) => existT tt [env].[x∷_ ↦ a].[y∷_ ↦ b]
      | pat_sum σ τ x y =>
          fun v =>
            match v with
            | inl a => existT true [env].[x∷σ ↦ a]
            | inr b => existT false [env].[y∷τ ↦ b]
            end
      | pat_unit =>
          fun _ => existT tt [env]
      | pat_enum E =>
          fun v : enumt E => existT v [env]
      | pat_bvec_split m n x y =>
          fun v =>
            match bv.appView m n v with
            | bv.isapp xs ys =>
                existT tt ([env].[x∷ty.bvec m ↦ xs].[y∷ty.bvec n ↦ ys])
            end
      | pat_bvec_exhaustive m =>
          fun v => existT v [env]
      | pat_tuple p =>
          fun v => existT tt (tuple_pattern_match_val p v)
      | pat_record R Δ p =>
          fun v => existT tt (record_pattern_match_val p v)
      | pat_union U p =>
          fun v =>
            let (K, u)    := unionv_unfold U v in
            let (pc, δpc) := pattern_match_val (p K) u in
            (existT (existT K pc) δpc)
      end.
    #[global] Arguments pattern_match_val {σ} !p v.

    (* Reverse a pattern match. Given a [PatternCase] and an environment with
       values for all variables in the pattern, reconstruct a value. *)
    Fixpoint pattern_match_val_reverse {σ} (p : Pattern σ) :
      forall (c : PatternCase p), NamedEnv Val (PatternCaseCtx c) -> Val σ :=
      match p with
      | pat_var x      => fun _ vs => nenv.head vs
      | pat_bool       => fun b _ => b
      | pat_list σ x y =>
          fun b =>
            match b with
            | true  => fun _ => nil
            | false => fun Eht =>
                         let (Eh,t) := nenv.view Eht in
                         let (E,h)  := nenv.view Eh in
                         cons h t
            end
      | pat_pair x y =>
          fun _ Exy =>
            let (Ex,vy) := nenv.view Exy in
            let (E,vx)  := nenv.view Ex in
            (vx,vy)
      | pat_sum σ τ x y =>
          fun b =>
            match b with
            | true  => fun vs => inl (nenv.head vs)
            | false => fun vs => inr (nenv.head vs)
            end
      | pat_unit =>
          fun _ _ => tt
      | pat_enum E =>
          fun v _ => v
      | pat_bvec_split m n x y =>
          fun _ Exy =>
            let (Ex,vy) := nenv.view Exy in
            let (E,vx)  := nenv.view Ex in
            bv.app vx vy
      | pat_bvec_exhaustive m =>
          fun v _ => v
      | pat_tuple p =>
          fun _ vs => envrec.of_env (tuple_pattern_match_env_reverse p vs)
      | pat_record R Δ p =>
          fun _ vs => recordv_fold R (record_pattern_match_env_reverse p vs)
      | pat_union U p =>
          fun '(existT K pc) δpc =>
            unionv_fold U (existT K (pattern_match_val_reverse (p K) pc δpc))
      end.

    (* A curried version of the above. *)
    Definition pattern_match_val_reverse' {σ} (p : Pattern σ) :
      MatchResult p -> Val σ :=
      fun c => pattern_match_val_reverse p (projT1 c) (projT2 c).

    Lemma pattern_match_val_inverse_right' {σ} (p : Pattern σ) :
      forall (r : MatchResult p),
        pattern_match_val p (pattern_match_val_reverse' p r) = r.
    Proof.
      induction p; cbn; intros [pc vs]; try progress cbn.
      - destruct pc; now env.destroy vs.
      - env.destroy vs. reflexivity.
      - destruct pc; now env.destroy vs.
      - destruct pc; now env.destroy vs.
      - destruct pc; now env.destroy vs.
      - destruct pc; now env.destroy vs.
      - now env.destroy vs.
      - destruct pc; env.destroy vs.
        now rewrite bv.appView_app.
      - now env.destroy vs.
      - destruct pc.
        unfold tuple_pattern_match_val.
        rewrite envrec.to_of_env.
        now rewrite tuple_pattern_match_env_inverse_right.
      - destruct pc.
        unfold record_pattern_match_val.
        rewrite recordv_unfold_fold.
        now rewrite record_pattern_match_env_inverse_right.
      - destruct pc as [K pc].
        rewrite unionv_unfold_fold.
        change (pattern_match_val_reverse _ ?pc ?vs) with
          (pattern_match_val_reverse' _ (existT pc vs)).
        now rewrite H.
    Qed.

    Lemma pattern_match_val_inverse_right {σ} (pat : Pattern σ)
      (pc : PatternCase pat) (δpc : NamedEnv Val (PatternCaseCtx pc)) :
      pattern_match_val pat (pattern_match_val_reverse pat pc δpc) = (existT pc δpc).
    Proof. apply (pattern_match_val_inverse_right' pat (existT pc δpc)). Qed.

    Lemma pattern_match_val_inverse_left {σ} (pat : Pattern σ) :
      forall v : Val σ,
        pattern_match_val_reverse' pat (pattern_match_val pat v) = v.
    Proof.
      induction pat; cbn; intros v; try progress cbn.
      - reflexivity.
      - reflexivity.
      - destruct v; reflexivity.
      - destruct v; reflexivity.
      - destruct v; reflexivity.
      - destruct v; reflexivity.
      - reflexivity.
      - destruct bv.appView; reflexivity.
      - reflexivity.
      - unfold tuple_pattern_match_val.
        rewrite tuple_pattern_match_env_inverse_left.
        now rewrite envrec.of_to_env.
      - unfold record_pattern_match_val.
        rewrite record_pattern_match_env_inverse_left.
        now rewrite recordv_fold_unfold.
      - destruct unionv_unfold as [K v'] eqn:Heq.
        apply (f_equal (unionv_fold U)) in Heq.
        rewrite unionv_fold_unfold in Heq. subst.
        destruct pattern_match_val eqn:Heq; cbn.
        change (pattern_match_val_reverse _ ?pc ?vs) with
          (pattern_match_val_reverse' _ (existT pc vs)).
        now rewrite <- Heq, H.
    Qed.

    (* The intendend use case of the above definitions is in the declaration of
       inductive types for AST that represent pattern matches. This will
       generally be of the form

         | my_sort_pattern_match {σ} (scrutinee : ... σ) (p : Pattern σ)
             (k : forall pc : PatternCase p, MySort (Γ ▻▻ PatternCaseCtx pc) ) :
             MySort Γ

       That is, we have a scrutinee represented using some sort, a pattern of
       the same type as the scrutinee and then for every case (there is only a
       finite amount of cases for each pattern), we have a right hand side. This
       scheme makes sure that Coq can derive good elimination schemes. However,
       the PatternCase type is unwieldy for writing down syntax terms. One of
       the problems is that for patterns of arity one a superfluous unit
       argument is introduced. More aggravating is the fact that for patterns of
       (multi-level) matches on unions the constructors are bundled together in
       a telescopic form in PatternCase. To write down such a match, the user
       would have to pattern match on the constructor of a sigma type,
       generalize over the second component again (i.e. revert), and then
       pattern on the first component, i.e. the union constructor. To avoid this
       burden on the user we define alternative versions that uncurry the
       telescope and also remove superfluous arguments.
     *)


    Section NewAlternative.
      Context {R : NCtx N Ty -> Type} {Γ : NCtx N Ty}.

      Fixpoint PatternCaseCurried {σ} (pat : Pattern σ) : Type :=
        match pat with
        | @pat_var x σ => R (Γ ▻ x∷σ)
        | pat_bool => bool -> R Γ
        | pat_list σ0 x y => (R Γ * R (Γ ▻ x∷σ0 ▻ y∷ty.list σ0))%type
        | @pat_pair x y σl σr => R (Γ ▻ x∷σl ▻ y∷σr)
        | pat_sum σ0 τ0 x y => (R (Γ ▻ x∷σ0) * R (Γ ▻ y∷τ0))%type
        | pat_unit => R Γ
        | pat_enum E => enumt E -> R Γ
        | pat_bvec_split m n x y => R (Γ ▻ x∷ty.bvec m ▻ y∷ty.bvec n)
        | pat_bvec_exhaustive m => bv m -> R Γ
        | @pat_tuple _ Δ _ => R (Γ ▻▻ Δ)
        | pat_record _ Δ _ => R (Γ ▻▻ Δ)
        | pat_union U p => forall K : unionk U, PatternCaseCurried (p K)
        end.

      (* Uncurry the representation of different cases to the curried functional
         form. *)
      Fixpoint of_pattern_case_curried {σ} (pat : Pattern σ) {struct pat} :
        PatternCaseCurried pat -> forall pc : PatternCase pat, R (Γ ▻▻ PatternCaseCtx pc) :=
        match pat with
        | pat_var x => fun rhs _ => rhs
        | pat_bool => fun rhs => rhs
        | pat_list σ0 x y => fun '(a,b) pc =>
                                     match pc with true => a | false => b end
        | pat_pair x y => fun rhs _ => rhs
        | pat_sum _ _ x y => fun '(a,b) pc =>
                                     match pc with true => a | false => b end
        | pat_unit => fun rhs _ => rhs
        | pat_enum E => fun rhs => rhs
        | pat_bvec_split m n x y => fun rhs _ => rhs
        | pat_bvec_exhaustive m => fun rhs => rhs
        | @pat_tuple _ Δ _ => fun rhs _ => rhs
        | pat_record _ Δ _ => fun rhs _ => rhs
        | pat_union U p0 => fun rhs '(existT K pc) =>
                              of_pattern_case_curried (p0 K) (rhs K) pc
        end.

      Record Alternative (σ : Ty) : Type :=
        MkAlt
          { alt_pat : Pattern σ;
            alt_rhs : PatternCaseCurried alt_pat;
          }.

    End NewAlternative.
    #[global] Arguments Alternative : clear implicits.
    #[global] Arguments MkAlt {R Γ σ} _ & _.
    #[global] Arguments alt_pat {R Γ σ} _.
    #[global] Arguments alt_rhs {R Γ σ} _.

  End Patterns.

  Section Freshen.
    Abbreviation LCtx := (NCtx LVar Ty).
    Context {N : Set} (n : N -> LVar).

    (* Freshen the name of the variables in a given named context [Δ]. The type
       of variables is also changed to logic variables, which covers all the
       cases where we currently do freshening. The first parameter [Σ] are all
       the logic variables that we consider to be in scope. Freshened variables
       from [Δ] are also added to [Σ] to pick a disjoint set of fresh
       variables. *)
    Fixpoint freshen_ctx (Σ : LCtx) (Δ : NCtx N Ty) : LCtx :=
      match Δ with
      | [ctx]   => [ctx]
      | Γ ▻ x∷σ => let Γ' := freshen_ctx Σ Γ in
                   (* TOneverDO: Always doing the concatenation of Σ and Γ'
                      is not very efficient. This has quadratic runtime in the
                      length of the context, i.e. the number of variables in
                      a pattern. *)
                   let x' := fresh_lvar (Σ ▻▻ Γ') (Some (n x)) in Γ' ▻ x'∷σ
      end.

    (* Translate an environment for an freshened context, i.e. unfreshened keys
       of a map from varaibles to stuff of type [D], back to an environment
       for unfreshened keys. *)
    Definition unfreshen_namedenv {D : Ty -> Set} :
      forall {Σ : LCtx} {Δ : NCtx N Ty},
        NamedEnv D (freshen_ctx Σ Δ) -> NamedEnv D Δ :=
      fix un Σ Δ :=
        match Δ with
        | [ctx] => fun _   => [env]
        | Γ ▻ b => fun EΓb : let Γ' := freshen_ctx Σ Γ in
                             NamedEnv D (Γ' ▻ fresh_lvar (Σ ▻▻ Γ') _∷_) =>
                     let (EΓ,tb) := nenv.view EΓb in
                     nenv.snoc (un Σ _ EΓ) b tb
        end.

    Definition freshen_namedenv {D : Ty -> Set} :
      forall {Σ : LCtx} {Δ : NCtx N Ty},
        NamedEnv D Δ -> NamedEnv D (freshen_ctx Σ Δ) :=
      fix fr {Σ Δ} (E : NamedEnv D Δ) {struct E} :=
        match E in NamedEnv _ Δ return NamedEnv D (freshen_ctx Σ Δ) with
        | [env]       => [env]
        | E ► (b ↦ d) =>
            let E' := fr E in
            let x' := fresh_lvar _ _ in
            E'.[x'∷type b ↦ d]
        end.

    (* Traverse a tuple pattern to freshen all variables inside it. The
       context index [Δ] is freshened according to witness the change. *)
    Fixpoint freshen_tuplepat (Σ : LCtx) {σs Δ} (p : @TuplePat N σs Δ) :
      TuplePat σs (freshen_ctx Σ Δ) :=
      match p with
      | tuplepat_nil        => tuplepat_nil
      | tuplepat_snoc pat x =>
          tuplepat_snoc
            (freshen_tuplepat Σ pat)
            (fresh_lvar (Σ ▻▻ freshen_ctx Σ _) (Some (n x)))
      end.

    (* Traverse a record pattern to freshen all variables inside it. The
       context index [Δ] is freshened according to witness the change. *)
    Fixpoint freshen_recordpat (Σ : LCtx) {rfs Δ} (p : @RecordPat N rfs Δ) :
      RecordPat rfs (freshen_ctx Σ Δ) :=
      match p with
      | recordpat_nil           => recordpat_nil
      | recordpat_snoc pat rf x =>
          recordpat_snoc
            (freshen_recordpat Σ pat) rf
            (fresh_lvar (Σ ▻▻ freshen_ctx Σ _) (Some (n x)))
      end.

    (* Freshen a pattern and transform it to a pattern using logic variables
       instead of [N]. Patterns, unlike record or tuple patterns, are not
       indexed by their context of bound variables, since that is dependent
       on the case. However, the pattern contains the variables names for all
       cases, which are freshened. *)
    Fixpoint freshen_pattern (Σ : LCtx) {σ} (p : Pattern (N:=N) σ) :
      Pattern (N:=LVar) σ :=
      match p in (Pattern t) return (Pattern t) with
      | pat_var x              => pat_var (fresh_lvar Σ (Some (n x)))
      | pat_bool               => pat_bool
      | pat_list σ x y         => let x' := fresh_lvar Σ (Some (n x)) in
                                  let y' := fresh_lvar (Σ▻x'∷σ) (Some (n y)) in
                                  pat_list σ x' y'
      | @pat_pair _ x y σ τ    => let x' := fresh_lvar Σ (Some (n x)) in
                                  let y' := fresh_lvar (Σ▻x'∷σ) (Some (n y)) in
                                  pat_pair x' y'
      | pat_sum σ τ x y        => pat_sum σ τ
                                    (fresh_lvar Σ (Some (n x)))
                                    (fresh_lvar Σ (Some (n y)))
      | pat_unit               => pat_unit
      | pat_enum E             => pat_enum E
      | pat_bvec_split m _ x y =>
          let x' := fresh_lvar Σ (Some (n x)) in
          let y' := fresh_lvar (Σ▻x'∷ty.bvec m) (Some (n y)) in
          pat_bvec_split m _ x' y'
      | pat_bvec_exhaustive m  => pat_bvec_exhaustive m
      | pat_tuple p            => pat_tuple (freshen_tuplepat Σ p)
      | pat_record R Δ p       => pat_record R
                                    (freshen_ctx Σ Δ)
                                    (freshen_recordpat Σ p)
      | pat_union U p          => pat_union U (fun K => freshen_pattern Σ (p K))
      end.

    (* The user will usually have written a function for all cases of a pattern
       [pat]:

         (forall pc : PatternCase pat, ... )

       However, for the freshened pattern we need to provide a function of type

         (forall pc : PatternCase (freshen_pattern Σ pat), ...)

       To use the user function, the following definition translates cases for a
       freshened pattern back and forth to cases on an unfreshened pattern. *)
    Fixpoint unfreshen_patterncase (Σ : LCtx) {σ} (p : Pattern (N:=N) σ) :
      PatternCase (freshen_pattern Σ p) -> PatternCase p :=
      match p with
      | pat_var _              => fun pc => pc
      | pat_bool               => fun pc => pc
      | pat_list _ _ _         => fun pc => pc
      | pat_pair _ _           => fun pc => pc
      | pat_sum _ _ _ _        => fun pc => pc
      | pat_unit               => fun pc => pc
      | pat_enum E             => fun pc => pc
      | pat_bvec_split _ _ _ _ => fun pc => pc
      | pat_bvec_exhaustive m  => fun pc => pc
      | pat_tuple _            => fun pc => pc
      | pat_record _ _ _       => fun pc => pc
      | pat_union U p          => fun '(existT K pc) =>
                                    @existT _
                                      (fun K => PatternCase (p K)) K
                                      (unfreshen_patterncase Σ (p K) pc)
      end.

    Fixpoint freshen_patterncase (Σ : LCtx) {σ} (p : Pattern (N:=N) σ) :
      PatternCase p -> PatternCase (freshen_pattern Σ p) :=
      match p with
      | pat_var _              => fun pc => pc
      | pat_bool               => fun pc => pc
      | pat_list _ _ _         => fun pc => pc
      | pat_pair _ _           => fun pc => pc
      | pat_sum _ _ _ _        => fun pc => pc
      | pat_unit               => fun pc => pc
      | pat_enum E             => fun pc => pc
      | pat_bvec_split _ _ _ _ => fun pc => pc
      | pat_bvec_exhaustive m  => fun pc => pc
      | pat_tuple _            => fun pc => pc
      | pat_record _ _ _       => fun pc => pc
      | pat_union U p          =>
             fun Kpc : {K : unionk U & PatternCase (p K)} =>
               let (K,pc) := Kpc in
               (existT K (freshen_patterncase Σ (p K) pc))
      end.

    (* The context of bound variables of a variable is the same as calculating
       the variables of the unfreshened pattern case and "refreshen" the
       result. *)
    Fixpoint freshen_patterncasectx (Σ : LCtx) {σ} (p : Pattern (N:=N) σ) :
      forall pc : PatternCase (freshen_pattern Σ p),
        PatternCaseCtx pc =
        freshen_ctx Σ (PatternCaseCtx (unfreshen_patterncase Σ p pc)) :=
      match p with
      | pat_var _              => fun _ => eq_refl
      | pat_bool               => fun _ => eq_refl
      | pat_list _ _ _         => fun pc => match pc with
                                            | true => eq_refl
                                            | false => eq_refl
                                            end
      | pat_pair _ _           => fun _ => eq_refl
      | pat_sum _ _ _ _        => fun pc => match pc with
                                            | true => eq_refl
                                            | false => eq_refl
                                            end
      | pat_unit               => fun _ => eq_refl
      | pat_enum _             => fun _ => eq_refl
      | pat_bvec_split _ _ _ _ => fun _ => eq_refl
      | pat_bvec_exhaustive m  => fun _ => eq_refl
      | pat_tuple _            => fun _ => eq_refl
      | pat_record _ _ _       => fun _ => eq_refl
      | pat_union _ p          => fun '(existT K pc) =>
                                    freshen_patterncasectx Σ (p K) pc
      end.

    (* Transports an environment for a freshened pattern case back. Use the
       equivalent function below which avoids the rewrite. *)
    Definition unfreshen_patterncaseenv' {D : Ty -> Set} {Σ σ} (p : Pattern (N:=N) σ) :
      forall (pc : PatternCase (freshen_pattern Σ p)),
        NamedEnv D (PatternCaseCtx pc) ->
        NamedEnv D (PatternCaseCtx (unfreshen_patterncase Σ p pc)) :=
      fun pc E =>
        unfreshen_namedenv
          (eq_rect _ (NamedEnv D) E _ (freshen_patterncasectx Σ p pc)).

    Fixpoint freshen_patterncaseenv {D : Ty -> Set} {Σ σ} (p : Pattern (N:=N) σ) :
      forall (pc : PatternCase p),
        NamedEnv D (PatternCaseCtx pc) ->
        NamedEnv D (PatternCaseCtx (freshen_patterncase Σ p pc)) :=
      match p with
      | pat_var _ => fun ps ts => let (_,t) := nenv.view ts in [nenv t]
      | pat_bool => fun _ _   => [env]
      | pat_list σ x y =>
          fun pc => match pc with
                    | true  => fun _  => [env]
                    | false => fun ts => let (ts1,t) := nenv.view ts in
                                         let (_,h)   := nenv.view ts1 in
                                         [nenv h; t]
                    end
      | pat_pair x y =>
          fun _ ts =>
            let (ts1,v) := nenv.view ts in
            let (_,v0) := nenv.view ts1 in
            [nenv v0; v]
      | pat_sum σ τ x y =>
          fun pc =>
            match pc with
            | true  => fun ts => let (_,v) := nenv.view ts in [nenv v]
            | false => fun ts => let (_,v) := nenv.view ts in [nenv v]
            end
      | pat_unit   => fun _ _ => [env]
      | pat_enum E => fun _ _ => [env]
      | pat_bvec_split m n x y =>
          fun _ ts =>
            let (ts1,vy) := nenv.view ts in
            let (_,vx)   := nenv.view ts1 in
            [env].[_∷ty.bvec m ↦ vx].[_∷ty.bvec n ↦ vy]
      | pat_bvec_exhaustive _ => fun _ _ => [env]
      | pat_tuple _ => fun _ => freshen_namedenv
      | pat_record _ Δ _ => fun _ => freshen_namedenv
      | pat_union U p => fun '(existT K pc) => freshen_patterncaseenv (p K) pc
      end.

    Fixpoint unfreshen_patterncaseenv {D : Ty -> Set} {Σ σ} (p : Pattern (N:=N) σ) :
      forall (pc : PatternCase (freshen_pattern Σ p)),
        NamedEnv D (PatternCaseCtx pc) ->
        NamedEnv D (PatternCaseCtx (unfreshen_patterncase Σ p pc)) :=
      match p with
      | pat_var _ => fun ps ts => let (_,t) := nenv.view ts in [nenv t]
      | pat_bool => fun _ _   => [env]
      | pat_list σ x y =>
          fun pc => match pc with
                    | true  => fun _  => [env]
                    | false => fun ts => let (ts1,t) := nenv.view ts in
                                         let (_,h)   := nenv.view ts1 in
                                         [nenv h; t]
                    end
      | pat_pair x y =>
          fun _ ts =>
            let (ts1,v) := nenv.view ts in
            let (_,v0) := nenv.view ts1 in
            [nenv v0; v]
      | pat_sum σ τ x y =>
          fun pc =>
            match pc with
            | true  => fun ts => let (_,v) := nenv.view ts in [nenv v]
            | false => fun ts => let (_,v) := nenv.view ts in [nenv v]
            end
      | pat_unit   => fun _ _ => [env]
      | pat_enum E => fun _ _ => [env]
      | pat_bvec_split m n x y =>
          fun _ ts =>
            let (ts1,vy) := nenv.view ts in
            let (_,vx)   := nenv.view ts1 in
            [env].[x∷ty.bvec m ↦ vx].[y∷ty.bvec n ↦ vy]
      | pat_bvec_exhaustive _ => fun _ _ => [env]
      | pat_tuple _ => fun _ => unfreshen_namedenv
      | pat_record _ Δ _ => fun _ => unfreshen_namedenv
      | pat_union U p => fun '(existT K pc) => unfreshen_patterncaseenv (p K) pc
      end.

    Definition freshen_matchresult {Σ σ} (p : Pattern (N:=N) σ) (r : MatchResult p) :
      MatchResult (freshen_pattern Σ p) :=
      let (pc, vs) := r in
      existT (freshen_patterncase Σ p pc) (freshen_patterncaseenv p pc vs).

    Definition unfreshen_matchresult {Σ σ} (p : Pattern (N:=N) σ)
      (r : MatchResult (freshen_pattern Σ p)) : MatchResult p :=
      let (pc, vs) := r in
      existT (unfreshen_patterncase Σ p pc) (unfreshen_patterncaseenv p pc vs).

    Lemma pattern_match_val_freshen {Σ : LCtx} {σ} (p : Pattern (N:=N) σ) (v : Val σ) :
      unfreshen_matchresult p (pattern_match_val (freshen_pattern Σ p) v) =
      pattern_match_val p v.
    Proof.
      induction p; cbn;
        repeat
          match goal with
          | |- _ = match ?v with _ => _ end =>
              is_var v; destruct v; try progress cbn
          end; f_equal; auto.
      - now destruct bv.appView.
      - unfold tuple_pattern_match_val.
        induction p; cbn; f_equal; auto.
      - unfold record_pattern_match_val.
        generalize (recordv_unfold R v); intros ts.
        induction p; cbn; f_equal; auto.
      - destruct unionv_unfold as [K u]. clear v.
        rewrite <- H. now destruct pattern_match_val.
    Qed.

  End Freshen.

  Bind Scope pat_scope with TuplePat.
  Bind Scope pat_scope with RecordPat.
  Bind Scope pat_scope with Pattern.

End PatternsOn.
