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
     Bool.Bool.
From iris Require bi.interface.
From Katamaran Require Import
     Base
     Notations
     Prelude
     Symbolic.Worlds
     Syntax.Chunks
     Syntax.Formulas
     Syntax.Predicates.

Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.

Module Type AssertionsOn
  (Import GLOBAL : GlobalState)
  (Import P      : PredicateKit GLOBAL)
  (Import W      : WorldsMixin GLOBAL P).
Module Import asn.

  Local Obligation Tactic := idtac.

  Inductive Assertion (Σ : LCtx) : Type :=
  | formula (fml : Formula Σ)
  | chunk (c : Chunk Σ)
  | chunk_angelic (c : Chunk Σ)
  | pattern_match {σ} (s : Term Σ σ) (pat : Pattern σ)
      (rhs : forall (pc : PatternCase pat), Assertion (Σ ▻▻ PatternCaseCtx pc))
  | sep  (A1 A2 : Assertion Σ)
  | or   (A1 A2 : Assertion Σ)
  | exist (ς : LVar) (τ : Ty) (a : Assertion (Σ ▻ ς∷τ))
  | debug.

  Definition match_bool {Σ} (b : Term Σ ty.bool) (A1 A2 : Assertion Σ) : Assertion Σ :=
    pattern_match b pat_bool (fun v => if v then A1 else A2).
  Definition match_enum {Σ} (E : enumi) (k : Term Σ (ty.enum E)) (alts : forall (K : enumt E), Assertion Σ) : Assertion Σ :=
    pattern_match k (pat_enum E) alts.
  Definition match_sum {Σ} (σ τ : Ty) (s : Term Σ (ty.sum σ τ)) (xl : LVar)
    (al : Assertion (Σ ▻ xl∷σ)) (xr : LVar) (ar : Assertion (Σ ▻ xr∷τ)) :
    Assertion Σ :=
    pattern_match s (pat_sum _ _ xl xr)
      (fun b => match b with true => al | false => ar end).
  Definition match_list {Σ σ} (s : Term Σ (ty.list σ)) (anil : Assertion Σ)
    (xh xt : LVar) (acons : Assertion (Σ ▻ xh∷σ ▻ xt∷ty.list σ)) : Assertion Σ :=
    pattern_match s (pat_list σ xh xt)
      (fun b => match b with true => anil | false => acons end).
  Definition match_prod {Σ σ1 σ2} (s : Term Σ (ty.prod σ1 σ2)) (xl xr : LVar)
    (rhs : Assertion (Σ ▻ xl∷σ1 ▻ xr∷σ2)) : Assertion Σ :=
    pattern_match s (pat_pair xl xr) (fun _ => rhs).
  Definition match_tuple {Σ σs Δ} (s : Term Σ (ty.tuple σs))
    (p : TuplePat σs Δ) (rhs : Assertion (Σ ▻▻ Δ)) : Assertion Σ :=
    pattern_match s (pat_tuple p) (fun _ => rhs).
  Definition match_record {Σ R Δ} (s : Term Σ (ty.record R))
    (p : RecordPat (recordf_ty R) Δ) (rhs : Assertion (Σ ▻▻ Δ)) : Assertion Σ :=
    pattern_match s (pat_record R Δ p) (fun _ => rhs).

  #[global] Arguments match_enum [_] E _ _.
  #[global] Arguments match_sum [_] σ τ _ _ _.
  #[global] Arguments match_list [_] {σ} s anil xh xt acons.
  #[global] Arguments match_prod [_] {σ1 σ2} s xl xr rhs.
  #[global] Arguments match_tuple [_] {σs Δ} s p rhs.
  #[global] Arguments match_record [_] R {Δ} s p rhs.
  #[global] Arguments exist [_] _ _ _.
  #[global] Arguments debug {_}.

  Definition match_union_alt {Σ} U (t : Term Σ (ty.union U))
    (alts : forall (K : unionk U), Alternative Assertion Σ (unionk_ty U K)) : Assertion Σ :=
    pattern_match t (pat_union U (fun K => alt_pat (alts K)))
      (fun '(existT K pc) =>
         of_pattern_case_curried
           (alt_pat (alts K))
           (alt_rhs (alts K)) pc).
  #[global] Arguments asn.match_union_alt {Σ} _ _ _.

  Fixpoint exs {Σ} Δ : Assertion (Σ ▻▻ Δ) -> Assertion Σ :=
    match Δ return Assertion (Σ ▻▻ Δ) -> Assertion Σ with
    | ctx.nil => fun A => A
    | ctx.snoc Γ (x :: τ) =>
      fun A =>
        @exs Σ Γ (exist x τ A)
    end.

  #[export] Instance sub_assertion : Subst Assertion :=
    fix sub_assertion {Σ1} (A : Assertion Σ1) {Σ2} (ζ : Sub Σ1 Σ2) {struct A} : Assertion Σ2 :=
      match A with
      | formula fml => formula (subst fml ζ)
      | chunk c => chunk (subst c ζ)
      | chunk_angelic c => chunk_angelic (subst c ζ)
      | pattern_match s pat rhs =>
        pattern_match (subst s ζ) pat (fun pc => sub_assertion (rhs pc) (sub_up ζ _))
      | sep A1 A2 => sep (sub_assertion A1 ζ) (sub_assertion A2 ζ)
      | or A1 A2  => sep (sub_assertion A1 ζ) (sub_assertion A2 ζ)
      | exist ς τ A => exist ς τ (sub_assertion A (sub_up1 ζ))
      | debug => debug
      end.

  (* TODO: This instance is currently unused and incomplete. Do not use. *)
  Import option.notations.
  #[local] Instance OccursCheckAssertion :
    OccursCheck Assertion :=
    fix occurs Σ b (bIn : b ∈ Σ) (asn : Assertion Σ) : option (Assertion (Σ - b)) :=
      match asn with
      | formula fml => option.map (@formula _) (occurs_check bIn fml)
      | chunk c     => option.map (@chunk _) (occurs_check bIn c)
      | chunk_angelic c => option.map (@chunk_angelic _) (occurs_check bIn c)
      | pattern_match s pat rhs =>
          s' <- occurs_check bIn s;;
          None (* TODO *)
      | sep A1 A2 =>
          A1' <- occurs _ _ bIn A1 ;;
          A2' <- occurs _ _ bIn A2 ;;
          Some (sep A1' A2')
      | or A1 A2  =>
          A1' <- occurs _ _ bIn A1 ;;
          A2' <- occurs _ _ bIn A2 ;;
          Some (or A1' A2')
      | exist ς τ A => option_map (@exist _ ς τ) (occurs _ _ (ctx.in_succ bIn) A)
      | debug => Some debug
      end.

  Fixpoint is_pure {Σ} (a : Assertion Σ) : bool :=
    match a with
    | formula fml => true
    | chunk c => false
    | chunk_angelic c => false
    | pattern_match s pat rhs =>
        List.forallb (fun pc => is_pure (rhs pc)) (finite.enum (PatternCase pat))
    | sep A1 A2 => is_pure A1 && is_pure A2
    | or A1 A2  => is_pure A1 && is_pure A2
    | exist ς τ A => is_pure A
    | debug => true
  end.

  Section Interpretation.
    (* Import iris.bi.interface. *)
    (* Import iris.bi.derived_laws. *)
    (* Import iris.bi.extensions. *)
    Import iris.proofmode.proofmode.

    Fixpoint interpret_pure {Σ} (a : Assertion Σ) (ι : Valuation Σ) : Prop :=
      match a with
      | formula F => instprop F ι
      | chunk c => False
      | chunk_angelic c => False
      | pattern_match s pat rhs =>
        let v := inst (T := fun Σ => Term Σ _) s ι in
        let (pc,δpc) := pattern_match_val pat v in
        interpret_pure (rhs pc) (ι ►► δpc)
      | sep A1 A2 => interpret_pure A1 ι /\ interpret_pure A2 ι
      | or A1 A2  => interpret_pure A1 ι \/ interpret_pure A2 ι
      | exist ς τ A => exists (v : Val τ), interpret_pure A (ι ► (ς∷τ ↦ v))
      | debug => True
    end.

    Context {PROP : bi} {biA : BiAffine PROP} {PI : PredicateDef PROP}.

    Fixpoint interpret {Σ} (A : Assertion Σ) (ι : Valuation Σ) : PROP :=
      match A with
      | formula F => ⌜instprop F ι⌝ ∧ emp
      | chunk c => interpret_chunk c ι
      | chunk_angelic c => interpret_chunk c ι
      | pattern_match s pat rhs =>
        let v := inst (T := fun Σ => Term Σ _) s ι in
        let (pc,δpc) := pattern_match_val pat v in
        interpret (rhs pc) (ι ►► δpc)
      | sep A1 A2 => interpret A1 ι ∗ interpret A2 ι
      | or A1 A2  => interpret A1 ι ∨ interpret A2 ι
      | exist ς τ A => ∃ (v : Val τ), interpret A (ι ► (ς∷τ ↦ v))
      | debug => emp
    end%I.

    Lemma interpret_pure_equiv {Σ} (a : Assertion Σ) (a_pure : is_pure a = true) :
      forall (ι : Valuation Σ),
        interpret a ι ⊣⊢ ⌜interpret_pure a ι⌝.
    Proof.
      induction a; cbn in *; intros ι; try discriminate a_pure.
      - now rewrite bi.and_emp.
      - destruct pattern_match_val.
        apply H. rewrite List.forallb_forall in a_pure. apply a_pure.
        apply base.list_elem_of_In. apply finite.elem_of_enum.
      - apply andb_true_iff in a_pure. destruct a_pure as [H1 H2].
        now rewrite (IHa1 H1) (IHa2 H2) -bi.persistent_and_sep bi.pure_and.
      - apply andb_true_iff in a_pure. destruct a_pure as [H1 H2].
        now rewrite (IHa1 H1) (IHa2 H2) bi.pure_or.
      - setoid_rewrite IHa; auto. now rewrite -bi.pure_exist.
      - now rewrite bi.True_emp.
    Qed.

  End Interpretation.

  Module notations.
    Open Scope asn_scope.

    Notation "r ↦ val" := (chunk (chunk_ptsreg r val)) (at level 70) : asn_scope.
    Notation "P ∗ Q" := (sep P Q) : asn_scope.
    Notation "∃ w , A" := (exist w _ A) (at level 79, right associativity) : asn_scope.
    Notation "P ∨ Q" := (or P Q) : asn_scope.
    Notation "⊤" := (formula (formula_bool (term_val ty.bool true))) : asn_scope.
    Notation "⊥" := (formula (formula_bool (term_val ty.bool false))) : asn_scope.
    Notation "'if:' c 'then' A1 'else' A2" := (match_bool c A1 A2)
      (at level 200, format
       "'[hv' 'if:'  c  '/' '[' 'then'  A1  ']' '/' '[' 'else'  A2 ']' ']'"
      ) : asn_scope.
    Notation "x = y" := (formula (formula_relop bop.eq x y)) (x in scope term_scope, y in scope term_scope) : asn_scope .
    Notation "x != y" := (formula (formula_relop bop.neq x y)) (x in scope term_scope, y in scope term_scope) : asn_scope .
    Notation "x >= y" := (formula (formula_relop bop.le y x)) (x in scope term_scope, y in scope term_scope) : asn_scope.
    Notation "x > y" := (formula (formula_relop bop.lt y x)) (x in scope term_scope, y in scope term_scope) : asn_scope.
    Notation "x <= y" := (formula (formula_relop bop.le x y)) (x in scope term_scope, y in scope term_scope) : asn_scope.
    Notation "x < y" := (formula (formula_relop bop.lt x y)) (x in scope term_scope, y in scope term_scope) : asn_scope.
    Notation "x = y" := (formula (formula_relop bop.eq x y)) (x in scope term_scope, y in scope term_scope) : asn_scope.
    Notation "x >=ˢ y" := (formula (formula_relop bop.bvsle y x)) (x in scope term_scope, y in scope term_scope) : asn_scope.
    Notation "x >ˢ y" := (formula (formula_relop bop.bvslt y x)) (x in scope term_scope, y in scope term_scope) : asn_scope.
    Notation "x <=ˢ y" := (formula (formula_relop bop.bvsle x y)) (x in scope term_scope, y in scope term_scope) : asn_scope.
    Notation "x <ˢ y" := (formula (formula_relop bop.bvslt x y)) (x in scope term_scope, y in scope term_scope) : asn_scope.
    Notation "x >=ᵘ y" := (formula (formula_relop bop.bvule y x)) (x in scope term_scope, y in scope term_scope) : asn_scope.
    Notation "x >ᵘ y" := (formula (formula_relop bop.bvult y x)) (x in scope term_scope, y in scope term_scope) : asn_scope.
    Notation "x <=ᵘ y" := (formula (formula_relop bop.bvule x y)) (x in scope term_scope, y in scope term_scope) : asn_scope.
    Notation "x <ᵘ y" := (formula (formula_relop bop.bvult x y)) (x in scope term_scope, y in scope term_scope) : asn_scope.
    Notation "x - y" := (term_binop bop.minus x y) (x in scope term_scope, y in scope term_scope) : term_scope.
    Notation "x + y" := (term_binop bop.plus x y) (x in scope term_scope, y in scope term_scope) : term_scope.
    Notation "x * y" := (term_binop bop.times x y) (x in scope term_scope, y in scope term_scope) : term_scope.

    Notation "'match:' e 'in' R 'with' [ x ; y ; .. ; z ] => rhs 'end'" :=
      (match_record R e%term
         (recordpat_snoc .. (recordpat_snoc (recordpat_snoc recordpat_nil _ x) _ y) .. _ z)
         rhs%asn)
      (format "'[hv' 'match:'  e  'in'  R  'with'  '/  ' [ x ; y ; .. ; z ]  =>  '/    ' rhs  '/' 'end' ']'") : asn_scope.

  End notations.

End asn.
Export asn ( Assertion ).
Bind Scope asn_scope with Assertion.

Section Contracts.
  #[local] Existing Instance OccursCheckAssertion.

  Record SepContract (Δ : PCtx) (τ : Ty) : Type :=
    MkSepContract
      { sep_contract_logic_variables  : LCtx;
        sep_contract_localstore       : SStore Δ sep_contract_logic_variables;
        sep_contract_precondition     : Assertion sep_contract_logic_variables;
        sep_contract_result           : LVar;
        sep_contract_postcondition    : Assertion (sep_contract_logic_variables ▻ sep_contract_result∷τ);
      }.

  #[global] Arguments MkSepContract : clear implicits.

  Record Lemma (Δ : PCtx) : Type :=
    MkLemma
      { lemma_logic_variables  : LCtx;
        lemma_patterns         : SStore Δ lemma_logic_variables;
        lemma_precondition     : Assertion lemma_logic_variables;
        lemma_postcondition    : Assertion lemma_logic_variables;
      }.

  #[global] Arguments MkLemma : clear implicits.

  Open Scope lazy_bool_scope.

  (* This function is used as part of the linter, which checks that all
     logic variables of the contract are in fact used in the pattern or
     the precondition. It essentially performs an occurs check, albeit with
     a boolean result.
   *)
  Fixpoint lint_assertion {Σ b} (bIn : b ∈ Σ) (asn : Assertion Σ) : bool :=
    match asn with
    | formula fml => option.isNone (occurs_check bIn fml)
    | chunk c     => option.isNone (option.map (@chunk _) (occurs_check bIn c))
    | chunk_angelic c => option.isNone (option.map (@chunk_angelic _) (occurs_check bIn c))
    | pattern_match s pat rhs =>
        option.isNone (occurs_check bIn s) |||
        List.existsb
          (fun pc => lint_assertion
                       (ctx.in_cat_left (PatternCaseCtx pc) bIn)
                       (rhs pc))
          (finite.enum (PatternCase pat))
    | sep A1 A2 =>
        lint_assertion bIn A1 |||
        lint_assertion bIn A2
    | or A1 A2  =>
        lint_assertion bIn A1 |||
        lint_assertion bIn A2
    | exist ς τ A =>
        lint_assertion (ctx.in_succ bIn) A
    | debug => false
    end.

  Definition lint_contract {Δ σ} (c : SepContract Δ σ) : bool :=
    match c with
    | {| sep_contract_logic_variables := Σ;
         sep_contract_localstore      := δ;
         sep_contract_precondition    := pre
      |} =>
      ctx.forallb Σ
        (fun b bIn =>
           option.isNone (occurs_check bIn δ) |||
           lint_assertion bIn pre)
    end.

  Definition lint_lemma {Δ} (l : Lemma Δ) : bool :=
    match l with
    | {| lemma_logic_variables := Σ;
         lemma_patterns        := δ;
         lemma_precondition    := pre
      |} =>
      ctx.forallb Σ
        (fun b bIn =>
           option.isNone (occurs_check bIn δ) |||
           lint_assertion bIn pre)
    end.

  Definition Linted {Δ σ} (c : SepContract Δ σ) : Prop :=
    lint_contract c = true.

  (* Notation "'CONTRACT' 'VARS' Σ 'PATS' δ 'REQ' pre 'RES' res 'ENS' post" := (@MkSepContract _ _ Σ δ pre res post) *)
  (*   (at level 200, *)
  (*    format "'[v  ' 'CONTRACT' '/' '[' 'VARS'  Σ ']' '/' '[' 'PATS'  δ ']' '/' '[' 'REQ'   pre ']' '/' '[' 'RES'   res ']' '/' '[' 'ENS'   post ']' ']'"). *)

  (* Notation "'LEMMA' 'VARS' Σ 'PATS' δ 'REQ' pre 'ENS' post" := (@MkLemma _ Σ δ pre post) *)
  (*   (at level 200, *)
  (*    format "'[v  ' 'LEMMA' '/' '[' 'VARS'  Σ ']' '/' '[' 'PATS'  δ ']' '/' '[' 'REQ'   pre ']' '/' '[' 'ENS'   post ']' ']'"). *)

  Section Experimental.

    Definition sep_contract_pun_logvars (Δ : PCtx) (Σ : LCtx) : LCtx :=
      ctx.map (fun '(x∷σ) => (PVartoLVar x∷σ)) Δ ▻▻ Σ.

    Record SepContractPun (Δ : PCtx) (τ : Ty) : Type :=
      MkSepContractPun
        { sep_contract_pun_logic_variables   : LCtx;
          sep_contract_pun_precondition      : Assertion
                                                 (sep_contract_pun_logvars
                                                    Δ sep_contract_pun_logic_variables);
          sep_contract_pun_result            : LVar;
          sep_contract_pun_postcondition     : Assertion
                                                 (sep_contract_pun_logvars Δ
                                                                           sep_contract_pun_logic_variables
                                                                           ▻ sep_contract_pun_result∷τ)
        }.

    Global Arguments MkSepContractPun : clear implicits.

    Definition sep_contract_pun_to_sep_contract {Δ τ} :
      SepContractPun Δ τ -> SepContract Δ τ :=
      fun c =>
        match c with
        | MkSepContractPun _ _ Σ req result ens =>
          MkSepContract
            Δ τ
            (sep_contract_pun_logvars Δ Σ)
            (env.tabulate (fun '(x∷σ) xIn =>
                             @term_var
                               (sep_contract_pun_logvars Δ Σ)
                               (PVartoLVar x)
                               σ
                               (ctx.in_cat_left Σ (ctx.in_map (fun '(y∷τ) => (PVartoLVar y∷τ)) xIn))))
            req result ens
        end.

    Global Coercion sep_contract_pun_to_sep_contract : SepContractPun >-> SepContract.

  End Experimental.

  Section ContractInt.
    Import iris.bi.interface.

    Context {PROP : bi} {PI : PredicateDef PROP}.

    Definition inst_contract_localstore {Δ τ} (c : SepContract Δ τ)
      (ι : Valuation (sep_contract_logic_variables c)) : CStore Δ :=
      inst (sep_contract_localstore c) ι.

    Definition interpret_contract_precondition {Δ τ} (c : SepContract Δ τ)
      (ι : Valuation (sep_contract_logic_variables c)) : PROP :=
      interpret (sep_contract_precondition c) ι.

    Definition interpret_contract_postcondition {Δ τ} (c : SepContract Δ τ)
      (ι : Valuation (sep_contract_logic_variables c)) (result : Val τ) : PROP :=
        interpret (sep_contract_postcondition c) (env.snoc ι (sep_contract_result c ∷ τ) result).

  End ContractInt.

End Contracts.
End AssertionsOn.
