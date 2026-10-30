(******************************************************************************)
(* Copyright (c) 2019 Dominique Devriese, Georgy Lukyanov,                    *)
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
     Bool.Bool
     Logic.Decidable
     Strings.String.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Base
     Bitvector
     Context
     Environment
     Notations Prelude
     Syntax.FunDecl.

Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.
Local Set Transparent Obligations.

Module Type StatementsOn (Import GLOBAL : GlobalState) (Import F : FunDeclKit GLOBAL).

  Inductive Stm (Γ : PCtx) (τ : Ty) : Type :=
  | stm_val           (v : Val τ)
  | stm_exp           (e : Exp Γ τ)
  | stm_let           (x : PVar) (σ : Ty) (s__σ : Stm Γ σ) (s__τ : Stm (Γ ▻ x∷σ) τ)
  | stm_block         (Δ : PCtx) (δ : CStore Δ) (s : Stm (Γ ▻▻ Δ) τ)
  | stm_assign        (x : PVar) {xInΓ : x∷τ ∈ Γ} (s : Stm Γ τ)
  | stm_call          {Δ : PCtx} (f : 𝑭 Δ τ) (es : NamedEnv (Exp Γ) Δ)
  | stm_call_frame    (Δ : PCtx) (δ : CStore Δ) (s : Stm Δ τ)
  | stm_foreign       {Δ : PCtx} (f : 𝑭𝑿 Δ τ) (es : NamedEnv (Exp Γ) Δ)
  | stm_lemmak        {Δ : PCtx} (l : 𝑳 Δ) (es : NamedEnv (Exp Γ) Δ) (k : Stm Γ τ)
  | stm_seq           {σ : Ty} (s : Stm Γ σ) (k : Stm Γ τ)
  | stm_assertk       (e1 : Exp Γ ty.bool) (e2 : Exp Γ ty.string) (k : Stm Γ τ)
  | stm_fail          (s : Val ty.string)
  | stm_pattern_match {σ : Ty} (s : Stm Γ σ) (pat : Pattern σ)
      (rhs : forall (pc : PatternCase pat), Stm (Γ ▻▻ PatternCaseCtx pc) τ)
  | stm_read_register (reg : 𝑹𝑬𝑮 τ)
  | stm_write_register (reg : 𝑹𝑬𝑮 τ) (e : Exp Γ τ)
  | stm_bind   {σ : Ty} (s : Stm Γ σ) (k : Val σ -> Stm Γ τ)
  | stm_debugk (k : Stm Γ τ).

  Derive NoConfusionHom Signature for Stm.

  Arguments stm_val {Γ} τ v.
  Arguments stm_exp {Γ τ} e%_exp.
  Arguments stm_let {Γ τ} x σ s__σ%_exp s__τ%_exp.
  Arguments stm_block {Γ τ Δ} δ s%_exp.
  Arguments stm_assign {Γ τ} x {xInΓ} s%_exp.
  Arguments stm_call {Γ τ Δ} f & _%_env.
  Arguments stm_call_frame {Γ τ Δ} δ s%_exp.
  Arguments stm_foreign {Γ τ Δ} f & _%_env.
  Arguments stm_lemmak {Γ τ Δ} l & _%_env k.
  Arguments stm_seq {Γ τ σ} s%_exp k%_exp.
  Arguments stm_assertk {Γ τ} e1%_exp e2%_exp k%_exp.
  Arguments stm_fail {Γ} τ s%_string.
  Arguments stm_pattern_match {Γ τ σ} s pat rhs.
  Arguments stm_read_register {Γ τ} reg.
  Arguments stm_write_register {Γ τ} reg e%_exp.
  Bind Scope exp_scope with Stm.

  Definition stm_assert {Γ} (e1 : Exp Γ ty.bool) (e2 : Exp Γ ty.string) : Stm Γ ty.unit :=
    stm_assertk e1 e2 (stm_val ty.unit tt).
  Definition stm_lemma {Γ Δ} (l : 𝑳 Δ) (es : NamedEnv (Exp Γ) Δ) : Stm Γ ty.unit :=
    stm_lemmak l es (stm_val ty.unit tt).

  Definition stm_if {Γ τ} (s : Stm Γ ty.bool) (s1 s2 : Stm Γ τ) : Stm Γ τ :=
    stm_pattern_match s pat_bool (fun b => if b then s1 else s2).
  Definition stm_match_prod {Γ τ σ1 σ2} (s : Stm Γ (ty.prod σ1 σ2))
    (xl xr : PVar) (rhs : Stm (Γ ▻ xl∷σ1 ▻ xr∷σ2) τ) : Stm Γ τ :=
    stm_pattern_match s (pat_pair xl xr) (fun _ => rhs).
  Definition stm_match_tuple {Γ τ σs Δ} (s : Stm Γ (ty.tuple σs))
    (p : TuplePat σs Δ) (rhs : Stm (Γ ▻▻ Δ) τ) : Stm Γ τ :=
    stm_pattern_match s (pat_tuple p) (fun _ => rhs).
  Definition stm_match_record {Γ τ R Δ} (s : Stm Γ (ty.record R))
    (p : RecordPat (recordf_ty R) Δ) (rhs : Stm (Γ ▻▻ Δ) τ) : Stm Γ τ :=
    stm_pattern_match s (pat_record R Δ p) (fun _ => rhs).

  Definition stm_match_bvec_split {Γ τ m n} (s : Stm Γ (ty.bvec (m + n))) (xl xr : PVar)
    (rhs : Stm (Γ ▻ xl ∷ ty.bvec m ▻ xr ∷ ty.bvec n) τ) : Stm Γ τ :=
    stm_pattern_match s (pat_bvec_split m n xl xr) (fun _ => rhs).
  Definition stm_match_list {Γ τ σ} (s : Stm Γ (ty.list σ))
    (alt_nil : Stm Γ τ) (xh xt : PVar)
    (alt_cons : Stm (Γ ▻ xh∷σ ▻ xt∷ty.list σ) τ) : Stm Γ τ :=
    stm_pattern_match s (pat_list σ xh xt)
      (fun b => match b with true => alt_nil | false => alt_cons end).
  Definition stm_match_sum {Γ τ σl σr} (s : Stm Γ (ty.sum σl σr))
    (xl : PVar) (sl : Stm (Γ ▻ xl∷σl) τ)
    (xr : PVar) (sr : Stm (Γ ▻ xr∷σr) τ) : Stm Γ τ :=
    stm_pattern_match s (pat_sum σl σr xl xr)
      (fun b => match b with true => sl | false => sr end).
  Definition stm_match_enum {Γ τ E} (s : Stm Γ (ty.enum E))
    (alts : forall (K : enumt E), Stm Γ τ) : Stm Γ τ :=
    stm_pattern_match s (pat_enum E) alts.
  Definition stm_match_bvec {Γ τ n} (s : Stm Γ (ty.bvec n))
    (rhs : bv n -> Stm Γ τ) : Stm Γ τ :=
    stm_pattern_match s (pat_bvec_exhaustive n) rhs.

  Arguments stm_assert {Γ} e1%_exp e2%_exp.
  Arguments stm_lemma {Γ Δ} l es%_env.
  Arguments stm_if {Γ τ} s%_exp s1%_exp s2%_exp.
  Arguments stm_match_prod {Γ τ _ _} _ _ _ _.
  Arguments stm_match_tuple {Γ τ σs Δ} s%_exp p%_pat rhs%_exp.
  Arguments stm_match_record {Γ%_ctx τ} R {Δ%_ctx} s%_exp p%_pat rhs%_exp.
  Arguments stm_match_bvec_split {Γ τ} (m n)%_nat_scope s%_exp xl xr rhs%_exp.
  Arguments stm_match_list {Γ τ _} _ _ _ _ _.
  Arguments stm_match_sum {Γ τ _ _} _ _ _ _ _.
  Arguments stm_match_enum {Γ τ} E s%_exp alts%_exp.
  Arguments stm_match_bvec {Γ τ} n%_nat_scope s%_exp rhs%_exp.

  Definition stm_match_union_alt {Γ τ} U (s : Stm Γ (ty.union U))
    (alts : forall (K : unionk U), Alternative (fun Γ => Stm Γ τ) Γ (unionk_ty U K)) : Stm Γ τ :=
    stm_pattern_match s
      (pat_union U (fun K => alt_pat (alts K)))
      (fun '(existT K pc) =>
         of_pattern_case_curried
           (alt_pat (alts K))
           (alt_rhs (alts K)) pc).
  Arguments stm_match_union_alt {_ _} _ _ _.

  Definition UnionAlt (U : unioni) (Γ : PCtx) (τ : Ty) (K : unionk U) : Type :=
    Alternative (fun Γ => Stm Γ τ) Γ (unionk_ty U K).
  Arguments UnionAlt : clear implicits.

  Definition UnionAlts (U : unioni) (Γ : PCtx) (τ : Ty) : Type :=
    list (sigT (@UnionAlt U Γ τ)).

  Definition findUnionAlt {U : unioni} {Γ : PCtx} {τ : Ty} (K : unionk U) :
    UnionAlts U Γ τ -> option (@UnionAlt U Γ τ K) := findAD K.

  (* The well-formedness property for lists of alternatives captures the
     exhaustiveness of pattern-matching. We currently don't rule out redundancy.
     The find function will always return the first alternative matching a given
     union constructor. *)
  Definition UnionAltsWf {U Γ τ} (alts : UnionAlts U Γ τ) : Prop :=
    Bool.Is_true
      (List.forallb
         (fun K => option.isSome (findUnionAlt K alts))
         (finite.enum (unionk U))).

  Lemma union_alts_wf' {U Γ τ} (alts : UnionAlts U Γ τ) (alts_wf : UnionAltsWf alts) :
    forall (K : unionk U), findUnionAlt K alts <> None.
  Proof.
    intros K. unfold UnionAltsWf in alts_wf.
    destruct List.forallb eqn:Hwf; [|easy].
    rewrite List.forallb_forall in Hwf.
    specialize (Hwf K).
    rewrite <- base.list_elem_of_In in Hwf.
    inster Hwf by apply finite.elem_of_enum.
    now destruct (findUnionAlt K alts).
  Qed.

  Definition stm_match_union_alt_list {Γ τ} U (s : Stm Γ (ty.union U))
    (alts : UnionAlts U Γ τ) (alts_wf : UnionAltsWf alts) : Stm Γ τ :=
    stm_match_union_alt U s
      (fun K =>
         match findUnionAlt K alts as o return findUnionAlt K alts = o -> _ with
         | Some alt => fun _   => alt
         | None     => fun Heq => False_rect _ (union_alts_wf' alts alts_wf Heq)
         end eq_refl).
  Arguments stm_match_union_alt_list {_ _} U s alts _.

  Section LazyBool.

    Open Scope lazy_bool_scope.

    Fixpoint stm_bindfree {Δ τ} (s : Stm Δ τ) : bool :=
      match s with
      | stm_val _ v => true
      | stm_exp e => true
      | stm_let x σ s1 s2 => stm_bindfree s1 &&& stm_bindfree s2
      | stm_block δ s => stm_bindfree s
      | stm_assign xInΓ s => stm_bindfree s
      | stm_call f2 es => true
      | stm_call_frame δ s => stm_bindfree s
      | stm_foreign f es => true
      | stm_lemmak l es k => stm_bindfree k
      | stm_seq s k => stm_bindfree s &&& stm_bindfree k
      | stm_assertk e1 e2 k => stm_bindfree k
      | stm_fail _ s => true
      | stm_pattern_match s pat rhs =>
          stm_bindfree s &&&
            List.forallb (fun pc => stm_bindfree (rhs pc))
            (finite.enum (PatternCase pat))
      | stm_read_register reg => true
      | stm_write_register reg e => true
      | stm_bind s k => false
      | stm_debugk k => stm_bindfree k
      end.

  End LazyBool.

  Section NameResolution.

    (* Ideally the following smart constructors would perform name resolution
       and fill in the de Bruijn index and the type of a variable. Unfortunately,
       they critically rely on the order that type-checking is performed. For
       instance in context Γ := (ε ▻ "x"∷ty.int) the expression
       (@exp_smart_var Γ "x" tt) type-checks while the (@exp_smart_var _ "x" tt)
       fails to type-check with error message

         The term "tt" has type "unit" while it is expected
         to have type "IsSome (ctx.resolve ?Γ0 "x")".

       So the variable ?Γ0 has not been unified and blocks the evaluation of
       ctx.resolve. Unfortunately, Coq decides to fail immediately. This can be
       can be solved using bidirectionality hints, but is brittle.
     *)
    Definition exp_smart_var {Γ : PCtx} (x : PVar) {p : IsSome (ctx.resolve Γ x)} :
      Exp Γ (fromSome (ctx.resolve Γ x) p) :=
      @exp_var Γ x (fromSome (ctx.resolve Γ x) p) (ctx.resolve_mk_in Γ x p).

    Definition stm_smart_assign {Γ : PCtx} (x : PVar) {p : IsSome (ctx.resolve Γ x)} :
      Stm Γ (fromSome (ctx.resolve Γ x) p) -> Stm Γ (fromSome (ctx.resolve Γ x) p) :=
      @stm_assign Γ (fromSome _ p) x (ctx.resolve_mk_in Γ x p).

    (* Instead we hook mk_inctx directly into the typeclass resolution mechanism.
       Apparently, the unification of Γ is performed before the resolution so
       evaluation of ctx_resolve and mk_inctx is not blocked. This hook is more
       generally defined in Context.
     *)

  End NameResolution.

  Notation "( x , y , .. , z )" :=
    (tuplepat_snoc .. (tuplepat_snoc (tuplepat_snoc tuplepat_nil x) y) .. z) (at level 0) : pat_scope.

  Notation "'if:' e 'then' s1 'else' s2" := (stm_if e%exp s1%exp s2%exp)
    (at level 200, format
     "'[hv' 'if:'  e  '/' '[' 'then'  s1  ']' '/' '[' 'else'  s2 ']' ']'"
    ) : exp_scope.

  (* The infix operators ∷ is at level 49, so all of the notations have to bind tighter. *)
  Notation "'let:' x := s1 'in' s2" := (stm_let x%string _ s1%exp s2%exp)
    (at level 200, x at level 48, format
     "'[hv' 'let:'  x  :=  s1  'in'  '/' s2 ']'"
    ) : exp_scope.
  Notation "'let:' x :: τ := s1 'in' s2" := (stm_let x%string τ s1%exp s2%exp)
    (at level 200, x at level 48, only parsing) : exp_scope.
  Notation "'let:' x ∷ τ := s1 'in' s2" := (stm_let x%string τ s1%exp s2%exp)
    (at level 200, x at level 48,
     format "'[hv' 'let:'  x  ∷  τ  :=  s1  'in'  '/' s2 ']'"
    ) : exp_scope.
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1%exp => rhs1%exp
                                  end))
    (at level 0, alt1 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' 'end' ']'"
    ) : exp_scope.
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1%exp => rhs1%exp
                                  | alt2%exp => rhs2%exp
                                  end))
    (at level 0, alt1 pattern, alt2 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' 'end' ']'"
    ) : exp_scope.
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1 => rhs1%exp
                                  | alt2 => rhs2%exp
                                  | alt3 => rhs3%exp
                                  end))
    (at level 0, alt1 pattern, alt2 pattern, alt3 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' 'end' ']'"
    ) : exp_scope.
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1 => rhs1%exp
                                  | alt2 => rhs2%exp
                                  | alt3 => rhs3%exp
                                  | alt4 => rhs4%exp
                                  end))
    (at level 0, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' 'end' ']'"
    ) : exp_scope.
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 | alt5 => rhs5 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1 => rhs1%exp
                                  | alt2 => rhs2%exp
                                  | alt3 => rhs3%exp
                                  | alt4 => rhs4%exp
                                  | alt5 => rhs5%exp
                                  end))
    (at level 0, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, alt5 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' |  alt5  =>  rhs5  '/' 'end' ']'"
    ) : exp_scope.
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 | alt5 => rhs5 | alt6 => rhs6 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1 => rhs1%exp
                                  | alt2 => rhs2%exp
                                  | alt3 => rhs3%exp
                                  | alt4 => rhs4%exp
                                  | alt5 => rhs5%exp
                                  | alt6 => rhs6%exp
                                  end))
    (at level 0, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, alt5 pattern, alt6 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' |  alt5  =>  rhs5  '/' |  alt6  =>  rhs6  '/' 'end' ']'"
    ) : exp_scope.
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 | alt5 => rhs5 | alt6 => rhs6 | alt7 => rhs7 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1 => rhs1%exp
                                  | alt2 => rhs2%exp
                                  | alt3 => rhs3%exp
                                  | alt4 => rhs4%exp
                                  | alt5 => rhs5%exp
                                  | alt6 => rhs6%exp
                                  | alt7 => rhs7%exp
                                  end))
    (at level 0, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, alt5 pattern, alt6 pattern, alt7 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' |  alt5  =>  rhs5  '/' |  alt6  =>  rhs6  '/' | alt7 => rhs7 '/' 'end' ']'"
    ) : exp_scope.
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 | alt5 => rhs5 | alt6 => rhs6 | alt7 => rhs7 | alt8 => rhs8 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1 => rhs1%exp
                                  | alt2 => rhs2%exp
                                  | alt3 => rhs3%exp
                                  | alt4 => rhs4%exp
                                  | alt5 => rhs5%exp
                                  | alt6 => rhs6%exp
                                  | alt7 => rhs7%exp
                                  | alt8 => rhs8%exp
                                  end))
    (at level 0, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, alt5 pattern, alt6 pattern, alt7 pattern, alt8 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' |  alt5  =>  rhs5  '/' |  alt6  =>  rhs6  '/' | alt7 => rhs7 '/' | alt8 => rhs8 '/' 'end' ']'"
    ) : exp_scope.

  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 | alt5 => rhs5 | alt6 => rhs6 | alt7 => rhs7 | alt8 => rhs8 | alt9 => rhs9 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1 => rhs1%exp
                                  | alt2 => rhs2%exp
                                  | alt3 => rhs3%exp
                                  | alt4 => rhs4%exp
                                  | alt5 => rhs5%exp
                                  | alt6 => rhs6%exp
                                  | alt7 => rhs7%exp
                                  | alt8 => rhs8%exp
                                  | alt9 => rhs9%exp
                                  end))
    (at level 0, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, alt5 pattern, alt6 pattern, alt7 pattern, alt8 pattern, alt9 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' |  alt5  =>  rhs5  '/' |  alt6  =>  rhs6  '/' | alt7 => rhs7 '/' | alt8 => rhs8 '/' | alt9 => rhs9 '/' 'end' ']'"
    ) : exp_scope.

  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 | alt5 => rhs5 | alt6 => rhs6 | alt7 => rhs7 | alt8 => rhs8 | alt9 => rhs9 | alt10 => rhs10 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1  => rhs1%exp
                                  | alt2  => rhs2%exp
                                  | alt3  => rhs3%exp
                                  | alt4  => rhs4%exp
                                  | alt5  => rhs5%exp
                                  | alt6  => rhs6%exp
                                  | alt7  => rhs7%exp
                                  | alt8  => rhs8%exp
                                  | alt9  => rhs9%exp
                                  | alt10 => rhs10%exp
                                  end))
    (at level 0, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, alt5 pattern, alt6 pattern, alt7 pattern, alt8 pattern, alt9 pattern, alt10 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' |  alt5  =>  rhs5  '/' |  alt6  =>  rhs6  '/' | alt7 => rhs7 '/' | alt8 => rhs8 '/' | alt9 => rhs9 '/' | alt10 => rhs10 '/' 'end' ']'"
    ) : exp_scope.

  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 | alt5 => rhs5 | alt6 => rhs6 | alt7 => rhs7 | alt8 => rhs8 | alt9 => rhs9 | alt10 => rhs10 | alt11 => rhs11 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1  => rhs1%exp
                                  | alt2  => rhs2%exp
                                  | alt3  => rhs3%exp
                                  | alt4  => rhs4%exp
                                  | alt5  => rhs5%exp
                                  | alt6  => rhs6%exp
                                  | alt7  => rhs7%exp
                                  | alt8  => rhs8%exp
                                  | alt9  => rhs9%exp
                                  | alt10 => rhs10%exp
                                  | alt11 => rhs11%exp
                               end))
    (at level 0, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, alt5 pattern, alt6 pattern, alt7 pattern, alt8 pattern, alt9 pattern, alt10 pattern, alt11 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' |  alt5  =>  rhs5  '/' |  alt6  =>  rhs6  '/' | alt7 => rhs7 '/' | alt8 => rhs8 '/' | alt9 => rhs9 '/' | alt10 => rhs10 '/' | alt11 => rhs11 '/' 'end' ']'"
    ) : exp_scope.

  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 | alt5 => rhs5 | alt6 => rhs6 | alt7 => rhs7 | alt8 => rhs8 | alt9 => rhs9 | alt10 => rhs10 | alt11 => rhs11 | alt12 => rhs12 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1  => rhs1%exp
                                  | alt2  => rhs2%exp
                                  | alt3  => rhs3%exp
                                  | alt4  => rhs4%exp
                                  | alt5  => rhs5%exp
                                  | alt6  => rhs6%exp
                                  | alt7  => rhs7%exp
                                  | alt8  => rhs8%exp
                                  | alt9  => rhs9%exp
                                  | alt10 => rhs10%exp
                                  | alt11 => rhs11%exp
                                  | alt12 => rhs12%exp
                               end))
    (at level 0, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, alt5 pattern, alt6 pattern, alt7 pattern, alt8 pattern, alt9 pattern, alt10 pattern, alt11 pattern, alt12 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' |  alt5  =>  rhs5  '/' |  alt6  =>  rhs6  '/' | alt7 => rhs7 '/' | alt8 => rhs8 '/' | alt9 => rhs9 '/' | alt10 => rhs10 '/' | alt11 => rhs11 '/' | alt12 => rhs12 '/' 'end' ']'"
    ) : exp_scope.

  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 | alt5 => rhs5 | alt6 => rhs6 | alt7 => rhs7 | alt8 => rhs8 | alt9 => rhs9 | alt10 => rhs10 | alt11 => rhs11 | alt12 => rhs12 | alt13 => rhs13 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1  => rhs1%exp
                                  | alt2  => rhs2%exp
                                  | alt3  => rhs3%exp
                                  | alt4  => rhs4%exp
                                  | alt5  => rhs5%exp
                                  | alt6  => rhs6%exp
                                  | alt7  => rhs7%exp
                                  | alt8  => rhs8%exp
                                  | alt9  => rhs9%exp
                                  | alt10 => rhs10%exp
                                  | alt11 => rhs11%exp
                                  | alt12 => rhs12%exp
                                  | alt13 => rhs13%exp
                               end))
    (at level 0, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, alt5 pattern, alt6 pattern, alt7 pattern, alt8 pattern, alt9 pattern, alt10 pattern, alt11 pattern, alt12 pattern, alt13 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' |  alt5  =>  rhs5  '/' |  alt6  =>  rhs6  '/' | alt7 => rhs7 '/' | alt8 => rhs8 '/' | alt9 => rhs9 '/' | alt10 => rhs10 '/' | alt11 => rhs11 '/' | alt12 => rhs12 '/' | alt13 => rhs13 '/' 'end' ']'"
    ) : exp_scope.

  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 | alt5 => rhs5 | alt6 => rhs6 | alt7 => rhs7 | alt8 => rhs8 | alt9 => rhs9 | alt10 => rhs10 | alt11 => rhs11 | alt12 => rhs12 | alt13 => rhs13 | alt14 => rhs14 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1  => rhs1%exp
                                  | alt2  => rhs2%exp
                                  | alt3  => rhs3%exp
                                  | alt4  => rhs4%exp
                                  | alt5  => rhs5%exp
                                  | alt6  => rhs6%exp
                                  | alt7  => rhs7%exp
                                  | alt8  => rhs8%exp
                                  | alt9  => rhs9%exp
                                  | alt10 => rhs10%exp
                                  | alt11 => rhs11%exp
                                  | alt12 => rhs12%exp
                                  | alt13 => rhs13%exp
                                  | alt14 => rhs14%exp
                               end))
    (at level 0, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, alt5 pattern, alt6 pattern, alt7 pattern, alt8 pattern, alt9 pattern, alt10 pattern, alt11 pattern, alt12 pattern, alt13 pattern, alt14 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' |  alt5  =>  rhs5  '/' |  alt6  =>  rhs6  '/' | alt7 => rhs7 '/' | alt8 => rhs8 '/' | alt9 => rhs9 '/' | alt10 => rhs10 '/' | alt11 => rhs11 '/' | alt12 => rhs12 '/' | alt13 => rhs13 '/' | alt14 => rhs14 '/' 'end' ']'"
    ) : exp_scope.

  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 | alt5 => rhs5 | alt6 => rhs6 | alt7 => rhs7 | alt8 => rhs8 | alt9 => rhs9 | alt10 => rhs10 | alt11 => rhs11 | alt12 => rhs12 | alt13 => rhs13 | alt14 => rhs14 | alt15 => rhs15 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1  => rhs1%exp
                                  | alt2  => rhs2%exp
                                  | alt3  => rhs3%exp
                                  | alt4  => rhs4%exp
                                  | alt5  => rhs5%exp
                                  | alt6  => rhs6%exp
                                  | alt7  => rhs7%exp
                                  | alt8  => rhs8%exp
                                  | alt9  => rhs9%exp
                                  | alt10 => rhs10%exp
                                  | alt11 => rhs11%exp
                                  | alt12 => rhs12%exp
                                  | alt13 => rhs13%exp
                                  | alt14 => rhs14%exp
                                  | alt15 => rhs15%exp
                               end))
    (at level 0, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, alt5 pattern, alt6 pattern, alt7 pattern, alt8 pattern, alt9 pattern, alt10 pattern, alt11 pattern, alt12 pattern, alt13 pattern, alt14 pattern, alt15 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' |  alt5  =>  rhs5  '/' |  alt6  =>  rhs6  '/' | alt7 => rhs7 '/' | alt8 => rhs8 '/' | alt9 => rhs9 '/' | alt10 => rhs10 '/' | alt11 => rhs11 '/' | alt12 => rhs12 '/' | alt13 => rhs13 '/' | alt14 => rhs14 '/' | alt15 => rhs15 '/' 'end' ']'"
    ) : exp_scope.

  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 | alt5 => rhs5 | alt6 => rhs6 | alt7 => rhs7 | alt8 => rhs8 | alt9 => rhs9 | alt10 => rhs10 | alt11 => rhs11 | alt12 => rhs12 | alt13 => rhs13 | alt14 => rhs14 | alt15 => rhs15 | alt16 => rhs16 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1  => rhs1%exp
                                  | alt2  => rhs2%exp
                                  | alt3  => rhs3%exp
                                  | alt4  => rhs4%exp
                                  | alt5  => rhs5%exp
                                  | alt6  => rhs6%exp
                                  | alt7  => rhs7%exp
                                  | alt8  => rhs8%exp
                                  | alt9  => rhs9%exp
                                  | alt10 => rhs10%exp
                                  | alt11 => rhs11%exp
                                  | alt12 => rhs12%exp
                                  | alt13 => rhs13%exp
                                  | alt14 => rhs14%exp
                                  | alt15 => rhs15%exp
                                  | alt16 => rhs16%exp
                               end))
    (at level 0, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, alt5 pattern, alt6 pattern, alt7 pattern, alt8 pattern, alt9 pattern, alt10 pattern, alt11 pattern, alt12 pattern, alt13 pattern, alt14 pattern, alt15 pattern, alt16 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' |  alt5  =>  rhs5  '/' |  alt6  =>  rhs6  '/' | alt7 => rhs7 '/' | alt8 => rhs8 '/' | alt9 => rhs9 '/' | alt10 => rhs10 '/' | alt11 => rhs11 '/' | alt12 => rhs12 '/' | alt13 => rhs13 '/' | alt14 => rhs14 '/' | alt15 => rhs15 '/' | alt16 => rhs16 '/' 'end' ']'"
    ) : exp_scope.

  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 | alt5 => rhs5 | alt6 => rhs6 | alt7 => rhs7 | alt8 => rhs8 | alt9 => rhs9 | alt10 => rhs10 | alt11 => rhs11 | alt12 => rhs12 | alt13 => rhs13 | alt14 => rhs14 | alt15 => rhs15 | alt16 => rhs16 | alt17 => rhs17 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1  => rhs1%exp
                                  | alt2  => rhs2%exp
                                  | alt3  => rhs3%exp
                                  | alt4  => rhs4%exp
                                  | alt5  => rhs5%exp
                                  | alt6  => rhs6%exp
                                  | alt7  => rhs7%exp
                                  | alt8  => rhs8%exp
                                  | alt9  => rhs9%exp
                                  | alt10 => rhs10%exp
                                  | alt11 => rhs11%exp
                                  | alt12 => rhs12%exp
                                  | alt13 => rhs13%exp
                                  | alt14 => rhs14%exp
                                  | alt15 => rhs15%exp
                                  | alt16 => rhs16%exp
                                  | alt17 => rhs17%exp
                               end))
    (at level 0, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, alt5 pattern, alt6 pattern, alt7 pattern, alt8 pattern, alt9 pattern, alt10 pattern, alt11 pattern, alt12 pattern, alt13 pattern, alt14 pattern, alt15 pattern, alt16 pattern, alt17 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' |  alt5  =>  rhs5  '/' |  alt6  =>  rhs6  '/' | alt7 => rhs7 '/' | alt8 => rhs8 '/' | alt9 => rhs9 '/' | alt10 => rhs10 '/' | alt11 => rhs11 '/' | alt12 => rhs12 '/' | alt13 => rhs13 '/' | alt14 => rhs14 '/' | alt15 => rhs15 '/' | alt16 => rhs16 '/' | alt17 => rhs17 '/' 'end' ']'"
    ) : exp_scope.

  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 | alt5 => rhs5 | alt6 => rhs6 | alt7 => rhs7 | alt8 => rhs8 | alt9 => rhs9 | alt10 => rhs10 | alt11 => rhs11 | alt12 => rhs12 | alt13 => rhs13 | alt14 => rhs14 | alt15 => rhs15 | alt16 => rhs16 | alt17 => rhs17 | alt18 => rhs18 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1  => rhs1%exp
                                  | alt2  => rhs2%exp
                                  | alt3  => rhs3%exp
                                  | alt4  => rhs4%exp
                                  | alt5  => rhs5%exp
                                  | alt6  => rhs6%exp
                                  | alt7  => rhs7%exp
                                  | alt8  => rhs8%exp
                                  | alt9  => rhs9%exp
                                  | alt10 => rhs10%exp
                                  | alt11 => rhs11%exp
                                  | alt12 => rhs12%exp
                                  | alt13 => rhs13%exp
                                  | alt14 => rhs14%exp
                                  | alt15 => rhs15%exp
                                  | alt16 => rhs16%exp
                                  | alt17 => rhs17%exp
                                  | alt18 => rhs18%exp
                               end))
    (at level 0, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, alt5 pattern, alt6 pattern, alt7 pattern, alt8 pattern, alt9 pattern, alt10 pattern, alt11 pattern, alt12 pattern, alt13 pattern, alt14 pattern, alt15 pattern, alt16 pattern, alt17 pattern, alt18 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' |  alt5  =>  rhs5  '/' |  alt6  =>  rhs6  '/' | alt7 => rhs7 '/' | alt8 => rhs8 '/' | alt9 => rhs9 '/' | alt10 => rhs10 '/' | alt11 => rhs11 '/' | alt12 => rhs12 '/' | alt13 => rhs13 '/' | alt14 => rhs14 '/' | alt15 => rhs15 '/' | alt16 => rhs16 '/' | alt17 => rhs17 '/' | alt18 => rhs18 '/' 'end' ']'"
    ) : exp_scope.

  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 | alt5 => rhs5 | alt6 => rhs6 | alt7 => rhs7 | alt8 => rhs8 | alt9 => rhs9 | alt10 => rhs10 | alt11 => rhs11 | alt12 => rhs12 | alt13 => rhs13 | alt14 => rhs14 | alt15 => rhs15 | alt16 => rhs16 | alt17 => rhs17 | alt18 => rhs18 | alt19 => rhs19 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1  => rhs1%exp
                                  | alt2  => rhs2%exp
                                  | alt3  => rhs3%exp
                                  | alt4  => rhs4%exp
                                  | alt5  => rhs5%exp
                                  | alt6  => rhs6%exp
                                  | alt7  => rhs7%exp
                                  | alt8  => rhs8%exp
                                  | alt9  => rhs9%exp
                                  | alt10 => rhs10%exp
                                  | alt11 => rhs11%exp
                                  | alt12 => rhs12%exp
                                  | alt13 => rhs13%exp
                                  | alt14 => rhs14%exp
                                  | alt15 => rhs15%exp
                                  | alt16 => rhs16%exp
                                  | alt17 => rhs17%exp
                                  | alt18 => rhs18%exp
                                  | alt19 => rhs19%exp
                               end))
    (at level 0, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, alt5 pattern, alt6 pattern, alt7 pattern, alt8 pattern, alt9 pattern, alt10 pattern, alt11 pattern, alt12 pattern, alt13 pattern, alt14 pattern, alt15 pattern, alt16 pattern, alt17 pattern, alt18 pattern, alt19 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' |  alt5  =>  rhs5  '/' |  alt6  =>  rhs6  '/' | alt7 => rhs7 '/' | alt8 => rhs8 '/' | alt9 => rhs9 '/' | alt10 => rhs10 '/' | alt11 => rhs11 '/' | alt12 => rhs12 '/' | alt13 => rhs13 '/' | alt14 => rhs14 '/' | alt15 => rhs15 '/' | alt16 => rhs16 '/' | alt17 => rhs17 '/' | alt18 => rhs18 '/' | alt19 => rhs19 '/' 'end' ']'"
    ) : exp_scope.

  Notation "'match:' e 'with' | 'inl' p1 => rhs1 | 'inr' p2 => rhs2 'end'" :=
    (stm_match_sum e p1%string rhs1 p2%string rhs2) (at level 0, only parsing) : exp_scope.

  Notation "'match:' e 'in' '(' σ1 ',' σ2 ')' 'with' | '(' fst ',' snd ')' => rhs 'end'" :=
    (@stm_match_prod _ _ σ1 σ2 e fst%string snd%string rhs)
    (at level 0, fst pattern, snd pattern, format
     "'[hv' 'match:' e 'in' '(' σ1 ',' σ2 ')' 'with' '/' | '(' fst ',' snd ')' => rhs '/' 'end' ']'"
    ) : exp_scope.

  Notation "'match:' e 'in' 'bvec' 1 'with' | alt1 => rhs1 | alt2 => rhs2 'end'" :=
    (@stm_match_bvec _ _ 1 e
       (fun (x : bv 1) =>
          match bv.to_bitstring x with
          | alt1 => rhs1%exp
          | alt2 => rhs2%exp
          end))
    (at level 0, alt1 pattern, alt2 pattern, format
     "'[hv' 'match:'  e  'in'  'bvec'  1  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' 'end' ']'"
    ) : exp_scope.
  Notation "'match:' e 'in' 'bvec' 2 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 'end'" :=
    (@stm_match_bvec _ _ 2 e
       (fun (x : bv 2) =>
          match bv.to_bitstring x with
          | alt1 => rhs1%exp
          | alt2 => rhs2%exp
          | alt3 => rhs3%exp
          | alt4 => rhs4%exp
          end))
    (at level 0, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, format
     "'[hv' 'match:'  e  'in'  'bvec'  2  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' 'end' ']'"
    ) : exp_scope.
  Notation "'match:' e 'in' 'bvec' 3 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 | alt5 => rhs5 | alt6 => rhs6 | alt7 => rhs7 | alt8 => rhs8 'end'" :=
    (@stm_match_bvec _ _ 3 e
       (fun (x : bv 3) =>
          match bv.to_bitstring x with
          | alt1 => rhs1%exp
          | alt2 => rhs2%exp
          | alt3 => rhs3%exp
          | alt4 => rhs4%exp
          | alt5 => rhs5%exp
          | alt6 => rhs6%exp
          | alt7 => rhs7%exp
          | alt8 => rhs8%exp
          end))
    (at level 0, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, alt5 pattern, alt6 pattern, alt7 pattern, alt8 pattern, format
     "'[hv' 'match:'  e  'in'  'bvec'  3  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' |  alt5  =>  rhs5  '/' |  alt6  =>  rhs6  '/' |  alt7  =>  rhs7  '/' |  alt8  =>  rhs8  '/' 'end' ']'"
    ) : exp_scope.
  Notation "'match:' e 'in' 'bvec' 4 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 | alt5 => rhs5 | alt6 => rhs6 | alt7 => rhs7 | alt8 => rhs8 | alt9 => rhs9 | alt10 => rhs10 | alt11 => rhs11 | alt12 => rhs12 | alt13 => rhs13 | alt14 => rhs14 | alt15 => rhs15 | alt16 => rhs16 'end'" :=
    (@stm_match_bvec _ _ 4 e
       (fun (x : bv 4) =>
          match bv.to_bitstring x with
          | alt1  => rhs1%exp
          | alt2  => rhs2%exp
          | alt3  => rhs3%exp
          | alt4  => rhs4%exp
          | alt5  => rhs5%exp
          | alt6  => rhs6%exp
          | alt7  => rhs7%exp
          | alt8  => rhs8%exp
          | alt9  => rhs9%exp
          | alt10 => rhs10%exp
          | alt11 => rhs11%exp
          | alt12 => rhs12%exp
          | alt13 => rhs13%exp
          | alt14 => rhs14%exp
          | alt15 => rhs15%exp
          | alt16 => rhs16%exp
          end))
    (at level 0, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, alt5 pattern, alt6 pattern, alt7 pattern, alt8 pattern, alt9 pattern, alt10 pattern, alt11 pattern, alt12 pattern, alt13 pattern, alt14 pattern, alt15 pattern, alt16 pattern, format
     "'[hv' 'match:'  e  'in'  'bvec'  4  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' |  alt5  =>  rhs5  '/' |  alt6  =>  rhs6  '/' |  alt7  =>  rhs7  '/' |  alt8  =>  rhs8  '/' | alt9 => rhs9 '/' | alt10 => rhs10 '/' | alt11 => rhs11 '/' | alt12 => rhs12 '/' | alt13 => rhs13 '/' | alt14 => rhs14 '/' | alt15 => rhs15 '/' | alt16 => rhs16 '/' 'end' ']'"
    ) : exp_scope.
  Notation "'match:' e 'in' 'bvec' 5 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 | alt5 => rhs5 | alt6 => rhs6 | alt7 => rhs7 | alt8 => rhs8 | alt9 => rhs9 | alt10 => rhs10 | alt11 => rhs11 | alt12 => rhs12 | alt13 => rhs13 | alt14 => rhs14 | alt15 => rhs15 | alt16 => rhs16 | alt17 => rhs17 | alt18 => rhs18 | alt19 => rhs19 | alt20 => rhs20 | alt21 => rhs21 | alt22 => rhs22 | alt23 => rhs23 | alt24 => rhs24 | alt25 => rhs25 | alt26 => rhs26 | alt27 => rhs27 | alt28 => rhs28 | alt29 => rhs29 | alt30 => rhs30 | alt31 => rhs31 | alt32 => rhs32 'end'" :=
    (@stm_match_bvec _ _ 5 e
       (fun (x : bv 5) =>
          match bv.to_bitstring x with
          | alt1  => rhs1%exp
          | alt2  => rhs2%exp
          | alt3  => rhs3%exp
          | alt4  => rhs4%exp
          | alt5  => rhs5%exp
          | alt6  => rhs6%exp
          | alt7  => rhs7%exp
          | alt8  => rhs8%exp
          | alt9  => rhs9%exp
          | alt10 => rhs10%exp
          | alt11 => rhs11%exp
          | alt12 => rhs12%exp
          | alt13 => rhs13%exp
          | alt14 => rhs14%exp
          | alt15 => rhs15%exp
          | alt16 => rhs16%exp
          | alt17 => rhs17%exp
          | alt18 => rhs18%exp
          | alt19 => rhs19%exp
          | alt20 => rhs20%exp
          | alt21 => rhs21%exp
          | alt22 => rhs22%exp
          | alt23 => rhs23%exp
          | alt24 => rhs24%exp
          | alt25 => rhs25%exp
          | alt26 => rhs26%exp
          | alt27 => rhs27%exp
          | alt28 => rhs28%exp
          | alt29 => rhs29%exp
          | alt30 => rhs30%exp
          | alt31 => rhs31%exp
          | alt32 => rhs32%exp
          end))
    (at level 0, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, alt5 pattern, alt6 pattern, alt7 pattern, alt8 pattern, alt9 pattern, alt10 pattern, alt11 pattern, alt12 pattern, alt13 pattern, alt14 pattern, alt15 pattern, alt16 pattern, alt17 pattern, alt18 pattern, alt19 pattern, alt20 pattern, alt21 pattern, alt22 pattern, alt23 pattern, alt24 pattern, alt25 pattern, alt26 pattern, alt27 pattern, alt28 pattern, alt29 pattern, alt30 pattern, alt31 pattern, alt32 pattern, format
     "'[hv' 'match:'  e  'in'  'bvec'  5  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' |  alt5  =>  rhs5  '/' |  alt6  =>  rhs6  '/' |  alt7  =>  rhs7  '/' |  alt8  =>  rhs8  '/' | alt9 => rhs9 '/' | alt10 => rhs10 '/' | alt11 => rhs11 '/' | alt12 => rhs12 '/' | alt13 => rhs13 '/' | alt14 => rhs14 '/' | alt15 => rhs15 '/' | alt16 => rhs16 '/' | alt17 => rhs17 '/' | alt18 => rhs18 '/' | alt19 => rhs19 '/' | alt20 => rhs20 '/' | alt21 => rhs21 '/' | alt22 => rhs22 '/' | alt23 => rhs23 '/' | alt24 => rhs24 '/' | alt25 => rhs25 '/' | alt26 => rhs26 '/' | alt27 => rhs27 '/' | alt28 => rhs28 '/' | alt29 => rhs29 '/' | alt30 => rhs30 '/' | alt31 => rhs31 '/' | alt32 => rhs32 '/' 'end' ']'"
    ) : exp_scope.

  Notation "'match:' e 'in' R 'with' [ x ] => rhs 'end'" :=
    (stm_match_record R e%exp
      (recordpat_snoc recordpat_nil _ x)
      rhs%exp)
    (format "'[hv' 'match:'  e  'in'  R  'with'  '/  ' [ x ]  =>  '/    ' rhs  '/' 'end' ']'") : exp_scope.

  Notation "'match:' e 'in' R 'with' [ x ; y ; .. ; z ] => rhs 'end'" :=
    (stm_match_record R e%exp
      (recordpat_snoc .. (recordpat_snoc (recordpat_snoc recordpat_nil _ x) _ y) .. _ z)
      rhs%exp)
    (format "'[hv' 'match:'  e  'in'  R  'with'  '/  ' [ x ; y ; .. ; z ]  =>  '/    ' rhs  '/' 'end' ']'") : exp_scope.

  Notation "'match:' e 'in' 'union' U 'with' | x | y | .. | z 'end'" :=
    (stm_match_union_alt_list U e (cons x%alt (cons y%alt .. (cons z%alt nil) ..)) Logic.I)
    (format "'[hv' 'match:'  e  'in'  'union'  U  'with'  '/' | x  '/' | y  '/' | ..  '/' | z  '/' 'end' ']'") : exp_scope.

  Notation "'>' K pat => rhs" := (existT K (MkAlt pat rhs%exp))
    (K global, at level 200, pat at level 9, format ">  K  pat  =>  rhs") : alt_scope.

  Notation "'call' f a1 .. an" :=
    (stm_call f (env.snoc .. (env.snoc env.nil (_∷_) a1%exp) .. (_∷_) an%exp))
    (at level 10, f global, a1, an at level 9) : exp_scope.
  Notation "'foreign' f a1 .. an" :=
    (stm_foreign f (env.snoc .. (env.snoc env.nil (_∷_) a1%exp) .. (_∷_) an%exp))
    (at level 10, f global, a1, an at level 9) : exp_scope.

  Notation "'call' f" :=
    (stm_call f env.nil)
    (at level 10, f global) : exp_scope.
  Notation "'foreign' f" :=
    (stm_foreign f env.nil)
    (at level 10, f global) : exp_scope.

  Notation "s1 ;; s2" := (stm_seq s1 s2) : exp_scope.
  Notation "x <- s" := (stm_assign x s)
    (at level 20, s at next level) : exp_scope.
  Notation "'fail' s" := (stm_fail _ s)
    (at level 10, no associativity) : exp_scope.
End StatementsOn.

Module Type FunDecl (GLOBAL : GlobalState) := FunDeclKit GLOBAL <+ StatementsOn GLOBAL.
