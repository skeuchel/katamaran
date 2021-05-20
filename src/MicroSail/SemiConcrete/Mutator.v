(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel                                          *)
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
     Bool.Bool
     Lists.List
     Logic.EqdepFacts
     Program.Equality
     Program.Tactics
     Strings.String
     Arith.PeanoNat
     ZArith.ZArith.

From Equations Require Import Equations.

From MicroSail Require Import
     Sep.Spec
     SemiConcrete.Outcome
     Syntax.

From stdpp Require Import base list option.

Import CtxNotations.
Import EnvNotations.
Import ListNotations.
Import OutcomeNotations.

Set Implicit Arguments.

Delimit Scope mutator_scope with mut.
Delimit Scope dmut_scope with dmut.

Module SemiConcrete
       (termkit : TermKit)
       (progkit : ProgramKit termkit)
       (assertkit : AssertionKit termkit progkit)
       (symcontractkit : SymbolicContractKit termkit progkit assertkit).

  Export symcontractkit.

  Section ChunkExtraction.

    Equations(noeqns) match_scchunk_eqb (ce : SCChunk) (cr : SCChunk) : bool :=
      match_scchunk_eqb (scchunk_user p1 vs1) (scchunk_user p2 vs2)
      with eq_dec p1 p2 => {
        match_scchunk_eqb (scchunk_user p1 vs1) (scchunk_user p2 vs2) (left eq_refl) := env_eqb_hom Lit_eqb vs1 vs2;
        match_scchunk_eqb (scchunk_user p1 vs1) (scchunk_user p2 vs2) (right _) := false
      };
      match_scchunk_eqb (scchunk_ptsreg r1 t1) (scchunk_ptsreg r2 t2)
      with eq_dec_het r1 r2 => {
        match_scchunk_eqb (scchunk_ptsreg r1 v1) (scchunk_ptsreg r2 v2) (left eq_refl) := Lit_eqb _ v1 v2;
        match_scchunk_eqb (scchunk_ptsreg r1 v1) (scchunk_ptsreg r2 v2) (right _)      := false
      };
      match_scchunk_eqb _ _  := false.

    Local Set Equations With UIP.
    Lemma match_scchunk_eqb_spec (c1 c2 : SCChunk) :
      reflect (c1 = c2) (match_scchunk_eqb c1 c2).
    Proof.
      destruct c1 as [p1 vs1|r1], c2 as [p2 vs2|r2]; cbn.
      - destruct (eq_dec p1 p2); cbn.
        + dependent elimination e; cbn.
          destruct (env_eqb_hom_spec _ Lit_eqb_spec vs1 vs2); constructor.
          * congruence.
          * intros e. now dependent elimination e.
        + constructor; intro e.
          now dependent elimination e.
      - constructor. discriminate.
      - constructor. discriminate.
      - destruct (eq_dec_het r r0); cbn.
        + dependent elimination e; cbn.
          apply (ssrbool.iffP (Lit_eqb_spec _ _ _));
            intro e; now dependent elimination e.
        + constructor.
          intro e; now dependent elimination e.
    Qed.

    Definition extract_scchunk_eqb (ce : SCChunk) (h : SCHeap) : list SCHeap :=
      List.map snd (List.filter (fun '(cr,_) => match_scchunk_eqb ce cr) (heap_extractions h)).

  End ChunkExtraction.

  Section SemiConcreteMutatorResult.

    Local Set Primitive Projections.
    Local Set Maximal Implicit Insertion.

    Record CMutResult (Γ : PCtx) (A : Type) : Type :=
      MkCMutResult {
          scmutres_value : A;
          scmutres_store : LocalStore Γ;
          scmutres_heap  : SCHeap;
        }.

  End SemiConcreteMutatorResult.

  Section SemiConcreteMutator.

    Definition CMut (Γ1 Γ2 : PCtx) (A : Type) : Type :=
      LocalStore Γ1 -> SCHeap -> Outcome (CMutResult Γ2 A).
    Bind Scope mutator_scope with CMut.

    Definition cmut_demonic {Γ1 Γ2 I A} (ms : I -> CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A :=
      fun δ h => (⨂ i : I => ms i δ h)%out.
    Definition cmut_angelic {Γ1 Γ2 I A} (ms : I -> CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A :=
      fun δ h => (⨁ i : I => ms i δ h)%out.
    Definition cmut_fail {Γ1 Γ2 A} (msg : string) : CMut Γ1 Γ2 A :=
      fun δ h => outcome_fail msg.
    Definition cmut_block {Γ1 Γ2 A} : CMut Γ1 Γ2 A :=
      fun δ h => outcome_block.

    Definition cmut_demonic_binary {Γ1 Γ2 A} (m1 m2 : CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A :=
      fun δ h => outcome_demonic_binary (m1 δ h) (m2 δ h).
    Definition cmut_angelic_binary {Γ1 Γ2 A} (m1 m2 : CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A :=
      fun δ h => outcome_angelic_binary (m1 δ h) (m2 δ h).

    Definition cmut_pure {Γ A} (a : A) : CMut Γ Γ A :=
      fun δ h => outcome_pure (MkCMutResult a δ h).
    Definition cmut_bind {Γ1 Γ2 Γ3 A B} (ma : CMut Γ1 Γ2 A) (f : A -> CMut Γ2 Γ3 B) : CMut Γ1 Γ3 B :=
      fun δ0 h0 => outcome_bind (ma δ0 h0) (fun '(MkCMutResult a δ1 h1) => f a δ1 h1).
    Definition cmut_bind_right {Γ1 Γ2 Γ3 A B} (ma : CMut Γ1 Γ2 A) (mb : CMut Γ2 Γ3 B) : CMut Γ1 Γ3 B :=
      cmut_bind ma (fun _ => mb).
    Definition cmut_bind_left {Γ1 Γ2 Γ3 A B} (ma : CMut Γ1 Γ2 A) (mb : CMut Γ2 Γ3 B) : CMut Γ1 Γ3 A :=
      cmut_bind ma (fun a => cmut_bind mb (fun _ => cmut_pure a)).
    Definition cmut_map {Γ1 Γ2 A B} (f : A -> B) (ma : CMut Γ1 Γ2 A) : CMut Γ1 Γ2 B :=
      cmut_bind ma (fun a => cmut_pure (f a)).
    Definition cmut_angelick_list {Γ1 Γ2 A B} (msg : string) (xs : list A) (k : A -> CMut Γ1 Γ2 B) : CMut Γ1 Γ2 B :=
      fun δ h => outcome_angelick_list msg xs (fun a => k a δ h).

  End SemiConcreteMutator.
  Bind Scope mutator_scope with CMut.

  Module MutatorNotations.

    Notation "'⨂' x .. y => F" :=
      (cmut_demonic (fun x => .. (cmut_demonic (fun y => F)) .. )) : mutator_scope.

    Notation "'⨁' x .. y => F" :=
      (cmut_angelic (fun x => .. (cmut_angelic (fun y => F)) .. )) : mutator_scope.

    Infix "⊗" := cmut_demonic_binary (at level 40, left associativity) : mutator_scope.
    Infix "⊕" := cmut_angelic_binary (at level 50, left associativity) : mutator_scope.

    Notation "x <- ma ;; mb" :=
      (cmut_bind ma (fun x => mb))
        (at level 80, ma at level 90, mb at level 200, right associativity) : mutator_scope.
    Notation "ma >>= f" := (cmut_bind ma f) (at level 50, left associativity) : mutator_scope.
    Notation "m1 ;; m2" := (cmut_bind_right m1 m2) : mutator_scope.
    Notation "ma *> mb" := (cmut_bind_right ma mb) (at level 50, left associativity) : mutator_scope.
    Notation "ma <* mb" := (cmut_bind_left ma mb) (at level 50, left associativity) : mutator_scope.

  End MutatorNotations.
  Import MutatorNotations.

  Section MutatorOperations.

    Local Open Scope mutator_scope.

    Definition cmut_state {Γ Γ' A} (f : LocalStore Γ -> SCHeap -> CMutResult Γ' A) : CMut Γ Γ' A :=
      fun δ h => outcome_pure (let (a,δ1,h1) := f δ h in MkCMutResult a δ1 h1).

    Definition cmut_put_local {Γ Γ'} (δ : LocalStore Γ') : CMut Γ Γ' unit :=
      cmut_state (fun _ h => MkCMutResult tt δ h).
    Definition cmut_get_local {Γ} : CMut Γ Γ (LocalStore Γ) :=
      cmut_state (fun δ h => MkCMutResult δ δ h).
    Definition cmut_pop_local {Γ x σ} : CMut (Γ ▻ (x :: σ)) Γ unit :=
      cmut_state (fun δ h => MkCMutResult () (env_tail δ) h).
    Definition cmut_pops_local {Γ} Δ : CMut (Γ ▻▻ Δ) Γ unit :=
      cmut_state (fun δ h => MkCMutResult () (env_drop Δ δ) h).
    Definition cmut_push_local {Γ x σ} (v : Lit σ) : CMut Γ (Γ ▻ (x :: σ)) unit :=
      cmut_state (fun δ h => MkCMutResult () (env_snoc δ (x :: σ) v) h).
    Definition cmut_pushs_local {Γ Δ} (δΔ : LocalStore Δ) : CMut Γ (Γ ▻▻ Δ) unit :=
      cmut_state (fun δ h => MkCMutResult () (env_cat δ δΔ) h).
    Definition cmut_pushpop {A} {Γ1 Γ2 x σ} (v : Lit σ) (d : CMut (Γ1 ▻ (x :: σ)) (Γ2 ▻ (x :: σ)) A) :
      CMut Γ1 Γ2 A :=
      cmut_push_local v ;; cmut_bind_left d cmut_pop_local.
    Definition cmut_pushspops {A} {Γ1 Γ2 Δ} (δΔ : LocalStore Δ) (d : CMut (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) A) :
      CMut Γ1 Γ2 A :=
      cmut_pushs_local δΔ ;; cmut_bind_left d (cmut_pops_local Δ).
    Definition cmut_get_heap {Γ} : CMut Γ Γ SCHeap :=
      cmut_state (fun δ h => MkCMutResult h δ h).
    Definition cmut_put_heap {Γ} (h : SCHeap) : CMut Γ Γ unit :=
      cmut_state (fun δ _ => MkCMutResult tt δ h).

    Definition cmut_eval_exp {Γ σ} (e : Exp Γ σ) : CMut Γ Γ (Lit σ) :=
      cmut_state (fun δ h => MkCMutResult (eval e δ) δ h).
    Definition cmut_eval_exps {Γ} {σs : PCtx} (es : NamedEnv (Exp Γ) σs) : CMut Γ Γ (LocalStore σs) :=
      cmut_state (fun δ h => MkCMutResult (env_map (fun _ e => eval e δ) es) δ h).
    Definition cmut_produce_chunk {Γ} (c : SCChunk) : CMut Γ Γ unit :=
      cmut_state (fun δ h => MkCMutResult () δ (cons c h)).
    Definition cmut_consume_chunk {Γ} (c : SCChunk) : CMut Γ Γ unit :=
      cmut_get_heap >>= fun h =>
        cmut_angelick_list
        "Err [cmut_consume_chunk]: empty extraction"
        (extract_scchunk_eqb c h)
        cmut_put_heap.
    Global Arguments cmut_push_local {Γ _ _} _.
    Global Arguments cmut_produce_chunk {Γ} _.
    Global Arguments cmut_consume_chunk {Γ} _.

    Local Opaque instantiate_env.
    Local Opaque instantiate_term.

    Definition cmut_assume_formula {Γ Σ} (ι : SymInstance Σ) (fml : Formula Σ) : CMut Γ Γ unit :=
      fun δ h => outcome_assumek (inst fml ι) (outcome_pure (MkCMutResult tt δ h)).
    Definition cmut_assume_formulak {A Γ1 Γ2 Σ} (ι : SymInstance Σ) (fml : Formula Σ) (k : CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A :=
      fun δ h => outcome_assumek (inst fml ι) (k δ h).
    Definition cmut_assume_term {Γ Σ} (ι : SymInstance Σ) (t : Term Σ ty_bool) : CMut Γ Γ unit :=
      cmut_assume_formula ι (formula_bool t).
    Definition cmut_assert_formula {Γ Σ} (ι : SymInstance Σ) (fml : Formula Σ) : CMut Γ Γ unit :=
      fun δ h => outcome_assertk (inst fml ι) (outcome_pure (MkCMutResult tt δ h)).
    Definition cmut_assert_formulak {A Γ1 Γ2 Σ} (ι : SymInstance Σ) (fml : Formula Σ) (k : CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A :=
      fun δ h => outcome_assertk (inst fml ι) (k δ h).
    Definition cmut_assert_formulask {A Γ1 Γ2 Σ} (ι : SymInstance Σ) (fmls : list (Formula Σ)) (k : CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A :=
      fold_right (cmut_assert_formulak ι) k fmls.

    Definition cmut_match_bool {A Γ1 Γ2} (v : Lit ty_bool) (kt kf : CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A :=
      if v then kt else kf.

    Definition cmut_match_sum {A} {Γ1 Γ2 σ τ} (v : Lit σ + Lit τ)
      (sinl : Lit σ -> CMut Γ1 Γ2 A) (sinr : Lit τ -> CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A :=
      match v with
      | inl v => sinl v
      | inr v => sinr v
      end.

    Definition cmut_match_pair {A} {Γ1 Γ2 σ τ} (v : Lit σ * Lit τ)
      (m : Lit σ -> Lit τ -> CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A :=
      match v with (vl,vr) => m vl vr end.

    Definition cmut_match_enum {A E} {Γ1 Γ2} (v : 𝑬𝑲 E)
      (m : 𝑬𝑲 E -> CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A :=
      m v.

    Definition cmut_match_record {A R} {Γ1 Γ2 Δ} (p : RecordPat (𝑹𝑭_Ty R) Δ) (t : Lit (ty_record R))
      (m : SymInstance Δ -> CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A :=
      m (record_pattern_match_lit p t).

    Fixpoint cmut_produce {Γ Σ} (ι : SymInstance Σ) (asn : Assertion Σ) : CMut Γ Γ unit :=
      match asn with
      | asn_formula fml => cmut_assume_formula ι fml
      | asn_chunk c     => cmut_produce_chunk (inst c ι)
      | asn_if b a1 a2  => cmut_match_bool (inst b ι) (cmut_produce ι a1) (cmut_produce ι a2)
      | asn_match_enum E k alts =>
        cmut_match_enum
          (inst (T := fun Σ => Term Σ _) k ι)
          (fun K => cmut_produce ι (alts K))
      | asn_match_sum σ τ s xl alt_inl xr alt_inr =>
        cmut_match_sum
          (inst (T := fun Σ => Term Σ _) s ι)
          (fun v => cmut_produce (env_snoc ι (xl :: σ) v) alt_inl)
          (fun v => cmut_produce (env_snoc ι (xr :: τ) v) alt_inr)
      | asn_match_list s alt_nil xh xt alt_cons =>
        match inst (T := fun Σ => Term Σ _) s ι with
        | nil        => cmut_produce ι alt_nil
        | cons vh vt => cmut_produce (ι ► (xh :: _ ↦ vh) ► (xt :: ty_list _ ↦ vt)) alt_cons
        end
      | asn_match_pair s xl xr rhs =>
        cmut_match_pair
          (inst (T := fun Σ => Term Σ _) s ι)
          (fun vl vr => cmut_produce (ι ► (xl :: _ ↦ vl) ► (xr :: _ ↦ vr)) rhs)
      | asn_match_tuple s p rhs =>
        let t := inst (T := fun Σ => Term Σ _) s ι in
        let ι' := tuple_pattern_match_lit p t in
        cmut_produce (ι ►► ι') rhs
      | asn_match_record R s p rhs =>
        cmut_match_record p
          (inst (T := fun Σ => Term Σ _) s ι)
          (fun ι' => cmut_produce (ι ►► ι') rhs)
      | asn_match_union U s alt__ctx alt__pat alt__rhs =>
        let t := inst (T := fun Σ => Term Σ _) s ι in
        let (K , v) := 𝑼_unfold t in
        let ι' := pattern_match_lit (alt__pat K) v in
        cmut_produce (ι ►► ι') (alt__rhs K)
      | asn_sep a1 a2   => cmut_produce ι a1 *> cmut_produce ι a2
      | asn_exist ς τ a => ⨂ v : Lit τ => cmut_produce (env_snoc ι (ς :: τ) v) a
      | asn_debug => cmut_pure tt
      end.

    Fixpoint cmut_consume {Γ Σ} (ι : SymInstance Σ) (asn : Assertion Σ) : CMut Γ Γ unit :=
      match asn with
      | asn_formula fml => cmut_assert_formula ι fml
      | asn_chunk c     => cmut_consume_chunk (inst c ι)
      | asn_if b a1 a2  => cmut_match_bool (inst b ι) (cmut_consume ι a1) (cmut_consume ι a2)
      | asn_match_enum E k alts =>
        cmut_match_enum
          (inst (T := fun Σ => Term Σ _) k ι)
          (fun K => cmut_consume ι (alts K))
      | asn_match_sum σ τ s xl alt_inl xr alt_inr =>
        cmut_match_sum
          (inst (T := fun Σ => Term Σ _) s ι)
          (fun v => cmut_consume (env_snoc ι (xl :: σ) v) alt_inl)
          (fun v => cmut_consume (env_snoc ι (xr :: τ) v) alt_inr)
      | asn_match_list s alt_nil xh xt alt_cons =>
        match inst (T := fun Σ => Term Σ _) s ι with
        | nil        => cmut_consume ι alt_nil
        | cons vh vt => cmut_consume (ι ► (xh :: _ ↦ vh) ► (xt :: ty_list _ ↦ vt)) alt_cons
        end
      | asn_match_pair s xl xr rhs =>
        cmut_match_pair
          (inst (T := fun Σ => Term Σ _) s ι)
          (fun vl vr => cmut_consume (ι ► (xl :: _ ↦ vl) ► (xr :: _ ↦ vr)) rhs)
      | asn_match_tuple s p rhs =>
        let t := inst (T := fun Σ => Term Σ _) s ι in
        let ι' := tuple_pattern_match_lit p t in
        cmut_consume (ι ►► ι') rhs
      | asn_match_record R s p rhs =>
        cmut_match_record p
          (inst (T := fun Σ => Term Σ _) s ι)
          (fun ι' => cmut_consume (ι ►► ι') rhs)
      | asn_match_union U s alt__ctx alt__pat alt__rhs =>
        let t := inst (T := fun Σ => Term Σ _) s ι in
        let (K , v) := 𝑼_unfold t in
        let ι' := pattern_match_lit (alt__pat K) v in
        cmut_consume (ι ►► ι') (alt__rhs K)
      | asn_sep a1 a2   => cmut_consume ι a1 *> cmut_consume ι a2
      | asn_exist ς τ a => ⨁ v : Lit τ => cmut_consume (env_snoc ι (ς :: τ) v) a
      | asn_debug => cmut_pure tt
      end.

    Definition cmut_call {Γ Δ τ} (contract : SepContract Δ τ) (vs : LocalStore Δ) : CMut Γ Γ (Lit τ) :=
      match contract with
      | MkSepContract _ _ Σe δ req result ens =>
        ⨁ ι : SymInstance Σe =>
        cmut_assert_formulask ι (formula_eqs δ (lift vs))
         (cmut_consume ι req  ;;
          ⨂ v : Lit τ =>
          cmut_produce (env_snoc ι (result::τ) v) ens ;;
          cmut_pure v)
      end.

    Fixpoint cmut_exec {Γ τ} (s : Stm Γ τ) : CMut Γ Γ (Lit τ) :=
      match s with
      | stm_lit _ l => cmut_pure l
      | stm_exp e => cmut_eval_exp e
      | stm_let x σ s k =>
        v <- cmut_exec s ;;
        cmut_pushpop v (cmut_exec k)
      | stm_block δ k =>
        cmut_pushspops δ (cmut_exec k)
      | stm_assign x e =>
        v <- cmut_exec e ;;
        cmut_state (fun δ h => MkCMutResult tt (δ ⟪ x ↦ v ⟫)%env h) ;;
        cmut_pure v
      | stm_call f es =>
        match CEnv f with
        | Some c => cmut_eval_exps es >>= cmut_call c
        | None   => cmut_fail "Err [cmut_exec]: Function call without contract"
        end
      | stm_call_external f es => cmut_eval_exps es >>= cmut_call (CEnvEx f)
      | stm_call_frame δ' s =>
        δ <- cmut_get_local ;;
        cmut_put_local δ' ;;
        v <- cmut_exec s ;;
        cmut_put_local δ ;;
        cmut_pure v
      | stm_if e s1 s2 =>
        v <- cmut_eval_exp e ;;
        cmut_match_bool v (cmut_exec s1) (cmut_exec s2)
      | stm_seq e k => cmut_exec e ;; cmut_exec k
      | stm_assertk e1 _ k =>
        v <- cmut_eval_exp e1 ;;
        if v
        then cmut_exec k
        else cmut_block
      | stm_fail _ s =>
        cmut_block
      | stm_match_enum E e alts =>
        K <- cmut_eval_exp e ;;
        cmut_match_enum
          K
          (fun K => cmut_exec (alts K))
      | stm_read_register reg =>
        ⨁ v : Lit τ =>
        let c := scchunk_ptsreg reg v in
        cmut_consume_chunk c ;;
        cmut_produce_chunk c ;;
        cmut_pure v
      | stm_write_register reg e =>
        v__new <- cmut_eval_exp e ;;
        ⨁ v__old : Lit τ =>
        cmut_consume_chunk (scchunk_ptsreg reg v__old) ;;
        cmut_produce_chunk (scchunk_ptsreg reg v__new) ;;
        cmut_pure v__new
      | @stm_match_list _ _ σ e s1 xh xt s2 =>
        v <- cmut_eval_exp e ;;
        match v : list (Lit σ) with
        | nil => cmut_exec s1
        | cons h t =>
          cmut_pushspops
            (env_snoc (env_snoc env_nil (xh :: σ) h) (xt :: ty_list σ) t)
            (cmut_exec s2)
        end
      | stm_match_sum e xinl s1 xinr s2 =>
        v <- cmut_eval_exp e ;;
        cmut_match_sum
          v
          (fun v => cmut_pushpop v (cmut_exec s1))
          (fun v => cmut_pushpop v (cmut_exec s2))
      | stm_match_pair e xl xr s =>
        v <- cmut_eval_exp e ;;
        cmut_match_pair
          v
          (fun vl vr =>
             cmut_pushspops
               (env_snoc (env_snoc env_nil (xl :: _) vl) (xr :: _) vr)
               (cmut_exec s))
      | stm_match_tuple e p rhs =>
        v <- cmut_eval_exp e ;;
        cmut_pushs_local (tuple_pattern_match_lit p v) ;;
        cmut_exec rhs <*
        cmut_pops_local _
      | stm_match_union U e alt__pat alt__rhs =>
        v <- cmut_eval_exp e ;;
        let (K , v) := 𝑼_unfold v in
        cmut_pushspops (pattern_match_lit (alt__pat K) v) (cmut_exec (alt__rhs K))
      | stm_match_record R e p rhs =>
        v <- cmut_eval_exp e ;;
        cmut_pushspops (record_pattern_match_lit p v) (cmut_exec rhs)
      | stm_bind s k =>
        v <- cmut_exec s ;;
        cmut_exec (k v)
      | stm_debugk k =>
        cmut_exec k
      end.

    Definition cmut_leakcheck {Γ} : CMut Γ Γ unit :=
      cmut_get_heap >>= fun h =>
      match h with
      | nil => cmut_pure tt
      | _   => cmut_fail "Err [cmut_leakcheck]: heap leak"
      end.

  End MutatorOperations.

  Import OutcomeNotations.

  Section SemiConcreteWP.

    Definition SCProp (Γ : PCtx) : Type :=
      LocalStore Γ -> SCHeap -> Prop.

    Definition cmut_wp {Γ1 Γ2 A} (m : CMut Γ1 Γ2 A) (POST : A -> SCProp Γ2) : SCProp Γ1 :=
      fun δ h =>
        outcome_satisfy
          (m δ h)
          (fun r => POST (scmutres_value r) (scmutres_store r) (scmutres_heap r)).
    Global Arguments cmut_wp : simpl never.

    Lemma cmut_wp_monotonic {A} {Γ1 Γ2} (m : CMut Γ1 Γ2 A)
      (P Q : A -> SCProp Γ2) (PQ : forall a δ h, P a δ h -> Q a δ h) :
      forall δ h,
        cmut_wp m P δ h -> cmut_wp m Q δ h.
    Proof.
      unfold cmut_wp. intros ? ?.
      apply outcome_satisfy_monotonic; intros []; apply PQ.
    Qed.

    Lemma cmut_wp_equiv {A} {Γ1 Γ2} (m : CMut Γ1 Γ2 A)
      (P Q : A -> SCProp Γ2) (PQ : forall a δ h, P a δ h <-> Q a δ h) :
      forall δ h, cmut_wp m P δ h <-> cmut_wp m Q δ h.
    Proof. split; apply cmut_wp_monotonic; apply PQ. Qed.

    Lemma cmut_wp_pure {A Γ} (a : A) (POST : A -> SCProp Γ) :
      forall δ h,
        cmut_wp (cmut_pure a) POST δ h <->
        POST a δ h.
    Proof. reflexivity. Qed.

    Lemma cmut_wp_bind {Γ1 Γ2 Γ3 A B} (ma : CMut Γ1 Γ2 A) (f : A -> CMut Γ2 Γ3 B)
      (POST : B -> SCProp Γ3) :
      forall δ h,
        cmut_wp (cmut_bind ma f) POST δ h <->
        cmut_wp ma (fun a => cmut_wp (f a) POST) δ h.
    Proof.
      unfold CMut, cmut_bind, cmut_wp in *; cbn; intros.
      now rewrite outcome_satisfy_bind.
    Qed.

    Lemma cmut_wp_demonic {Γ1 Γ2 A B} (sm : B -> CMut Γ1 Γ2 A) (POST : A -> SCProp Γ2) :
      forall δ h,
        cmut_wp (cmut_demonic sm) POST δ h <-> forall v, cmut_wp (sm v) POST δ h.
    Proof. unfold cmut_wp, cmut_demonic; cbn; intuition. Qed.

    Lemma cmut_wp_demonic_binary {Γ1 Γ2 A} (sm1 sm2 : CMut Γ1 Γ2 A) (POST : A -> SCProp Γ2) :
      forall δ h,
        cmut_wp (cmut_demonic_binary sm1 sm2) POST δ h <->
        cmut_wp sm1 POST δ h /\ cmut_wp sm2 POST δ h.
    Proof. unfold cmut_wp, cmut_demonic_binary; cbn; intuition. Qed.

    Lemma cmut_wp_angelic {Γ1 Γ2 A B} (sm : B -> CMut Γ1 Γ2 A) (POST : A -> SCProp Γ2) :
      forall δ h,
        cmut_wp (cmut_angelic sm) POST δ h <-> exists v, cmut_wp (sm v) POST δ h.
    Proof. unfold cmut_wp, cmut_angelic; cbn; intuition. Qed.

    Lemma cmut_wp_angelic_binary {Γ1 Γ2 A} (sm1 sm2 : CMut Γ1 Γ2 A) (POST : A -> SCProp Γ2) :
      forall δ h,
        cmut_wp (cmut_angelic_binary sm1 sm2) POST δ h <->
        cmut_wp sm1 POST δ h \/ cmut_wp sm2 POST δ h.
    Proof. unfold cmut_wp, cmut_angelic_binary; cbn; intuition. Qed.

    Lemma cmut_wp_state {Γ1 Γ2 A} (f : LocalStore Γ1 -> SCHeap -> CMutResult Γ2 A) (POST : A -> SCProp Γ2) :
      forall δ h,
        cmut_wp (cmut_state f) POST δ h <->
        match f δ h with
        | MkCMutResult a δ' h' => POST a δ' h'
        end.
    Proof.
      unfold cmut_wp, cmut_state. cbn.
      intros. reflexivity.
    Qed.

    Lemma cmut_wp_bind_right {Γ1 Γ2 Γ3 A B} (ma : CMut Γ1 Γ2 A) (mb : CMut Γ2 Γ3 B)
      (POST : B -> SCProp Γ3) :
      forall δ h,
        cmut_wp (cmut_bind_right ma mb) POST δ h <->
        cmut_wp ma (fun _ => cmut_wp mb POST) δ h.
    Proof. intros δ h. unfold cmut_bind_right. now rewrite cmut_wp_bind. Qed.

    Lemma cmut_wp_assert_formula {Γ Σ} {ι : SymInstance Σ} {fml : Formula Σ}
      (POST : unit -> SCProp Γ ) :
      forall δ h,
        cmut_wp (cmut_assert_formula ι fml) POST δ h <->
        inst fml ι /\ POST tt δ h.
    Proof. reflexivity. Qed.

    Lemma cmut_wp_assume_formula {Γ Σ} {ι : SymInstance Σ} {fml : Formula Σ}
      (POST : unit -> SCProp Γ ) :
      forall δ h,
        cmut_wp (cmut_assume_formula ι fml) POST δ h <->
        (inst (A := Prop) fml ι -> POST tt δ h).
    Proof. reflexivity. Qed.

    Lemma cmut_wp_assume_formulak {A Γ1 Γ2 Σ} {ι : SymInstance Σ} {fml : Formula Σ}
      {k : CMut Γ1 Γ2 A} (POST : A -> SCProp Γ2) :
      forall δ h,
        cmut_wp (cmut_assume_formulak ι fml k) POST δ h <->
        (inst (A := Prop) fml ι -> cmut_wp k POST δ h).
    Proof. reflexivity. Qed.

    Lemma cmut_wp_assert_formulak {A Γ1 Γ2 Σ} {ι : SymInstance Σ} {fml : Formula Σ}
      {k : CMut Γ1 Γ2 A} (POST : A -> SCProp Γ2) :
      forall δ h,
        cmut_wp (cmut_assert_formulak ι fml k) POST δ h <->
        inst fml ι /\ cmut_wp k POST δ h.
    Proof. reflexivity. Qed.

    Lemma cmut_wp_assert_formulask {A Γ1 Γ2 Σ} {ι : SymInstance Σ} {fmls : list (Formula Σ)}
      {k : CMut Γ1 Γ2 A} (POST : A -> SCProp Γ2) :
      forall δ h,
        cmut_wp (cmut_assert_formulask ι fmls k) POST δ h <->
        inst (T := PathCondition) fmls ι /\ cmut_wp k POST δ h.
    Proof.
      intros δ h. unfold cmut_assert_formulask.
      induction fmls; cbn.
      - clear. intuition. constructor.
      - rewrite inst_pathcondition_cons, cmut_wp_assert_formulak, IHfmls.
        clear. intuition.
    Qed.

    Lemma cmut_wp_match_bool {A Γ1 Γ2} (v : Lit ty_bool) (kt kf : CMut Γ1 Γ2 A) :
      forall POST δ h,
        cmut_wp (cmut_match_bool v kt kf) POST δ h <->
        if v
        then cmut_wp kt POST δ h
        else cmut_wp kf POST δ h.
    Proof. destruct v; reflexivity. Qed.

    Lemma cmut_wp_demonic_match_bool {A Γ1 Γ2 Σ} (v : Lit ty_bool) (kt kf : CMut Γ1 Γ2 A) :
      forall POST δ h (ι : SymInstance Σ),
        cmut_wp (cmut_match_bool v kt kf) POST δ h <->
        cmut_wp (cmut_demonic_binary
                   (cmut_assume_formulak ι (formula_bool (term_lit ty_bool v)) kt)
                   (cmut_assume_formulak ι (formula_bool (term_not (term_lit ty_bool v))) kf)) POST δ h.
    Proof.
      intros *.
      rewrite cmut_wp_match_bool, cmut_wp_demonic_binary, ?cmut_wp_assume_formulak.
      destruct v; cbn; unfold is_true; intuition; discriminate.
    Qed.

    Lemma cmut_wp_match_sum {A Γ1 Γ2 σ τ} (v : Lit σ + Lit τ)
      (kl : Lit σ -> CMut Γ1 Γ2 A) (kr : Lit τ -> CMut Γ1 Γ2 A) :
      forall POST δ h,
        cmut_wp (cmut_match_sum v kl kr) POST δ h <->
        match v with
        | inl v => cmut_wp (kl v) POST δ h
        | inr v => cmut_wp (kr v) POST δ h
        end.
    Proof. destruct v; reflexivity. Qed.

    Lemma cmut_wp_match_pair {A Γ1 Γ2 σ τ} (v : Lit σ * Lit τ)
      (k : Lit σ -> Lit τ -> CMut Γ1 Γ2 A) :
      forall POST δ h,
        cmut_wp (cmut_match_pair v k) POST δ h <->
        match v with
        | (vl,vr) => cmut_wp (k vl vr) POST δ h
        end.
    Proof. destruct v; reflexivity. Qed.

    Lemma cmut_wp_match_record {A R Γ1 Γ2 Δ} (p : RecordPat (𝑹𝑭_Ty R) Δ) (v : Lit (ty_record R))
          (k : SymInstance Δ → CMut Γ1 Γ2 A) :
      forall POST δ h,
        cmut_wp (cmut_match_record p v k) POST δ h <->
        forall vs : NamedEnv Lit (𝑹𝑭_Ty R),
          v = 𝑹_fold vs ->
          cmut_wp (k (record_pattern_match_env p vs)) POST δ h.
    Proof.
      intros. unfold cmut_match_record.
      split; intros Hwp.
      - intros vs ->.
        unfold record_pattern_match_lit in Hwp.
        now rewrite 𝑹_unfold_fold in Hwp.
      - specialize (Hwp (𝑹_unfold v)).
        rewrite 𝑹_fold_unfold in Hwp.
        now apply Hwp.
    Qed.

  End SemiConcreteWP.

  Definition cmut_contract {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) :
   SymInstance (sep_contract_logic_variables c) -> CMut Δ Δ unit :=
    match c with
    | MkSepContract _ _ Σ δ req result ens =>
      fun ι =>
      cmut_produce ι req ;;
      cmut_exec s >>= fun v =>
      cmut_consume (env_snoc ι (result::τ) v) ens ;;
      cmut_block
      (* cmut_leakcheck *)
    end%mut.

  Definition ValidContractCMut {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
    forall ι : SymInstance (sep_contract_logic_variables c),
      let δΔ : LocalStore Δ := inst (sep_contract_localstore c) ι in
      cmut_wp (cmut_contract c body ι) (fun _ _ _ => True) δΔ nil.

End SemiConcrete.
