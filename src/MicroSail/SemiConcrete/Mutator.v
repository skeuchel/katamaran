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
     Symbolic.Outcome
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
       (typekit : TypeKit)
       (termkit : TermKit typekit)
       (progkit : ProgramKit typekit termkit)
       (assertkit : AssertionKit typekit termkit progkit)
       (symcontractkit : SymbolicContractKit typekit termkit progkit assertkit).

  Export symcontractkit.

  Inductive SCChunk : Type :=
  | scchunk_pred   (p : 𝑷) (vs : Env Lit (𝑷_Ty p))
  | scchunk_ptsreg {σ : Ty} (r : 𝑹𝑬𝑮 σ) (v : Lit σ).
  Arguments scchunk_pred _ _ : clear implicits.

  Section TransparentObligations.
    Local Set Transparent Obligations.
    Derive NoConfusion for SCChunk.
  End TransparentObligations.

  Definition SCHeap  : Type :=
    list SCChunk.

  Section SemiConcreteState.

    Local Set Primitive Projections.

    Record SCState (Γ : Ctx (𝑿 * Ty)) : Type :=
      MkSCState
        { scstate_localstore    : LocalStore Γ;
          scstate_heap          : SCHeap;
        }.
    Global Arguments scstate_localstore {_} _.
    Global Arguments scstate_heap {_} _.

    Definition scstate_initial {Γ} (δ : LocalStore Γ) : SCState Γ :=
      MkSCState δ nil.

  End SemiConcreteState.

  Section ChunkExtraction.

    Fixpoint heap_extractions (h : SCHeap) : list (SCChunk * SCHeap) :=
      match h with
      | []     => []
      | c :: h => (c , h) :: map (fun '(c', h') => (c' , c :: h')) (heap_extractions h)
      end.

    Equations(noeqns) match_chunk_eqb (ce : SCChunk) (cr : SCChunk) : bool :=
      match_chunk_eqb (scchunk_pred p1 vs1) (scchunk_pred p2 vs2)
      with 𝑷_eq_dec p1 p2 => {
        match_chunk_eqb (scchunk_pred p1 vs1) (scchunk_pred p2 vs2) (left eq_refl) := env_beq Lit_eqb vs1 vs2;
        match_chunk_eqb (scchunk_pred p1 vs1) (scchunk_pred p2 vs2) (right _) := false
      };
      match_chunk_eqb (scchunk_ptsreg r1 t1) (scchunk_ptsreg r2 t2)
      with 𝑹𝑬𝑮_eq_dec r1 r2 => {
        match_chunk_eqb (scchunk_ptsreg r1 v1) (scchunk_ptsreg r2 v2) (left (@teq_refl eq_refl eq_refl)) := Lit_eqb _ v1 v2;
        match_chunk_eqb (scchunk_ptsreg r1 v1) (scchunk_ptsreg r2 v2) (right _)      := false
      };
      match_chunk_eqb _ _  := false.

    Lemma match_chunk_eqb_spec (c1 c2 : SCChunk) :
      reflect (c1 = c2) (match_chunk_eqb c1 c2).
    Proof.
    Admitted.

    Definition extract_chunk_eqb (ce : SCChunk) (h : SCHeap) : list SCHeap :=
      List.map snd (List.filter (fun '(cr,_) => match_chunk_eqb ce cr) (heap_extractions h)).

  End ChunkExtraction.

  Section SemiConcreteMutatorResult.

    Local Set Primitive Projections.
    Local Set Maximal Implicit Insertion.

    Record SCMutResult (Γ : Ctx (𝑿 * Ty)) (A : Type) : Type :=
      MkSCMutResult {
          scmutres_value : A;
          scmutres_state : SCState Γ;
        }.

  End SemiConcreteMutatorResult.

  Section SemiConcreteMutator.

    Inductive SCMut (Γ1 Γ2 : Ctx (𝑿 * Ty)) (A : Type) : Type :=
    | scmut_state (f: SCState Γ1 -> SCState Γ2 * A)
    | scmut_block
    | scmut_fail (msg: string)
    | scmut_angelic {I : Type} (os: I -> SCMut Γ1 Γ2 A)
    | scmut_demonic {I : Type} (os: I -> SCMut Γ1 Γ2 A)
    | scmut_angelic_binary (o1 o2 : SCMut Γ1 Γ2 A)
    | scmut_demonic_binary (o1 o2 : SCMut Γ1 Γ2 A)
    | scmut_bind {B : Type} {Γ12} (ma : SCMut Γ1 Γ12 B) (f : B -> SCMut Γ12 Γ2 A)
    .

    Global Arguments scmut_block {_ _ _}.
    Global Arguments scmut_fail {_ _ _} _.

    Bind Scope mutator_scope with SCMut.

    Definition scmut_pure {Γ A} (a : A) : SCMut Γ Γ A :=
      scmut_state (fun s => (s,a)).
    Definition scmut_bind_right {Γ1 Γ2 Γ3 A B} (ma : SCMut Γ1 Γ2 A) (mb : SCMut Γ2 Γ3 B) : SCMut Γ1 Γ3 B :=
      scmut_bind ma (fun _ => mb).
    Definition scmut_bind_left {Γ1 Γ2 Γ3 A B} (ma : SCMut Γ1 Γ2 A) (mb : SCMut Γ2 Γ3 B) : SCMut Γ1 Γ3 A :=
      scmut_bind ma (fun a => scmut_bind mb (fun _ => scmut_pure a)).
    Definition scmut_map {Γ1 Γ2 A B} (f : A -> B) (ma : SCMut Γ1 Γ2 A) : SCMut Γ1 Γ2 B :=
      scmut_bind ma (fun a => scmut_pure (f a)).
    Definition scmut_angelic_list {Γ A} (msg : string) :
      list A -> SCMut Γ Γ A.
    Admitted.

    (* Definition outcome_angelic_list {A} (msg : string) : list A -> Outcome A := *)
    (*   fix outcome_angelic_list (xs : list A) := *)
    (*     match xs with *)
    (*     | nil        => outcome_fail msg *)
    (*     | cons x xs  => outcome_angelic_binary (outcome_pure x) (outcome_angelic_list xs) *)
    (*     end. *)

  End SemiConcreteMutator.
  Bind Scope mutator_scope with SCMut.

  Module MutatorNotations.

    Notation "'⨂' x .. y => F" :=
      (scmut_demonic (fun x => .. (scmut_demonic (fun y => F)) .. )) : mutator_scope.

    Notation "'⨁' x .. y => F" :=
      (scmut_angelic (fun x => .. (scmut_angelic (fun y => F)) .. )) : mutator_scope.

    Infix "⊗" := scmut_demonic_binary (at level 40, left associativity) : mutator_scope.
    Infix "⊕" := scmut_angelic_binary (at level 50, left associativity) : mutator_scope.

    Notation "x <- ma ;; mb" :=
      (scmut_bind ma (fun x => mb))
        (at level 80, ma at level 90, mb at level 200, right associativity) : mutator_scope.
    Notation "ma >>= f" := (scmut_bind ma f) (at level 50, left associativity) : mutator_scope.
    Notation "m1 ;; m2" := (scmut_bind m1 (fun _ => m2)) : mutator_scope.
    Notation "ma *> mb" := (scmut_bind_right ma mb) (at level 50, left associativity) : mutator_scope.
    Notation "ma <* mb" := (scmut_bind_left ma mb) (at level 50, left associativity) : mutator_scope.

  End MutatorNotations.
  Import MutatorNotations.

  Section MutatorOperations.

    Local Open Scope mutator_scope.

    Definition scmut_modify {Γ Γ'} (f : SCState Γ -> SCState Γ') : SCMut Γ Γ' unit :=
      scmut_state (fun s => (f s,tt)).
    Definition scmut_put {Γ Γ'} (s : SCState Γ') : SCMut Γ Γ' unit :=
      scmut_state (fun _ => (s,tt)).
    Definition scmut_get {Γ} : SCMut Γ Γ (SCState Γ) :=
      scmut_state (fun s => (s,s)).

    Definition scmut_state_local {Γ Γ' A} (f : LocalStore Γ -> (LocalStore Γ' * A)) : SCMut Γ Γ' A :=
      scmut_state (fun '(MkSCState δ ĥ) => let (δ',a) := f δ in (MkSCState δ' ĥ,a)).
    Definition scmut_modify_local {Γ Γ'} (f : LocalStore Γ -> LocalStore Γ') : SCMut Γ Γ' unit :=
      scmut_state_local (fun δ => (f δ,tt)).
    Definition scmut_put_local {Γ Γ'} (δ : LocalStore Γ') : SCMut Γ Γ' unit :=
      scmut_state_local (fun _ => (δ,tt)).
    Definition scmut_get_local {Γ} : SCMut Γ Γ (LocalStore Γ) :=
      scmut_state_local (fun δ => (δ,δ)).
    Definition scmut_gets_local {Γ A} (f : LocalStore Γ -> A) : SCMut Γ Γ A :=
      scmut_state_local (fun δ => (δ,f δ)).
    Definition scmut_pop_local {Γ x σ} : SCMut (Γ ▻ (x , σ)) Γ unit :=
      scmut_modify_local (fun δ => env_tail δ).
    Definition scmut_pops_local {Γ} Δ : SCMut (Γ ▻▻ Δ) Γ unit :=
      scmut_modify_local (fun δΓΔ => env_drop Δ δΓΔ).
    Definition scmut_push_local {Γ x σ} (v : Lit σ) : SCMut Γ (Γ ▻ (x , σ)) unit :=
      scmut_modify_local (fun δ => env_snoc δ (x , σ) v).
    Definition scmut_pushs_local {Γ Δ} (δΔ : LocalStore Δ) : SCMut Γ (Γ ▻▻ Δ) unit :=
      scmut_modify_local (fun δΓ => env_cat δΓ δΔ).
    Definition scmut_pushpop {Γ x σ A} (v : Lit σ) (m : SCMut (Γ ▻ (x,σ)) (Γ ▻ (x,σ)) A) : SCMut Γ Γ A :=
      scmut_push_local v ;; m <* scmut_pop_local.
    Definition scmut_pushspops {Γ Δ A} (δΔ : LocalStore Δ) (m : SCMut (Γ ▻▻ Δ) (Γ ▻▻ Δ) A) : SCMut Γ Γ A :=
      scmut_pushs_local δΔ ;; m <* scmut_pops_local Δ.

    Definition scmut_state_heap {Γ A} (f : SCHeap -> (SCHeap * A)) : SCMut Γ Γ A :=
      scmut_state (fun '(MkSCState δ h) => let (h',a) := f h in (MkSCState δ h',a)).
    Definition scmut_modify_heap {Γ} (f : SCHeap -> SCHeap) : SCMut Γ Γ unit :=
      scmut_state_heap (fun h => (f h,tt)).
    Definition scmut_get_heap {Γ} : SCMut Γ Γ SCHeap :=
      scmut_state_heap (fun h => (h,h)).
    Definition scmut_put_heap {Γ} (h : SCHeap) : SCMut Γ Γ unit :=
      scmut_state_heap (fun _ => (h,tt)).

    Definition scmut_eval_exp {Γ σ} (e : Exp Γ σ) : SCMut Γ Γ (Lit σ) :=
      scmut_gets_local (fun δ => eval e δ).
    Definition scmut_eval_exps {Γ} {σs : Ctx (𝑿 * Ty)} (es : NamedEnv (Exp Γ) σs) : SCMut Γ Γ (LocalStore σs) :=
      scmut_gets_local (fun δ => env_map (fun _ e => eval e δ) es).

    Definition scmut_assert_eq {Γ σ} (v1 v2 : Lit σ) : SCMut Γ Γ unit :=
      if Lit_eqb σ v1 v2
      then scmut_pure tt
      else scmut_fail "Err [smut_assert_eq]: unsatisfiable".

    Definition scmut_produce_chunk {Γ} (c : SCChunk) : SCMut Γ Γ unit :=
      scmut_modify_heap (fun h => c :: h).
    Definition scmut_consume_chunk {Γ} (c : SCChunk) : SCMut Γ Γ unit :=
      scmut_get_heap >>= fun h =>
      scmut_angelic_list
        "Err [scmut_consume_chunk]: empty extraction"
        (extract_chunk_eqb c h) >>= fun h' =>
        scmut_put_heap h'.

    Global Arguments scmut_push_local {Γ _ _} _.
    Global Arguments scmut_produce_chunk {Γ} _.
    Global Arguments scmut_consume_chunk {Γ} _.

    Definition inst_chunk {Σ} (ι : SymInstance Σ) (c : Chunk Σ) : SCChunk :=
      match c with
      | chunk_pred p ts  => scchunk_pred p (env_map (fun _ => inst_term ι) ts)
      | chunk_ptsreg r t => scchunk_ptsreg r (inst_term ι t)
      end.

    Fixpoint scmut_produce {Γ Σ} (ι : SymInstance Σ) (asn : Assertion Σ) : SCMut Γ Γ unit :=
      match asn with
      | asn_bool b      => if inst_term ι b
                           then scmut_pure tt
                           else scmut_block
      | asn_prop P      => scmut_fail "scmut_produce"
      | asn_chunk c     => scmut_produce_chunk (inst_chunk ι c)
      | asn_if b a1 a2  => if inst_term ι b
                           then scmut_produce ι a1
                           else scmut_produce ι a2
      | @asn_match_enum _ E k alts =>
        scmut_produce ι (alts (inst_term ι k))
      | asn_sep a1 a2   => scmut_produce ι a1 *> scmut_produce ι a2
      | asn_exist ς τ a => ⨂ v : Lit τ => scmut_produce (env_snoc ι (ς , τ) v) a
      end.

    Fixpoint scmut_consume {Γ Σ} (ι : SymInstance Σ) (asn : Assertion Σ) : SCMut Γ Γ unit :=
      match asn with
      | asn_bool b      => if inst_term ι b
                           then scmut_pure tt
                           else scmut_fail "scmut_consume"
      | asn_prop P      => scmut_fail "scmut_consume"
      | asn_chunk c     => scmut_consume_chunk (inst_chunk ι c)
      | asn_if b a1 a2  => if inst_term ι b
                           then scmut_consume ι a1
                           else scmut_consume ι a2
      | @asn_match_enum _ E k alts =>
        scmut_consume ι (alts (inst_term ι k))
      | asn_sep a1 a2   => scmut_consume ι a1 *> scmut_consume ι a2
      | asn_exist ς τ a => ⨁ v : Lit τ => scmut_consume (env_snoc ι (ς , τ) v) a
      end.

    Definition scmut_call {Γ Δ τ} (contract : SepContract Δ τ) (vs : LocalStore Δ) : SCMut Γ Γ (Lit τ) :=
      match contract with
      | MkSepContract _ _ Σe δ req result ens =>
        ⨁ ι : SymInstance Σe =>
        ⨁ H : vs = inst_localstore ι δ =>
        scmut_consume ι req  ;;
        ⨂ v : Lit τ =>
        scmut_produce (env_snoc ι (result,τ) v) ens ;;
        scmut_pure v
      end.

    Fixpoint scmut_exec {Γ σ} (s : Stm Γ σ) : SCMut Γ Γ (Lit σ) :=
      match s with
      | stm_lit τ l => scmut_pure l
      | stm_exp e => scmut_eval_exp e
      | stm_let x τ s k =>
        v <- scmut_exec s ;;
        scmut_pushpop v (scmut_exec k)
      | stm_block δ k =>
        scmut_pushspops δ (scmut_exec k)
      | stm_assign x e =>
        v <- scmut_exec e ;;
        scmut_modify_local (fun δ => δ ⟪ x ↦ v ⟫)%env *>
        scmut_pure v
      | stm_call f es =>
        match CEnv f with
        | Some c => scmut_eval_exps es >>= scmut_call c
        | None   => scmut_fail "Err [scmut_exec]: Function call without contract"
        end
      | stm_call_external f es =>
        scmut_eval_exps es >>= scmut_call (CEnvEx f)
      | stm_call_frame Δ δ' τ s =>
        δ <- scmut_get_local ;;
        scmut_put_local δ' ;;
        v <- scmut_exec s ;;
        scmut_put_local δ ;;
        scmut_pure v
      | stm_if e s1 s2 =>
        v <- scmut_eval_exp e ;;
        if v
        then scmut_exec s1
        else scmut_exec s2
      | stm_seq e k => scmut_exec e ;; scmut_exec k
      | stm_assert e1 _ =>
        v <- scmut_eval_exp e1 ;;
        if v
        then scmut_pure v
        else scmut_block
      | stm_fail τ s =>
        scmut_block
      | stm_match_enum E e alts =>
        K <- scmut_eval_exp e ;;
        scmut_exec (alts K)
      | @stm_read_register _ τ reg =>
        ⨁ v : Lit τ =>
        let c := scchunk_ptsreg reg v in
        scmut_consume_chunk c ;;
        scmut_produce_chunk c ;;
        scmut_pure v
      | @stm_write_register _ τ reg e =>
        v__new <- scmut_eval_exp e ;;
        ⨁ v__old : Lit τ =>
        scmut_consume_chunk (scchunk_ptsreg reg v__old) ;;
        scmut_produce_chunk (scchunk_ptsreg reg v__new) ;;
        scmut_pure v__new
      | stm_match_list e s1 xh xt s2 =>
        v <- scmut_eval_exp e ;;
        match v with
        | nil => scmut_exec s1
        | cons h t =>
          scmut_pushpop h (scmut_pushpop (σ := ty_list _) t (scmut_exec s2))
        end
      | stm_match_sum e xinl s1 xinr s2 =>
        v <- scmut_eval_exp e ;;
        match v with
        | inl v => scmut_pushpop v (scmut_exec s1)
        | inr v => scmut_pushpop v (scmut_exec s2)
        end
      | stm_match_pair e xl xr s =>
        v <- scmut_eval_exp e ;;
        scmut_pushspops
          [fst v,snd v]%arg
          (scmut_exec s)
      | stm_match_tuple e p rhs =>
        v <- scmut_eval_exp e ;;
        scmut_pushspops
          (tuple_pattern_match p v)
          (scmut_exec rhs)
      | stm_match_union U e alts =>
        v <- scmut_eval_exp e ;;
        let (K , v) := 𝑼_unfold v in
        scmut_pushspops
          (pattern_match (proj_alt_pat (alts K)) v)
          (scmut_exec (proj_alt_rhs (alts K)))
      | stm_match_record R e p rhs =>
        v <- scmut_eval_exp e ;;
        scmut_pushspops
          (record_pattern_match p (𝑹_unfold v))
          (scmut_exec rhs)
      | stm_bind s k =>
        v <- scmut_exec s ;;
        scmut_exec (k v)
      end.

    Definition scmut_leakcheck {Γ} : SCMut Γ Γ unit :=
      scmut_get_heap >>= fun h =>
      match h with
      | nil => scmut_pure tt
      | _   => scmut_fail "Err [scmut_leakcheck]: heap leak"
      end.

  End MutatorOperations.

  Import OutcomeNotations.

  Fixpoint scmut_wp {Γ1 Γ2 A} (m : SCMut Γ1 Γ2 A) (POST : A -> SCState Γ2 -> Prop) (s1 : SCState Γ1) {struct m} : Prop :=
    match m with
    | scmut_state f => let sa := f s1 in POST (snd sa) (fst sa)
    | scmut_block => True
    | scmut_fail _ => False
    | scmut_angelic os => forall i, scmut_wp (os i) POST s1
    | scmut_demonic os => exists i, scmut_wp (os i) POST s1
    | scmut_angelic_binary m1 m2 => scmut_wp m1 POST s1 \/ scmut_wp m2 POST s1
    | scmut_demonic_binary m1 m2 => scmut_wp m1 POST s1 /\ scmut_wp m2 POST s1
    | scmut_bind m f => scmut_wp m (fun b s2 => scmut_wp (f b) POST s2) s1
    end.

  Lemma scmut_monotonic {Γ1 Γ2 A} (m : SCMut Γ1 Γ2 A) {P Q : A -> SCState Γ2 -> Prop}
        (hyp : forall a s, P a s -> Q a s) (s : SCState Γ1) :
    scmut_wp m P s -> scmut_wp m Q s.
  Proof.
    induction m; cbn in *.
    6: intros []; [ left | right ]; firstorder.
    all: firstorder eauto.
  Qed.

  Definition ValidContractSCMut {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
    match c with
    | MkSepContract _ _ Σ δ req result ens =>
      forall (ι : SymInstance Σ),
        scmut_wp
          (scmut_produce ι req ;;
           v <- scmut_exec body ;;
           scmut_consume (env_snoc ι (result,τ) v) ens ;;
           scmut_leakcheck
          )%mut
          (fun (v : unit) (s' : SCState Δ) => True)
          (scstate_initial (inst_localstore ι δ))
    end.

End SemiConcrete.
