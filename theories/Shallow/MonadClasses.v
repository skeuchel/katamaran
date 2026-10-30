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
  Classes.Morphisms
  Relations.Relation_Definitions.
From Katamaran Require Import
  Prelude
  Base
  Syntax.Assertions
  Syntax.Chunks
  Syntax.Predicates
  Symbolic.Worlds.

Import SignatureNotations ctx.notations env.notations.

#[local] Set Implicit Arguments.

(* Monotonicity proofs use [Proper] and its automation for partial
   applications. The [monotonic] hints decompose the remaining goals: lambdas,
   matches and [::>]. They are kept out of [typeclass_instances]. *)
Create HintDb monotonic.
Ltac solve_monotonic := typeclasses eauto with typeclass_instances monotonic.

Lemma proper_eq_respectful_intro {A B} {MB : relation B} {f : A -> B} :
  (forall a, Proper MB (f a)) -> Proper (eq ==> MB) f.
Proof. intros pf ? ? <-. apply pf. Qed.

Lemma proper_pointwise_intro {A B} {MB : relation B} {f : A -> B} :
  (forall a, Proper MB (f a)) -> Proper (A ::> MB) f.
Proof. intros pf a. apply pf. Qed.
Lemma proper_pointwise_to_eq {A B} {MB : relation B} {f : A -> B} :
  Proper (A ::> MB) f -> Proper (eq ==> MB) f.
Proof. intros pf ? ? <-. apply pf. Qed.

#[export] Hint Extern 1 (Proper (eq ==> _) (fun _ => _)) =>
  class_apply @proper_eq_respectful_intro : monotonic.
#[export] Hint Extern 1 (Proper (_ ::> _) (fun _ => _)) =>
  class_apply @proper_pointwise_intro : monotonic.
(* Lets partial application use instances stated with [::>]. *)
#[export] Hint Resolve proper_pointwise_to_eq | 5 : monotonic.
#[export] Hint Extern 1 (Proper _ (match ?p with existT _ _ => _ end)) =>
  destruct p : monotonic.
#[export] Hint Extern 1 (Proper _ (match ?p with pair _ _ => _ end)) =>
  destruct p : monotonic.
#[export] Hint Extern 1 (Proper _ (match ?p with left _ => _ | right _ => _ end)) =>
  destruct p : monotonic.

Module Type ShallowMonadClassesOn (Import GLOBAL : GlobalState) (Import P : PredicateKit GLOBAL)
  (Import W : WorldsMixin GLOBAL P) (Import AS : AssertionsOn GLOBAL P W).

  (* Interface of monads with the verification effects and a heap. *)
  Module CHeapSpecM.

    Class CHeapSpecM (M : Type -> Type) : Type :=
      { pure {A} : A -> M A;
        bind {A B} : M A -> (A -> M B) -> M B;
        error {A} : M A;
        block {A} : M A;
        angelic (σ : Ty) : M (Val σ);
        demonic (σ : Ty) : M (Val σ);
        angelic_binary {A} : M A -> M A -> M A;
        demonic_binary {A} : M A -> M A -> M A;
        assert_formula : Prop -> M unit;
        assume_formula : Prop -> M unit;
        angelic_pattern_match {N : Set} {σ} (pat : Pattern (N:=N) σ) :
          Val σ -> M (MatchResult pat);
        demonic_pattern_match {N : Set} {σ} (pat : Pattern (N:=N) σ) :
          Val σ -> M (MatchResult pat);
        debug {A} : M A -> M A;
        produce_chunk : SCChunk -> M unit;
        consume_chunk : SCChunk -> M unit;
        read_register {τ} (reg : 𝑹𝑬𝑮 τ) : M (Val τ);
        write_register {τ} (reg : 𝑹𝑬𝑮 τ) : Val τ -> M (Val τ);
      }.
    #[global] Arguments pure {M _ A} a.
    #[global] Arguments bind {M _ A B} m f.
    #[global] Arguments error {M _ A}.
    #[global] Arguments block {M _ A}.
    #[global] Arguments angelic {M _} σ.
    #[global] Arguments demonic {M _} σ.
    #[global] Arguments angelic_binary {M _ A} m1 m2.
    #[global] Arguments demonic_binary {M _ A} m1 m2.
    #[global] Arguments assert_formula {M _} fml.
    #[global] Arguments assume_formula {M _} fml.
    #[global] Arguments angelic_pattern_match {M _ N σ} pat v.
    #[global] Arguments demonic_pattern_match {M _ N σ} pat v.
    #[global] Arguments debug {M _ A} m.
    #[global] Arguments produce_chunk {M _} c.
    #[global] Arguments consume_chunk {M _} c.
    #[global] Arguments read_register {M _ τ} reg.
    #[global] Arguments write_register {M _ τ} reg v.

    Module Import notations.
      Notation "' x <- ma ;; mb" :=
        (bind ma (fun x => mb))
          (at level 20, x pattern, ma at next level, mb at level 200, right associativity,
             format "' x  <-  ma  ;;  mb").
      Notation "x <- ma ;; mb" :=
        (bind ma (fun x => mb))
          (at level 20, ma at next level, mb at level 200, right associativity).
      Notation "ma ;; mb" := (bind ma (fun _ => mb)).
    End notations.

    (* Operations that are derived from the interface. *)
    Section Derived.

    Context {M} {cm : CHeapSpecM M}.

    Definition angelic_ctx {N : Set} :
      forall Δ : NCtx N Ty, M (NamedEnv Val Δ) :=
      fix rec Δ {struct Δ} :=
        match Δ with
        | [ctx]   => pure [env]
        | Δ ▻ x∷σ => vs <- rec Δ;;
                     v  <- angelic σ;;
                     pure (vs ► (x∷σ ↦ v))
        end.

    Definition demonic_ctx {N : Set} :
      forall Δ : NCtx N Ty, M (NamedEnv Val Δ) :=
      fix rec Δ {struct Δ} :=
        match Δ with
        | [ctx]   => pure [env]
        | Δ ▻ x∷σ => vs <- rec Δ;;
                     v  <- demonic σ;;
                     pure (vs ► (x∷σ ↦ v))
        end.

    Equations(noeqns) assert_eq_nenv {N : Set} [Δ : NCtx N Ty]
      (δ δ' : NamedEnv Val Δ) : M unit :=
      assert_eq_nenv env.nil          env.nil            := pure tt;
      assert_eq_nenv (env.snoc δ _ t) (env.snoc δ' _ t') :=
        bind (assert_eq_nenv δ δ') (fun _ => assert_formula (t = t')).

    Fixpoint produce {Σ} (asn : Assertion Σ) (ι : Valuation Σ) : M unit :=
      match asn with
      | asn.formula fml =>
          assume_formula (instprop fml ι)
      | asn.chunk c =>
          produce_chunk (inst c ι)
      | asn.chunk_angelic c =>
          produce_chunk (inst c ι)
      | asn.pattern_match s pat rhs =>
          '(existT pc δpc) <-
            demonic_pattern_match pat (inst s ι) ;;
          produce (rhs pc) (ι ►► δpc)
      | asn.sep a1 a2 =>
          _ <- produce a1 ι ;;
          produce a2 ι
      | asn.or a1 a2 =>
          demonic_binary (produce a1 ι) (produce a2 ι)
      | asn.exist ς τ a =>
          t <- demonic τ ;;
          produce a (env.snoc ι (ς∷τ) t)
      | asn.debug =>
          debug (pure tt)
      end.

    Fixpoint consume {Σ} (asn : Assertion Σ) (ι : Valuation Σ) : M unit :=
      match asn with
      | asn.formula fml =>
          assert_formula (instprop fml ι)
      | asn.chunk c =>
          consume_chunk (inst c ι)
      | asn.chunk_angelic c =>
          consume_chunk (inst c ι)
      | asn.pattern_match s pat rhs =>
          '(existT pc δpc) <- angelic_pattern_match pat (inst s ι) ;;
          consume (rhs pc) (ι ►► δpc)
      | asn.sep a1 a2 =>
          _ <- consume a1 ι ;;
          consume a2 ι
      | asn.or a1 a2 =>
          angelic_binary (consume a1 ι) (consume a2 ι)
      | asn.exist ς τ a =>
          t <- angelic τ ;;
          consume a (env.snoc ι (ς∷τ) t)
      | asn.debug =>
          debug (pure tt)
      end.

    Definition call_contract [Δ τ] (c : SepContract Δ τ) (args : CStore Δ) : M (Val τ) :=
      match c with
      | MkSepContract _ _ Σe δ req result ens =>
          ι <- angelic_ctx Σe ;;
          assert_eq_nenv (inst δ ι) args ;;
          consume req ι ;;
          v <- demonic τ ;;
          produce ens (env.snoc ι (result∷τ) v) ;;
          pure v
      end.

    Definition call_lemma [Δ] (lem : Lemma Δ) (vs : CStore Δ) : M unit :=
      match lem with
      | MkLemma _ Σe δ req ens =>
          ι <- angelic_ctx Σe ;;
          assert_eq_nenv (inst δ ι) vs ;;
          consume req ι ;;
          produce ens ι
      end.

    End Derived.
    #[global] Arguments angelic_ctx {M _ N} Δ.
    #[global] Arguments demonic_ctx {M _ N} Δ.

  End CHeapSpecM.
  Export CHeapSpecM (CHeapSpecM).

  (* Monotonicity of the operations of a [CHeapSpecM] monad, with respect to a
     lifting [RM] of relations on results to relations on computations. *)
  Module MHeapSpecM.

    Import CHeapSpecM.

    Class MHeapSpecM M {cm : CHeapSpecM M} (RM : forall {A}, relation A -> relation (M A)) :
      Prop :=
      { mon_pure {A} {MA : relation A} :: Proper (MA ==> RM MA) pure;
        mon_bind {A B} {MA : relation A} {MB : relation B} ::
          Proper (RM MA ==> (MA ==> RM MB) ==> RM MB) bind;
        mon_error {A} {MA : relation A} :: Proper (RM MA) error;
        mon_block {A} {MA : relation A} :: Proper (RM MA) block;
        mon_angelic σ :: Proper (RM eq) (angelic σ);
        mon_demonic σ :: Proper (RM eq) (demonic σ);
        mon_angelic_binary {A} {MA : relation A} ::
          Proper (RM MA ==> RM MA ==> RM MA) angelic_binary;
        mon_demonic_binary {A} {MA : relation A} ::
          Proper (RM MA ==> RM MA ==> RM MA) demonic_binary;
        mon_assert_formula fml :: Proper (RM eq) (assert_formula fml);
        mon_assume_formula fml :: Proper (RM eq) (assume_formula fml);
        mon_angelic_pattern_match {N : Set} {σ} (pat : Pattern (N:=N) σ) v ::
          Proper (RM eq) (angelic_pattern_match pat v);
        mon_demonic_pattern_match {N : Set} {σ} (pat : Pattern (N:=N) σ) v ::
          Proper (RM eq) (demonic_pattern_match pat v);
        mon_debug {A} {MA : relation A} :: Proper (RM MA ==> RM MA) debug;
        mon_produce_chunk c :: Proper (RM eq) (produce_chunk c);
        mon_consume_chunk c :: Proper (RM eq) (consume_chunk c);
        mon_read_register {τ} (reg : 𝑹𝑬𝑮 τ) :: Proper (RM eq) (read_register reg);
        mon_write_register {τ} (reg : 𝑹𝑬𝑮 τ) v ::
          Proper (RM eq) (write_register reg v);
      }.
    #[global] Arguments MHeapSpecM M {cm} RM.

    Section Derived.

    Context `{mm : MHeapSpecM M RM}.

    #[export] Instance mon_angelic_ctx {N : Set} (Δ : NCtx N Ty) :
      Proper (RM eq) (angelic_ctx Δ).
    Proof. induction Δ; cbn; solve_monotonic. Qed.

    #[export] Instance mon_demonic_ctx {N : Set} (Δ : NCtx N Ty) :
      Proper (RM eq) (demonic_ctx Δ).
    Proof. induction Δ; cbn; solve_monotonic. Qed.

    #[export] Instance mon_assert_eq_nenv {N : Set} {Δ : NCtx N Ty} (δ δ' : NamedEnv Val Δ) :
      Proper (RM eq) (assert_eq_nenv δ δ').
    Proof.
      induction δ; env.destroy δ'; cbn; solve_monotonic.
    Qed.

    #[export] Instance mon_produce {Σ} (asn : Assertion Σ) ι :
      Proper (RM eq) (produce asn ι).
    Proof. induction asn; cbn [produce]; solve_monotonic. Qed.

    #[export] Instance mon_consume {Σ} (asn : Assertion Σ) ι :
      Proper (RM eq) (consume asn ι).
    Proof. induction asn; cbn [consume]; solve_monotonic. Qed.

    #[export] Instance mon_call_contract
      [Δ τ] (c : SepContract Δ τ) (args : CStore Δ) :
      Proper (RM eq) (call_contract c args).
    Proof. destruct c; cbn [call_contract]; solve_monotonic. Qed.

    #[export] Instance mon_call_lemma
      [Δ] (lem : Lemma Δ) (vs : CStore Δ) :
      Proper (RM eq) (call_lemma lem vs).
    Proof. destruct lem; cbn [call_lemma]; solve_monotonic. Qed.

    End Derived.

  End MHeapSpecM.
  Export MHeapSpecM (MHeapSpecM).
  Export (hints) MHeapSpecM.

End ShallowMonadClassesOn.
