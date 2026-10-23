(******************************************************************************)
(* Copyright (c) 2020 Dominique Devriese, Sander Huyghebaert, Steven Keuchel  *)
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
     Classes.Morphisms
     Classes.Morphisms_Prop
     Classes.RelationClasses
     Lists.List
     NArith.NArith
     Program.Tactics
     Relations.Relation_Definitions
     Strings.String
     ZArith.BinInt.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Notations
     Prelude
     Sep.Hoare
     Sep.Logic
     Signature.

From stdpp Require base list option.

Import ctx.notations.
Import env.notations.
Import ListNotations.
Import SignatureNotations.

Set Implicit Arguments.


Open Scope signature_scope.

Module Type NewShallowExecOn
  (Import B : Base)
  (Import SIG : Signature B)
  (Import PROG : Program B)
  (Import PLOG : ProgramLogic B SIG PROG).

  Import iris.proofmode.proofmode.

  (* Interface of monads with the pure verification effects, i.e. those that
     do not need access to the store or the heap. *)
  Module CPureSpecM.

    Class CPureSpecM (M : Type -> Type) : Type :=
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

    Module notations.

      Infix "⊗" := demonic_binary (at level 40, left associativity) : mut_scope.
      Infix "⊕" := angelic_binary (at level 50, left associativity) : mut_scope.

      Notation "' x <- ma ;; mb" :=
        (bind ma (fun x => mb))
          (at level 20, x pattern, ma at next level, mb at level 200, right associativity,
             format "' x  <-  ma  ;;  mb") : mut_scope.
      Notation "x <- ma ;; mb" :=
        (bind ma (fun x => mb))
          (at level 20, ma at next level, mb at level 200, right associativity) : mut_scope.
      Notation "ma ;; mb" := (bind ma (fun _ => mb)) : mut_scope.

    End notations.
    Import notations.

    (* Operations that are derived from the interface. *)
    Section Derived.

      Context {M} {pureM : CPureSpecM M}.
      #[local] Open Scope mut_scope.

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
          end%ctx.

      Definition angelic_list' {A} : A -> list A -> M A :=
        fix rec d xs :=
          match xs with
          | nil        => pure d
          | cons x xs  => pure d ⊕ rec x xs
          end.

      Definition angelic_list {A} (xs : list A) : M A :=
        match xs with
        | nil       => error
        | cons x xs => angelic_list' x xs
        end.

      Definition demonic_list' {A} : A -> list A -> M A :=
        fix rec d xs :=
          match xs with
          | nil        => pure d
          | cons x xs  => pure d ⊗ rec x xs
          end.

      Definition demonic_list {A} (xs : list A) : M A :=
        match xs with
        | nil       => block
        | cons x xs => demonic_list' x xs
        end.

      Definition angelic_finite F `{finite.Finite F} : M F :=
        angelic_list (finite.enum F).

      Definition demonic_finite F `{finite.Finite F} : M F :=
        demonic_list (finite.enum F).

      (* The paper uses asserted equalities between multiple types, but the
         symbolic executor can in fact only assert equalities between symbolic
         terms. We mirror the structure of the symbolic execution and also
         traverse (the statically known parts) of other data structures. *)
      Equations(noeqns) assert_eq_env [Δ : Ctx Ty]
        (δ δ' : Env Val Δ) : M unit :=
        assert_eq_env env.nil          env.nil            := pure tt;
        assert_eq_env (env.snoc δ _ t) (env.snoc δ' _ t') :=
          bind (assert_eq_env δ δ') (fun _ => assert_formula (t = t')).

      Equations(noeqns) assert_eq_nenv {N : Set} [Δ : NCtx N Ty]
        (δ δ' : NamedEnv Val Δ) : M unit :=
        assert_eq_nenv env.nil          env.nil            := pure tt;
        assert_eq_nenv (env.snoc δ _ t) (env.snoc δ' _ t') :=
          bind (assert_eq_nenv δ δ') (fun _ => assert_formula (t = t')).

      Definition pattern_match {N : Set} {A σ} (v : Val σ) (pat : Pattern (N:=N) σ)
        (k : forall (pc : PatternCase pat), NamedEnv Val (PatternCaseCtx pc) -> M A) :
        M A :=
        let (pc,δpc) := pattern_match_val pat v in k pc δpc.

    End Derived.

  End CPureSpecM.
  Export CPureSpecM (CPureSpecM).

  (* Interface of monads that additionally have a heap. *)
  Module CHeapSpecM.

    Import CPureSpecM CPureSpecM.notations.

    Class CHeapSpecM (M : Type -> Type) : Type :=
      { produce_chunk : SCChunk -> M unit;
        consume_chunk : SCChunk -> M unit;
      }.
    #[global] Arguments produce_chunk {M _} c.
    #[global] Arguments consume_chunk {M _} c.

    Section Derived.

      Context {M} {pureM : CPureSpecM M} {heapM : CHeapSpecM M}.
      #[local] Open Scope mut_scope.

      Fixpoint produce {Σ} (asn : Assertion Σ) (ι : Valuation Σ) : M unit :=
        match asn with
        | asn.formula fml => assume_formula (instprop fml ι)
        | asn.chunk c     => produce_chunk (inst c ι)
        | asn.chunk_angelic c => produce_chunk (inst c ι)
        | asn.pattern_match s pat rhs =>
            pattern_match
              (inst (T := fun Σ => Term Σ _) s ι)
              pat
              (fun pc δpc => produce (rhs pc) (ι ►► δpc))
        | asn.sep a1 a2   => _ <- produce a1 ι ;; produce a2 ι
        | asn.or a1 a2    => produce a1 ι ⊗ produce a2 ι
        | asn.exist ς τ a =>
          v <- demonic τ ;;
          produce a (env.snoc ι (ς∷τ) v)
        | asn.debug => pure tt
        end.

      Fixpoint consume {Σ} (asn : Assertion Σ) (ι : Valuation Σ) : M unit :=
        match asn with
        | asn.formula fml => assert_formula (instprop fml ι)
        | asn.chunk c     => consume_chunk (inst c ι)
        | asn.chunk_angelic c => consume_chunk (inst c ι)
        | asn.pattern_match s pat rhs =>
            pattern_match
              (inst (T := fun Σ => Term Σ _) s ι)
              pat
              (fun pc δpc => consume (rhs pc) (ι ►► δpc))
        | asn.sep a1 a2   => _ <- consume a1 ι ;; consume a2 ι
        | asn.or a1 a2    => consume a1 ι ⊕ consume a2 ι
        | asn.exist ς τ a =>
          v <- angelic τ ;;
          consume a (env.snoc ι (ς∷τ) v)
        | asn.debug => pure tt
        end.

      Definition call_contract {Δ τ} (ctr : SepContract Δ τ) (args : CStore Δ) :
        M (Val τ) :=
        match ctr with
        | MkSepContract _ _ Σe δ req result ens =>
            ι <- angelic_ctx Σe ;;
            _ <- assert_eq_nenv args (inst δ ι) ;;
            _ <- consume req ι ;;
            v <- demonic τ ;;
            _ <- produce ens (env.snoc ι (result∷τ) v) ;;
            pure v
        end.

      Definition call_lemma {Δ} (lem : Lemma Δ) (args : CStore Δ) : M unit :=
        match lem with
        | MkLemma _ Σe δ req ens =>
            ι <- angelic_ctx Σe ;;
            _ <- assert_eq_nenv args (inst δ ι) ;;
            _ <- consume req ι ;;
            produce ens ι
        end.

    End Derived.

  End CHeapSpecM.
  Export CHeapSpecM (CHeapSpecM).

  (* The store transformer. It is indexed by two program variable contexts Γ1
     Γ2 that encode the shape of the program variable store before and after
     execution. *)
  Module CStoreT.

    Import CPureSpecM CHeapSpecM.

    Section WithMonad.

      Context {M} {pureM : CPureSpecM M} {heapM : CHeapSpecM M}.

      Definition CStoreT (Γ1 Γ2 : PCtx) (A : Type) : Type :=
        CStore Γ1 -> M (A * CStore Γ2).

      Definition lift {Γ A} (m : M A) : CStoreT Γ Γ A :=
        fun δ => CPureSpecM.bind m (fun a => CPureSpecM.pure (a, δ)).
      Definition evalCStoreT {Γ1 Γ2 A} (m : CStoreT Γ1 Γ2 A) (δ : CStore Γ1) : M A :=
        CPureSpecM.bind (m δ) (fun '(a,_) => CPureSpecM.pure a).
      Definition state {Γ1 Γ2 A} (f : CStore Γ1 -> A * CStore Γ2) : CStoreT Γ1 Γ2 A :=
        fun δ => CPureSpecM.pure (f δ).

      Definition pure {Γ A} (a : A) : CStoreT Γ Γ A :=
        state (fun δ => (a, δ)).
      Definition bind {Γ1 Γ2 Γ3 A B} (m : CStoreT Γ1 Γ2 A) (f : A -> CStoreT Γ2 Γ3 B) :
        CStoreT Γ1 Γ3 B :=
        fun δ1 => CPureSpecM.bind (m δ1) (fun '(a,δ2) => f a δ2).

      Definition pushpop {A Γ1 Γ2 x σ} (v : Val σ)
        (m : CStoreT (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) A) : CStoreT Γ1 Γ2 A :=
        fun δ1 =>
          CPureSpecM.bind (m δ1.[x∷σ ↦ v])
            (fun '(a,δ2) => CPureSpecM.pure (a, env.tail δ2)).
      Definition pushspops {A Γ1 Γ2 Δ} (δΔ : CStore Δ)
        (m : CStoreT (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) A) : CStoreT Γ1 Γ2 A :=
        fun δ1 =>
          CPureSpecM.bind (m (δ1 ►► δΔ))
            (fun '(a,δ2) => CPureSpecM.pure (a, env.drop Δ δ2)).
      Definition get_local {Γ} : CStoreT Γ Γ (CStore Γ) :=
        state (fun δ => (δ, δ)).
      Definition put_local {Γ1 Γ2} (δ : CStore Γ2) : CStoreT Γ1 Γ2 unit :=
        state (fun _ => (tt, δ)).

      Definition eval_exp {Γ σ} (e : Exp Γ σ) : CStoreT Γ Γ (Val σ) :=
        state (fun δ => (eval e δ, δ)).
      Definition eval_exps {Γ} {σs : PCtx} (es : NamedEnv (Exp Γ) σs) :
        CStoreT Γ Γ (CStore σs) :=
        state (fun δ => (evals es δ, δ)).
      Definition assign {Γ} x {σ} {xIn : (x∷σ ∈ Γ)%katamaran} (v : Val σ) :
        CStoreT Γ Γ unit :=
        state (fun δ => (tt, δ ⟪ x ↦ v ⟫)).

      Definition pattern_match {N : Set} {A σ Γ1 Γ2} (v : Val σ) (pat : Pattern (N:=N) σ)
        (k : forall (c : PatternCase pat), NamedEnv Val (PatternCaseCtx c) -> CStoreT Γ1 Γ2 A) :
        CStoreT Γ1 Γ2 A :=
        fun δ1 => let (pc,δpc) := pattern_match_val pat v in k pc δpc δ1.

      #[local] Notation "x <- ma ;; mb" :=
        (bind ma (fun x => mb))
          (at level 20, ma at next level, mb at level 200, right associativity).

      (* The paper discusses the case that a function call is replaced by
         interpreting the contract instead. However, this is not always
         convenient. We therefore make contracts for functions optional and if a
         function does not have a contract, we continue executing the body of
         the called function. A parameter [inline_fuel] bounds the number of
         allowed levels before failing execution. Therefore, we write the
         executor in an open-recusion style and [Exec] is the closed type of
         such an executor. *)
      Definition ExecCall := forall Δ τ, 𝑭 Δ τ -> CStore Δ -> M (Val τ).
      Definition ExecCallForeign := forall Δ τ, 𝑭𝑿 Δ τ -> CStore Δ -> M (Val τ).
      Definition ExecLemma := forall Δ, 𝑳 Δ -> CStore Δ -> M unit.
      Definition ExecFail := forall Γ τ (s : Val ty.string), CStoreT Γ Γ (Val τ).
      Definition Exec := forall Γ τ (s : Stm Γ τ), CStoreT Γ Γ (Val τ).

      Section ExecAux.

        Context {SPEC : Specification}.
        Variable exec_call_foreign : ExecCallForeign.
        Variable exec_lemma : ExecLemma.
        Variable exec_call : ExecCall.
        Variable exec_fail : ExecFail.

        (* The openly-recursive executor. *)
        Definition exec_aux : Exec :=
          fix exec {Γ τ} (s : Stm Γ τ) : CStoreT Γ Γ (Val τ) :=
            match s with
            | stm_val _ l => pure l
            | stm_exp e => eval_exp e
            | stm_let x σ s k =>
              v <- exec s ;;
              pushpop v (exec k)
            | stm_block δ k =>
              pushspops δ (exec k)
            | stm_assign x e =>
              v <- exec e ;;
              _ <- assign (x := x) v ;;
              pure v
            | stm_call f es =>
              args <- eval_exps es ;;
              lift (exec_call f args)
            | stm_foreign f es =>
              ts <- eval_exps es ;;
              lift (exec_call_foreign f ts)
            | stm_lemmak l es k =>
              ts <- eval_exps es ;;
              _  <- lift (exec_lemma l ts) ;;
              exec k
            | stm_call_frame δ' s =>
              δ <- get_local ;;
              _ <- put_local δ' ;;
              v <- exec s ;;
              _ <- put_local δ ;;
              pure v
            | stm_seq e k => _ <- exec e ;; exec k
            | stm_assertk e1 _ k =>
              v <- eval_exp e1 ;;
              _ <- lift (assert_formula
                           (if fail_rule_pre then True else v <> false)) ;;
              _ <- lift (assume_formula (v = true)) ;;
              exec k
            | stm_fail _ s =>
              exec_fail _ s
            | stm_pattern_match s pat rhs =>
              v <- exec s ;;
              pattern_match v pat
                (fun pc δpc => pushspops δpc (exec (rhs pc)))
            | stm_read_register reg =>
              v <- lift (angelic τ) ;;
              let c := chunk_ptsreg reg v in
              _ <- lift (consume_chunk c) ;;
              _ <- lift (produce_chunk c) ;;
              pure v
            | stm_write_register reg e =>
              v__old <- lift (angelic τ) ;;
              _    <- lift (consume_chunk (chunk_ptsreg reg v__old)) ;;
              v__new <- eval_exp e ;;
              _    <- lift (produce_chunk (chunk_ptsreg reg v__new)) ;;
              pure v__new
            | stm_bind s k =>
              v <- exec s ;;
              exec (k v)
            | stm_debugk k =>
              exec k
            end.

      End ExecAux.

    End WithMonad.
    #[global] Arguments CStoreT M Γ1 Γ2 A : clear implicits.
    #[global] Arguments ExecCall M : clear implicits.
    #[global] Arguments ExecCallForeign M : clear implicits.
    #[global] Arguments ExecLemma M : clear implicits.
    #[global] Arguments ExecFail M : clear implicits.
    #[global] Arguments Exec M : clear implicits.
    #[global] Arguments assign {M _ Γ} x {σ xIn} v.
    #[global] Arguments exec_aux {M _ _ SPEC} _ _ _ _ [Γ τ] !s.

  End CStoreT.
  Export CStoreT (CStoreT, ExecCall, ExecCallForeign, ExecLemma, ExecFail, Exec).

  (* The executor, independent of the monad instance. *)
  Section WithSpec.

    Import CPureSpecM CPureSpecM.notations CHeapSpecM.

    Context {M} {pureM : CPureSpecM M} {heapM : CHeapSpecM M}.
    Context {SPEC : Specification}.
    Open Scope mut_scope.

    Definition exec_contract (exec : Exec M) {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) :
      M unit :=
      match c with
      | MkSepContract _ _ lvars pats req result ens =>
          lenv <- demonic_ctx lvars ;;
          _    <- produce req lenv ;;
          v    <- CStoreT.evalCStoreT (exec _ _ s) (inst pats lenv) ;;
          consume ens (env.snoc lenv (result∷τ) v)
      end.

    Definition exec_call_error_no_fuel : ExecCall M :=
      fun Δ τ f args => error.

    Definition cexec_call_foreign : ExecCallForeign M :=
      fun Δ τ f args => call_contract (CEnvEx f) args.

    Definition debug_lemma [Δ] (f : 𝑳 Δ) (args : CStore Δ) : M unit :=
      pure tt.

    Definition cexec_lemma : ExecLemma M :=
      fun Δ l args =>
        _ <- debug_lemma l args ;;
        call_lemma (LEnv l) args.

    Definition debug_call [Δ τ] (f : 𝑭 Δ τ) (args : CStore Δ) : M unit :=
      pure tt.

    Definition cexec_fail : ExecFail M :=
      fun Γ τ s => CStoreT.lift (if fail_rule_pre then block else error).

    (* If a function does not have a contract, we continue executing the body of
       the called function. A parameter [inline_fuel] bounds the number of
       allowed levels before failing execution. *)
    Fixpoint cexec_call (inline_fuel : nat) : ExecCall M :=
      fun Δ τ f args =>
        _ <- debug_call f args ;;
        (* Let's first see if we have a contract defined for function [f]
           and then if we have enough fuel for inlining. *)
        match CEnv f , inline_fuel with
        | Some c , _ =>
            (* YES: Execute the call by interpreting the contract. *)
            call_contract c args
        | None   , 0 =>
            (* Out of fuel *)
            exec_call_error_no_fuel f args
        | None   , S n =>
            CStoreT.evalCStoreT
              (CStoreT.exec_aux cexec_call_foreign cexec_lemma
                 (cexec_call n) cexec_fail (FunDef f))
              args
        end.

    Definition cexec (inline_fuel : nat) : Exec M :=
      CStoreT.exec_aux cexec_call_foreign cexec_lemma
        (cexec_call inline_fuel) cexec_fail.

  End WithSpec.
  #[global] Arguments cexec {M _ _ SPEC} _ [_ _] s : simpl never.

  (* The predicate transformer instance, which is used for verification. *)
  Module CPureSpec.
  Section WithProp.

    Context {L} {biA : BiAffine L} {PI : PredicateDef L}.

    Bind Scope bi_scope with L.

    (* The pure backwards predicate transformer monad. *)
    Definition CPureSpec (A : Type) : Type :=
      (A -> L) -> L.

    Definition Monotonic {A} : relation (CPureSpec A) :=
      (A ::> (⊢)) ==> (⊢).

    #[export] Instance monotonic_transitive {A} : Transitive (@Monotonic A).
    Proof.
      intros f g h fg gh P Q PQ. transitivity (g Q).
      - now apply fg.
      - now apply gh.
    Qed.

    (* For counting the different execution paths of the shallow executor we use
     different aliases for False and True to distinguish between them. TRUE
     and FALSE represent execution paths that are pruned, i.e. do not reach
     the end of a function, and FINISH encodes the successful execution
     case. *)
    Definition FALSE : L := False.
    Definition TRUE : L := True.
    Definition FINISH : L := True.
    #[global] Typeclasses Opaque TRUE.
    #[global] Typeclasses Opaque FALSE.
    #[global] Typeclasses Opaque FINISH.

    Local Ltac solve_wp :=
      repeat
        (try progress subst;
         lazymatch goal with
         (* These first rules do not change the provability if the goal, i.e.
            these steps are always complete. *)
         | x : NamedEnv Val [ctx] |- _ => destruct (env.view x)
         | x: NamedEnv Val (_ ▻ _) |- _ => destruct (env.view x)
         | |- _ ⊣⊢ _ => apply bi.entails_anti_sym
         | |- False ⊢ _ => apply bi.False_elim
         | |- _ ⊢ True => apply bi.True_intro
         | |- (∃ x : _, _) ⊢ _ => apply bi.exist_elim; intros ?
         | |- _ ⊢ ∀ x : _, _ => apply bi.forall_intro; intros ?
         | |- ?P ∧ _  ⊢ ?P => apply bi.and_elim_l
         | |- _  ∧ ?P ⊢ ?P => apply bi.and_elim_r
         | |- ⌜_⌝ ∧ _ ⊢ _ => apply bi.impl_elim_r'
         | |- _ ∧ ⌜_⌝ ⊢ _ => apply bi.impl_elim_l'
         | |- _ ⊢ ⌜?x = ?x⌝ => apply bi.pure_intro; reflexivity
         | |- _ ⊢ ⌜_⌝ → _ => rewrite bi.pure_impl_forall;
                             apply bi.forall_intro; intros ?
         | |- _ ⊢ _ ∧ _ => apply bi.and_intro
         | |- _ ⊢ ⌜?P⌝  => is_ground P; apply bi.pure_intro; intuition auto; fail
         | _ => easy
         end).

    Definition run : CPureSpec unit → L :=
      (* We use the FINISH alias of True for the purpose
       of counting nodes in a shallowly-generated VC. *)
      fun m => m (fun _ => FINISH).

    Definition pure {A : Type} : A → CPureSpec A :=
      fun a POST => POST a.
    Definition bind {A B} :
      CPureSpec A → (A → CPureSpec B) → CPureSpec B :=
      fun m f POST => m (fun a1 => f a1 POST).
    Definition error {A} : CPureSpec A :=
      fun POST => FALSE.
    Definition block {A} : CPureSpec A :=
      fun POST => TRUE.
    Definition angelic (σ : Ty) : CPureSpec (Val σ) :=
      fun POST => (∃ v : Val σ, POST v)%I.
    Definition demonic σ : CPureSpec (Val σ) :=
      fun POST => (∀ v : Val σ, POST v)%I.
    Definition angelic_binary {A} :
      CPureSpec A -> CPureSpec A -> CPureSpec A :=
      fun m1 m2 POST =>
        (m1 POST ∨ m2 POST)%I.
    Definition demonic_binary {A} :
      CPureSpec A -> CPureSpec A -> CPureSpec A :=
      fun m1 m2 POST =>
        (m1 POST ∧ m2 POST)%I.
    Definition assume_formula (fml : Prop) : CPureSpec unit :=
      fun POST => (⌜fml⌝ → POST tt)%I.
    Definition assert_formula (fml : Prop) : CPureSpec unit :=
      fun POST => (⌜fml⌝ ∧ POST tt)%I.
    Definition produce_chunk (c : SCChunk) : CPureSpec unit :=
      fun POST => (interpret_scchunk c -∗ POST tt)%I.
    Definition consume_chunk (c : SCChunk) : CPureSpec unit :=
      fun POST => (interpret_scchunk c ∗ POST tt)%I.
    #[global] Arguments pure {A} a _ /.
    #[global] Arguments bind {A B} m f _ /.
    #[global] Arguments error {A} _ /.
    #[global] Arguments block {A} _ /.
    #[global] Arguments angelic σ _ /.
    #[global] Arguments demonic σ _ /.
    #[global] Arguments angelic_binary {A} m1 m2 _ /.
    #[global] Arguments demonic_binary {A} m1 m2 _ /.
    #[global] Arguments assume_formula _ _ /.
    #[global] Arguments assert_formula _ _ /.
    #[global] Arguments produce_chunk c _ /.
    #[global] Arguments consume_chunk c _ /.

    #[global] Instance purespecm : CPureSpecM CPureSpec :=
      {| CPureSpecM.pure := @pure;
         CPureSpecM.bind := @bind;
         CPureSpecM.error := @error;
         CPureSpecM.block := @block;
         CPureSpecM.angelic := angelic;
         CPureSpecM.demonic := demonic;
         CPureSpecM.angelic_binary := @angelic_binary;
         CPureSpecM.demonic_binary := @demonic_binary;
         CPureSpecM.assert_formula := assert_formula;
         CPureSpecM.assume_formula := assume_formula;
      |}.

    #[global] Instance heapspecm : CHeapSpecM CPureSpec :=
      {| CHeapSpecM.produce_chunk := produce_chunk;
         CHeapSpecM.consume_chunk := consume_chunk;
      |}.

    Section Nondeterminism.

      Import CPureSpecM.

      Lemma wp_angelic_ctx {N : Set} {Δ : NCtx N Ty} (Φ : NamedEnv Val Δ -> L) :
        angelic_ctx (M := CPureSpec) Δ Φ ⊣⊢ ∃ vs : NamedEnv Val Δ, Φ vs.
      Proof.
        revert Φ; induction Δ as [|Δ IHΔ [x σ]]; intros Φ; cbn; [|rewrite IHΔ].
        - iSplit; [iIntros "H"; now iExists [env]|].
          iIntros "(%vs & H)". now destruct (env.view vs).
        - iSplit.
          + iIntros "(%vs & %v & H)". now iExists (vs ► (x∷σ ↦ v)).
          + iIntros "(%vs & H)". destruct (env.view vs) as [vs v].
            now iExists vs, v.
      Qed.

      Lemma wp_demonic_ctx {N : Set} {Δ : NCtx N Ty} (Φ : NamedEnv Val Δ -> L) :
        demonic_ctx (M := CPureSpec) Δ Φ ⊣⊢ ∀ vs : NamedEnv Val Δ, Φ vs.
      Proof.
        revert Φ; induction Δ as [|Δ IHΔ [x σ]]; intros Φ; cbn; [|rewrite IHΔ].
        - iSplit; [iIntros "H %vs"; now destruct (env.view vs)|].
          iIntros "H". iApply "H".
        - iSplit.
          + iIntros "H %vs". destruct (env.view vs) as [vs v]. iApply "H".
          + iIntros "H %vs %v". iApply "H".
      Qed.

      Lemma wp_angelic_list' {A} (xs : list A) (Φ : A -> L) :
        ∀ d, angelic_list' (M := CPureSpec) d xs Φ ⊣⊢
               ∃ x : A, ⌜d = x \/ In x xs⌝ ∧ Φ x.
      Proof.
        induction xs; cbn; intros d.
        - iSplit.
          + iIntros "HΦ". iExists d. iSplit; auto.
          + iIntros "(%x & %Heq & HΦ)". destruct Heq; now subst.
        - rewrite IHxs. clear IHxs. iSplit.
          + iIntros "[HΦ|(%x & %Heq & HΦ)]".
            * iExists d. iSplit; auto.
            * iExists x. iSplit; auto.
          + iIntros "(%x & %Heq & HΦ)". destruct Heq.
            * iLeft. now subst.
            * iRight. iExists x. iSplit; auto.
      Qed.

      Lemma wp_angelic_list {A} (xs : list A) (Φ : A -> L) :
        angelic_list (M := CPureSpec) xs Φ ⊣⊢ ∃ x : A, ⌜List.In x xs⌝ ∧ Φ x.
      Proof.
        destruct xs; cbn.
        - unfold FALSE. solve_wp.
        - apply wp_angelic_list'.
      Qed.

      Lemma wp_demonic_list' {A} (xs : list A) (Φ : A -> L) :
        ∀ d, demonic_list' (M := CPureSpec) d xs Φ ⊣⊢
               ∀ x : A, ⌜d = x \/ In x xs⌝ → Φ x.
      Proof.
        induction xs; cbn; intros d.
        - iSplit.
          + iIntros "HΦ %x %Heq". destruct Heq; now subst.
          + iIntros "H". iApply "H". now iLeft.
        - rewrite IHxs. clear IHxs. iSplit.
          + iIntros "HΦ %x %Heq". destruct Heq; [subst|].
            * now rewrite bi.and_elim_l.
            * rewrite bi.and_elim_r. now iApply "HΦ".
          + iIntros "HΦ". iSplit.
            * iApply "HΦ"; auto.
            * iIntros "%x %Heq". iApply "HΦ". auto.
      Qed.

      Lemma wp_demonic_list {A} (xs : list A) (POST : A -> L) :
        demonic_list (M := CPureSpec) xs POST ⊣⊢ ∀ x : A, ⌜List.In x xs⌝ → POST x.
      Proof.
        destruct xs; cbn.
        - unfold TRUE. solve_wp.
        - apply wp_demonic_list'.
      Qed.

    End Nondeterminism.

    Section Guards.

      Import CPureSpecM.

      Lemma wp_assert_formula {F : Prop} (Φ : unit -> L) :
        assert_formula (M := CPureSpec) F Φ ⊣⊢ (⌜F⌝ ∧ emp) ∗ Φ tt.
      Proof. cbn. now rewrite bi.and_emp bi.persistent_and_sep. Qed.

      Lemma wp_assume_formula {F : Prop} (Φ : unit -> L) :
        assume_formula (M := CPureSpec) F Φ ⊣⊢ ((⌜F⌝ ∧ emp) -∗ Φ tt).
      Proof. cbn. now rewrite bi.and_emp bi.impl_wand. Qed.

      Lemma wp_assert_eq_env {Δ : Ctx Ty} (δ δ' : Env Val Δ) :
        forall Φ,
          assert_eq_env (M := CPureSpec) δ δ' Φ ⊣⊢ ⌜δ = δ'⌝ ∧ Φ tt.
      Proof.
        induction δ; intros Φ; env.destroy δ'; cbn.
        - solve_wp.
        - rewrite IHδ env.inversion_eq_snoc. solve_wp.
      Qed.

      Lemma wp_assert_eq_nenv {N} {Δ : NCtx N Ty} (δ δ' : NamedEnv Val Δ) :
        forall POST,
          assert_eq_nenv (M := CPureSpec) δ δ' POST ⊣⊢ ⌜δ = δ'⌝ ∧ POST tt.
      Proof.
        unfold NamedEnv.
        induction δ; intros POST; env.destroy δ'; cbn.
        - solve_wp.
        - rewrite IHδ env.inversion_eq_snoc.
          solve_wp.
      Qed.

    End Guards.

    Section ProduceConsume.

      Import CHeapSpecM.

      Lemma wp_produce {Σ} {ι : Valuation Σ} {asn : Assertion Σ} (POST : unit -> L) :
        produce (M := CPureSpec) asn ι POST ⊣⊢ (asn.interpret asn ι -∗ POST tt).
      Proof.
        revert POST. induction asn; cbn - [inst inst_term]; intros POST.
        - apply wp_assume_formula.
        - now rewrite interpret_scchunk_inst.
        - now rewrite interpret_scchunk_inst.
        - unfold CPureSpecM.pattern_match. destruct pattern_match_val; auto.
        - now rewrite IHasn1 IHasn2 bi.wand_curry.
        - now rewrite IHasn1 IHasn2 wand_or_distr.
        - rewrite bi.exist_wand_forall.
          now apply bi.forall_proper.
        - now rewrite bi.emp_wand.
      Qed.

      Lemma wp_consume {Σ} {ι : Valuation Σ} {asn : Assertion Σ} (POST : unit -> L) :
        consume (M := CPureSpec) asn ι POST ⊣⊢ asn.interpret asn ι ∗ POST tt.
      Proof.
        revert POST. induction asn; cbn - [inst inst_term]; intros POST.
        - apply wp_assert_formula.
        - now rewrite interpret_scchunk_inst.
        - now rewrite interpret_scchunk_inst.
        - unfold CPureSpecM.pattern_match. destruct pattern_match_val; auto.
        - now rewrite IHasn1 IHasn2 bi.sep_assoc.
        - rewrite bi.sep_or_r.
          now apply bi.or_proper.
        - rewrite bi.sep_exist_r.
          now apply bi.exist_proper.
        - now rewrite bi.emp_sep.
      Qed.

    End ProduceConsume.

    Section Calls.

      Import CHeapSpecM.

      Definition call_contract' {Δ τ} (ctr : SepContract Δ τ) (args : CStore Δ) :
        CPureSpec (Val τ) :=
        fun POST =>
          match ctr with
          | MkSepContract _ _ Σe δ req result ens =>
              ∃ ι : Valuation Σe, ⌜args = inst δ ι⌝ ∧
              asn.interpret req ι ∗ (∀ v : Val τ, asn.interpret ens ι.[result∷τ ↦ v] -∗ POST v)
          end%I.

      Definition call_lemma' {Δ} (lem : Lemma Δ) (args : CStore Δ) : CPureSpec (Val ty.unit) :=
        fun POST =>
          match lem with
          | MkLemma _ Σe δ req ens =>
              ∃ ι : Valuation Σe, ⌜args = inst δ ι⌝ ∧
              asn.interpret req ι ∗ (asn.interpret ens ι -∗ POST tt)
          end%I.

      Lemma equiv_call_contract {Δ τ} (ctr : SepContract Δ τ) (args : CStore Δ) :
        forall (POST : Val τ -> L),
          call_contract (M := CPureSpec) ctr args POST ⊣⊢ call_contract' ctr args POST.
      Proof.
        intros POST; destruct ctr as [Σe δΔ req res ens]; cbn.
        rewrite wp_angelic_ctx. apply bi.exist_proper. intros ι.
        rewrite wp_assert_eq_nenv. apply bi.and_proper; [easy|].
        rewrite wp_consume. apply bi.sep_proper; [easy|].
        apply bi.forall_proper. intros v. apply wp_produce.
      Qed.

      Lemma equiv_call_lemma {Δ} (lem : Lemma Δ) (args : CStore Δ) :
        forall (POST : Val ty.unit -> L),
        call_lemma (M := CPureSpec) lem args POST ⊣⊢ call_lemma' lem args POST.
      Proof.
        intros POST; destruct lem as [Σe δΔ req ens]; cbn.
        rewrite wp_angelic_ctx. apply bi.exist_proper. intros ι.
        rewrite wp_assert_eq_nenv. apply bi.and_proper; [easy|].
        rewrite wp_consume. apply bi.sep_proper; [easy|].
        apply wp_produce.
      Qed.

      Instance monotonic_call_contract {Δ τ} (ctr : SepContract Δ τ) (args : CStore Δ) :
        Proper Monotonic (call_contract (M := CPureSpec) ctr args).
      Proof.
        intros P Q PQ. rewrite !equiv_call_contract.
        destruct ctr; cbn. now setoid_rewrite PQ.
      Qed.

      Instance monotonic_call_lemma {Δ} (lem : Lemma Δ) (args : CStore Δ) :
        Proper Monotonic (call_lemma (M := CPureSpec) lem args).
      Proof.
        intros P Q PQ. rewrite !equiv_call_lemma.
        destruct lem; cbn. now setoid_rewrite PQ.
      Qed.

    End Calls.

  End WithProp.
  End CPureSpec.
  Export CPureSpec (CPureSpec).
  #[export] Hint Unfold CPureSpec.Monotonic : typeclass_instances.

  Definition vcgen {L} {biA : BiAffine L} {PI : PredicateDef L} {SPEC : Specification}
    (inline_fuel : nat) {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : L :=
    CPureSpec.run (exec_contract (M := CPureSpec) (cexec inline_fuel) c body).

  Module Shallow.

    Section Soundness.
      Context {L} {biA : BiAffine L} {PI : PredicateDef L} {SPEC : Specification}.

      Definition ValidContract {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
        (* Use inline_fuel = 1 by default. *)
        ⊢ vcgen (L := L) 1 c body.

      Definition ValidContractCEnv : Prop :=
        forall (Δ : PCtx) (τ : Ty) (f : 𝑭 Δ τ) (c : SepContract Δ τ),
          CEnv f = Some c ->
          ValidContract c (FunDef f).

      (* Import CHeapSpecM. *)

      (* Lemma rule_syntactic' (ec : ExecCall) (ec_mon : Proper MonotonicCall ec) *)
      (*   (ex : Exec) (ex_mdl : Model ex) : *)
      (*   MonotonicCall ec (exec_call_inline ex) -> *)
      (*   MonotonicExec (exec_aux ec) ex. *)
      (* Proof. *)
      (*   intros. apply fold_exec_aux; [assumption|]. *)
      (*   transitivity (exec_open ex (exec_call_inline ex)). *)
      (*   apply exec_open_monotonic. *)
      (*   apply ex_monotonic; auto. *)
      (*   assumption. *)
      (*   intros Γ τ s P Q PQ δ. *)
      (*   transitivity (ex _ _ s P δ). *)
      (*   apply (rule_syntactic ex_mdl). *)
      (*   apply ex_monotonic; auto. *)
      (* Qed. *)

      (* Definition ValidContractSem (ex : Exec) {Δ σ} (body : Stm Δ σ) (contract : SepContract Δ σ) : L := *)
      (*   match contract with *)
      (*   | MkSepContract _ _ ctxΣ θΔ req res ens => *)
      (*       ∀ (ι : Valuation ctxΣ), *)
      (*         asn.interpret req ι -∗ *)
      (*          ex _ _ body (fun v _ => asn.interpret ens ι.[res∷σ ↦ v]) (inst θΔ ι) *)
      (*   end. *)

      (* Definition ValidContractEnvSem (ex : Exec) : L := *)
      (*   ∀ Δ σ (f : 𝑭 Δ σ), *)
      (*     match CEnv f with *)
      (*     | Some c => ValidContractSem ex (FunDef f) c *)
      (*     | None   => True *)
      (*     end%I. *)

      (* Lemma validcontractsem_monotonic : *)
      (*   Proper *)
      (*     (MonotonicExec ==> ∀ Γ τ, Stm Γ τ ::> SepContract Γ τ ::> (⊢)) *)
      (*     ValidContractSem. *)
      (* Proof. *)
      (*   intros ex1 ex2 ex_mon Γ τ s [Σe δΔ req res ens]; cbn. *)
      (*   apply bi.forall_mono'; intros ι. *)
      (*   apply bi.wand_mono'; [easy|]. *)
      (*   now apply ex_mon. *)
      (* Qed. *)

      (* Instance validcontractenvsem_monotonic : *)
      (*   Proper (MonotonicExec ==> (⊢)) ValidContractEnvSem. *)
      (* Proof. *)
      (*   intros ex1 ex2 ex_mon. *)
      (*   unfold ValidContractEnvSem. *)
      (*   apply bi.forall_mono'; intros Δ. *)
      (*   apply bi.forall_mono'; intros σ. *)
      (*   apply bi.forall_mono'; intros f. *)
      (*   destruct CEnv; [|easy]. *)
      (*   now apply validcontractsem_monotonic. *)
      (* Qed. *)

      (* Definition sound_shallow (vcenv : ValidContractCEnv) : *)
      (*   ⊢ ValidContractEnvSem (exec 1). *)
      (* Proof. *)
      (*   iIntros (Δ σ f). *)
      (*   specialize (vcenv Δ σ f). *)
      (*   destruct (CEnv f) as [ctr|]; [|auto]. *)
      (*   specialize (vcenv _ eq_refl). *)
      (*   unfold ValidContract in vcenv. *)
      (*   rewrite vcgen_equiv in vcenv. *)
      (*   destruct ctr as [Σe δΔ req res ens]. *)
      (*   iIntros (ι) "Hreq". *)
      (*   specialize (vcenv ι). *)
      (*   now iApply vcenv. *)
      (* Qed. *)

      (* Lemma soundness (ex : Exec) (exmdl : Model ex) : *)
      (*   ValidContractCEnv -> ⊢ ValidContractEnvSem ex. *)
      (* Proof. *)
      (*   unfold ValidContractCEnv. *)
      (*   intros vcenv. *)
      (*   apply bi.forall_intro. intros Δ. *)
      (*   apply bi.forall_intro. intros σ. *)
      (*   apply bi.forall_intro. intros f. *)
      (*   specialize (vcenv Δ σ f). *)
      (*   destruct (CEnv f) as [ctr|]; [|auto]. *)
      (*   specialize (vcenv ctr eq_refl). *)
      (*   destruct ctr as [ctxΣ θΔ req res ens]; cbn in *. *)
      (*   apply bi.forall_intro. intros ι. *)
      (*   rewrite env.Forall_forall in vcenv. *)
      (*   change (emp ⊢ ?P) with (⊢ P). *)
      (*   specialize (vcenv ι). revert vcenv. *)
      (*   apply bi.bi_emp_valid_mono. *)
      (*   rewrite CPureSpec.wp_produce. *)
      (*   apply bi.wand_mono'; [easy|]. *)
      (*   apply rule_syntactic'; auto. *)
      (*   apply exec_call_with_contracts_monotonic. *)
      (*   apply exec_error_initial. *)
      (*   apply rule_contract; auto. *)
      (*   intros ? ?. *)
      (*   rewrite CPureSpec.wp_consume. *)
      (*   unfold CPureSpec.FINISH. *)
      (*   now rewrite bi.sep_True. *)
      (* Qed. *)

    End Soundness.

    Module Statistics.

      Inductive PropShape : Type :=
      | psfork (P Q : PropShape)
      | psquant (P : PropShape)
      | pspruned
      | psfinish
      | psother.

      Fixpoint shape_to_stats (s : PropShape) : Stats :=
        match s with
        | psfork p q => plus_stats (shape_to_stats p) (shape_to_stats q)
        | psquant p  => shape_to_stats p
        | pspruned   => {| branches := 1; pruned := 1 |}
        | psfinish   => {| branches := 1; pruned := 0 |}
        | psother     => {| branches := 0; pruned := 0 |}
        end.

      (* See: Building a Reification Tactic that Recurses Under Binders
         http://adam.chlipala.net/cpdt/html/Cpdt.Reflection.html

         This calculates a deeply-embedded PropShape for a given Prop P
         for which we can then run shape_to_stats to calculate the
         number of different kinds of execution paths. *)
      Ltac reifyProp P :=
        match eval simpl in P with
        | forall (x : ?T), CPureSpec.TRUE => pspruned
        | forall (x : ?T), CPureSpec.FALSE => pspruned
        | forall (x : ?T), CPureSpec.FINISH => psfinish
        | forall (x : ?T), True => psother
        | forall (x : ?T), False => psother
        | forall (x : ?T), @?P1 x /\ @?P2 x =>
          let t1 := reifyProp (forall x : T, P1 x) in
          let t2 := reifyProp (forall x : T, P2 x) in
            constr:(psfork t1 t2)
        | forall (x : ?T), @?P1 x \/ @?P2 x =>
          let t1 := reifyProp (forall x : T, P1 x) in
          let t2 := reifyProp (forall x : T, P2 x) in
            constr:(psfork t1 t2)
        | forall (x : ?T), @?P1 x -> @?P2 x =>
          let t1 := reifyProp (forall x : T, P1 x) in
          let t2 := reifyProp (forall x : T, P2 x) in
            constr:(psfork t1 t2)
        | forall (x : ?T), forall (v : ?U), @?P x v =>
          let t := reifyProp (forall xv : T * U, P (fst xv) (snd xv)) in
            constr:(psquant t)
        | forall (x : ?T), exists (v : ?U), @?P x v =>
          let t := reifyProp (forall xv : T * U, P (fst xv) (snd xv)) in
            constr:(psquant t)
        | forall (x : ?T), _ = _ => psother
        | forall (x : ?T), Z.le _ _ => psother
        (* | _ => constr:(sprop P) *)
        end.

      Section WithSepLogic.
        Context {L} {biA : BiAffine L} {PI : PredicateDef L}.
        (* This typeclass approach seems to be much faster than the reifyProp
           tactic above. *)
        Class ShallowStats (P : L) :=
          stats : Stats.
        Arguments stats P {_}.

        (* We make these instances global so that users can simply use the
           calc tactic qualified without importing the rest of this module. *)
        #[global] Instance stats_true {L : bi} : ShallowStats CPureSpec.TRUE :=
          {| branches := 1; pruned := 1 |}.
        #[global] Instance stats_false : ShallowStats CPureSpec.FALSE :=
          {| branches := 1; pruned := 1 |}.
        #[global] Instance stats_finish : ShallowStats CPureSpec.FINISH :=
          {| branches := 1; pruned := 0 |}.
        (* We do not count regular True and False towards the statistics
           because they do not (should not) represent leaves of the shallow
           execution. *)
        #[global] Instance stats_true' : ShallowStats True :=
          {| branches := 0; pruned := 0 |}.
        #[global] Instance stats_false' : ShallowStats False :=
          {| branches := 0; pruned := 0 |}.

        #[global] Instance stats_eq {A} {x y : A} : ShallowStats ⌜x = y⌝ :=
          {| branches := 0; pruned := 0 |}.
        #[global] Instance stats_zle {x y : Z} : ShallowStats ⌜Z.le x y⌝ :=
          {| branches := 0; pruned := 0 |}.

        #[global] Instance stats_and `{ShallowStats P, ShallowStats Q} :
          ShallowStats (P ∧ Q) := plus_stats (stats P) (stats Q).
        #[global] Instance stats_or `{ShallowStats P, ShallowStats Q} :
          ShallowStats (P ∨ Q) := plus_stats (stats P) (stats Q).
        #[global] Instance stats_impl `{ShallowStats P, ShallowStats Q} :
          ShallowStats (P → Q) := plus_stats (stats P) (stats Q).
        #[global] Instance stats_star `{ShallowStats P, ShallowStats Q} :
          ShallowStats (P ∗ Q) := plus_stats (stats P) (stats Q).
        #[global] Instance stats_wand `{ShallowStats P, ShallowStats Q} :
          ShallowStats (P -∗ Q) := plus_stats (stats P) (stats Q).

        Axiom undefined : forall A, A.

        #[global] Instance stats_forall {A} {B : A -> L} {SP : forall a, ShallowStats (B a)} :
          ShallowStats (∀ a : A, B a) := SP (undefined A).
        #[global] Instance stats_exists {A} {B : A -> L} {SP : forall a, ShallowStats (B a)} :
          ShallowStats (∃ a : A, B a) := SP (undefined A).

      End WithSepLogic.

      Ltac calc fnc :=
        let P := eval compute - [CPureSpec.FALSE CPureSpec.TRUE CPureSpec.FINISH
                                 negb Z.mul Z.opp Z.compare Z.add Z.geb Z.eqb
                                 Z.leb Z.gtb Z.ltb Z.le Z.lt Z.gt Z.ge Z.of_nat
                                 List.app List.length rev rev_append
            ] in
                   (match CEnv fnc with
                    | Some c => Shallow.ValidContract c (FunDef fnc)
                    | None => False
                    end) in
        let s := eval compute in (stats P) in s.

    End Statistics.

  End Shallow.

End NewShallowExecOn.

Module MakeNewShallowExecutor
  (Import B    : Base)
  (Import SIG  : Signature B)
  (Import PROG : Program B)
  (Import PLOG : ProgramLogic B SIG PROG).

  Include NewShallowExecOn B SIG PROG PLOG.

End MakeNewShallowExecutor.
