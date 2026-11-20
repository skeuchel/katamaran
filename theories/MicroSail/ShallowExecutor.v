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
     Lists.List
     NArith.NArith
     Program.Basics
     Program.Tactics
     Strings.String
     Relations.Relation_Definitions
     ZArith.BinInt.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Notations
     Prelude
     Signature
     Symbolic.Propositions
     Hoare.

From stdpp Require base list option.

Import ctx.notations.
Import env.notations.
Import ListNotations.
Import SignatureNotations.

Set Implicit Arguments.

Module Type ShallowExecOn
  (Import B : Base)
  (Import SIG : Signature B)
  (Import PROG : Program B)
  (Import PLOG : ProgramLogic B SIG PROG).

  (* The store transformer. It is indexed by two program variable contexts Γ1
     Γ2 that encode the shape of the program variable store before and after
     execution. *)
  Definition CStoreT (M : Type -> Type) (Γ1 Γ2 : PCtx) (A : Type) : Type :=
    CStore Γ1 -> M (A * CStore Γ2)%type.

  Definition MProd {A B} (MA : relation A) (MB : relation B) : relation (A * B) :=
    fun '(a1,b1) '(a2,b2) => MA a1 a2 /\ MB b1 b2.

  Definition MStoreT {M} (RM : forall {A}, relation A -> relation (M A))
    (Γ1 Γ2 : PCtx) [A] (MA : relation A) : relation (CStoreT M Γ1 Γ2 A) :=
    CStore Γ1 ::> RM (MProd MA eq).
  #[global] Arguments MStoreT {M} RM Γ1 Γ2 [A] MA.

  (* The paper discusses the case that a function call is replaced by
     interpreting the contract instead. However, this is not always
     convenient. We therefore parameterize the executor by other functions
     that interpret function calls and lemma applications. The following
     types describe the executor and the parameters. *)
  Definition ExecCall M := forall Δ τ, 𝑭 Δ τ -> CStore Δ -> M (Val τ).
  Definition ExecCallForeign M := forall Δ τ, 𝑭𝑿 Δ τ -> CStore Δ -> M (Val τ).
  Definition ExecLemma M := forall Δ, 𝑳 Δ -> CStore Δ -> M unit.
  Definition ExecFail M := forall Γ τ (s : Val ty.string), CStoreT M Γ Γ (Val τ).
  Definition Exec M := forall Γ τ (s : Stm Γ τ), CStoreT M Γ Γ (Val τ).

  Abbreviation MonotonicExecCall RM exec_call :=
    (forall Δ τ (f : 𝑭 Δ τ) (δ : CStore Δ),
       Proper (RM _ eq) (exec_call Δ τ f δ)).
  Abbreviation MonotonicExecCallForeign RM exec_call_foreign :=
    (forall Δ τ (f : 𝑭𝑿 Δ τ) (δ : CStore Δ),
       Proper (RM _ eq) (exec_call_foreign Δ τ f δ)).
  Abbreviation MonotonicExecLemma RM exec_lemma :=
    (forall Δ (l : 𝑳 Δ) (δ : CStore Δ),
       Proper (RM _ eq) (exec_lemma Δ l δ)).
  Abbreviation MonotonicExecFail RM exec_fail :=
    (forall Γ τ (s : Val ty.string),
       Proper (MStoreT RM Γ Γ eq) (exec_fail Γ τ s)).
  Abbreviation MonotonicExec RM exec :=
    (forall Γ τ (s : Stm Γ τ),
       Proper (MStoreT RM Γ Γ eq) (exec Γ τ s)).

  Module CStoreT.

    Import (hints) CHeapSpec.

    Section Basic.

      Context {M} {cm : CHeapSpecM M}.

      Definition lift_heapspec {Γ A} (m : M A) : CStoreT M Γ Γ A :=
        fun δ => CHeapSpecM.bind m (fun a => CHeapSpecM.pure (a, δ)).
      Definition evalStoreT {Γ1 Γ2 A} (m : CStoreT M Γ1 Γ2 A) (δ : CStore Γ1) : M A :=
        CHeapSpecM.bind (m δ) (fun '(a,_) => CHeapSpecM.pure a).

      Definition pure {Γ A} (a : A) : CStoreT M Γ Γ A :=
        fun δ => CHeapSpecM.pure (a, δ).
      Definition bind {Γ1 Γ2 Γ3 A B} (m : CStoreT M Γ1 Γ2 A) (f : A -> CStoreT M Γ2 Γ3 B) :
        CStoreT M Γ1 Γ3 B :=
        fun δ1 => CHeapSpecM.bind (m δ1) (fun '(a,δ2) => f a δ2).

      Definition error {Γ1 Γ2 A} : CStoreT M Γ1 Γ2 A :=
        fun _ => CHeapSpecM.error.
      Definition block {Γ1 Γ2 A} : CStoreT M Γ1 Γ2 A :=
        fun _ => CHeapSpecM.block.

      Definition demonic_pattern_match {N : Set} {Γ σ} (pat : Pattern (N:=N) σ) (v : Val σ) :
        CStoreT M Γ Γ (MatchResult pat) :=
        lift_heapspec (CHeapSpecM.demonic_pattern_match pat v).
      #[global] Arguments demonic_pattern_match {N Γ σ} pat v.

      Definition pushpop {A Γ1 Γ2 x σ} (v : Val σ)
        (m : CStoreT M (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) A) : CStoreT M Γ1 Γ2 A :=
        fun δ1 =>
          CHeapSpecM.bind (m (δ1 ► (x∷σ ↦ v)))
            (fun '(a,δ2) => CHeapSpecM.pure (a, env.tail δ2)).
      Definition pushspops {A Γ1 Γ2 Δ} (δΔ : CStore Δ)
        (m : CStoreT M (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) A) : CStoreT M Γ1 Γ2 A :=
        fun δ1 =>
          CHeapSpecM.bind (m (δ1 ►► δΔ))
            (fun '(a,δ2) => CHeapSpecM.pure (a, env.drop Δ δ2)).
      Definition get_local {Γ} : CStoreT M Γ Γ (CStore Γ) :=
        fun δ => CHeapSpecM.pure (δ, δ).
      Definition put_local {Γ1 Γ2} (δ : CStore Γ2) : CStoreT M Γ1 Γ2 unit :=
        fun _ => CHeapSpecM.pure (tt, δ).

      Definition eval_exp {Γ σ} (e : Exp Γ σ) : CStoreT M Γ Γ (Val σ) :=
        fun δ => CHeapSpecM.pure (eval e δ, δ).
      Definition eval_exps {Γ} {σs : PCtx} (es : NamedEnv (Exp Γ) σs) :
        CStoreT M Γ Γ (CStore σs) :=
        fun δ => CHeapSpecM.pure (evals es δ, δ).
      Definition assign {Γ} x {σ} {xIn : x∷σ ∈ Γ} (v : Val σ) : CStoreT M Γ Γ unit :=
        fun δ => CHeapSpecM.pure (tt, δ ⟪ x ↦ v ⟫).
      Global Arguments assign {Γ} x {σ xIn} v.

    End Basic.

    Module CStoreTNotations.

      Notation "' x <- ma ;; mb" :=
        (bind ma (fun x => mb))
          (at level 20, x pattern, ma at next level, mb at level 200, right associativity,
           format "' x  <-  ma  ;;  mb") : mut_scope.
      Notation "x <- ma ;; mb" :=
        (bind ma (fun x => mb))
          (at level 20, ma at next level, mb at level 200, right associativity) : mut_scope.
      Notation "ma ;; mb" := (bind ma (fun _ => mb)) : mut_scope.

    End CStoreTNotations.
    Import CStoreTNotations.
    Local Open Scope mut_scope.

    Section ExecAux.

      Context {M} {cm : CHeapSpecM M}.
      Context {SPEC : Specification}.
      Variable exec_call_foreign : ExecCallForeign M.
      Variable exec_lemma : ExecLemma M.
      Variable exec_call : ExecCall M.
      Variable exec_fail : ExecFail M.

      (* The openly-recursive executor. *)
      Definition exec_aux : Exec M :=
        fix exec_aux {Γ τ} (s : Stm Γ τ) : CStoreT M Γ Γ (Val τ) :=
          match s with
          | stm_val _ l => pure l
          | stm_exp e => eval_exp e
          | stm_let x σ s k =>
              v <- exec_aux s ;;
              pushpop v (exec_aux k)
          | stm_block δ k =>
              pushspops δ (exec_aux k)
          | stm_assign x e =>
              v <- exec_aux e ;;
              _ <- assign x v ;;
              pure v
          | stm_call f es =>
              args <- eval_exps es ;;
              lift_heapspec (exec_call f args)
          | stm_foreign f es =>
              ts <- eval_exps es ;;
              lift_heapspec (exec_call_foreign f ts)
          | stm_lemmak l es k =>
              ts <- eval_exps es ;;
              _  <- lift_heapspec (exec_lemma l ts) ;;
              exec_aux k
          | stm_call_frame δ' s =>
              δ <- get_local ;;
              _ <- put_local δ' ;;
              v <- exec_aux s ;;
              _ <- put_local δ ;;
              pure v
          | stm_seq e k => _ <- exec_aux e ;; exec_aux k
          | stm_assertk e1 _ k =>
              v <- eval_exp e1 ;;
              _ <- lift_heapspec (CHeapSpecM.assert_formula (if fail_rule_pre then True else v <> false)) ;;
              _ <- lift_heapspec (CHeapSpecM.assume_formula (v = true)) ;;
              exec_aux k
          | stm_fail _ s =>
              exec_fail _ s
          | stm_pattern_match s pat rhs =>
              v  <- exec_aux s ;;
              '(existT pc δpc) <- demonic_pattern_match pat v ;;
              pushspops δpc (exec_aux (rhs pc))
          | stm_read_register reg =>
              lift_heapspec (CHeapSpecM.read_register reg)
          | stm_write_register reg e =>
              v__new <- eval_exp e ;;
              lift_heapspec (CHeapSpecM.write_register reg v__new)
          | stm_bind s k =>
              v <- exec_aux s ;;
              exec_aux (k v)
          | stm_debugk k =>
              exec_aux k
          end.

    End ExecAux.
    #[global] Arguments exec_aux {M _ SPEC} _ _ _ _ [Γ τ] !s.

    Section Monotonicity.

      Context {M} {cm : CHeapSpecM M} {RM : forall {A}, relation A -> relation (M A)}
        {mm : MHeapSpecM M (@RM)}.

      #[export] Instance mon_lift_heapspec {Γ} `{MA : relation A} :
        Proper (RM MA ==> MStoreT (@RM) Γ Γ MA) lift_heapspec.
      Proof.
        intros m1 m2 rm δ. unfold lift_heapspec. eapply MHeapSpecM.mon_bind; [exact rm|].
        intros a1 a2 ra. apply MHeapSpecM.mon_pure. now split.
      Qed.

      #[export] Instance mon_evalStoreT {Γ1 Γ2} `{MA : relation A} :
        Proper (MStoreT (@RM) Γ1 Γ2 MA ==> CStore Γ1 ::> RM MA) evalStoreT.
      Proof.
        intros m1 m2 rm δ. unfold evalStoreT. eapply MHeapSpecM.mon_bind; [apply rm|].
        intros [a1 δ1] [a2 δ2] [ra _]. now apply MHeapSpecM.mon_pure.
      Qed.

      #[export] Instance mon_pure {Γ} `{MA : relation A} :
        Proper (MA ==> MStoreT (@RM) Γ Γ MA) pure.
      Proof. intros a1 a2 ra δ. apply MHeapSpecM.mon_pure. now split. Qed.

      #[export] Instance mon_bind {Γ1 Γ2 Γ3} `{MA : relation A, MB : relation B} :
        Proper (MStoreT (@RM) Γ1 Γ2 MA ==> (MA ==> MStoreT (@RM) Γ2 Γ3 MB) ==>
                MStoreT (@RM) Γ1 Γ3 MB) bind.
      Proof.
        intros m1 m2 rm f1 f2 rf δ. unfold bind. eapply MHeapSpecM.mon_bind; [apply rm|].
        intros [a1 δ1] [a2 δ2] [ra <-]. now apply rf.
      Qed.

      #[export] Instance mon_error {Γ1 Γ2} `{MA : relation A} :
        Proper (MStoreT (@RM) Γ1 Γ2 MA) error.
      Proof. intros δ. apply MHeapSpecM.mon_error. Qed.

      #[export] Instance mon_block {Γ1 Γ2} `{MA : relation A} :
        Proper (MStoreT (@RM) Γ1 Γ2 MA) block.
      Proof. intros δ. apply MHeapSpecM.mon_block. Qed.

      #[export] Instance mon_demonic_pattern_match {N : Set} {Γ σ}
        (pat : Pattern (N:=N) σ) (v : Val σ) :
        Proper (MStoreT (@RM) Γ Γ eq) (demonic_pattern_match pat v).
      Proof. unfold demonic_pattern_match. solve_monotonic. Qed.

      #[export] Instance mon_pushpop `{MA : relation A} {Γ1 Γ2 x σ} (v : Val σ) :
        Proper (MStoreT (@RM) (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) MA ==> MStoreT (@RM) Γ1 Γ2 MA)
          (pushpop v).
      Proof.
        intros m1 m2 rm δ. unfold pushpop. eapply MHeapSpecM.mon_bind; [apply rm|].
        intros [a1 δ1] [a2 δ2] [ra <-]. apply MHeapSpecM.mon_pure. now split.
      Qed.

      #[export] Instance mon_pushspops `{MA : relation A} {Γ1 Γ2 Δ} (δΔ : CStore Δ) :
        Proper (MStoreT (@RM) (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) MA ==> MStoreT (@RM) Γ1 Γ2 MA)
          (pushspops δΔ).
      Proof.
        intros m1 m2 rm δ. unfold pushspops. eapply MHeapSpecM.mon_bind; [apply rm|].
        intros [a1 δ1] [a2 δ2] [ra <-]. apply MHeapSpecM.mon_pure. now split.
      Qed.

      #[export] Instance mon_get_local {Γ} :
        Proper (MStoreT (@RM) Γ Γ eq) get_local.
      Proof. intros δ. apply MHeapSpecM.mon_pure. now split. Qed.

      #[export] Instance mon_put_local {Γ1 Γ2} (δ : CStore Γ2) :
        Proper (MStoreT (@RM) Γ1 Γ2 eq) (put_local δ).
      Proof. intros δ'. apply MHeapSpecM.mon_pure. now split. Qed.

      #[export] Instance mon_eval_exp {Γ σ} (e : Exp Γ σ) :
        Proper (MStoreT (@RM) Γ Γ eq) (eval_exp e).
      Proof. intros δ. apply MHeapSpecM.mon_pure. now split. Qed.

      #[export] Instance mon_eval_exps {Γ} {σs : PCtx} (es : NamedEnv (Exp Γ) σs) :
        Proper (MStoreT (@RM) Γ Γ eq) (eval_exps es).
      Proof. intros δ. apply MHeapSpecM.mon_pure. now split. Qed.

      #[export] Instance mon_assign {Γ} x {σ} {xIn : x∷σ ∈ Γ} (v : Val σ) :
        Proper (MStoreT (@RM) Γ Γ eq) (assign x v).
      Proof. intros δ. apply MHeapSpecM.mon_pure. now split. Qed.

      #[global] Typeclasses Opaque lift_heapspec evalStoreT pure bind error block
        demonic_pattern_match pushpop pushspops get_local put_local eval_exp
        eval_exps assign.

    Section ExecAux.

      Context {SPEC : Specification}.
      Variable exec_call_foreign : ExecCallForeign M.
      Variable exec_lemma : ExecLemma M.
      Variable exec_call : ExecCall M.
      Variable exec_fail : ExecFail M.

      Context
        (mexec_call_foreign : MonotonicExecCallForeign (@RM) exec_call_foreign)
        (mexec_lemma : MonotonicExecLemma (@RM) exec_lemma)
        (mexec_call : MonotonicExecCall (@RM) exec_call)
        (mexec_fail : MonotonicExecFail (@RM) exec_fail).

      #[export] Instance mon_exec_aux :
        MonotonicExec (@RM) (exec_aux exec_call_foreign exec_lemma exec_call exec_fail).
      Proof. induction s; cbn [exec_aux]; solve_monotonic. Qed.

    End ExecAux.

    End Monotonicity.

  End CStoreT.

  Section WithSpec.

    Import CHeapSpecM.notations.

    Context {M} {cm : CHeapSpecM M}.

    Definition exec_contract (exec : Exec M) {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) : M unit :=
      match c with
      | MkSepContract _ _ lvars pats req result ens =>
          lenv <- CHeapSpecM.demonic_ctx lvars ;;
          _    <- CHeapSpecM.produce req lenv ;;
          v    <- CStoreT.evalStoreT (exec _ _ s) (inst pats lenv) ;;
          CHeapSpecM.consume ens (env.snoc lenv (result∷τ) v)
      end.

    Definition exec_call_error_no_fuel : ExecCall M :=
      fun Δ τ f args => CHeapSpecM.error.

    Definition cexec_call_foreign {SPEC : Specification} : ExecCallForeign M :=
      fun Δ τ f args =>
        CHeapSpecM.call_contract (CEnvEx f) args.

    Definition debug_lemma [Δ] (f : 𝑳 Δ) (args : CStore Δ) : M unit :=
      CHeapSpecM.pure tt.

    Definition cexec_lemma {SPEC : Specification} : ExecLemma M :=
      fun Δ l args =>
        _ <- debug_lemma l args ;;
        CHeapSpecM.call_lemma (LEnv l) args.

    Definition debug_call [Δ τ] (f : 𝑭 Δ τ) (args : CStore Δ) : M unit :=
      CHeapSpecM.pure tt.

    Definition cexec_fail {SPEC : Specification} : ExecFail M :=
      fun Γ τ s => if fail_rule_pre then CStoreT.block else CStoreT.error.

    (* If a function does not have a contract, we continue executing the body of
       the called function. A parameter [inline_fuel] bounds the number of
       allowed levels before failing execution. *)
    Fixpoint cexec_call {SPEC : Specification} (inline_fuel : nat) : ExecCall M :=
      fun Δ τ f args =>
        _ <- debug_call f args ;;
        (* Let's first see if we have a contract defined for function [f]
           and then if we have enough fuel for inlining. *)
        match CEnv f , inline_fuel with
        | Some c , _ =>
            (* YES: Execute the call by interpreting the contract. *)
            CHeapSpecM.call_contract c args
        | None   , 0 =>
            (* Out of fuel *)
            exec_call_error_no_fuel f args
        | None   , S n =>
            CStoreT.evalStoreT
              (CStoreT.exec_aux cexec_call_foreign cexec_lemma (cexec_call n) cexec_fail (FunDef f))
              args
        end.

    Definition cexec {SPEC : Specification} (inline_fuel : nat) : Exec M :=
      @CStoreT.exec_aux M _ SPEC cexec_call_foreign cexec_lemma
        (cexec_call inline_fuel) cexec_fail.

  End WithSpec.
  #[global] Arguments exec_call_error_no_fuel {M _}.
  #[global] Arguments cexec {M _ SPEC} _ [_ _] s _ : simpl never.

  Section Monotonicity.

    Import (hints) CStoreT.

    Context {M} {cm : CHeapSpecM M} {RM : forall {A}, relation A -> relation (M A)}
      {mm : MHeapSpecM M (@RM)}.

    #[export] Instance mon_exec_contract (exec : Exec M) (mexec : MonotonicExec (@RM) exec)
      {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) :
      Proper (RM eq) (exec_contract exec c s).
    Proof. destruct c; cbn [exec_contract]. solve_monotonic. Qed.

    #[export] Instance mon_exec_call_error_no_fuel :
      MonotonicExecCall (@RM) (exec_call_error_no_fuel (M := M)).
    Proof. solve_monotonic. Qed.

    #[export] Instance mon_cexec_call_foreign {SPEC : Specification} :
      MonotonicExecCallForeign (@RM) (cexec_call_foreign (M := M)).
    Proof. solve_monotonic. Qed.

    #[export] Instance mon_cexec_lemma {SPEC : Specification} :
      MonotonicExecLemma (@RM) (cexec_lemma (M := M)).
    Proof. unfold cexec_lemma, debug_lemma. solve_monotonic. Qed.

    #[export] Instance mon_cexec_fail {SPEC : Specification} :
      MonotonicExecFail (@RM) (cexec_fail (M := M)).
    Proof. unfold cexec_fail; destruct fail_rule_pre; solve_monotonic. Qed.

    #[export] Instance mon_cexec_call {SPEC : Specification} (fuel : nat) :
      MonotonicExecCall (@RM) (cexec_call (M := M) fuel).
    Proof.
      induction fuel; intros; cbn [cexec_call]; unfold debug_call; destruct CEnv;
        solve_monotonic.
    Qed.

    #[export] Instance mon_cexec {SPEC : Specification} (fuel : nat) :
      MonotonicExec (@RM) (cexec (M := M) fuel).
    Proof. unfold cexec. solve_monotonic. Qed.

  End Monotonicity.

End ShallowExecOn.
