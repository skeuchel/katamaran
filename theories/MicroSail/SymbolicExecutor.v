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
     Arith.PeanoNat
     Bool.Bool
     Classes.Morphisms
     Classes.Morphisms_Prop
     Classes.Morphisms_Relations
     Classes.RelationClasses
     Relations.Relation_Definitions
     Lists.List
     NArith.NArith
     Program.Tactics
     Strings.String
     ZArith.BinInt.
From Stdlib Require
     Classes.CRelationClasses.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Prelude
     Bitvector
     Signature
     Symbolic.Worlds
     Hoare
     Base.

From stdpp Require
     base.

Import ctx.notations.
Import env.notations.
Import ListNotations.
Import (hints) bv.finite.

Set Implicit Arguments.

Module Type SymbolicExecOn
  (Import B : Base)
  (Import SIG : Signature B)
  (Import PROG : Program B)
  (Import PLOG : ProgramLogic B SIG PROG).

  Import Entailment.
  Import Erasure.
  Import ModalNotations.
  Local Open Scope modal.

  Section DebugInfo.

    Record DebugCall (Σ : LCtx) : Type :=
      MkDebugCall
        { debug_call_function_parameters    : PCtx;
          debug_call_function_result_type   : Ty;
          debug_call_function_name          : 𝑭 debug_call_function_parameters debug_call_function_result_type;
          debug_call_function_contract      : option (SepContract debug_call_function_parameters debug_call_function_result_type);
          debug_call_function_arguments     : SStore debug_call_function_parameters Σ;
          (* debug_call_program_context        : PCtx; *)
          debug_call_pathcondition          : PathCondition Σ;
          (* debug_call_localstore             : SStore debug_call_program_context Σ; *)
          debug_call_heap                   : SHeap Σ;
        }.

    Record EDebugCall : Type :=
      MkEDebugCall
        { edebug_call_function_parameters    : PCtx;
          edebug_call_function_result_type   : Ty;
          edebug_call_function_name          : 𝑭 edebug_call_function_parameters edebug_call_function_result_type;
          edebug_call_function_contract      : option (SepContract edebug_call_function_parameters edebug_call_function_result_type);
          edebug_call_function_arguments     : NamedEnv ETerm edebug_call_function_parameters;
          (* edebug_call_program_context        : PCtx; *)
          edebug_call_pathcondition          : list EFormula;
          (* edebug_call_localstore             : SStore debug_call_program_context Σ; *)
          edebug_call_heap                   : list EChunk;
        }.

    #[export] Instance EraseDebugCall : Erase DebugCall EDebugCall :=
      fun _ '(MkDebugCall f fc args pc h) => MkEDebugCall f fc (erase args) (erase pc) (erase h).

    Record DebugCallLemma (Σ : LCtx) : Type :=
      MkDebugCallLemma
        { debug_call_lemma_parameters    : PCtx;
          debug_call_lemma_name          : 𝑳 debug_call_lemma_parameters;
          debug_call_lemma_contract      : Lemma debug_call_lemma_parameters;
          debug_call_lemma_arguments     : SStore debug_call_lemma_parameters Σ;
          debug_call_lemma_pathcondition : PathCondition Σ;
          (* debug_call_localstore       : SStore debug_call_program_context Σ; *)
          debug_call_lemma_heap          : SHeap Σ;
        }.

    Record EDebugCallLemma : Type :=
      MkEDebugCallLemma
        { edebug_call_lemma_parameters    : PCtx;
          edebug_call_lemma_name          : 𝑳 edebug_call_lemma_parameters;
          edebug_call_lemma_contract      : Lemma edebug_call_lemma_parameters;
          edebug_call_lemma_arguments     : NamedEnv ETerm edebug_call_lemma_parameters;
          edebug_call_lemma_pathcondition : list EFormula;
          (* edebug_call_localstore       : NamedEnv ETerm debug_call_program_context; *)
          edebug_call_lemma_heap          : list EChunk;
        }.

    #[export] Instance EraseDebugCallLemma : Erase DebugCallLemma EDebugCallLemma :=
      fun _ '(MkDebugCallLemma l lc args pc h) => MkEDebugCallLemma l lc (erase args) (erase pc) (erase h).


    #[export] Instance SubstDebugCallLemma : Subst DebugCallLemma :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugCallLemma l c ts pc (* δ *) h =>
          MkDebugCallLemma l c (subst ts ζ01) (subst pc ζ01) (subst h ζ01)
        end.

    #[export] Instance SubstSUDebugCallLemma `{SubstUniv Sb} : SubstSU Sb DebugCallLemma :=
      fun Σ0 Σ1 d ζ01 =>
        match d with
        | MkDebugCallLemma l c ts pc (* δ *) h =>
          MkDebugCallLemma l c (substSU ts ζ01) (substSU pc ζ01) (substSU h ζ01)
        end.

    #[export] Instance SubstLawsDebugCallLemma : SubstLaws DebugCallLemma.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    #[export] Instance SubstSULawsDebugCallLemma `{SubstUnivLaws Sb} :
      SubstSULaws Sb DebugCallLemma.
    Proof.
      intros ? ? ? ? ? []; cbn; f_equal; now apply substSU_trans.
    Qed.

    Import option.notations.
    #[export] Instance OccursCheckDebugCallLemma : OccursCheck DebugCallLemma :=
      fun Σ x xIn d =>
        match d with
        | MkDebugCallLemma l c ts pc (* δ *) h =>
            ts' <- occurs_check xIn ts ;;
            pc' <- occurs_check xIn pc ;;
            (* δ'  <- occurs_check xIn δ ;; *)
            h'  <- occurs_check xIn h ;;
            Some (MkDebugCallLemma l c ts' pc' (* δ' *) h')
        end.

    #[export] Instance GenOccursCheckDebugCallLemma : GenOccursCheck (Sb := WeakensTo) DebugCallLemma :=
      fun Σ d =>
        match d with
        | MkDebugCallLemma l c ts pc (* δ *) h =>
            liftTernOp (fun Σ ts' pc' h' => MkDebugCallLemma l c ts' pc' h')
              (fun _ _ _ _ _ _ => eq_refl)
              (gen_occurs_check ts) (gen_occurs_check pc) (gen_occurs_check h)
        end.

    #[export] Instance SubstDebugCall : Subst DebugCall :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugCall f c ts pc (* δ *) h =>
          MkDebugCall f c (subst ts ζ01) (subst pc ζ01) (* (subst δ ζ01) *) (subst h ζ01)
        end.

    #[export] Instance SubstSUDebugCall `{SubstUniv Sb} : SubstSU Sb DebugCall :=
      fun Σ0 Σ1 d ζ01 =>
        match d with
        | MkDebugCall f c ts pc (* δ *) h =>
            MkDebugCall f c (substSU ts ζ01) (substSU pc ζ01) (* (substSU δ ζ01) *) (substSU h ζ01)
        end.

    #[export] Instance SubstLawsDebugCall : SubstLaws DebugCall.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    #[export] Instance SubstSULawsDebugCall `{SubstUnivLaws Sb} :
      SubstSULaws Sb DebugCall.
    Proof.
      intros ? ? ? ? ? []; cbn; f_equal; now apply substSU_trans.
    Qed.

    Import option.notations.
    #[export] Instance OccursCheckDebugCall : OccursCheck DebugCall :=
      fun Σ x xIn d =>
        match d with
        | MkDebugCall f c ts pc (* δ *) h =>
            ts' <- occurs_check xIn ts ;;
            pc' <- occurs_check xIn pc ;;
            (* δ'  <- occurs_check xIn δ ;; *)
            h'  <- occurs_check xIn h ;;
            Some (MkDebugCall f c ts' pc' (* δ' *) h')
        end.

    #[export] Instance GenOccursCheckDebugCall : GenOccursCheck (Sb := WeakensTo) DebugCall :=
      fun Σ d =>
        match d with
        | MkDebugCall f c ts pc (* δ *) h =>
            liftTernOp (fun Σ ts' pc' h' => MkDebugCall f c ts' pc' h')
              (fun _ _ _ _ _ _ => eq_refl)
              (gen_occurs_check ts) (gen_occurs_check pc) (gen_occurs_check h)
        end.

    Record DebugStm (Σ : LCtx) : Type :=
      MkDebugStm
        { debug_stm_program_context        : PCtx;
          debug_stm_statement_type         : Ty;
          debug_stm_statement              : Stm debug_stm_program_context debug_stm_statement_type;
          debug_stm_pathcondition          : PathCondition Σ;
          debug_stm_localstore             : SStore debug_stm_program_context Σ;
          debug_stm_heap                   : SHeap Σ;
        }.

    Record EDebugStm : Type :=
      MkEDebugStm
        { edebug_stm_program_context        : PCtx;
          edebug_stm_statement_type         : Ty;
          edebug_stm_statement              : Stm edebug_stm_program_context edebug_stm_statement_type;
          edebug_stm_pathcondition          : list EFormula;
          edebug_stm_localstore             : NamedEnv ETerm edebug_stm_program_context;
          edebug_stm_heap                   : list EChunk;
        }.

    #[export] Instance EraseDebugStm : Erase DebugStm EDebugStm :=
      fun _ '(MkDebugStm s pc Δ h) => MkEDebugStm s (erase pc) (erase Δ) (erase h).

    #[export] Instance SubstDebugStm : Subst DebugStm :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugStm s pc δ h =>
          MkDebugStm s (subst pc ζ01) (subst δ ζ01) (subst h ζ01)
        end.

    #[export] Instance SubstSUDebugStm `{SubstUniv Sb} : SubstSU Sb DebugStm :=
      fun Σ0 Σ1 d ζ01 =>
        match d with
        | MkDebugStm s pc δ h =>
          MkDebugStm s (substSU pc ζ01) (substSU δ ζ01) (substSU h ζ01)
        end.

    #[export] Instance SubstLawsDebugStm : SubstLaws DebugStm.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    #[export] Instance SubstSULawsDebugStm `{SubstUnivLaws Sb} :
      SubstSULaws Sb DebugStm.
    Proof.
      intros ? ? ? ? ? []; cbn; f_equal; now apply substSU_trans.
    Qed.

    #[export] Instance OccursCheckDebugStm : OccursCheck DebugStm :=
      fun Σ x xIn d =>
        match d with
        | MkDebugStm s pc δ h =>
            pc' <- occurs_check xIn pc ;;
            δ'  <- occurs_check xIn δ ;;
            h'  <- occurs_check xIn h ;;
            Some (MkDebugStm s pc' δ' h')
        end.

    #[export] Instance GenOccursCheckDebugStm : GenOccursCheck (Sb := WeakensTo) DebugStm :=
      fun Σ d =>
        match d with
        | MkDebugStm s pc δ h =>
            liftTernOp (fun Σ pc' δ' h' => MkDebugStm s pc' δ' h')
              (fun _ _ _ _ _ _ => eq_refl)
              (gen_occurs_check pc) (gen_occurs_check δ) (gen_occurs_check h)
        end.

    Record ErrorNoFuel (Σ : LCtx) : Type :=
      MkErrorNoFuel
        { error_no_fuel_call_parameter_types : PCtx;
          error_no_fuel_call_return_type     : Ty;
          error_no_fuel_call_function        :
            𝑭 error_no_fuel_call_parameter_types
              error_no_fuel_call_return_type;
          error_no_fuel_call_arguments :
            SStore error_no_fuel_call_parameter_types Σ;
          error_no_fuel_pathcondition : PathCondition Σ;
          error_no_fuel_heap           : SHeap Σ;
        }.

    Record EErrorNoFuel : Type :=
      MkEErrorNoFuel
        { eerror_no_fuel_call_parameter_types : PCtx;
          eerror_no_fuel_call_return_type     : Ty;
          eerror_no_fuel_call_function        :
            𝑭 eerror_no_fuel_call_parameter_types
              eerror_no_fuel_call_return_type;
          eerror_no_fuel_call_arguments :
            NamedEnv ETerm eerror_no_fuel_call_parameter_types;
          eerror_no_fuel_pathcondition : list EFormula;
          eerror_no_fuel_heap           : list EChunk;
        }.

    #[export] Instance EraseErrorNoFuel : Erase ErrorNoFuel EErrorNoFuel :=
      fun _ '(MkErrorNoFuel f Δ pc h) => MkEErrorNoFuel f (erase Δ) (erase pc) (erase h).

    #[export] Instance SubstErrorNoFuel : Subst ErrorNoFuel :=
      fun Σ0 e Σ1 ζ01 =>
        match e with
        | MkErrorNoFuel f args pc h =>
          MkErrorNoFuel f (subst args ζ01) (subst pc ζ01) (subst h ζ01)
        end.

    #[export] Instance SubstSUErrorNoFuel `{SubstUniv Sb} : SubstSU Sb ErrorNoFuel :=
      fun Σ0 Σ1 e ζ01 =>
        match e with
        | MkErrorNoFuel f args pc h =>
          MkErrorNoFuel f (substSU args ζ01) (substSU pc ζ01) (substSU h ζ01)
        end.

    #[export] Instance SubstLawsErrorNoFuel : SubstLaws ErrorNoFuel.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    #[export] Instance SubstSULawsErrorNoFuel `{SubstUnivLaws Sb} :
      SubstSULaws Sb ErrorNoFuel.
    Proof.
      intros ? ? ? ? ? []; cbn; f_equal; now apply substSU_trans.
    Qed.

    #[export] Instance OccursCheckErrorNoFuel : OccursCheck ErrorNoFuel :=
      fun Σ x xIn d =>
        match d with
        | MkErrorNoFuel f args pc h =>
            args' <- occurs_check xIn args ;;
            pc'   <- occurs_check xIn pc ;;
            h'    <- occurs_check xIn h ;;
            Some (MkErrorNoFuel f args' pc' h')
        end.

    #[export] Instance GenOccursCheckErrorNoFuel : GenOccursCheck (Sb := WeakensTo) ErrorNoFuel :=
      fun Σ d =>
        match d with
        | MkErrorNoFuel f args pc h=>
            liftTernOp (fun Σ args' pc' h' => MkErrorNoFuel f args' pc' h')
              (fun _ _ _ _ _ _ => eq_refl)
              (gen_occurs_check args) (gen_occurs_check pc) (gen_occurs_check h)
        end.

  End DebugInfo.

  Definition PROP : TYPE :=
    fun _ => Prop.

  Import SymProp.
  Import Postprocessing.

  Section VerificationConditions.

    Inductive VerificationCondition (p : 𝕊 ctx.nil) : Prop :=
    | vc (P : safe p env.nil).

    Lemma vc_debug (p : 𝕊 ctx.nil) (H : safe_debug p env.nil) : VerificationCondition p.
    Proof.
      constructor; now rewrite safe_debug_safe in H.
    Qed.

    #[export] Instance proper_vc : Proper (sequiv ctx.nil ==> iff) VerificationCondition.
    Proof. intros p q pq. split; intros []; constructor; now apply pq. Qed.

    Inductive VerificationConditionWithErasure (p : Erasure.ESymProp) : Prop :=
    | vce (P : Erasure.inst_symprop nil p).

  End VerificationConditions.

  Section Configuration.

    Record Config : Type :=
      MkConfig
        { config_debug_function : forall Δ τ, 𝑭 Δ τ -> bool;
          config_debug_lemma : forall Δ, 𝑳 Δ -> bool;
        }.

    Definition default_config : Config :=
      {| config_debug_function _ _ f := false;
         config_debug_lemma _ l := false;
      |}.

  End Configuration.

  (* The symbolic store transformer. *)
  Definition SStoreT (M : TYPE -> TYPE) (Γ1 Γ2 : PCtx) (A : TYPE) : TYPE :=
    SStore Γ1 -> M (WProd A (SStore Γ2)).

  (* The paper discusses the case that a function call is replaced by
     interpreting the contract instead. However, this is not always
     convenient. We therefore parameterize the executor by other functions
     that interpret function calls and lemma applications. The following
     types describe the executor and the parameters. *)
  Definition ExecCall M := forall Δ τ, 𝑭 Δ τ -> ⊢ SStore Δ -> M (WTerm τ).
  Definition ExecCallForeign M := forall Δ τ, 𝑭𝑿 Δ τ -> ⊢ SStore Δ -> M (WTerm τ).
  Definition ExecLemma M := forall Δ, 𝑳 Δ -> ⊢ SStore Δ -> M Unit.
  Definition ExecFail M := forall Γ τ (s : Val ty.string), ⊢ SStoreT M Γ Γ (WTerm τ).
  Definition Exec M := forall Γ τ (s : Stm Γ τ), ⊢ SStoreT M Γ Γ (WTerm τ).

  Module SStoreT.

    Local Hint Extern 2 (Persistent (WTerm ?σ)) =>
      refine (@persistent_subst (STerm σ) (@SubstTerm σ)) : typeclass_instances.

    Section Basic.

      Context {M : TYPE -> TYPE} {sm : SHeapSpecM M}.

      Definition lift_heapspec {Γ A} : ⊢ M A -> SStoreT M Γ Γ A :=
        fun w m δ =>
          SHeapSpecM.bind m
            (fun w1 θ1 a =>
               SHeapSpecM.pure (A := WProd A (SStore Γ)) (a, persist δ θ1)).

      Definition evalStoreT {Γ1 Γ2 A} : ⊢ SStoreT M Γ1 Γ2 A -> SStore Γ1 -> M A :=
        fun w m δ =>
          SHeapSpecM.bind (m δ) (fun w1 θ1 '(a,_) => SHeapSpecM.pure a).

      Definition pure {Γ A} : ⊢ A -> SStoreT M Γ Γ A :=
        fun w a δ => SHeapSpecM.pure (A := WProd A (SStore Γ)) (a, δ).

      Definition bind {Γ1 Γ2 Γ3 A B} :
        ⊢ SStoreT M Γ1 Γ2 A -> □(A -> SStoreT M Γ2 Γ3 B) -> SStoreT M Γ1 Γ3 B :=
        fun w m f δ =>
          SHeapSpecM.bind (m δ) (fun w1 θ1 '(a,δ2) => f w1 θ1 a δ2).

      Definition error {Γ1 Γ2 A} :
        ⊢ (SStore Γ1 -> SHeap -> AMessage) -> SStoreT M Γ1 Γ2 A :=
        fun w msg δ => SHeapSpecM.error (msg δ).

      Definition block {Γ1 Γ2 A} : ⊢ SStoreT M Γ1 Γ2 A :=
        fun w δ => SHeapSpecM.block.

      Definition debug {AT} {Γ1 Γ2} :
        ⊢ (SStore Γ1 -> SHeap -> AMessage) -> (SStoreT M Γ1 Γ2 AT) -> (SStoreT M Γ1 Γ2 AT) :=
        fun w msg m δ => SHeapSpecM.debug (msg δ) (m δ).

    End Basic.

    Module Import notations.

      (* Notation "x <- ma ;; mb" := (bind ma (fun _ _ x => mb)) (at level 80, ma at level 90, mb at level 200, right associativity) : mut_scope. *)
      (* Notation "ma >>= f" := (bind ma f) (at level 50, left associativity, only parsing) : mut_scope. *)
      (* Notation "ma >> mb" := (bind_right ma mb) (at level 50, left associativity, only parsing) : mut_scope. *)
      (* Notation "m1 ;; m2" := (bind_right m1 m2) : mut_scope. *)

      Notation "⟨ ω ⟩ x <- ma ;; mb" :=
        (bind ma (fun _ ω x => mb))
          (at level 0, x at next level,
            ma at level 19, mb at level 200,
            right associativity) : mut_scope.
      Notation "⟨ ω ⟩ ' x <- ma ;; mb" :=
        (bind ma (fun _ ω x => mb))
          (at level 0, x pattern,
           ma at level 19, mb at level 200,
           right associativity) : mut_scope.
      Notation "x ⟨ ω ⟩" := (persist x ω).

    End notations.
    Local Open Scope mut_scope.

    Section PatternMatching.

      Context {M : TYPE -> TYPE} {sm : SHeapSpecM M}.

      Definition demonic_pattern_match {N : Set} (n : N -> LVar) {Γ σ} (pat : Pattern (N:=N) σ) :
        ⊢ STerm σ -> SStoreT M Γ Γ (SMatchResult pat) :=
        fun w t => lift_heapspec (SHeapSpecM.demonic_pattern_match n pat t).
      #[global] Arguments demonic_pattern_match {N} n {Γ σ} pat [w].

    End PatternMatching.

    Section State.

      Context {M : TYPE -> TYPE} {sm : SHeapSpecM M}.

      Definition pushpop {AT Γ1 Γ2 x σ} :
        ⊢ STerm σ -> SStoreT M (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) AT -> SStoreT M Γ1 Γ2 AT :=
        fun w t m δ =>
          SHeapSpecM.bind (m δ.[x∷σ↦t])
            (fun w1 θ1 '(a,δ1) =>
               SHeapSpecM.pure (A := WProd AT (SStore Γ2)) (a, env.tail δ1)).

      Definition pushspops {AT Γ1 Γ2 Δ} :
        ⊢ SStore Δ -> SStoreT M (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) AT -> SStoreT M Γ1 Γ2 AT :=
        fun w δΔ m δ =>
          SHeapSpecM.bind (m (δ ►► δΔ))
            (fun w1 θ1 '(a,δ1) =>
               SHeapSpecM.pure (A := WProd AT (SStore Γ2)) (a, env.drop Δ δ1)).

      Definition get_local {Γ} : ⊢ SStoreT M Γ Γ (SStore Γ) :=
        fun w δ => SHeapSpecM.pure (A := WProd (SStore Γ) (SStore Γ)) (δ, δ).
      Definition put_local {Γ1 Γ2} : ⊢ SStore Γ2 -> SStoreT M Γ1 Γ2 Unit :=
        fun w δ' _ => SHeapSpecM.pure (A := WProd Unit (SStore Γ2)) (tt, δ').

      Definition eval_exp {Γ σ} (e : Exp Γ σ) :
        ⊢ SStoreT M Γ Γ (STerm σ) :=
        fun w δ =>
          SHeapSpecM.pure (A := WProd (STerm σ) (SStore Γ)) (peval (seval_exp δ e), δ).

      Definition eval_exps {Γ} {σs : PCtx} (es : NamedEnv (Exp Γ) σs) :
        ⊢ SStoreT M Γ Γ (SStore σs) :=
        fun w δ =>
          SHeapSpecM.pure (A := WProd (SStore σs) (SStore Γ)) (seval_exps δ es, δ).

      Definition assign {Γ} x {σ} {xIn : x∷σ ∈ Γ} : ⊢ STerm σ -> SStoreT M Γ Γ Unit :=
        fun w t δ => SHeapSpecM.pure (A := WProd Unit (SStore Γ)) (tt, δ ⟪ x ↦ t ⟫).
      Global Arguments assign {Γ} x {σ xIn} [w] v.

    End State.

    Section ExecAux.

      Context {M : TYPE -> TYPE} {sm : SHeapSpecM M}.
      Context {SPEC : Specification}.
      Variable exec_call_foreign : ExecCallForeign M.
      Variable exec_lemma : ExecLemma M.
      Variable exec_call : ExecCall M.
      Variable exec_fail : ExecFail M.

      (* The openly-recursive executor. *)
      Definition exec_aux : forall {Γ τ} (s : Stm Γ τ), ⊢ SStoreT M Γ Γ (STerm τ) :=
      fix exec_aux {Γ τ} s {w0} :=
        match s with
        | stm_val _ v => pure (term_val τ v)
        | stm_exp e => eval_exp e (w:=w0)
        | stm_let x σ s__σ s__τ =>
            ⟨ ω01 ⟩ t <- exec_aux s__σ;;
            pushpop t (exec_aux s__τ)
        | stm_block δ s =>
            pushspops (lift δ) (exec_aux s)
        | stm_assign x s =>
            ⟨ ω01 ⟩ t <- exec_aux s;;
            ⟨ ω12 ⟩ _ <- assign x t;;
            pure (persist__term t ω12)
        | stm_call f es =>
            ⟨ ω01 ⟩ args <- eval_exps es (w:=w0) ;;
            lift_heapspec (exec_call f args)
        | stm_call_frame δ s =>
            ⟨ ω01 ⟩ δ1 <- get_local (w:=w0);;
            ⟨ ω12 ⟩ _  <- put_local (lift δ);;
            ⟨ ω23 ⟩ t  <- exec_aux s;;
            ⟨ ω34 ⟩ _  <- put_local (persist δ1 (ω12 ∘ ω23));;
            pure (persist__term t ω34)
        | stm_foreign f es =>
            ⟨ ω01 ⟩ args <- eval_exps es (w:=w0) ;;
            lift_heapspec (exec_call_foreign f args)
        | stm_lemmak l es k =>
            ⟨ ω01 ⟩ args <- eval_exps es (w:=w0) ;;
            ⟨ ω12 ⟩ _  <- lift_heapspec (exec_lemma l args) ;;
            exec_aux k
        | stm_seq s1 s2 =>
            ⟨ ω01 ⟩ _ <- exec_aux s1 ;;
            exec_aux s2
        | stm_assertk e _ k =>
            ⟨ ω01 ⟩ t <- eval_exp e (w:=w0) ;;
            ⟨ ω12 ⟩ _ <- lift_heapspec (SHeapSpecM.assert_formula (fun _ => amsg.empty)
                                          (if fail_rule_pre
                                           then formula_true
                                           else formula_relop bop.neq t (term_val ty.bool false))) ;;
            (* This uses assume_formula for a partial correctness
               interpretation of the object language failure effect. *)
            ⟨ ω13 ⟩ _ <- lift_heapspec (SHeapSpecM.assume_formula (formula_bool (persist t ω12))) ;;
            exec_aux k
        | stm_fail _ s =>
            @exec_fail _ _ s w0
        | stm_read_register reg =>
            lift_heapspec (SHeapSpecM.read_register reg)
        | stm_write_register reg e =>
            ⟨ _ ⟩ tnew <- eval_exp e (w:=_) ;;
            lift_heapspec (SHeapSpecM.write_register reg tnew)
        | stm_pattern_match s pat rhs =>
            ⟨ θ1 ⟩ v  <- exec_aux s ;;
            ⟨ θ2 ⟩ '(existT pc vs) <- demonic_pattern_match PVartoLVar pat v ;;
            pushspops vs (exec_aux (rhs pc))
        | stm_bind _ _ =>
            error
              (fun δ h =>
                 amsg.mk
                   {| msg_function := "SStoreSpec.exec";
                     msg_message := "stm_bind not supported";
                     msg_program_context := _;
                     msg_localstore := δ;
                     msg_heap := h;
                     msg_pathcondition := wco w0
                   |})
        | stm_debugk k =>
            debug
              (fun (δ0 : SStore Γ w0) (h0 : SHeap w0) =>
                 amsg.mk
                   {| debug_stm_program_context := Γ;
                     debug_stm_statement_type := τ;
                     debug_stm_statement := k;
                     debug_stm_pathcondition := wco w0;
                     debug_stm_localstore := δ0;
                     debug_stm_heap := h0
                   |})
              (exec_aux k)
        end.

    End ExecAux.

  End SStoreT.

  Section WithSpec.

    Import SHeapSpecM.notations.

    Context {M : TYPE -> TYPE} {sm : SHeapSpecM M}.

    Definition exec_contract (exec : Exec M) {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) :
      ⊢ M Unit :=
      fun w =>
        match c with
        | MkSepContract _ _ lvars pats req result ens =>
            ⟨ θ1 ⟩ lenv  <- SHeapSpecM.demonic_ctx id lvars ;;
            ⟨ θ2 ⟩ _     <- SHeapSpecM.produce req lenv ;;
            let lenv2 := persist (A := Sub _) lenv θ2 in
            ⟨ θ3 ⟩ res   <- SStoreT.evalStoreT (exec _ _ s _) (subst pats lenv2) ;;
            let lenv3 := persist (A := Sub _) lenv2 θ3 in
            SHeapSpecM.consume ens (sub_snoc lenv3 (result∷τ) res)
        end.

    Definition exec_call_error_no_fuel : ExecCall M :=
      fun Δ τ f w args =>
        SHeapSpecM.error (fun h =>
                 amsg.mk {|
                   error_no_fuel_call_function := f;
                   error_no_fuel_call_arguments := args;
                   error_no_fuel_pathcondition := wco w;
                   error_no_fuel_heap := h
                 |}).

    Definition sexec_call_foreign {SPEC : Specification} : ExecCallForeign M :=
      fun Δ τ f w args =>
        SHeapSpecM.call_contract (CEnvEx f) args.

    Variable cfg : Config.

    Definition debug_lemma {SPEC : Specification} [Δ] (l : 𝑳 Δ) :
      ⊢ SStore Δ -> M Unit :=
      fun w0 args0 =>
        if config_debug_lemma cfg l
        then
          SHeapSpecM.debug
            (fun h0 => amsg.mk {|
                           debug_call_lemma_parameters := Δ;
                           debug_call_lemma_name := l;
                           debug_call_lemma_contract := LEnv l;
                           debug_call_lemma_arguments := args0;
                           debug_call_lemma_pathcondition := wco w0;
                           debug_call_lemma_heap := h0
                         |}) (SHeapSpecM.pure tt)
        else SHeapSpecM.pure tt.
    Definition sexec_lemma {SPEC : Specification} : ExecLemma M :=
      fun Δ l w args =>
        ⟨ θ ⟩ _ <- debug_lemma l args ;;
        SHeapSpecM.call_lemma (LEnv l) (persist args θ).

    Definition debug_call {SPEC : Specification} [Δ τ] (f : 𝑭 Δ τ) :
      ⊢ SStore Δ -> M Unit :=
      fun w0 args0 =>
        if config_debug_function cfg f
        then SHeapSpecM.debug
               (fun h0 => amsg.mk {|
                              debug_call_function_parameters := Δ;
                              debug_call_function_result_type := τ;
                              debug_call_function_name := f;
                              debug_call_function_contract := CEnv f;
                              debug_call_function_arguments := args0;
                              (* debug_call_program_context := _; *)
                              debug_call_pathcondition := wco w0;
                              (* debug_call_localstore := _; *)
                              debug_call_heap := h0
                            |})
               (SHeapSpecM.pure tt)
        else SHeapSpecM.pure tt.

    Definition sexec_fail {SPEC : Specification} : ExecFail M :=
      fun Γ τ s {w0} =>
        if fail_rule_pre
        then SStoreT.block (w := w0)
        else SStoreT.error (fun δ h =>
                 amsg.mk
                   {| msg_function := "sexec_fail";
                     msg_message := "Encountered fail";
                     msg_program_context := _;
                     msg_localstore := δ;
                     msg_heap := h;
                     msg_pathcondition := wco w0
                   |}).

    (* If a function does not have a contract, we continue executing the body of
       the called function. A parameter [inline_fuel] bounds the number of
       allowed levels before failing execution. *)
    Fixpoint sexec_call {SPEC : Specification} (inline_fuel : nat) : ExecCall M :=
      fun Δ τ f w0 args0 =>
        ⟨ θ1 ⟩ _ <- debug_call f args0 ;;
        (* Let's first see if we have a contract defined for function [f]
           and then if we have enough fuel for inlining. *)
        match CEnv f , inline_fuel with
        | Some c , _ =>
            (* YES: Execute the call by interpreting the contract. *)
            SHeapSpecM.call_contract c (persist args0 θ1)
        | None   , 0 =>
            (* Out of fuel *)
            exec_call_error_no_fuel f (persist args0 θ1)
        | None   , S n =>
            SStoreT.evalStoreT
              (SStoreT.exec_aux sexec_call_foreign sexec_lemma (sexec_call n) sexec_fail (FunDef f) (w := _))
              (persist args0 θ1)
        end.

    Definition sexec {SPEC : Specification} (inline_fuel : nat) : Exec M :=
      @SStoreT.exec_aux M _ SPEC sexec_call_foreign sexec_lemma
        (sexec_call inline_fuel) sexec_fail.

  End WithSpec.
  #[global] Arguments exec_call_error_no_fuel {M _}.
  #[global] Arguments sexec {M _} cfg {SPEC} _ [_ _] s _ : simpl never.

End SymbolicExecOn.
