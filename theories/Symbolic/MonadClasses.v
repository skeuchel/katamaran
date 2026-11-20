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
  Strings.String.
From Katamaran Require Import
  Prelude
  Base
  Syntax.Chunks
  Syntax.Predicates
  Symbolic.Propositions
  Symbolic.Worlds.

Import ctx.notations.
Import env.notations.

#[local] Set Implicit Arguments.

Module Type SymbolicMonadClassesOn (Import B : Base) (Import P : PredicateKit B)
  (Import W : WorldsMixin B P) (Import SP : SymPropOn B P W).

  Import ModalNotations.
  Import Erasure.
  #[local] Open Scope modal.

  Definition seval_exps {Γ Σ N} (δ : SStore Γ Σ) {Δ} :
    NamedEnv (X := N) (Exp Γ) Δ -> NamedEnv (Term Σ) Δ
      := env.map (fun b (e : Exp Γ (type b)) => peval (seval_exp δ e)).

  Section DebugInfo.

    Import option.notations.

    Record DebugAsn (Σ : LCtx) : Type :=
      MkDebugAsn
        { (* debug_asn_program_context        : PCtx; *)
          debug_asn_pathcondition          : PathCondition Σ;
          (* debug_asn_localstore             : SStore debug_asn_program_context Σ; *)
          debug_asn_heap                   : SHeap Σ;
        }.

    #[export] Instance SubstDebugAsn : Subst DebugAsn :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugAsn pc (* δ *) h =>
          MkDebugAsn (subst pc ζ01) (* (subst δ ζ01) *) (subst h ζ01)
        end.

    #[export] Instance SubstSUDebugAsn : SubstSU WeakensTo DebugAsn :=
      fun Σ0 Σ1 d ζ01 =>
        match d with
        | MkDebugAsn pc (* δ *) h =>
          MkDebugAsn (substSU pc ζ01) (* (substSU δ ζ01) *) (substSU h ζ01)
        end.

    #[export] Instance SubstLawsDebugAsn : SubstLaws DebugAsn.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    #[export] Instance SubstSULawsDebugAsn : SubstSULaws WeakensTo DebugAsn.
    Proof.
      intros Σ1 Σ2 Σ3 ζ1 ζ2 [pc h]; cbn -[transSU]; f_equal; now apply substSU_trans.
    Qed.

    #[export] Instance OccursCheckDebugAsn : OccursCheck DebugAsn :=
      fun Σ x xIn d =>
        match d with
        | MkDebugAsn pc (* δ *) h =>
            pc' <- occurs_check xIn pc ;;
            (* δ'  <- occurs_check xIn δ ;; *)
            h'  <- occurs_check xIn h ;;
            Some (MkDebugAsn pc' (* δ' *) h')
        end.

    (* #[export] Instance GenOccursCheckDebugAsn : GenOccursCheck DebugAsn := *)
    (*   fun Σ d => *)
    (*     match d with *)
    (*     | MkDebugAsn pc h => *)
    (*         liftBinOp (fun _ pc' h' => MkDebugAsn pc' h') (fun _ _ _ _ _ => eq_refl) *)
    (*           (gen_occurs_check pc) (gen_occurs_check h) *)
    (*     end. *)

    Record DebugConsumeChunk (Σ : LCtx) : Type :=
      MkDebugConsumeChunk
        { (* debug_consume_chunk_program_context        : PCtx; *)
          debug_consume_chunk_pathcondition          : PathCondition Σ;
          (* debug_consume_chunk_localstore             : SStore debug_consume_chunk_program_context Σ; *)
          debug_consume_chunk_heap                   : SHeap Σ;
          debug_consume_chunk_chunk                  : Chunk Σ;
        }.

    Record EDebugConsumeChunk : Type :=
      MkEDebugConsumeChunk
        { (* edebug_consume_chunk_program_context        : PCtx; *)
          edebug_consume_chunk_pathcondition          : list EFormula;
          (* edebug_consume_chunk_localstore             : SStore debug_consume_chunk_program_context Σ; *)
          edebug_consume_chunk_heap                   : list EChunk;
          edebug_consume_chunk_chunk                  : EChunk;
        }.
    #[export] Instance Erase_DebugConsumeChunk : Erase DebugConsumeChunk EDebugConsumeChunk :=
      fun _ '(MkDebugConsumeChunk pc h c) => MkEDebugConsumeChunk (erase pc) (erase h) (erase c).

    #[export] Instance SubstDebugConsumeChunk : Subst DebugConsumeChunk :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugConsumeChunk pc (* δ *) h c =>
            MkDebugConsumeChunk (subst pc ζ01) (* (subst δ ζ01) *) (subst h ζ01) (subst c ζ01)
        end.

    #[export] Instance SubstSUDebugConsumeChunk `{SubstUniv Sb}: SubstSU Sb DebugConsumeChunk :=
      fun Σ0 Σ1 d ζ01 =>
        match d with
        | MkDebugConsumeChunk pc (* δ *) h c =>
            MkDebugConsumeChunk (substSU pc ζ01) (* (substSU δ ζ01) *) (substSU h ζ01) (substSU c ζ01)
        end.

    #[export] Instance SubstLawsDebugConsumeChunk : SubstLaws DebugConsumeChunk.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    #[export] Instance SubstSULawsDebugConsumeChunk `{SubstUnivLaws Sb} :
      SubstSULaws Sb DebugConsumeChunk.
    Proof.
      intros ? ? ? ? ? []; cbn; f_equal; apply substSU_trans.
    Qed.

    #[export] Instance OccursCheckDebugConsumeChunk : OccursCheck DebugConsumeChunk :=
      fun Σ x xIn d =>
        match d with
        | MkDebugConsumeChunk pc (* δ *) h c =>
            pc' <- occurs_check xIn pc ;;
            (* δ'  <- occurs_check xIn δ ;; *)
            h'  <- occurs_check xIn h ;;
            c'  <- occurs_check xIn c ;;
            Some (MkDebugConsumeChunk pc' (* δ' *) h'  c')
        end.

    (* #[export] Instance GenOccursCheckDebugConsumeChunk : GenOccursCheck (Sb := WeakensTo) DebugConsumeChunk := *)
    (*   fun Σ d => *)
    (*     match d with *)
    (*     | MkDebugConsumeChunk pc (* δ *) h c => *)
    (*         liftTernOp (fun Σ pc' h' c' => MkDebugConsumeChunk pc' h' c') *)
    (*           (fun _ _ _ _ _ _ => eq_refl) *)
    (*           (gen_occurs_check pc) (gen_occurs_check h) (gen_occurs_check c) *)
    (*     end. *)

    Record DebugReadRegister (Σ : LCtx) : Type :=
      MkDebugReadRegister
        { debug_read_register_pathcondition : PathCondition Σ;
          debug_read_register_heap          : SHeap Σ;
          debug_read_register_type          : Ty;
          debug_read_register_register      : 𝑹𝑬𝑮 debug_read_register_type;
        }.

    Record EDebugReadRegister : Type :=
      MkEDebugReadRegister
        { edebug_read_register_pathcondition : list EFormula;
          edebug_read_register_heap          : list EChunk;
          edebug_read_register_type          : Ty;
          edebug_read_register_register      : 𝑹𝑬𝑮 edebug_read_register_type;
        }.

    #[export] Instance EraseDebugReadRegister : Erase DebugReadRegister EDebugReadRegister :=
      fun _ '(MkDebugReadRegister pc h r) => MkEDebugReadRegister (erase pc) (erase h) r.

    #[export] Instance SubstDebugReadRegister : Subst DebugReadRegister :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugReadRegister pc h r =>
            MkDebugReadRegister (subst pc ζ01) (subst h ζ01) r
        end.

    #[export] Instance SubstSUDebugReadRegister `{SubstUniv Sb} : SubstSU Sb DebugReadRegister :=
      fun Σ0 Σ1 d ζ01 =>
        match d with
        | MkDebugReadRegister pc h r =>
            MkDebugReadRegister (substSU pc ζ01) (substSU h ζ01) r
        end.

    #[export] Instance SubstLawsDebugReadRegister : SubstLaws DebugReadRegister.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    #[export] Instance SubstSULawsDebugReadRegister `{SubstUnivLaws Sb} :
      SubstSULaws Sb DebugReadRegister.
    Proof.
      intros ? ? ? ? ? []; cbn; f_equal; apply substSU_trans.
    Qed.

    #[export] Instance OccursCheckDebugReadRegister : OccursCheck DebugReadRegister :=
      fun Σ x xIn d =>
        match d with
        | MkDebugReadRegister pc h r =>
            pc' <- occurs_check xIn pc ;;
            h'  <- occurs_check xIn h ;;
            Some (MkDebugReadRegister pc' h' r)
        end.

    (* #[export] Instance GenOccursCheckDebugReadRegister : GenOccursCheck DebugReadRegister := *)
    (*   fun Σ d => *)
    (*     match d with *)
    (*     | MkDebugReadRegister pc h r => *)
    (*         liftBinOp (fun Σ pc' h' => MkDebugReadRegister pc' h' r) *)
    (*           (fun _ _ _ _ _ => eq_refl) *)
    (*           (gen_occurs_check pc) (gen_occurs_check h) *)
    (*     end. *)

    Record DebugWriteRegister (Σ : LCtx) : Type :=
      MkDebugWriteRegister
        { debug_write_register_pathcondition : PathCondition Σ;
          debug_write_register_heap          : SHeap Σ;
          debug_write_register_type          : Ty;
          debug_write_register_register      : 𝑹𝑬𝑮 debug_write_register_type;
          debug_write_register_value         : Term Σ debug_write_register_type;
        }.
    Record EDebugWriteRegister : Type :=
      MkEDebugWriteRegister
        { edebug_write_register_pathcondition : list EFormula;
          edebug_write_register_heap          : list EChunk;
          edebug_write_register_type          : Ty;
          edebug_write_register_register      : 𝑹𝑬𝑮 edebug_write_register_type;
          edebug_write_register_value         : ETerm edebug_write_register_type;
        }.

    #[export] Instance EraseDebugWriteRegister : Erase DebugWriteRegister EDebugWriteRegister :=
      fun _ '(MkDebugWriteRegister pc h r t) => MkEDebugWriteRegister (erase pc) (erase h) r (erase t).

    #[export] Instance SubstDebugWriteRegister : Subst DebugWriteRegister :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugWriteRegister pc h r t =>
            MkDebugWriteRegister (subst pc ζ01) (subst h ζ01) r (subst t ζ01)
        end.

    #[export] Instance SubstSUDebugWriteRegister `{SubstUniv Sb} : SubstSU Sb DebugWriteRegister :=
      fun Σ0 Σ1 d ζ01 =>
        match d with
        | MkDebugWriteRegister pc h r t =>
            MkDebugWriteRegister (substSU pc ζ01) (substSU h ζ01) r (substSU t ζ01)
        end.

    #[export] Instance SubstLawsDebugWriteRegister : SubstLaws DebugWriteRegister.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    #[export] Instance SubstSULawsDebugWriteRegister `{SubstUnivLaws Sb} :
      SubstSULaws Sb DebugWriteRegister.
    Proof.
      intros ? ? ? ? ? []; cbn; f_equal; now apply substSU_trans.
    Qed.

    #[export] Instance OccursCheckDebugWriteRegister : OccursCheck DebugWriteRegister :=
      fun Σ x xIn d =>
        match d with
        | MkDebugWriteRegister pc h r t =>
            pc' <- occurs_check xIn pc ;;
            h'  <- occurs_check xIn h ;;
            t'  <- occurs_check xIn t ;;
            Some (MkDebugWriteRegister pc' h' r t')
        end.

    (* #[export] Instance GenOccursCheckDebugWriteRegister : GenOccursCheck DebugWriteRegister := *)
    (*   fun Σ d => *)
    (*     match d with *)
    (*     | MkDebugWriteRegister pc h r t => *)
    (*         liftTernOp (fun Σ pc' h' t' => MkDebugWriteRegister pc' h' r t') *)
    (*           (fun _ _ _ _ _ _ => eq_refl) *)
    (*           (gen_occurs_check pc) (gen_occurs_check h) (gen_occurs_check t) *)
    (*     end. *)

    Record DebugString (Σ : LCtx) : Type :=
      MkDebugString
        { debug_string_pathcondition : PathCondition Σ;
          debug_string_message       : string;
        }.
    Record EDebugString : Type :=
      MkEDebugString
        { edebug_string_pathcondition : list EFormula;
          edebug_string_message       : string;
        }.
    #[export] Instance EraseDebugString : Erase DebugString EDebugString :=
      fun _ '(MkDebugString pc s) => MkEDebugString (erase pc) s.

    #[export] Instance SubstDebugString : Subst DebugString :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugString pc s =>
            MkDebugString (subst pc ζ01) s
        end.

    #[export] Instance SubstSUDebugString : SubstSU WeakensTo DebugString :=
      fun Σ0 Σ1 d ζ01 =>
        match d with
        | MkDebugString pc s =>
            MkDebugString (substSU pc ζ01) s
        end.

    #[export] Instance SubstLawsDebugString : SubstLaws DebugString.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    #[export] Instance OccursCheckDebugString : OccursCheck DebugString :=
      fun Σ x xIn d =>
        match d with
        | MkDebugString pc s =>
            pc' <- occurs_check xIn pc ;;
            Some (MkDebugString pc' s)
        end.

    (* #[export] Instance GenOccursCheckDebugString : GenOccursCheck DebugString := *)
    (*   fun Σ d => *)
    (*     match d with *)
    (*     | MkDebugString pc s => *)
    (*         liftUnOp (fun Σ pc' => MkDebugString pc' s) (fun _ _ _ _ => eq_refl) *)
    (*           (gen_occurs_check pc) *)
    (*     end. *)

    Record DebugAssertFormula (Σ : LCtx) : Type :=
      MkDebugAssertFormula
        { debug_assert_formula_pathcondition   : PathCondition Σ;
          debug_assert_formula_heap            : SHeap Σ;
          debug_assert_formula_formula         : Formula Σ;
        }.

    #[export] Instance SubstDebugAssertFormula : Subst DebugAssertFormula :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugAssertFormula pc h fml =>
          MkDebugAssertFormula (subst pc ζ01) (subst h ζ01) (subst fml ζ01)
        end.

    #[export] Instance SubstSUDebugAssertFormula : SubstSU WeakensTo DebugAssertFormula :=
      fun Σ0 Σ1 d ζ01 =>
        match d with
        | MkDebugAssertFormula pc h fml =>
          MkDebugAssertFormula (substSU pc ζ01) (substSU h ζ01) (substSU fml ζ01)
        end.

    #[export] Instance SubstLawsDebugAssertFormula : SubstLaws DebugAssertFormula.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    #[export] Instance OccursCheckDebugAssertFormula : OccursCheck DebugAssertFormula :=
      fun Σ x xIn d =>
        match d with
        | MkDebugAssertFormula pc h fml =>
            pc' <- occurs_check xIn pc ;;
            h'  <- occurs_check xIn h ;;
            fml'  <- occurs_check xIn fml ;;
            Some (MkDebugAssertFormula pc' h' fml')
        end.

    (* #[export] Instance GenOccursCheckDebugAssertFormula : GenOccursCheck (Sb := WeakensTo) DebugAssertFormula := *)
    (*   fun Σ d => *)
    (*     match d with *)
    (*     | MkDebugAssertFormula pc h fml => *)
    (*         liftTernOp (fun Σ pc' h' fml' => MkDebugAssertFormula pc' h' fml') *)
    (*           (fun _ _ _ _ _ _ => eq_refl) *)
    (*           (gen_occurs_check pc) (gen_occurs_check h) (gen_occurs_check fml) *)
    (*     end. *)

  End DebugInfo.

  (* Interface of symbolic monads with the verification effects and a heap.
     Messages can depend on the current heap. *)
  Module SHeapSpecM.

    Class SHeapSpecM (M : TYPE -> TYPE) : Type :=
      { pure {A} : ⊢ A -> M A;
        bind {A B} : ⊢ M A -> □(A -> M B) -> M B;
        error {A} : ⊢ (SHeap -> AMessage) -> M A;
        block {A} : ⊢ M A;
        angelic (x : option LVar) : ⊢ ∀ σ, M (STerm σ);
        demonic (x : option LVar) : ⊢ ∀ σ, M (STerm σ);
        angelic_binary {A} : ⊢ M A -> M A -> M A;
        demonic_binary {A} : ⊢ M A -> M A -> M A;
        assert_formula : ⊢ (SHeap -> AMessage) -> Formula -> M Unit;
        assume_formula : ⊢ Formula -> M Unit;
        angelic_pattern_match {N : Set} (n : N -> LVar) {σ} (pat : Pattern (N:=N) σ) :
          ⊢ (SHeap -> AMessage) -> WTerm σ -> M (SMatchResult pat);
        demonic_pattern_match {N : Set} (n : N -> LVar) {σ} (pat : Pattern (N:=N) σ) :
          ⊢ WTerm σ -> M (SMatchResult pat);
        debug {A} : ⊢ (SHeap -> AMessage) -> M A -> M A;
        produce_chunk : ⊢ Chunk -> M Unit;
        consume_chunk : ⊢ Chunk -> M Unit;
        consume_chunk_angelic : ⊢ Chunk -> M Unit;
        read_register {τ} (reg : 𝑹𝑬𝑮 τ) : ⊢ M (WTerm τ);
        write_register {τ} (reg : 𝑹𝑬𝑮 τ) : ⊢ WTerm τ -> M (WTerm τ);
      }.
    #[global] Arguments pure {M _ A} [w] a.
    #[global] Arguments bind {M _ A B} [w] m f.
    #[global] Arguments error {M _ A} [w] msg.
    #[global] Arguments block {M _ A w}.
    #[global] Arguments angelic {M _} x [w] σ : rename.
    #[global] Arguments demonic {M _} x [w] σ : rename.
    #[global] Arguments angelic_binary {M _ A} [w] m1 m2.
    #[global] Arguments demonic_binary {M _ A} [w] m1 m2.
    #[global] Arguments assert_formula {M _} [w] msg fml.
    #[global] Arguments assume_formula {M _} [w] fml.
    #[global] Arguments angelic_pattern_match {M _ N} n {σ} pat [w] msg t.
    #[global] Arguments demonic_pattern_match {M _ N} n {σ} pat [w] t.
    #[global] Arguments debug {M _ A} [w] msg m.
    #[global] Arguments produce_chunk {M _} [w] c.
    #[global] Arguments consume_chunk {M _} [w] c.
    #[global] Arguments consume_chunk_angelic {M _} [w] c.
    #[global] Arguments read_register {M _ τ} reg {w}.
    #[global] Arguments write_register {M _ τ} reg [w] t.

    Module Import notations.
      Notation "⟨ θ ⟩ ' x <- ma ;; mb" :=
        (bind ma (fun _ θ x => mb))
          (at level 0, x pattern,
             ma at level 19, mb at level 200,
               right associativity).
      Notation "⟨ θ ⟩ x <- ma ;; mb" :=
        (bind ma (fun _ θ x => mb))
          (at level 0, x at next level,
             ma at level 19, mb at level 200,
               right associativity).
      Notation "x ⟨ θ ⟩" := (persist x θ).
    End notations.

  End SHeapSpecM.
  Export SHeapSpecM (SHeapSpecM).

End SymbolicMonadClassesOn.
