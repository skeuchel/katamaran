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
     Lists.List
     Strings.String.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Prelude
     Signature
     Symbolic.Worlds
     Sep.Hoare
     Base.

Import ctx.notations.
Import env.notations.
Import ListNotations.

Set Implicit Arguments.

Module Type NewSymbolicExecOn
  (Import B : Base)
  (Import SIG : Signature B)
  (Import PROG : Program B)
  (Import PLOG : ProgramLogic B SIG PROG).

  Import ModalNotations.
  #[local] Open Scope modal.

  #[local] Hint Extern 2 (Persistent (WTerm ?σ)) =>
    refine (@persistent_subst (STerm σ) (@SubstTerm σ)) : typeclass_instances.
  #[local] Hint Extern 2 (Persistent (fun w : World => NamedEnv (Term (wctx w)) ?Γ)) =>
    refine (@persistent_subst (fun Σ : LCtx => NamedEnv (Term Σ) Γ) _) : typeclass_instances.

  Section DebugInfo.

    Import option.notations.

    Record DebugMsg (Σ : LCtx) : Type :=
      MkDebugMsg
        { debug_msg_pathcondition : PathCondition Σ;
          debug_msg_message       : string;
        }.

    #[export] Instance SubstDebugMsg : Subst DebugMsg :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugMsg pc s => MkDebugMsg (subst pc ζ01) s
        end.

    #[export] Instance SubstSUDebugMsg : SubstSU WeakensTo DebugMsg :=
      fun Σ0 Σ1 d ζ01 =>
        match d with
        | MkDebugMsg pc s => MkDebugMsg (substSU pc ζ01) s
        end.

    #[export] Instance SubstLawsDebugMsg : SubstLaws DebugMsg.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    #[export] Instance SubstSULawsDebugMsg : SubstSULaws WeakensTo DebugMsg.
    Proof.
      intros Σ1 Σ2 Σ3 ζ1 ζ2 [pc s]; cbn -[transSU]; f_equal; now apply substSU_trans.
    Qed.

    #[export] Instance OccursCheckDebugMsg : OccursCheck DebugMsg :=
      fun Σ x xIn d =>
        match d with
        | MkDebugMsg pc s =>
            pc' <- occurs_check xIn pc ;;
            Some (MkDebugMsg pc' s)
        end.

    #[export] Instance EraseDebugMsg : Erase DebugMsg EDebugString :=
      fun _ '(MkDebugMsg pc s) => MkEDebugString (erase pc) s.

    (* A function activation on the symbolic call stack. *)
    Inductive Frame (Σ : LCtx) : Type :=
    | frame_call {Δ τ} (f : 𝑭 Δ τ) (args : SStore Δ Σ)
    | frame_foreign {Δ τ} (f : 𝑭𝑿 Δ τ) (args : SStore Δ Σ)
    | frame_lemma {Δ} (l : 𝑳 Δ) (args : SStore Δ Σ).

    Inductive EFrame : Type :=
    | eframe_call {Δ τ} (f : 𝑭 Δ τ) (args : NamedEnv ETerm Δ)
    | eframe_foreign {Δ τ} (f : 𝑭𝑿 Δ τ) (args : NamedEnv ETerm Δ)
    | eframe_lemma {Δ} (l : 𝑳 Δ) (args : NamedEnv ETerm Δ).

    #[export] Instance SubstFrame : Subst Frame :=
      fun Σ0 fr Σ1 ζ01 =>
        match fr with
        | frame_call f args    => frame_call f (subst args ζ01)
        | frame_foreign f args => frame_foreign f (subst args ζ01)
        | frame_lemma l args   => frame_lemma l (subst args ζ01)
        end.

    #[export] Instance SubstSUFrame : SubstSU WeakensTo Frame :=
      fun Σ0 Σ1 fr ζ01 =>
        match fr with
        | frame_call f args    => frame_call f (substSU args ζ01)
        | frame_foreign f args => frame_foreign f (substSU args ζ01)
        | frame_lemma l args   => frame_lemma l (substSU args ζ01)
        end.

    #[export] Instance SubstLawsFrame : SubstLaws Frame.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    #[export] Instance SubstSULawsFrame : SubstSULaws WeakensTo Frame.
    Proof.
      intros Σ1 Σ2 Σ3 ζ1 ζ2 []; cbn -[transSU]; f_equal; now apply substSU_trans.
    Qed.

    #[export] Instance OccursCheckFrame : OccursCheck Frame :=
      fun Σ x xIn fr =>
        match fr with
        | frame_call f args    => args' <- occurs_check xIn args ;; Some (frame_call f args')
        | frame_foreign f args => args' <- occurs_check xIn args ;; Some (frame_foreign f args')
        | frame_lemma l args   => args' <- occurs_check xIn args ;; Some (frame_lemma l args')
        end.

    #[export] Instance EraseFrame : Erase Frame EFrame :=
      fun _ fr =>
        match fr with
        | frame_call f args    => eframe_call f (erase args)
        | frame_foreign f args => eframe_foreign f (erase args)
        | frame_lemma l args   => eframe_lemma l (erase args)
        end.

    (* What a message produced by the executor is about. *)
    Inductive DebugKind (Σ : LCtx) : Type :=
    | dk_string (s : string)
    | dk_formula (s : string) (fml : Formula Σ)
    | dk_stm {Γ τ} (s : Stm Γ τ) (δ : SStore Γ Σ) (descr : string).

    Inductive EDebugKind : Type :=
    | edk_string (s : string)
    | edk_formula (s : string) (fml : EFormula)
    | edk_stm {Γ τ} (s : Stm Γ τ) (δ : NamedEnv ETerm Γ) (descr : string).

    #[export] Instance SubstDebugKind : Subst DebugKind :=
      fun Σ0 k Σ1 ζ01 =>
        match k with
        | dk_string _ s      => dk_string _ s
        | dk_formula s fml   => dk_formula s (subst fml ζ01)
        | dk_stm s δ descr   => dk_stm s (subst δ ζ01) descr
        end.

    #[export] Instance SubstSUDebugKind : SubstSU WeakensTo DebugKind :=
      fun Σ0 Σ1 k ζ01 =>
        match k with
        | dk_string _ s      => dk_string _ s
        | dk_formula s fml   => dk_formula s (substSU fml ζ01)
        | dk_stm s δ descr   => dk_stm s (substSU δ ζ01) descr
        end.

    #[export] Instance SubstLawsDebugKind : SubstLaws DebugKind.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    #[export] Instance SubstSULawsDebugKind : SubstSULaws WeakensTo DebugKind.
    Proof.
      intros Σ1 Σ2 Σ3 ζ1 ζ2 []; cbn -[transSU]; f_equal; now apply substSU_trans.
    Qed.

    #[export] Instance OccursCheckDebugKind : OccursCheck DebugKind :=
      fun Σ x xIn k =>
        match k with
        | dk_string _ s    => Some (dk_string _ s)
        | dk_formula s fml => fml' <- occurs_check xIn fml ;; Some (dk_formula s fml')
        | dk_stm s δ descr => δ' <- occurs_check xIn δ ;; Some (dk_stm s δ' descr)
        end.

    #[export] Instance EraseDebugKind : Erase DebugKind EDebugKind :=
      fun _ k =>
        match k with
        | dk_string _ s    => edk_string s
        | dk_formula s fml => edk_formula s (erase fml)
        | dk_stm s δ descr => edk_stm s (erase δ) descr
        end.

    (* The messages of the symbolic monad interface: what happened and the
       call stack, innermost activation first. The executor leaves the stack
       empty; monads that track activations fill it in. *)
    Record SMsg (Σ : LCtx) : Type :=
      MkSMsg
        { smsg_kind   : DebugKind Σ;
          smsg_frames : List Frame Σ;
        }.

    Definition smsg_string {Σ} (s : string) : SMsg Σ :=
      MkSMsg (dk_string Σ s) nil.

    #[export] Instance SubstSMsg : Subst SMsg :=
      fun Σ0 m Σ1 ζ01 =>
        match m with
        | MkSMsg k fs => MkSMsg (subst k ζ01) (subst fs ζ01)
        end.

    #[export] Instance SubstLawsSMsg : SubstLaws SMsg.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    (* The full debug information of a message: what happened, the path
       condition, the heap, and the call stack. *)
    Record DebugInfo (Σ : LCtx) : Type :=
      MkDebugInfo
        { debug_info_kind          : DebugKind Σ;
          debug_info_pathcondition : PathCondition Σ;
          debug_info_heap          : SHeap Σ;
          debug_info_frames        : List Frame Σ;
        }.

    Record EDebugInfo : Type :=
      MkEDebugInfo
        { edebug_info_kind          : EDebugKind;
          edebug_info_pathcondition : list EFormula;
          edebug_info_heap          : list EChunk;
          edebug_info_frames        : list EFrame;
        }.

    #[export] Instance SubstDebugInfo : Subst DebugInfo :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugInfo k pc h fs =>
            MkDebugInfo (subst k ζ01) (subst pc ζ01) (subst h ζ01) (subst fs ζ01)
        end.

    #[export] Instance SubstSUDebugInfo : SubstSU WeakensTo DebugInfo :=
      fun Σ0 Σ1 d ζ01 =>
        match d with
        | MkDebugInfo k pc h fs =>
            MkDebugInfo (substSU k ζ01) (substSU pc ζ01) (substSU h ζ01) (substSU fs ζ01)
        end.

    #[export] Instance SubstLawsDebugInfo : SubstLaws DebugInfo.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    #[export] Instance SubstSULawsDebugInfo : SubstSULaws WeakensTo DebugInfo.
    Proof.
      intros Σ1 Σ2 Σ3 ζ1 ζ2 []; cbn -[transSU]; f_equal; now apply substSU_trans.
    Qed.

    #[export] Instance OccursCheckDebugInfo : OccursCheck DebugInfo :=
      fun Σ x xIn d =>
        match d with
        | MkDebugInfo k pc h fs =>
            k'  <- occurs_check xIn k ;;
            pc' <- occurs_check xIn pc ;;
            h'  <- occurs_check xIn h ;;
            fs' <- occurs_check xIn fs ;;
            Some (MkDebugInfo k' pc' h' fs')
        end.

    #[export] Instance EraseDebugInfo : Erase DebugInfo EDebugInfo :=
      fun _ '(MkDebugInfo k pc h fs) =>
        MkEDebugInfo (erase k) (erase pc) (erase h) (List.map (fun fr => erase fr) fs).

    Definition debug_info {Σ} (pc : PathCondition Σ) (h : SHeap Σ) (m : SMsg Σ) :
      AMessage Σ :=
      amsg.mk (M := DebugInfo) (MkDebugInfo (smsg_kind m) pc h (smsg_frames m)).

  End DebugInfo.

  (* Interface of symbolic monads with the pure verification effects. *)
  Module SPureSpecM.

    Class SPureSpecM (M : TYPE -> TYPE) : Type :=
      { pure {A} : ⊢ A -> M A;
        bind {A B} : ⊢ M A -> □(A -> M B) -> M B;
        error {A} : ⊢ SMsg -> M A;
        block {A} : ⊢ M A;
        angelic (x : option LVar) : ⊢ ∀ σ, M (STerm σ);
        demonic (x : option LVar) : ⊢ ∀ σ, M (STerm σ);
        angelic_binary {A} : ⊢ M A -> M A -> M A;
        demonic_binary {A} : ⊢ M A -> M A -> M A;
        assert_formula : ⊢ SMsg -> Formula -> M Unit;
        assume_formula : ⊢ Formula -> M Unit;
        angelic_pattern_match {N : Set} (n : N -> LVar) {σ} (pat : Pattern (N:=N) σ) :
          ⊢ SMsg -> STerm σ -> M (SMatchResult pat);
        demonic_pattern_match {N : Set} (n : N -> LVar) {σ} (pat : Pattern (N:=N) σ) :
          ⊢ STerm σ -> M (SMatchResult pat);
        debug {A} : ⊢ SMsg -> M A -> M A;
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

    Module notations.
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
    Import notations.

    (* Operations that are derived from the interface. *)
    Section Derived.

      Context {M} {pureM : SPureSpecM M}.

      Definition angelic_ctx {N : Set} (n : N -> LVar) :
        ⊢ ∀ Δ : NCtx N Ty, M (fun w => NamedEnv (Term w) Δ) :=
        fix rec {w} Δ {struct Δ} :=
          match Δ with
          | []%ctx => pure []%env
          | Γ ▻ x∷σ =>
              bind (rec Γ) (fun w1 _ (tΔ : NamedEnv (Term w1) Γ) =>
              bind (angelic (Some (n x)) σ) (fun w2 ω2 (tσ : Term w2 σ) =>
              pure (A := fun w => NamedEnv (Term w) (Γ ▻ x∷σ))
                (env.snoc (persist (A := fun w => NamedEnv (Term w) Γ) tΔ ω2) (x∷σ) tσ)))
          end.

      Definition demonic_ctx {N : Set} (n : N -> LVar) :
        ⊢ ∀ Δ : NCtx N Ty, M (fun w => NamedEnv (Term w) Δ) :=
        fix rec {w} Δ {struct Δ} :=
          match Δ with
          | []%ctx => pure []%env
          | Γ ▻ x∷σ =>
              bind (rec Γ) (fun w1 _ (tΔ : NamedEnv (Term w1) Γ) =>
              bind (demonic (Some (n x)) σ) (fun w2 ω2 (tσ : Term w2 σ) =>
              pure (A := fun w => NamedEnv (Term w) (Γ ▻ x∷σ))
                (env.snoc (persist (A := fun w => NamedEnv (Term w) Γ) tΔ ω2) (x∷σ) tσ)))
          end.

      Equations(noeqns) assert_eq_nenv {N} :
        let E Δ := fun w : World => NamedEnv (Term w) Δ in
        ⊢ ∀ Δ : NCtx N Ty, SMsg -> E Δ -> E Δ -> M Unit :=
      assert_eq_nenv msg env.nil          env.nil            := pure tt;
      assert_eq_nenv msg (env.snoc δ _ t) (env.snoc δ' _ t') :=
        ⟨ θ ⟩ _ <- assert_eq_nenv msg δ δ' ;;
        assert_formula (persist msg θ) (formula_relop bop.eq t t')⟨θ⟩.

    End Derived.
    #[global] Arguments angelic_ctx {M _ N} n [w] Δ : rename.
    #[global] Arguments demonic_ctx {M _ N} n [w] Δ : rename.

  End SPureSpecM.
  Export SPureSpecM (SPureSpecM).

  (* Interface of symbolic monads that additionally have a heap. *)
  Module SHeapSpecM.

    Import SPureSpecM SPureSpecM.notations.

    Class SHeapSpecM (M : TYPE -> TYPE) : Type :=
      { produce_chunk : ⊢ Chunk -> M Unit;
        consume_chunk : ⊢ Chunk -> M Unit;
        consume_chunk_angelic : ⊢ Chunk -> M Unit;
        read_register {τ} (reg : 𝑹𝑬𝑮 τ) : ⊢ M (STerm τ);
        write_register {τ} (reg : 𝑹𝑬𝑮 τ) : ⊢ STerm τ -> M (STerm τ);
      }.
    #[global] Arguments produce_chunk {M _} [w] c.
    #[global] Arguments consume_chunk {M _} [w] c.
    #[global] Arguments consume_chunk_angelic {M _} [w] c.
    #[global] Arguments read_register {M _ τ} reg {w}.
    #[global] Arguments write_register {M _ τ} reg [w] t.

    Section Derived.

      Context {M} {pureM : SPureSpecM M} {heapM : SHeapSpecM M}.

      Definition produce :
        forall {Σ} (asn : Assertion Σ), ⊢ Sub Σ -> M Unit :=
        fix produce {Σ} asn {w} ζ :=
          match asn with
          | asn.formula fml =>
              assume_formula (subst fml ζ)
          | asn.chunk c =>
              produce_chunk (subst c ζ)
          | asn.chunk_angelic c =>
              produce_chunk (subst c ζ)
          | asn.pattern_match s pat rhs =>
              ⟨ θ ⟩ '(existT pc δpc) <- demonic_pattern_match id pat (subst s ζ) ;;
              produce (rhs pc) (persist ζ θ ►► δpc)
          | asn.sep a1 a2 =>
              ⟨ θ ⟩ _ <- produce a1 ζ ;;
              produce a2 (persist ζ θ)
          | asn.or a1 a2 =>
              demonic_binary (produce a1 ζ) (produce a2 ζ)
          | asn.exist ς τ a =>
              ⟨ θ ⟩ t <- demonic (Some ς) τ ;;
              produce a (env.snoc (persist ζ θ) (ς∷τ) t)
          | asn.debug =>
              debug
                (smsg_string "produce")
                (pure tt)
          end.

      Definition consume :
        forall {Σ} (asn : Assertion Σ), ⊢ Sub Σ -> M Unit :=
        fix consume {Σ} asn {w} ζ :=
          match asn with
          | asn.formula fml =>
              let fml := subst fml ζ in
              assert_formula
                (MkSMsg (dk_formula "consume.formula" fml) nil)
                fml
          | asn.chunk c =>
              consume_chunk (subst c ζ)
          | asn.chunk_angelic c =>
              consume_chunk_angelic (subst c ζ)
          | asn.pattern_match s pat rhs =>
              ⟨ θ ⟩ '(existT pc δpc) <-
                angelic_pattern_match id pat
                  (smsg_string "consume.pattern_match")
                  (subst s ζ) ;;
              consume (rhs pc) (persist ζ θ ►► δpc)
          | asn.sep a1 a2 =>
              ⟨ θ ⟩ _ <- consume a1 ζ ;;
              consume a2 (persist ζ θ)
          | asn.or a1 a2 =>
              angelic_binary (consume a1 ζ) (consume a2 ζ)
          | asn.exist ς τ a =>
              ⟨ θ ⟩ t <- angelic (Some ς) τ ;;
              consume a (env.snoc (persist ζ θ) (ς∷τ) t)
          | asn.debug =>
              debug
                (smsg_string "consume")
                (pure tt)
          end.

      Definition call_contract {Δ τ} (c : SepContract Δ τ) :
        ⊢ SStore Δ -> M (STerm τ) :=
        fun w0 args =>
          match c with
          | MkSepContract _ _ Σe δe req result ens =>
              ⟨ θ1 ⟩ evars <- angelic_ctx id Σe ;;
              ⟨ θ2 ⟩ _     <-
                assert_eq_nenv
                  (smsg_string "call_contract")
                  args⟨θ1⟩ (subst δe evars) ;;
              let evars2 := persist (A := Sub _) evars θ2 in
              ⟨ θ3 ⟩ _     <- consume req evars2 ;;
              ⟨ θ4 ⟩ res   <- demonic (Some result) τ ;;
              let evars4 := persist (A := Sub _) evars2 (θ3 ∘ θ4) in
              ⟨ θ5 ⟩ _     <- produce ens (sub_snoc evars4 (result∷τ) res) ;;
              pure (persist__term res θ5)
          end.

      Definition call_lemma {Δ} (lem : Lemma Δ) :
        ⊢ SStore Δ -> M Unit :=
        fun w0 args =>
          match lem with
          | MkLemma _ Σe δe req ens =>
              ⟨ θ1 ⟩ evars <- angelic_ctx id Σe ;;
              ⟨ θ2 ⟩ _     <-
                assert_eq_nenv
                  (smsg_string "call_lemma")
                  args⟨θ1⟩ (subst δe evars) ;;
              let evars2 := persist (A := Sub _) evars θ2 in
              ⟨ θ3 ⟩ _     <- consume req evars2 ;;
              let evars3 := persist (A := Sub _) evars2 θ3 in
              produce ens evars3
          end.

    End Derived.

  End SHeapSpecM.
  Export SHeapSpecM (SHeapSpecM).

  (* Interface of symbolic monads that keep track of function activations. *)
  Module SStackM.

    Class SStackM (M : TYPE -> TYPE) : Type :=
      { with_frame {A} : ⊢ Frame -> M A -> M A }.
    #[global] Arguments with_frame {M _ A} [w] fr m.

  End SStackM.
  Export SStackM (SStackM).

  (* A reader transformer for the symbolic call stack. Messages that are
     constructed by the executor are annotated with the stack. Failures inside
     heap primitives are preceded by a debug node with the stack; the nearest
     enclosing such node is the backtrace of a failure. *)
  Module SStackT.

    Import SPureSpecM SHeapSpecM.

    Definition SStackT (M : TYPE -> TYPE) (A : TYPE) : TYPE :=
      List Frame -> M A.

    Section WithMonad.

      Context {M} {pureM : SPureSpecM M} {heapM : SHeapSpecM M}.

      Definition annotate : ⊢ List Frame -> SMsg -> SMsg :=
        fun w stk msg => MkSMsg (smsg_kind msg) stk.

      Definition backtrace {A} : ⊢ List Frame -> M A -> M A :=
        fun w stk m =>
          match stk with
          | nil => m
          | cons _ _ => SPureSpecM.debug (MkSMsg (dk_string _ "backtrace") stk) m
          end.

      #[global] Instance spurespecm_sstackt : SPureSpecM (SStackT M) :=
        {| SPureSpecM.pure A w a stk := pure a;
           SPureSpecM.bind A B w m f stk :=
             bind (m stk) (fun w1 ω a => f w1 ω a (persist (A := List Frame) stk ω));
           SPureSpecM.error A w msg stk := error (annotate stk msg);
           SPureSpecM.block A w stk := block;
           SPureSpecM.angelic x w σ stk := angelic x σ;
           SPureSpecM.demonic x w σ stk := demonic x σ;
           SPureSpecM.angelic_binary A w m1 m2 stk := angelic_binary (m1 stk) (m2 stk);
           SPureSpecM.demonic_binary A w m1 m2 stk := demonic_binary (m1 stk) (m2 stk);
           SPureSpecM.assert_formula w msg fml stk := assert_formula (annotate stk msg) fml;
           SPureSpecM.assume_formula w fml stk := assume_formula fml;
           SPureSpecM.angelic_pattern_match N n σ pat w msg t stk :=
             angelic_pattern_match n pat (annotate stk msg) t;
           SPureSpecM.demonic_pattern_match N n σ pat w t stk :=
             demonic_pattern_match n pat t;
           SPureSpecM.debug A w msg m stk := debug (annotate stk msg) (m stk);
        |}.

      #[global] Instance sheapspecm_sstackt : SHeapSpecM (SStackT M) :=
        SHeapSpecM.Build_SHeapSpecM (SStackT M)
          (fun w c stk => produce_chunk (M := M) c)
          (fun w c stk => backtrace stk (consume_chunk (M := M) c))
          (fun w c stk => backtrace stk (consume_chunk_angelic (M := M) c))
          (fun τ reg (w : World) (stk : List Frame w) =>
             backtrace stk (read_register (M := M) reg (w := w)))
          (fun τ reg (w : World) t (stk : List Frame w) =>
             backtrace stk (write_register (M := M) reg t)).

      #[global] Instance sstackm_sstackt : SStackM (SStackT M) :=
        {| SStackM.with_frame A w fr m stk := m (cons fr stk) |}.

    End WithMonad.

  End SStackT.
  Export SStackT (SStackT).

  (* The symbolic store transformer. *)
  Module SStoreT.

    Import SPureSpecM SHeapSpecM.

    Section WithMonad.

      Context {M} {pureM : SPureSpecM M} {heapM : SHeapSpecM M}.

      Definition SStoreT (Γ1 Γ2 : PCtx) (A : TYPE) : TYPE :=
        SStore Γ1 -> M (WProd A (SStore Γ2)).

      Definition liftM {Γ A} : ⊢ M A -> SStoreT Γ Γ A :=
        fun w m δ =>
          SPureSpecM.bind m (fun w1 ω a => SPureSpecM.pure (a, persist δ ω)).
      Definition evalSStoreT {Γ1 Γ2 A} : ⊢ SStoreT Γ1 Γ2 A -> SStore Γ1 -> M A :=
        fun w m δ =>
          SPureSpecM.bind (m δ) (fun w1 ω '(a,_) => SPureSpecM.pure a).

      Definition pure {Γ A} : ⊢ A -> SStoreT Γ Γ A :=
        fun w a δ => SPureSpecM.pure (a, δ).
      Definition bind {Γ1 Γ2 Γ3 A B} :
        ⊢ SStoreT Γ1 Γ2 A -> □(A -> SStoreT Γ2 Γ3 B) -> SStoreT Γ1 Γ3 B :=
        fun w m f δ =>
          SPureSpecM.bind (m δ) (fun w1 ω '(a,δ1) => f w1 ω a δ1).
      Definition error {Γ1 Γ2 A} : ⊢ (SStore Γ1 -> SMsg) -> SStoreT Γ1 Γ2 A :=
        fun w msg δ => SPureSpecM.error (msg δ).
      Definition block {Γ1 Γ2 A} : ⊢ SStoreT Γ1 Γ2 A :=
        fun w δ => SPureSpecM.block.
      Definition debug {Γ1 Γ2 A} :
        ⊢ (SStore Γ1 -> SMsg) -> SStoreT Γ1 Γ2 A -> SStoreT Γ1 Γ2 A :=
        fun w msg m δ => SPureSpecM.debug (msg δ) (m δ).

      Definition pushpop {A Γ1 Γ2 x σ} :
        ⊢ STerm σ -> SStoreT (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) A -> SStoreT Γ1 Γ2 A :=
        fun w t m δ =>
          SPureSpecM.bind (m δ.[x∷σ ↦ t])
            (fun w1 ω '(a,δ1) => SPureSpecM.pure (a, env.tail δ1)).
      Definition pushspops {A Γ1 Γ2 Δ} :
        ⊢ SStore Δ -> SStoreT (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) A -> SStoreT Γ1 Γ2 A :=
        fun w δΔ m δ =>
          SPureSpecM.bind (m (δ ►► δΔ))
            (fun w1 ω '(a,δ1) => SPureSpecM.pure (a, env.drop Δ δ1)).
      Definition get_local {Γ} : ⊢ SStoreT Γ Γ (SStore Γ) :=
        fun w δ => SPureSpecM.pure (δ, δ).
      Definition put_local {Γ1 Γ2} : ⊢ SStore Γ2 -> SStoreT Γ1 Γ2 Unit :=
        fun w δ' δ => SPureSpecM.pure (tt, δ').

      Definition eval_exp {Γ σ} (e : Exp Γ σ) : ⊢ SStoreT Γ Γ (STerm σ) :=
        fun w δ => SPureSpecM.pure (peval (seval_exp δ e), δ).
      Definition eval_exps {Γ} {σs : PCtx} (es : NamedEnv (Exp Γ) σs) :
        ⊢ SStoreT Γ Γ (SStore σs) :=
        fun w δ => SPureSpecM.pure (seval_exps δ es, δ).
      Definition assign {Γ} x {σ} {xIn : (x∷σ ∈ Γ)%katamaran} :
        ⊢ STerm σ -> SStoreT Γ Γ Unit :=
        fun w t δ => SPureSpecM.pure (tt, δ ⟪ x ↦ t ⟫).

      Definition demonic_pattern_match {N : Set} (n : N -> LVar) {Γ σ}
        (pat : Pattern (N:=N) σ) : ⊢ STerm σ -> SStoreT Γ Γ (SMatchResult pat) :=
        fun w t => liftM (SPureSpecM.demonic_pattern_match n pat t).

      #[local] Notation "⟨ θ ⟩ ' x <- ma ;; mb" :=
        (bind ma (fun _ θ x => mb))
          (at level 0, x pattern, ma at level 19, mb at level 200,
             right associativity).
      #[local] Notation "⟨ θ ⟩ x <- ma ;; mb" :=
        (bind ma (fun _ θ x => mb))
          (at level 0, x at next level, ma at level 19, mb at level 200,
             right associativity).

      Definition ExecCall := forall Δ τ, 𝑭 Δ τ -> ⊢ SStore Δ -> M (STerm τ).
      Definition ExecCallForeign := forall Δ τ, 𝑭𝑿 Δ τ -> ⊢ SStore Δ -> M (STerm τ).
      Definition ExecLemma := forall Δ, 𝑳 Δ -> ⊢ SStore Δ -> M Unit.
      Definition ExecFail := forall Γ τ (s : Val ty.string), ⊢ SStoreT Γ Γ (STerm τ).
      Definition Exec := forall Γ τ (s : Stm Γ τ), ⊢ SStoreT Γ Γ (STerm τ).

      Section ExecAux.

        Context {SPEC : Specification}.
        Variable exec_call_foreign : ExecCallForeign.
        Variable exec_lemma : ExecLemma.
        Variable exec_call : ExecCall.
        Variable exec_fail : ExecFail.

        Definition exec_aux : Exec :=
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
                ⟨ ω12 ⟩ _ <- assign (x := x) t;;
                pure (persist__term t ω12)
            | stm_call f es =>
                ⟨ ω01 ⟩ args <- eval_exps es (w:=w0) ;;
                liftM (exec_call f args)
            | stm_call_frame δ s =>
                ⟨ ω01 ⟩ δ1 <- get_local (w:=w0);;
                ⟨ ω12 ⟩ _  <- put_local (lift δ);;
                ⟨ ω23 ⟩ t  <- exec_aux s;;
                ⟨ ω34 ⟩ _  <- put_local (persist δ1 (ω12 ∘ ω23));;
                pure (persist__term t ω34)
            | stm_foreign f es =>
                ⟨ ω01 ⟩ args <- eval_exps es (w:=w0) ;;
                liftM (exec_call_foreign f args)
            | stm_lemmak l es k =>
                ⟨ ω01 ⟩ args <- eval_exps es (w:=w0) ;;
                ⟨ ω12 ⟩ _  <- liftM (exec_lemma l args) ;;
                exec_aux k
            | stm_seq s1 s2 =>
                ⟨ ω01 ⟩ _ <- exec_aux s1 ;;
                exec_aux s2
            | stm_assertk e _ k =>
                ⟨ ω01 ⟩ t <- eval_exp e (w:=w0) ;;
                ⟨ ω12 ⟩ _ <- liftM (assert_formula (smsg_string "assert")
                                     (if fail_rule_pre
                                      then formula_true
                                      else formula_relop bop.neq t (term_val ty.bool false))) ;;
                ⟨ ω23 ⟩ _ <- liftM (assume_formula (formula_bool (persist__term t ω12))) ;;
                exec_aux k
            | stm_fail _ s =>
                @exec_fail _ _ s w0
            | stm_read_register reg =>
                liftM (read_register reg)
            | stm_write_register reg e =>
                ⟨ ω01 ⟩ tnew <- eval_exp e (w:=w0) ;;
                liftM (write_register reg tnew)
            | stm_pattern_match s pat rhs =>
                ⟨ θ1 ⟩ v  <- exec_aux s ;;
                ⟨ θ2 ⟩ '(existT pc vs) <- demonic_pattern_match PVartoLVar pat v ;;
                pushspops vs (exec_aux (rhs pc))
            | stm_bind _ _ =>
                error
                  (fun δ =>
                     MkSMsg (dk_stm s δ "stm_bind not supported") nil)
            | stm_debugk k =>
                debug
                  (fun δ => MkSMsg (dk_stm k δ "stm_debugk") nil)
                  (exec_aux k)
            end.

      End ExecAux.

    End WithMonad.
    #[global] Arguments SStoreT M Γ1 Γ2 A : clear implicits.
    #[global] Arguments ExecCall M : clear implicits.
    #[global] Arguments ExecCallForeign M : clear implicits.
    #[global] Arguments ExecLemma M : clear implicits.
    #[global] Arguments ExecFail M : clear implicits.
    #[global] Arguments Exec M : clear implicits.
    #[global] Arguments exec_aux {M _ _ SPEC} _ _ _ _ [Γ τ] !s.

  End SStoreT.
  Export SStoreT (SStoreT, ExecCall, ExecCallForeign, ExecLemma, ExecFail, Exec).

  (* The executor, independent of the monad instance. *)
  Section WithSpec.

    Import SPureSpecM SPureSpecM.notations SHeapSpecM SStackM.

    Context {M} {pureM : SPureSpecM M} {heapM : SHeapSpecM M} {stackM : SStackM M}.
    Context {SPEC : Specification}.

    Definition exec_contract (exec : Exec M) {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) :
      ⊢ M Unit :=
      fun w =>
        match c with
        | MkSepContract _ _ lvars pats req result ens =>
            ⟨ θ1 ⟩ lenv  <- demonic_ctx id lvars ;;
            ⟨ θ2 ⟩ _     <- produce req lenv ;;
            let lenv2 := persist (A := Sub _) lenv θ2 in
            ⟨ θ3 ⟩ res   <- SStoreT.evalSStoreT (exec _ _ s _) (subst pats lenv2) ;;
            let lenv3 := persist (A := Sub _) lenv2 θ3 in
            consume ens (sub_snoc lenv3 (result∷τ) res)
        end.

    Definition sexec_call_error_no_fuel : ExecCall M :=
      fun Δ τ f w args =>
        error
          (smsg_string "out of fuel for inlining").

    Definition sexec_call_foreign : ExecCallForeign M :=
      fun Δ τ f w args =>
        with_frame (frame_foreign f args) (call_contract (CEnvEx f) args).

    Definition sexec_lemma : ExecLemma M :=
      fun Δ l w args =>
        with_frame (frame_lemma l args) (call_lemma (LEnv l) args).

    Definition sexec_fail : ExecFail M :=
      fun Γ τ s w =>
        SStoreT.liftM
          (if fail_rule_pre
           then block
           else error
                  (smsg_string "Encountered fail")).

    (* If a function does not have a contract, we continue executing the body of
       the called function. A parameter [inline_fuel] bounds the number of
       allowed levels before failing execution. *)
    Fixpoint sexec_call (inline_fuel : nat) : ExecCall M :=
      fun Δ τ f w args =>
        with_frame (frame_call f args)
          match CEnv f , inline_fuel with
          | Some c , _ => call_contract c args
          | None   , 0 => sexec_call_error_no_fuel f args
          | None   , S n =>
              SStoreT.evalSStoreT
                (SStoreT.exec_aux sexec_call_foreign sexec_lemma (sexec_call n)
                   sexec_fail (FunDef f) w)
                args
          end.

    Definition sexec (inline_fuel : nat) : Exec M :=
      SStoreT.exec_aux sexec_call_foreign sexec_lemma
        (sexec_call inline_fuel) sexec_fail.

  End WithSpec.
  #[global] Arguments sexec {M _ _ _ SPEC} _ [_ _] s : simpl never.

  (* The heap specification monad is the instance used for verification. *)
  #[global] Instance spurespecm_sheapspec : SPureSpecM SHeapSpec :=
    {| SPureSpecM.pure A := @SHeapSpec.pure A;
       SPureSpecM.bind A B := @SHeapSpec.bind A B;
       SPureSpecM.error A w msg :=
         SHeapSpec.error (fun h => debug_info (wco w) h msg);
       SPureSpecM.block A w := fun _ _ => SymProp.block;
       SPureSpecM.angelic x w σ := SHeapSpec.angelic x σ;
       SPureSpecM.demonic x w σ := SHeapSpec.demonic x σ;
       SPureSpecM.angelic_binary A := @SHeapSpec.angelic_binary A;
       SPureSpecM.demonic_binary A := @SHeapSpec.demonic_binary A;
       SPureSpecM.assert_formula w msg :=
         SHeapSpec.assert_formula (fun h => debug_info (wco w) h msg);
       SPureSpecM.assume_formula := @SHeapSpec.assume_formula;
       SPureSpecM.angelic_pattern_match N n σ pat w msg t Φ h :=
         SHeapSpec.lift_purespec
           (SPureSpec.angelic_pattern_match n pat (debug_info (wco w) h msg) t) Φ h;
       SPureSpecM.demonic_pattern_match N n σ pat w t :=
         SHeapSpec.lift_purespec (SPureSpec.demonic_pattern_match n pat t);
       SPureSpecM.debug A w msg :=
         SHeapSpec.debug (fun h => debug_info (wco w) h msg);
    |}.

  #[global] Instance sheapspecm_sheapspec : SHeapSpecM SHeapSpec :=
    {| SHeapSpecM.produce_chunk := @SHeapSpec.produce_chunk;
       SHeapSpecM.consume_chunk := @SHeapSpec.consume_chunk;
       SHeapSpecM.consume_chunk_angelic := @SHeapSpec.consume_chunk_angelic;
       SHeapSpecM.read_register τ reg w := SHeapSpec.read_register reg;
       SHeapSpecM.write_register τ reg := @SHeapSpec.write_register τ reg;
    |}.

  Definition vcgen {SPEC : Specification} (inline_fuel : nat) {Δ τ}
    (c : SepContract Δ τ) (s : Stm Δ τ) : ⊢ 𝕊 :=
    fun w =>
      SHeapSpec.run
        (exec_contract (M := SStackT SHeapSpec) (sexec inline_fuel) c s w nil).

  Module Symbolic.

    Import SymProp Postprocessing.

    Inductive VerificationCondition (p : 𝕊 ctx.nil) : Prop :=
    | vc (P : safe p env.nil).

    Definition ValidContractWithFuel {SPEC : Specification} {Δ τ} (fuel : nat)
      (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      VerificationCondition
        (postprocess (SPureSpec.replay (postprocess (vcgen fuel c body wnil)))).

    Definition ValidContract {SPEC : Specification} {Δ τ} (c : SepContract Δ τ)
      (body : Stm Δ τ) : Prop :=
      (* Use inline_fuel = 1 by default. *)
      ValidContractWithFuel 1 c body.

  End Symbolic.

End NewSymbolicExecOn.

Module MakeNewSymbolicExecutor
  (Import B    : Base)
  (Import SIG  : Signature B)
  (Import PROG : Program B)
  (Import PLOG : ProgramLogic B SIG PROG).

  Include NewSymbolicExecOn B SIG PROG PLOG.

End MakeNewSymbolicExecutor.
