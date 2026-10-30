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

From Katamaran Require Import
  Prelude
  Base
  Shallow.MonadClasses
  Symbolic.MonadClasses
  Symbolic.Propositions
  Symbolic.UnifLogic
  Symbolic.Worlds
  Syntax.Assertions
  Syntax.Chunks
  Syntax.Predicates.

#[local] Set Implicit Arguments.

Module Type RefinementMonadClassesOn
  (Import GLOBAL : GlobalState)
  (Import PK : PredicateKit GLOBAL)
  (Import WR : WorldsMixin GLOBAL PK)
  (Import SP : SymPropOn GLOBAL PK WR)
  (Import UL : UnifLogicOn GLOBAL PK WR)
  (Import AS : AssertionsOn GLOBAL PK WR)
  (Import SHC : ShallowMonadClassesOn GLOBAL PK WR AS)
  (Import SYC : SymbolicMonadClassesOn GLOBAL PK WR SP AS).

  Import ModalNotations.
  Import logicalrelation logicalrelation.notations proofmode.
  Import iris.bi.interface iris.proofmode.proofmode.

  (* Interface of logical relations between a symbolic and a shallow monad:
     each operation of [SHeapSpecM] refines that of [CHeapSpecM]. *)
  Module RHeapSpecM.

    Section WithMonads.

      Context {MT : TYPE -> TYPE} {M : Type -> Type}
        {smT : SHeapSpecM MT} {cm : CHeapSpecM M}
        {RM : forall {AT A} (R : Rel AT A), Rel (MT AT) (M A)}.

      (* The methods are [Related] instances, so the solver uses them for any
         monad with an instance of this class. *)
      Class RHeapSpecM : Type :=
        { refine_pure {AT A} {RA : Rel AT A} {w} ::
            Related (RA -> RM RA) CHeapSpecM.pure w (SHeapSpecM.pure (w := w));
          refine_bind {AT A BT B} {RA : Rel AT A} {RB : Rel BT B} {w} ::
            Related (RM RA -> □ᵣ(RA -> RM RB) -> RM RB)
              CHeapSpecM.bind w (SHeapSpecM.bind (w := w));
          refine_error {AT A} {RA : Rel AT A} (cm : M A) {w} ::
            Related (RMsg _ (RM RA)) cm w (SHeapSpecM.error (w := w));
          refine_block {AT A} {RA : Rel AT A} {w} ::
            Related (RM RA) CHeapSpecM.block w (SHeapSpecM.block (w := w));
          refine_angelic (x : option LVar) σ {w} ::
            Related (RM (RVal σ))
              (CHeapSpecM.angelic σ) w (SHeapSpecM.angelic x σ (w := w));
          refine_demonic (x : option LVar) σ {w} ::
            Related (RM (RVal σ))
              (CHeapSpecM.demonic σ) w (SHeapSpecM.demonic x σ (w := w));
          refine_angelic_binary {AT A} {RA : Rel AT A} {w} ::
            Related (RM RA -> RM RA -> RM RA)
              CHeapSpecM.angelic_binary w (SHeapSpecM.angelic_binary (w := w));
          refine_demonic_binary {AT A} {RA : Rel AT A} {w} ::
            Related (RM RA -> RM RA -> RM RA)
              CHeapSpecM.demonic_binary w (SHeapSpecM.demonic_binary (w := w));
          refine_assert_formula {w} ::
            Related (RMsg _ (RFormula -> RM RUnit))
              CHeapSpecM.assert_formula w (SHeapSpecM.assert_formula (w := w));
          refine_assume_formula {w} ::
            Related (RFormula -> RM RUnit)
              CHeapSpecM.assume_formula w (SHeapSpecM.assume_formula (w := w));
          refine_angelic_pattern_match {N : Set} (n : N -> LVar)
            {σ} (pat : Pattern (N:=N) σ) {w} ::
            Related (RMsg _ (RVal σ -> RM (RMatchResult pat)))
              (CHeapSpecM.angelic_pattern_match pat) w
              (SHeapSpecM.angelic_pattern_match n pat (w := w));
          refine_demonic_pattern_match {N : Set} (n : N -> LVar)
            {σ} (pat : Pattern (N:=N) σ) {w} ::
            Related (RVal σ -> RM (RMatchResult pat))
              (CHeapSpecM.demonic_pattern_match pat) w
              (SHeapSpecM.demonic_pattern_match n pat (w := w));
          refine_debug {AT A} {RA : Rel AT A} {w} ::
            Related (RMsg _ (RM RA -> RM RA))
              CHeapSpecM.debug w (SHeapSpecM.debug (w := w));
          refine_produce_chunk {w} ::
            Related (RChunk -> RM RUnit)
              CHeapSpecM.produce_chunk w (SHeapSpecM.produce_chunk (w := w));
          refine_consume_chunk {w} ::
            Related (RChunk -> RM RUnit)
              CHeapSpecM.consume_chunk w (SHeapSpecM.consume_chunk (w := w));
          refine_consume_chunk_angelic {w} ::
            Related (RChunk -> RM RUnit)
              CHeapSpecM.consume_chunk w (SHeapSpecM.consume_chunk_angelic (w := w));
          refine_read_register {τ} (reg : 𝑹𝑬𝑮 τ) {w} ::
            Related (RM (RVal τ))
              (CHeapSpecM.read_register reg) w (SHeapSpecM.read_register reg (w := w));
          refine_write_register {τ} (reg : 𝑹𝑬𝑮 τ) {w} ::
            Related (RVal τ -> RM (RVal τ))
              (CHeapSpecM.write_register reg) w (SHeapSpecM.write_register reg (w := w));
        }.

    End WithMonads.
    #[global] Arguments RHeapSpecM {MT M smT cm} RM.

    Section WithRM.

    Import SHeapSpecM.notations.

    Context {MT : TYPE -> TYPE} {M : Type -> Type}
      {smT : SHeapSpecM MT} {cmM : CHeapSpecM M}
      {RM : forall {AT A} (R : Rel AT A), Rel (MT AT) (M A)}
      {rm : RHeapSpecM (@RM)}.

    #[export] Instance refine_angelic_ctx {N : Set} {n : N -> LVar} Δ {w} :
      Related (RM (RNEnv N Δ))
        (CHeapSpecM.angelic_ctx Δ) w (SHeapSpecM.angelic_ctx (w := w) n Δ).
    Proof.
      induction Δ; cbn [SHeapSpecM.angelic_ctx CHeapSpecM.angelic_ctx]; solve_related.
    Qed.

    #[export] Instance refine_demonic_ctx {N : Set} {n : N -> LVar} Δ {w} :
      Related (RM (RNEnv N Δ))
        (CHeapSpecM.demonic_ctx Δ) w (SHeapSpecM.demonic_ctx (w := w) n Δ).
    Proof.
      induction Δ; cbn [SHeapSpecM.demonic_ctx CHeapSpecM.demonic_ctx]; solve_related.
    Qed.

    Lemma refine_assert_eq_nenv {N : Set} {w} :
      ⊢ ℛ⟦∀ᵣ Δ : NCtx N Ty, RMsg _ (RNEnv _ Δ -> RNEnv _ Δ -> RM RUnit)⟧
        CHeapSpecM.assert_eq_nenv (SHeapSpecM.assert_eq_nenv (w := w)).
    Proof.
      iIntros (Δ msg E1 Es1) "HE1 %E2 %Es2 HE2".
      iInduction Es1 as [|Es1] "IHEs1";
        env.destroy Es2; env.destroy E1; env.destroy E2; cbn -[RSat].
      - now iApply (refine_pure (RA := RUnit)).
      - iDestruct (repₚ_invert_snoc with "HE1") as "(HE1 & Hv0db)".
        iDestruct (repₚ_invert_snoc with "HE2") as "(HE2 & Hv1v)".
        iSpecialize ("IHEs1" with "HE1 HE2").
        iApply (refine_bind (RA := RUnit) (RB := RUnit) with "IHEs1"); solve_related.
    Qed.

    #[export] Instance refine_compat_assert_eq_nenv {N : Set} {w} {Δ : NCtx N Ty} :
      Related (RMsg _ (RNEnv _ Δ -> RNEnv _ Δ -> RM RUnit))
        (CHeapSpecM.assert_eq_nenv (Δ := Δ)) w (@SHeapSpecM.assert_eq_nenv _ _ N w Δ).
    Proof. iIntros. iApply refine_assert_eq_nenv. Qed.

    #[export] Instance refine_produce {Σ} (asn : Assertion Σ) :
      ∀ w, Related (RInst (Sub Σ) (Valuation Σ) -> RM RUnit)
             (CHeapSpecM.produce asn) w (SHeapSpecM.produce (w := w) asn).
    Proof.
      induction asn; cbn - [RSat]; intros w; solve_related.
    Qed.

    #[export] Instance refine_consume {Σ} (asn : Assertion Σ) :
      ∀ w, Related (RInst (Sub Σ) (Valuation Σ) -> RM RUnit)
             (CHeapSpecM.consume asn) w (SHeapSpecM.consume asn (w := w)).
    Proof.
      induction asn; cbn - [RSat]; intros w; solve_related.
    Qed.

    #[export] Instance refine_call_contract {Δ τ} (c : SepContract Δ τ) {w} :
      Related (RInst (SStore Δ) (CStore Δ) -> RM (RVal τ))
        (CHeapSpecM.call_contract c) w (SHeapSpecM.call_contract c (w := w)).
    Proof. unfold CHeapSpecM.call_contract, SHeapSpecM.call_contract; solve_related. Qed.

    #[export] Instance refine_call_lemma {Δ} (lem : Lemma Δ) w :
      Related (RInst (SStore Δ) (CStore Δ) -> RM RUnit)
        (CHeapSpecM.call_lemma lem) w (SHeapSpecM.call_lemma lem (w := w)).
    Proof. unfold CHeapSpecM.call_lemma, SHeapSpecM.call_lemma; solve_related. Qed.

    End WithRM.

  End RHeapSpecM.
  Export RHeapSpecM (RHeapSpecM).
  Export (hints) RHeapSpecM.

End RefinementMonadClassesOn.
