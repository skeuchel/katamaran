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
  Syntax.Chunks
  Syntax.Predicates.

#[local] Set Implicit Arguments.

Module Type RefinementMonadClassesOn
  (Import B : Base)
  (Import PK : PredicateKit B)
  (Import WR : WorldsMixin B PK)
  (Import SP : SymPropOn B PK WR)
  (Import UL : UnifLogicOn B PK WR)
  (Import SHC : ShallowMonadClassesOn B PK WR)
  (Import SYC : SymbolicMonadClassesOn B PK WR SP).

  Import ModalNotations.
  Import logicalrelation logicalrelation.notations.

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
          refine_debug {AT A} {RA : Rel AT A} {w} msg (cm : M A) (sm : MT AT w) ::
            RelatedFrom (RM RA) cm w (SHeapSpecM.debug msg sm) (ℛ⟦RM RA⟧ cm sm);
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

  End RHeapSpecM.
  Export RHeapSpecM (RHeapSpecM).
  Export (hints) RHeapSpecM.

End RefinementMonadClassesOn.
