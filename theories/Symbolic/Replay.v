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
  Symbolic.MonadClasses
  Symbolic.Monads
  Symbolic.Propositions
  Symbolic.UnifLogic
  Symbolic.Solver
  Symbolic.Worlds
  Syntax.Assertions
  Syntax.Chunks
  Syntax.Predicates.

Import ctx.notations.
Import env.notations.

#[local] Set Implicit Arguments.
#[local] Open Scope string_scope.

(* Replaying a symbolic proposition as a symbolic computation, generic over
   the monad classes. *)
Module Type SymbolicReplayOn (Import B : Base) (Import P : PredicateKit B)
  (Import W : WorldsMixin B P)
  (Import SK : SolverKit B P W)
  (Import SP : SymPropOn B P W)
  (Import UL : UnifLogicOn B P W)
  (Import LSP : LogSymPropOn B P W SP UL)
  (Import GS : GenericSolverOn B P W SK SP UL LSP)
  (Import A : AssertionsOn B P W)
  (Import SC : SymbolicMonadClassesOn B P W SP A)
  (Import SYMB : SymbolicMonadsOn B P W SK SP UL LSP GS A SC).

  Import ModalNotations.
  #[local] Open Scope modal.

  Module SReplay.

    Section WithMonad.

      Import SHeapSpecM.notations.

      Context {M} {sm : SHeapSpecM M}.

      (* Messages do not depend on the heap. *)
      Definition replay_aux :
        forall {Σ} (s : 𝕊 Σ), ⊢ Sub Σ -> M Unit :=
        fix replay {Σ} s {w0} δ {struct s} :=
          match s with
          | SymProp.angelic_binary o1 o2 =>
              SHeapSpecM.angelic_binary (replay o1 δ) (replay o2 δ)
          | SymProp.demonic_binary o1 o2 =>
              SHeapSpecM.demonic_binary (replay o1 δ) (replay o2 δ)
          | SymProp.block => SHeapSpecM.block
          | SymProp.error msg =>
              SHeapSpecM.error (fun _ => subst msg δ)
          | SymProp.assertk fml msg k =>
              ⟨ θ ⟩ _ <- SHeapSpecM.assert_formula (fun _ => subst msg δ) (subst fml δ) ;;
              replay k (persist δ θ)
          | SymProp.assumek fml k =>
              ⟨ θ ⟩ _ <- SHeapSpecM.assume_formula (subst fml δ) ;;
              replay k (persist δ θ)
          | SymProp.angelicv b k =>
              ⟨ θ ⟩ t <- SHeapSpecM.angelic (Some (name b)) (type b) ;;
              replay k (env.snoc (persist δ θ) b t)
          | SymProp.demonicv b k =>
              ⟨ θ ⟩ t <- SHeapSpecM.demonic (Some (name b)) (type b) ;;
              replay k (env.snoc (persist δ θ) b t)
          | SymProp.assert_vareq x t msg k =>
              let ζ    := sub_shift (b:=x∷_) _ in
              let msg  := subst msg ζ in
              let fml  := formula_relop bop.eq (subst t ζ) (term_var x) in
              ⟨ θ ⟩ _ <- SHeapSpecM.assert_formula (fun _ => subst msg δ) (subst fml δ) ;;
              replay k (env.remove (x∷_) δ⟨θ⟩ _)
          | SymProp.assume_vareq x t k =>
              let ζ    := sub_shift (b:=x∷_) _ in
              let fml  := formula_relop bop.eq (subst t ζ) (term_var x) in
              ⟨ θ ⟩ _ <- SHeapSpecM.assume_formula (subst fml δ) ;;
              replay k (env.remove (x∷_) δ⟨θ⟩ _)
          | SymProp.pattern_match s pat rhs =>
              (* FIXME *)
              SHeapSpecM.error
                (fun _ =>
                   amsg.mk
                     {| debug_string_pathcondition := wco w0;
                        debug_string_message       :=
                          "NOT IMPLEMENTED: replay_aux.pattern_match";
                     |})
          | SymProp.pattern_match_var x pat rhs =>
              (* FIXME *)
              SHeapSpecM.error
                (fun _ =>
                   amsg.mk
                     {| debug_string_pathcondition := wco w0;
                        debug_string_message       :=
                          "NOT IMPLEMENTED: replay_aux.pattern_match_var";
                     |})
          | SymProp.debug msg k =>
              SHeapSpecM.debug (fun _ => subst msg δ) (replay k δ)
          end.

    End WithMonad.

  End SReplay.

End SymbolicReplayOn.
