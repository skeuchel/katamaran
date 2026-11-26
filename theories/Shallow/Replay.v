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
  Shallow.Monads
  Syntax.Assertions
  Syntax.Chunks
  Syntax.Predicates
  Symbolic.Propositions
  Symbolic.Worlds.

Import ctx.notations env.notations.

#[local] Set Implicit Arguments.

(* Replaying a symbolic proposition as a shallow computation, generic over the
   monad classes. *)
Module Type ShallowReplayOn (Import B : Base) (Import P : PredicateKit B)
  (Import W : WorldsMixin B P) (Import SP : SymPropOn B P W)
  (Import AS : AssertionsOn B P W) (Import SHC : ShallowMonadClassesOn B P W AS)
  (Import SHAL : ShallowMonadsOn B P W SP AS SHC).

  Module CReplay.

    Section WithMonad.

      Context {M} {cm : CHeapSpecM M}.

      Definition replay_aux :
        forall {Σ} (s : 𝕊 Σ) (ι : Valuation Σ), M unit :=
        fix replay {Σ} s ι :=
          match s with
          | SymProp.angelic_binary o1 o2 =>
              CHeapSpecM.angelic_binary (replay o1 ι) (replay o2 ι)
          | SymProp.demonic_binary o1 o2 =>
              CHeapSpecM.demonic_binary (replay o1 ι) (replay o2 ι)
          | SymProp.block =>
              CHeapSpecM.block
          | SymProp.error msg =>
              CHeapSpecM.error
          | SymProp.assertk fml msg k =>
              CHeapSpecM.bind (CHeapSpecM.assert_formula (instprop fml ι))
                (fun _ => replay k ι)
          | SymProp.assumek fml k =>
              CHeapSpecM.bind (CHeapSpecM.assume_formula (instprop fml ι))
                (fun _ => replay k ι)
          | SymProp.angelicv b k =>
              CHeapSpecM.bind (CHeapSpecM.angelic _)
                (fun v => replay k (env.snoc ι b v))
          | SymProp.demonicv b k =>
              CHeapSpecM.bind (CHeapSpecM.demonic _)
                (fun v => replay k (env.snoc ι b v))
          | @SymProp.assert_vareq _ x σ xIn t msg k =>
              let ι' := env.remove (x ∷ σ) ι xIn in
              let x' := ι.[? x∷σ] in
              let t' := inst t ι' in
              CHeapSpecM.bind (CHeapSpecM.assert_formula (t' = x'))
                (fun _ => replay k ι')
          | @SymProp.assume_vareq _ x σ xIn t k =>
              let ι' := env.remove (x ∷ σ) ι xIn in
              let x' := ι.[? x∷σ] in
              let t' := inst t ι' in
              CHeapSpecM.bind (CHeapSpecM.assume_formula (t' = x'))
                (fun _ => replay k ι')
          | SymProp.pattern_match s pat rhs =>
              CHeapSpecM.error
          | SymProp.pattern_match_var x pat rhs =>
              CHeapSpecM.error
          | SymProp.debug b k =>
              CHeapSpecM.debug (replay k ι)
          end.

    End WithMonad.

  End CReplay.

End ShallowReplayOn.
