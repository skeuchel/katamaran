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
  Refinement.Monads
  Shallow.Monads
  Shallow.Replay
  Signature
  Symbolic.Monads
  Symbolic.Replay
  Symbolic.Solver.

Import ctx.notations.
Import env.notations.

Set Implicit Arguments.

(* The shallow and symbolic replay are related, for any pair of monads that
   are related by [RHeapSpecM]. *)
Module Type RefinementReplayOn
  (Import B : Base)
  (Import SIG : Signature B)
  (Import GS : GenericSolverOn B SIG SIG SIG SIG SIG SIG)
  (Import SHAL : ShallowMonadsOn B SIG)
  (Import SHR : ShallowReplayOn B SIG SHAL)
  (Import SYMB : SymbolicMonadsOn B SIG GS)
  (Import SYR : SymbolicReplayOn B SIG GS SYMB)
  (Import RMON : RefinementMonadsOn B SIG GS SHAL SYMB).

  Import ModalNotations.
  Import SymProp.
  Import logicalrelation logicalrelation.notations.
  Import LogicalSoundness.
  Import proofmode.
  Import iris.bi.interface iris.proofmode.proofmode.
  Import (hints) PureSpec HeapSpec.

  Module RReplay.

    Section WithRM.

      Context {MT : TYPE -> TYPE} {M : Type -> Type}
        {smT : SHeapSpecM MT} {cm : CHeapSpecM M}
        {RM : forall {AT A} (R : Rel AT A), Rel (MT AT) (M A)}
        {rm : RHeapSpecM (@RM)}.

      Lemma refine_replay_aux {Σ} (s : 𝕊 Σ) {w} :
        Related (RNEnv LVar Σ -> RM RUnit)
          (CReplay.replay_aux s) w (SReplay.replay_aux (w := w) s).
      Proof.
        revert w; induction s; intros w; cbn -[RSat]; solve_related.
        all: rewrite <-inst_sub_shift, <-inst_subst; solve_related.
      Qed.

    End WithRM.

  End RReplay.

End RefinementReplayOn.
