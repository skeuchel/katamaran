(******************************************************************************)
(* Copyright (c) 2019 Steven Keuchel                                          *)
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

From Coq Require Import
     Program.Tactics.
From MicroSail Require Import
     SmallStep.Step
     Syntax.

Set Implicit Arguments.

Module Progress
       (Import termkit : TermKit)
       (Import progkit : ProgramKit termkit).
  Module SS := SmallStep termkit progkit.
  Import SS.

  Local Ltac progress_can_form :=
    match goal with
    | [ H: Final ?s |- _ ] => destruct s; cbn in H
    end; destruct_conjs; subst; try contradiction.

  Local Ltac progress_simpl :=
    repeat
      (cbn in *; destruct_conjs; subst;
       try progress_can_form;
       try match goal with
           | [ |- True \/ _] => left; constructor
           | [ |- False \/ _] => right
           | [ |- forall _, _ ] => intro
           | [ H : True |- _ ] => clear H
           | [ H : _ \/ _ |- _ ] => destruct H
           end).

  Local Ltac progress_tac :=
    progress_simpl;
    solve
      [ repeat eexists; constructor; eauto
      ].

  Lemma progress {σ} (s : Stm σ) :
    Final s \/ exists s', s ---> s'.
  Proof. induction s; intros; try progress_tac. Qed.

End Progress.
