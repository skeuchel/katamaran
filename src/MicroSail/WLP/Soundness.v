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
     Program.Equality
     Program.Tactics.

From MicroSail Require Import
     SmallStep.Inversion
     SmallStep.Step
     Syntax
     WLP.Spec.

Set Implicit Arguments.

Import CtxNotations.

Module Soundness
       (Import termkit : TermKit)
       (Import progkit : ProgramKit termkit)
       (Import contkit : ContractKit termkit progkit).
  Module WLP := WLP termkit progkit contkit.
  Import WLP.
  Module SSI := Inversion termkit progkit.
  Import SSI.
  Import SS.

  Ltac wlp_sound_steps_inversion :=
    repeat
      match goal with
      | [ H: stm_app _ _ ---> _ |- _ ] =>               dependent destruction H
      | [ H: stm_app _ _ --->* _ |- _ ] =>              dependent destruction H
      | [ H: stm_assert _ _ ---> _ |- _ ] =>            dependent destruction H
      | [ H: stm_assert _ _ --->* _ |- _ ] =>           dependent destruction H
      | [ H: stm_exit _ _ ---> _ |- _ ] =>              dependent destruction H
      | [ H: stm_exit _ _ --->* _ |- _ ] =>             dependent destruction H
      | [ H: stm_if _ _ _ ---> _ |- _ ] =>              dependent destruction H
      | [ H: stm_if _ _ _ --->* _ |- _ ] =>             dependent destruction H
      | [ H: stm_lit _ ---> _ |- _ ] =>               dependent destruction H
      | [ H: stm_lit _ --->* _ |- _ ] =>              dependent destruction H

      | [ H: stm_bind (stm_lit _) _ ---> _ |- _ ] =>     dependent destruction H

      | [ H: stm_bind _ _ --->* ?s1 , HF: Final ?s1 |- _ ] =>     apply (steps_inversion_bind HF) in H; destruct_conjs
      | [ H: IsLit _ _ |- _ ] => apply IsLit_inversion in H; destruct_conjs; subst
      end; cbn in *.

  Ltac wlp_sound_inst :=
    match goal with
    | [ IH: forall _, ?s --->* _ -> _,
        HS: ?s --->* ?t, HF: Final ?t |- _ ] =>
      specialize (IH _ HS HF); clear HS HF
    | [ IH: forall _ _, _ --->* _ -> _,
        HS: _ --->* ?t, HF: Final ?t |- _ ] =>
      specialize (IH _ _ HS HF); clear HS HF
    | [ IH: forall POST, WLP ?s POST -> _, WP: WLP ?s _ |- _ ] =>
      specialize (IH _ WP); clear WP
    end.

  Ltac wlp_sound_simpl :=
    repeat
      (cbn in *; destruct_conjs; subst;
       try match goal with
           | [ H: True |- _ ] => clear H
           | [ H: False |- _ ] => destruct H
           (* | [ _: context[match eval ?e ?δ with _ => _ end] |- _ ] => *)
           (*   destruct (eval e δ) *)
           end).

  Ltac wlp_sound_solve :=
    repeat
      (wlp_sound_steps_inversion;
       wlp_sound_simpl;
       try wlp_sound_inst); auto.

  Definition ValidContract {τ : Set} (P : Pred τ) (s : Stm τ) : Prop :=
    forall (s' : Stm τ),
      s --->* s' ->
      Final s' ->
      IsLit s' P.

  Definition ValidContractEnv (cenv : ContractEnv) : Type :=
    forall σs σ (f : 𝑭 σs σ),
      match cenv σs σ f with
      | ContractWLP _ _ pre post =>
        forall (δ : LocalStore σs) (s' : Stm σ),
          apply (Pi f) δ --->* s' ->
          Final s' ->
          apply pre δ ->
          IsLit s' (apply post δ)
      | _ => False
      end.

  Lemma WLP_sound (validCEnv : ValidContractEnv CEnv) {σ} (s : Stm σ) :
    forall (s' : Stm σ), s --->* s' -> Final s' ->
      forall (POST : Pred σ), WLP s POST -> IsLit s' POST.
  Proof.
    induction s; cbn; intros.
    - wlp_sound_solve.
    - pose proof (validCEnv _ _ f).
      destruct (CEnv f); wlp_sound_solve.
      intuition.
      wlp_sound_solve.
    - destruct b.
      + wlp_sound_solve.
      + wlp_sound_solve.
    - destruct b.
      + wlp_sound_solve.
      + wlp_sound_solve.
    - wlp_sound_solve.
    - wlp_sound_solve.
      rewrite blast_sound in H3.
      wlp_sound_solve.
  Qed.

End Soundness.
