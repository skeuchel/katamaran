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
     Program.Equality.
From MicroSail Require Import
     SmallStep.Step
     Syntax.

Set Implicit Arguments.

Import CtxNotations.

Module Inversion
       (Import termkit : TermKit)
       (Import progkit : ProgramKit termkit).
  Module SS := SmallStep termkit progkit.
  Import SS.

  Local Ltac steps_inversion_simpl :=
    repeat
      (try match goal with
           | [ H: exists t, _ |- _ ] => destruct H
           | [ H: _ /\ _ |- _ ] => destruct H
           | [ H: existT _ _ _ = existT _ _ _ |- _ ] => dependent destruction H
           | [ H : False |- _ ] => destruct H
           end;
       cbn in *).

  Local Ltac extend p :=
    let P := type of p in
    match goal with
    | [ _ : P |- _ ] => fail 1
    | _ => pose proof p
    end.

  Local Ltac steps_inversion_inster :=
    repeat
      (try match goal with
           | [ H : forall _, _ = _ -> _ |- _ ]
             => specialize (H _ eq_refl)
           | [ H : forall _ _, _ = _ -> _ |- _ ]
             => specialize (H _ _ eq_refl)
           | [ H : forall _ _ _, _ = _ -> _ |- _ ]
             => specialize (H _ _ _ eq_refl)
           | [ H : Final ?s -> _, H' : Final ?s |- _ ]
             => specialize (H H')
           | [ H1 : ?s1 ---> ?s2,
               H2 : ?s2 --->* ?s3 |- _ ]
             => extend (step_trans H1 H2)
           end;
       steps_inversion_simpl).

  Local Ltac steps_inversion_solve :=
    repeat
      (match goal with
       | [ |- exists t, _ ] => eexists
       | [ |- _ /\ _ ] => constructor
       | [ |- True ] => constructor
       | [ |- stm_lit _ --->* _ ] => constructor 1
       | [ |- stm_exit _ _ --->* _ ] => constructor 1
       end; cbn); try eassumption.

  Local Ltac steps_inversion_induction :=
    let step := fresh in
    induction 1 as [|? ? ? ? ? ? step]; intros; subst;
      [ cbn in *; contradiction
      | inversion step; steps_inversion_inster; steps_inversion_solve
      ].

  Lemma steps_inversion_bind {τ σ} `{Blastable τ}
    (s1 : Stm τ) (k : τ -> Stm σ) (t : Stm σ) (final : Final t)
    (steps : stm_bind s1 k --->* t) :
    exists s1',
      s1 --->* s1' /\ Final s1' /\
      exists (s0 : Stm σ),
        (stm_bind s1' k ---> s0) /\ (s0 --->* t).
  Proof.
    remember (stm_bind s1 k) as s. revert steps s1 k Heqs.
    steps_inversion_induction.
  Qed.

End Inversion.
