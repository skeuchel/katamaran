(******************************************************************************)
(* Copyright (c) 2021 Steven Keuchel                                          *)
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

From Equations Require Import
     Equations.
From Katamaran Require Import
     Context
     Prelude
     Base.

Local Set Implicit Arguments.

Module Type RegStoreKit (Import GLOBAL : GlobalState).

  (* We choose to make [RegStore] a parameter so the users of the module would be able to
     instantiate it with their own data structure and [read_register]/[write_register]
     functions *)
  Parameter RegStore : Type.
  Parameter read_register : forall (γ : RegStore) {σ} (r : 𝑹𝑬𝑮 σ), Val σ.
  Parameter write_register : forall (γ : RegStore) {σ} (r : 𝑹𝑬𝑮 σ) (v : Val σ), RegStore.

  Parameter read_write : forall (γ : RegStore) σ (r : 𝑹𝑬𝑮 σ) (v : Val σ),
            read_register (write_register γ r v) r = v.

  Parameter read_write_distinct :
    forall (γ : RegStore) {σ τ} (r__σ : 𝑹𝑬𝑮 σ) (r__τ : 𝑹𝑬𝑮 τ) (v__σ : Val σ),
      existT _ r__σ <> existT _ r__τ ->
      read_register (write_register γ r__σ v__σ) r__τ = read_register γ r__τ.

End RegStoreKit.

Module DefaultRegStoreKit (Import GLOBAL : GlobalState) <: RegStoreKit GLOBAL.

  Definition RegStore : Type := forall σ, 𝑹𝑬𝑮 σ -> Val σ.

  Definition write_register (γ : RegStore) {σ} (r : 𝑹𝑬𝑮 σ)
    (v : Val σ) : RegStore :=
    fun τ r' =>
      match eq_dec_het r r' with
      | left eqt => eq_rect σ Val v τ (f_equal projT1 eqt)
      | right _ => γ τ r'
      end.

  Definition read_register (γ : RegStore) {σ} (r : 𝑹𝑬𝑮 σ) :
    Val σ := γ _ r.

  Lemma read_write γ {σ} (r : 𝑹𝑬𝑮 σ) (v : Val σ) :
    read_register (write_register γ r v) r = v.
  Proof.
    unfold read_register, write_register.
    unfold eq_dec_het. now rewrite EqDec.eq_dec_refl.
  Qed.

  Lemma read_write_distinct γ {σ τ} (r : 𝑹𝑬𝑮 σ) (k : 𝑹𝑬𝑮 τ) (v : Val σ):
    existT _ r <> existT _ k ->
    read_register (write_register γ r v) k = read_register γ k.
  Proof.
    intros ?; unfold read_register, write_register.
    destruct (eq_dec_het r k); congruence.
  Qed.

  Lemma write_read γ {σ} (r : 𝑹𝑬𝑮 σ) :
    forall τ (r' : 𝑹𝑬𝑮 τ),
      write_register γ r (read_register γ r) r' = γ τ r'.
  Proof.
    intros ? ?.
    unfold write_register, read_register.
    destruct (eq_dec_het r r') as [e|].
    - now dependent elimination e.
    - reflexivity.
  Qed.

  Lemma write_write γ {σ} (r : 𝑹𝑬𝑮 σ) (v1 v2 : Val σ) :
    forall τ (r' : 𝑹𝑬𝑮 τ),
      write_register (write_register γ r v1) r v2 r' =
      write_register γ r v2 r'.
  Proof.
    intros ? ?.
    unfold write_register.
    destruct (eq_dec_het r r'); reflexivity.
  Qed.

End DefaultRegStoreKit.
