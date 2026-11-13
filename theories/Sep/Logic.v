(******************************************************************************)
(* Copyright (c) 2020 Dominique Devriese, Georgy Lukyanov, Steven Keuchel     *)
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

From iris.bi Require Export interface derived_laws.
From Katamaran Require Import Context Environment Prelude.

Section WithBi.
  Context {L : bi}.

  Lemma forall_elim' {A : Type} (a : A) (Ψ : A → L) Φ :
    (Ψ a ⊢ Φ) → (bi_forall Ψ ⊢ Φ).
  Proof. intros. transitivity (Ψ a); auto. apply bi.forall_elim. Qed.

  Section Forall.

    Context {N T : Set} {D : T -> Set}.

    Fixpoint Forall {Δ : NCtx N T} : (NamedEnv D Δ -> L) -> L :=
      match Δ with
      | ctx.nil      => fun P => P nenv.nil
      | ctx.snoc Δ b => fun P => Forall (fun E => ∀ v, P (nenv.snoc E b v))
      end%I.

    Lemma Forall_forall (Δ : NCtx N T) (P : NamedEnv D Δ -> L) :
      (Forall P) ⊣⊢ (∀ E : NamedEnv D Δ, P E).
    Proof.
      induction Δ; cbn.
      - apply bi.entails_anti_sym.
        + apply bi.forall_intro; intros E. now env.destroy E.
        + apply bi.forall_elim.
      - rewrite IHΔ. clear IHΔ.
        apply bi.entails_anti_sym; apply bi.forall_intro.
        + intros E. destruct (nenv.view E) as [E v].
          now apply (forall_elim' E), (forall_elim' v).
        + intros E. apply bi.forall_intro. intros v.
          now apply (forall_elim' (nenv.snoc E _ v)).
    Qed.

  End Forall.

  Lemma wand_or_distr {P Q R : L} :
    ((P ∨ Q) -∗ R) ⊣⊢ ((P -∗ R) ∧ (Q -∗ R)).
  Proof.
    apply bi.entails_anti_sym.
    - apply bi.and_intro; apply bi.wand_mono; try easy.
      apply bi.or_intro_l. apply bi.or_intro_r.
    - apply bi.wand_intro_r.
      rewrite bi.sep_comm.
      apply bi.wand_elim_l'.
      apply bi.or_elim.
      + apply bi.wand_intro_r.
        rewrite bi.and_elim_l.
        apply bi.wand_elim_r.
      + apply bi.wand_intro_r.
        rewrite bi.and_elim_r.
        apply bi.wand_elim_r.
  Qed.

  Lemma entails_wand_iff {P Q : L} :
    (P ⊢ Q) ↔ (P -∗ Q).
  Proof. split. apply bi.entails_wand. apply bi.wand_entails. Qed.

  Lemma entails_apply {P Q : L} :
    (True ⊢ P) -> ((P → Q) ⊢ Q).
  Proof.
    intros H. transitivity ((P → Q) ∧ P)%I.
    - apply bi.and_intro. easy.
      transitivity (@bi_pure L True); auto.
      apply bi.True_intro.
    - apply bi.impl_elim_l.
  Qed.

End WithBi.
