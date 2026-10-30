(******************************************************************************)
(* Copyright (c) 2020 Dominique Devriese, Sander Huyghebaert, Steven Keuchel  *)
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
     Classes.Morphisms
     Strings.String
     ZArith.BinInt.
From Katamaran Require Import
     Signature
     Sep.Hoare
     Sep.Logic
     Prelude
     Program
     Staging.NewShallow.Executor.

Set Implicit Arguments.

Import ctx.notations.
Import env.notations.

Module Type Soundness
  (Import GLOBAL : GlobalState)
  (Import SIG    : Signature GLOBAL)
  (Import PROG   : Program GLOBAL)
  (Import PLOG   : ProgramLogic GLOBAL SIG PROG)
  (Import EXEC   : NewShallowExecOn GLOBAL SIG PROG PLOG).

  Import ProgLog.

  Section Soundness.

    Context {L} {biA : BiAffine L} {PI : PredicateDef L}.

    Lemma call_contract_sound {Δ τ}
      (c : SepContract Δ τ) (δΔ : CStore Δ) (POST : Val τ -> L) :
      CTriple (CPureSpec.call_contract c δΔ POST) c δΔ POST.
    Proof.
      unfold CTriple. destruct c as [Σe δe req result ens].
      now rewrite CPureSpec.equiv_call_contract.
    Qed.

    Lemma call_lemma_sound {Δ}
      (lem : Lemma Δ) (δΔ : CStore Δ) (POST : unit -> L) :
      LTriple δΔ (CPureSpec.call_lemma lem δΔ POST) (POST tt) lem.
    Proof.
      destruct lem as [Σe δe req ens]. constructor.
      now rewrite CPureSpec.equiv_call_lemma.
    Qed.

    Import CStoreSpec.

    Context {SPEC : Specification}.

    Definition SoundExecCall (exec_call : ExecCall (L := L)) : Prop :=
      forall Γ τ Δ (f : 𝑭 Δ τ) (es : NamedEnv (Exp Γ) Δ)
        (POST : Val τ -> CStore Γ -> L) (δ : CStore Γ),
        ⦃ exec_call _ _ f (evals es δ) (fun v => POST v δ) ⦄
          stm_call f es ; δ
        ⦃ POST ⦄.

    Definition SoundExecCallForeign (exec_call_foreign : ExecCallForeign (L := L)) : Prop :=
      forall Δ τ (f : 𝑭𝑿 Δ τ) (args : CStore Δ) (POST : Val τ -> L),
        CTriple (exec_call_foreign _ _ f args POST) (CEnvEx f) args POST.

    Definition SoundExecLemma (exec_lemma : ExecLemma (L := L)) : Prop :=
      forall Δ (l : 𝑳 Δ) (args : CStore Δ) (POST : unit -> L),
        LTriple args (exec_lemma _ l args POST) (POST tt) (LEnv l).

    Definition SoundExecFail (exec_fail : ExecFail (L := L)) : Prop :=
      forall Γ τ (s : Val ty.string) (POST : Val τ -> CStore Γ -> L) (δ : CStore Γ),
        ⦃ exec_fail _ _ s POST δ ⦄ stm_fail τ s ; δ ⦃ POST ⦄.

    Definition SoundExec (exec : Exec (L := L)) : Prop :=
      forall Γ σ (s : Stm Γ σ) (POST : Val σ -> CStore Γ -> L) (δ1 : CStore Γ),
        ⦃ exec _ _ s POST δ1 ⦄ s ; δ1 ⦃ POST ⦄.

    Section ExecAux.

      Variable exec_call_foreign : ExecCallForeign (L := L).
      Variable exec_lemma : ExecLemma (L := L).
      Variable exec_call : ExecCall (L := L).
      Variable exec_fail : ExecFail (L := L).

      Hypothesis sound_exec_call_foreign : SoundExecCallForeign exec_call_foreign.
      Hypothesis sound_exec_lemma : SoundExecLemma exec_lemma.
      Hypothesis sound_exec_call : SoundExecCall exec_call.
      Hypothesis sound_exec_fail : SoundExecFail exec_fail.

      Lemma exec_aux_sound :
        SoundExec (exec_aux exec_call_foreign exec_lemma exec_call exec_fail).
      Proof.
        unfold SoundExec. intros ? ? s.
        induction s; intros ? ?; cbn.

        - (* stm_val *)
          now apply rule_stm_val.

        - (* stm_exp *)
          now apply rule_stm_exp.

        - (* stm_let *)
          eapply rule_stm_let. apply IHs1. intros v2 δ2; cbn. apply IHs2.

        - (* stm_block *)
          now apply rule_stm_block, IHs.

        - (* stm_assign *)
          now apply rule_stm_assign, IHs.

        - (* stm_call *)
          apply sound_exec_call.

        - (* stm_call_frame *)
          now apply rule_stm_call_frame, IHs.

        - (* stm_foreign *)
          apply rule_stm_foreign, sound_exec_call_foreign.

        - (* stm_lemmak *)
          eapply rule_stm_lemmak. apply sound_exec_lemma. apply IHs.

        - (* stm_seq *)
          eapply rule_stm_seq. apply IHs1. intros δ2. apply IHs2.

        - (* stm_assert *)
          rewrite bi.and_comm. apply rule_pull. intros HYP.
          apply rule_stm_assert; auto. intro Heval.
          eapply rule_consequence_left. apply IHs.
          now apply entails_apply, bi.pure_intro.

        - (* stm_fail *)
          apply sound_exec_fail.

        - (* stm_pattern_match *)
          eapply rule_stm_pattern_match. apply IHs. cbn.
          intros pc δpc δ1'. rewrite pattern_match_val_inverse_right.
          now apply H.

        - (* stm_read_register *)
          apply rule_exist. intros v.
          apply (rule_stm_read_register_backwards (v := v)).

        - (* stm_write_register *)
          apply rule_exist. intros v.
          apply (rule_stm_write_register_backwards (v := v)).

        - (* stm_bind *)
          eapply rule_stm_bind. apply IHs. intros v2 δ2; cbn. apply H.
        - (* stm_debugk *)
          constructor. auto.
      Qed.

    End ExecAux.

    Lemma sound_cexec_call_foreign : SoundExecCallForeign cexec_call_foreign.
    Proof. intros Δ τ f args POST. apply (call_contract_sound (CEnvEx f)). Qed.

    Lemma sound_cexec_lemma : SoundExecLemma cexec_lemma.
    Proof. intros Δ l args POST. apply call_lemma_sound. Qed.

    Lemma sound_cexec_fail : SoundExecFail cexec_fail.
    Proof.
      intros Γ τ s POST δ. unfold cexec_fail.
      eapply rule_consequence_left. apply rule_stm_fail.
      now destruct fail_rule_pre.
    Qed.

    Lemma sound_cexec_call (fuel : nat) : SoundExecCall (cexec_call fuel).
    Proof.
      induction fuel; intros Γ τ Δ f es POST δ; cbn [cexec_call];
        cbv [CPureSpec.bind debug_call CPureSpec.pure];
        destruct (CEnv f) as [c|] eqn:Heq.
      - eapply rule_stm_call; [exact Heq|apply (call_contract_sound c)].
      - eapply rule_consequence_left. apply rule_false. easy.
      - eapply rule_stm_call; [exact Heq|apply (call_contract_sound c)].
      - apply rule_stm_call_inline. unfold evalStoreSpec.
        apply exec_aux_sound; auto using sound_cexec_call_foreign,
          sound_cexec_lemma, sound_cexec_fail.
    Qed.

    Lemma sound_cexec (fuel : nat) : SoundExec (cexec fuel).
    Proof.
      apply exec_aux_sound; auto using sound_cexec_call_foreign,
        sound_cexec_lemma, sound_cexec_call, sound_cexec_fail.
    Qed.

    Lemma vcgen_sound fuel {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
      (⊢ vcgen fuel c body) ->
      ProgLog.ValidContract c body.
    Proof.
      destruct c as [Σ δΣ req result ens].
      cbv [vcgen CPureSpec.run exec_contract CPureSpec.bind evalStoreSpec].
      rewrite CPureSpec.wp_demonic_ctx. intros HYP ι. cbn.
      rewrite (bi.forall_elim ι) CPureSpec.wp_produce in HYP.
      apply bi.wand_entails in HYP.
      refine (rule_consequence_left _
                (rule_consequence_right _ (sound_cexec _ _ _ _) _) HYP).
      intros v δ'. cbn. rewrite CPureSpec.wp_consume.
      apply bi.sep_elim_l, _.
    Qed.

    Lemma shallow_vcgen_soundness {Δ τ}
      (c : SepContract Δ τ) (body : Stm Δ τ) :
      Shallow.ValidContract c body ->
      ProgLog.ValidContract c body.
    Proof. apply vcgen_sound. Qed.

    Lemma shallow_vcgen_soundness_cenv :
      Shallow.ValidContractCEnv -> ProgLog.ValidContractCEnv.
    Proof. intros H Δ τ f c Hf. now apply shallow_vcgen_soundness, H. Qed.

  End Soundness.

End Soundness.
