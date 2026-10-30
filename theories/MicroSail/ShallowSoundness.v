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
     Strings.String
     ZArith.BinInt.
From Katamaran Require Import
     Signature
     Sep.Hoare
     Prelude
     Program
     MicroSail.ShallowExecutor.

Set Implicit Arguments.

Import ctx.notations.
Import env.notations.

Module Type Soundness
  (Import GLOBAL : GlobalState)
  (Import SIG    : Signature GLOBAL)
  (Import PROG   : Program GLOBAL)
  (Import PLOG   : ProgramLogic GLOBAL SIG PROG)
  (Import EXEC   : ShallowExecOn GLOBAL SIG PROG PLOG).

  Import CStoreSpec.
  Import ProgLog.

  Section Soundness.

    Import iris.proofmode.proofmode.

    Context {L} {biA : BiAffine L} {PI : PredicateDef L} {SPEC : Specification}.

    (* liftP converts the "proof theoretic" predicates (CStore Γ -> L), with L
       being a type of separation logic propositions, to the "model theoretic"
       heap predicates (CStore Γ -> SCHeap -> Prop) that are used as the type of
       postconditions in the shallow executor. *)
    Definition liftP {Γ} (POST : CStore Γ -> L) : CStore Γ -> SCHeap -> Prop :=
      fun δ h => interpret_scheap h ⊢ POST δ.

    Lemma call_contract_sound {Δ τ} (c : SepContract Δ τ) (args : CStore Δ)
      (Φ : Val τ → SCHeap → Prop) (h1 : SCHeap) :
      CHeapSpec.call_contract c args Φ h1 →
      CTriple (interpret_scheap h1) c args
        (fun v => ∃ h' : SCHeap, interpret_scheap h' ∧ ⌜Φ v h'⌝)%I.
    Proof.
      destruct c as [Σe δe req result ens]. cbn.
      cbv [CHeapSpec.call_contract CHeapSpec.bind CHeapSpec.lift_purespec
           CHeapSpec.demonic CPureSpec.demonic].
      rewrite CPureSpec.wp_angelic_ctx.
      intros [ι Hwp]; revert Hwp.
      rewrite CPureSpec.wp_assert_eq_nenv.
      intros [Hfmls ->%CHeapSpec.consume_sound].
      apply bi.exist_intro' with ι.
      apply bi.and_intro; auto.
      apply bi.sep_mono'; auto.
      apply bi.exist_elim. intros h'.
      apply bi.pure_elim_r.
      intros Hwp. apply bi.forall_intro; intro v.
      specialize (Hwp v). now apply CHeapSpec.produce_sound in Hwp.
    Qed.

    Lemma call_lemma_sound [Δ] (l : Lemma Δ) (δ : CStore Δ)
      (Φ : () → SCHeap → Prop) (h : SCHeap)   :
      CHeapSpec.call_lemma l δ Φ h →
      LTriple δ (interpret_scheap h) (∃ h', interpret_scheap h' ∧ ⌜Φ tt h'⌝) l.
    Proof.
      destruct l as [Σe δe req ens].
      unfold CHeapSpec.call_lemma.
      unfold CHeapSpec.bind, CHeapSpec.lift_purespec.
      rewrite CPureSpec.wp_angelic_ctx.
      intros [ι Hwp]; revert Hwp.
      rewrite CPureSpec.wp_assert_eq_nenv.
      intros [Hfmls Hwp%CHeapSpec.consume_sound].
      constructor.
      apply bi.exist_intro' with ι.
      apply bi.and_intro; auto.
      rewrite Hwp. clear Hwp.
      apply bi.sep_mono'; auto.
      apply bi.exist_elim. intros h'.
      apply bi.pure_elim_r.
      apply CHeapSpec.produce_sound.
    Qed.

    Definition SoundExecCall (exec_call : ExecCall) : Prop :=
      forall Γ τ Δ (f : 𝑭 Δ τ) (es : NamedEnv (Exp Γ) Δ)
        (Φ : Val τ → SCHeap → Prop)
        (δ1 : CStore Γ) (h1 : SCHeap),
        exec_call _ _ f (evals es δ1) Φ h1 →
        ⦃ interpret_scheap h1 ⦄
          stm_call f es; δ1
        ⦃ fun v δ' =>
            ∃ h' : SCHeap, interpret_scheap h' ∧ ⌜Φ v h' ∧ δ' = δ1⌝ ⦄.

    Definition SoundExecFail (exec_fail : ExecFail) : Prop :=
      forall Γ τ (s : Val ty.string)
        (Φ : Val τ → CStore Γ → SCHeap → Prop)
        (δ1 : CStore Γ) (h1 : SCHeap),
        exec_fail _ _ s Φ δ1 h1 →
        ⦃ interpret_scheap h1 ⦄
          stm_fail _ s; δ1
        ⦃ fun (v : Val τ) (δ' : CStore Γ) =>
            ∃ h' : SCHeap, interpret_scheap h' ∧ ⌜Φ v δ' h'⌝ ⦄.

    Definition SoundExecCallForeign (exec_call_foreign : ExecCallForeign) : Prop :=
      forall Γ τ Δ (f : 𝑭𝑿 Δ τ) (es : NamedEnv (Exp Γ) Δ)
        (Φ : Val τ → SCHeap → Prop) (δ1 : CStore Γ) (h1 : SCHeap),
      exec_call_foreign _ _ f (evals es δ1) Φ h1 →
      ⦃ interpret_scheap h1 ⦄
        stm_foreign f es; δ1
      ⦃ fun v δ' =>
          ∃ h' : SCHeap, interpret_scheap h' ∧ ⌜Φ v h' ∧ δ' = δ1⌝ ⦄.

    Definition SoundExecLemma (exec_lemma : ExecLemma) : Prop :=
      forall Γ Δ (l : 𝑳 Δ) (es : NamedEnv (Exp Γ) Δ)
        (Φ : unit → SCHeap → Prop) (δ1 : CStore Γ) (h1 : SCHeap),
      exec_lemma _ l (evals es δ1) Φ h1 →
      LTriple (evals es δ1) (interpret_scheap h1)
        (∃ h' : SCHeap, interpret_scheap h' ∧ ⌜Φ tt h'⌝)
        (LEnv l).

    Definition SoundExec (exec : Exec) :=
      forall
        Γ σ (s : Stm Γ σ) (Φ : Val σ → CStore Γ → SCHeap → Prop)
        (δ1 : CStore Γ) (h1 : SCHeap),
        exec _ _ s Φ δ1 h1 ->
        ⦃ interpret_scheap h1 ⦄
          s ; δ1
        ⦃ fun v δ' =>
            ∃ h' : SCHeap, interpret_scheap h' ∧ ⌜Φ v δ' h'⌝
        ⦄.

    Section ExecAux.

      Variable exec_call_foreign : ExecCallForeign.
      Variable exec_lemma : ExecLemma.
      Variable exec_call : ExecCall.
      Variable exec_fail : ExecFail.

      Variable mexec_call_foreign : MonotonicExecCallForeign exec_call_foreign.
      Variable mexec_lemma : MonotonicExecLemma exec_lemma.
      Variable mexec_call : MonotonicExecCall exec_call.
      Variable mexec_fail : MonotonicExecFail exec_fail.

      Variable sound_exec_call_foreign : SoundExecCallForeign exec_call_foreign.
      Variable sound_exec_lemma : SoundExecLemma exec_lemma.
      Variable sound_exec_call : SoundExecCall exec_call.
      Variable sound_exec_fail : SoundExecFail exec_fail.

      Lemma exec_aux_sound :
        SoundExec (exec_aux exec_call_foreign exec_lemma exec_call exec_fail).
      Proof.
        unfold SoundExec. intros ? ? s.
        induction s; intros ? ? ?; cbn;
          cbv [pure pushspops pushpop eval_exp get_local put_local bind];
          cbn; intros HYP.

        - (* stm_val *)
          apply rule_stm_val.
          apply bi.exist_intro' with h1.
          apply bi.and_intro.
          reflexivity.
          apply bi.pure_intro.
          auto.

        - (* stm_exp *)
          apply rule_stm_exp.
          apply bi.exist_intro' with h1.
          apply bi.and_intro.
          reflexivity.
          apply bi.pure_intro.
          auto.

        - (* stm_let *)
          eapply rule_stm_let.
          apply IHs1, HYP. clear IHs1 HYP.
          intros v1 δ2.
          apply rule_exist. intros h.
          apply rule_pull. intros HYP.
          now apply IHs2.

        - (* stm_block *)
          now apply rule_stm_block, IHs.

        - (* stm_assign *)
          now apply rule_stm_assign, IHs.

        - (* stm_call *)
          eapply sound_exec_call in HYP.
          apply (rule_consequence_right _ HYP).
          intros.
          apply bi.exist_mono'. intros h.
          apply bi.and_mono'; auto.
          apply bi.pure_mono; intros []; now subst.

        - (* stm_call_frame *)
          now apply rule_stm_call_frame, IHs.

        - (* stm_foreign *)
          eapply sound_exec_call_foreign in HYP.
          apply (rule_consequence_right _ HYP).
          intros.
          apply bi.exist_mono'. intros h.
          apply bi.and_mono'; auto.
          apply bi.pure_mono; intros []; now subst.

        - (* stm_lemmak *)
          eapply rule_stm_lemmak.
          apply (sound_exec_lemma _ _ HYP). clear HYP.
          apply rule_exist. intros h.
          apply rule_pull. intros HYP.
          now apply IHs.

        - (* stm_seq *)
          eapply rule_stm_seq.
          apply IHs1, HYP. clear IHs1 HYP.
          intros v1 δ2.
          apply rule_exist. intros h.
          apply rule_pull. intros HYP.
          now apply IHs2.

        - (* stm_assert *)
          destruct HYP as [Hf HYP].
          apply rule_stm_assert; auto.

        - (* stm_fail *)
          now eapply sound_exec_fail.

        - (* stm_match_newpattern *)
          eapply rule_stm_pattern_match.
          apply IHs, HYP. clear IHs HYP.
          intros pc δpc δΓ'. cbn.
          apply rule_exist. intros h.
          apply rule_pull. intros HYP.
          apply wp_demonic_pattern_match in HYP.
          rewrite pattern_match_val_inverse_right in HYP.
          now apply H.

        - (* stm_read_register *)
          destruct HYP as [v HYP].
          eapply rule_consequence_left.
          apply (rule_stm_read_register_backwards (v := v)).
          apply CPureSpec.wp_consume_chunk in HYP.
          rewrite HYP. clear HYP. cbn.
          apply bi.sep_mono'. easy.
          apply bi.exist_elim. intros h2.
          apply bi.pure_elim_r.
          now intros ->%CPureSpec.wp_produce_chunk.

        - (* stm_write_register *)
          destruct HYP as [v HYP].
          eapply rule_consequence_left.
          apply (rule_stm_write_register_backwards (v := v)).
          apply CPureSpec.wp_consume_chunk in HYP.
          rewrite HYP. clear HYP. cbn.
          apply bi.sep_mono'. easy.
          apply bi.exist_elim. intros h2.
          apply bi.pure_elim_r.
          now intros ->%CPureSpec.wp_produce_chunk.

        - (* stm_bind *)
          eapply rule_stm_bind.
          apply IHs, HYP. clear IHs HYP.
          intros v1 δ2. cbn.
          apply rule_exist. intros h.
          apply rule_pull. intros HYP.
          now apply H.

        - (* stm_debug *)
          constructor. auto.
      Qed.

    End ExecAux.

    Section WithExec.

      Context (exec : Exec) (mexec : MonotonicExec exec) (sound_exec : SoundExec exec).

      Lemma exec_contract_sound [Δ τ] (c : SepContract Δ τ) (body : Stm Δ τ) Φ h :
        exec_contract exec c body Φ h →
        ∀ ι : Valuation (sep_contract_logic_variables c),
        ⦃ interpret_scheap h ∗
          asn.interpret (sep_contract_precondition c) ι ⦄
          body ; inst (sep_contract_localstore c) ι
        ⦃ fun v _ =>
            asn.interpret
              (sep_contract_postcondition c)
              ι.[sep_contract_result c∷τ ↦ v] ∗
            ∃ h', ⌜ Φ tt h' ⌝ ⦄.
      Proof.
        destruct c as [Σ δΣ req result ens]; cbn.
        cbv [CHeapSpec.bind CHeapSpec.demonic_ctx
               CHeapSpec.lift_purespec evalStoreSpec].
        intros HYP ι.
        rewrite CPureSpec.wp_demonic_ctx in HYP.
        specialize (HYP ι). remember (inst δΣ ι) as δ.
        apply CHeapSpec.produce_sound, bi.wand_elim_l' in HYP.
        refine (rule_consequence_left _ _ HYP). clear HYP.
        apply rule_exist. intros h'.
        apply rule_pull. intros HYP.
        eapply sound_exec in HYP.
        apply (rule_consequence_right _ HYP).
        intros v _.
        apply bi.exist_elim. intros h2.
        apply bi.pure_elim_r.
        intros ->%CHeapSpec.consume_sound.
        apply bi.sep_mono'; auto.
        apply bi.exist_elim. intros h3.
        apply bi.pure_elim_r. auto.
      Qed.

    End WithExec.

    Lemma sound_cexec_call_foreign : SoundExecCallForeign cexec_call_foreign.
    Proof.
      unfold SoundExecCallForeign, cexec_call_foreign.
      intros * HYP%call_contract_sound. constructor.
      destruct (CEnvEx f) as [Σ δΣ req result ens]; cbn in *.
      rewrite HYP. clear HYP.
      apply bi.exist_mono'. intros ι.
      apply bi.and_mono'; auto.
      apply bi.sep_mono'; auto.
      apply bi.forall_mono'; intros v.
      apply bi.wand_mono'. easy.
      apply bi.exist_mono'. intros h'.
      apply bi.and_mono'; auto.
    Qed.

    Lemma sound_cexec_lemma : SoundExecLemma cexec_lemma.
    Proof.
      unfold SoundExecLemma, cexec_lemma. intros *.
      now apply call_lemma_sound.
    Qed.

    Lemma sound_cexec_fail : SoundExecFail cexec_fail.
    Proof.
      unfold SoundExecFail, cexec_fail. intros *.
      intros HYP.
      destruct fail_rule_pre eqn:Ef.
      - eapply rule_consequence_left.
        eapply rule_stm_fail.
        rewrite Ef.
        auto.
      - destruct HYP.
    Qed.

    Lemma sound_cexec_call (fuel : nat) : SoundExecCall (cexec_call fuel).
    Proof.
      induction fuel; unfold SoundExecCall, evalStoreSpec; cbn; intros.
      - destruct (CEnv f) as [c|] eqn:?.
        + apply call_contract_sound in H.
          apply rule_stm_call with c; auto. clear Heqo.
          destruct c as [Σ δΣ req result ens]; cbn in *.
          rewrite H. clear H.
          apply bi.exist_mono'. intros ι.
          apply bi.and_mono'; auto.
          apply bi.sep_mono'; auto.
          apply bi.forall_mono'; intros v.
          apply bi.wand_mono'. easy.
          apply bi.exist_mono'. intros h'.
          apply bi.and_mono'; auto.
        + contradiction H.
      - destruct (CEnv f) as [c|] eqn:?.
        + apply call_contract_sound in H.
          apply rule_stm_call with c; auto. clear Heqo.
          destruct c as [Σ δΣ req result ens]; cbn in *.
          rewrite H. clear H.
          apply bi.exist_mono'. intros ι.
          apply bi.and_mono'; auto.
          apply bi.sep_mono'; auto.
          apply bi.forall_mono'; intros v.
          apply bi.wand_mono'. easy.
          apply bi.exist_mono'. intros h'.
          apply bi.and_mono'; auto.
        + apply rule_stm_call_inline.
          eapply exec_aux_sound in H.
          * apply (rule_consequence_right _ H).
            intros ? _.
            apply bi.exist_mono'. intros h.
            apply bi.and_mono'; auto.
          * apply sound_cexec_call_foreign.
          * apply sound_cexec_lemma.
          * auto.
          * apply sound_cexec_fail.
    Qed.

    Lemma sound_cexec (fuel : nat) : SoundExec (cexec fuel).
    Proof.
      apply exec_aux_sound.
      - apply sound_cexec_call_foreign.
      - apply sound_cexec_lemma.
      - apply sound_cexec_call.
      - apply sound_cexec_fail.
    Qed.

    Lemma vcgen_sound fuel {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
      vcgen fuel c body ->
      ProgLog.ValidContract c body.
    Proof.
      cbv [vcgen CHeapSpec.run ProgLog.ValidContract]. intros HYP ι.
      eapply exec_contract_sound in HYP; auto using sound_cexec. cbn in HYP.
      rewrite bi.emp_sep in HYP.
      apply (rule_consequence_right _ HYP). clear HYP.
      intros ? _.
      apply bi.sep_elim_l; auto with typeclass_instances.
    Qed.

    Lemma shallow_vcgen_soundness {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
      Shallow.ValidContract c body ->
      ProgLog.ValidContract c body.
    Proof. apply vcgen_sound. Qed.

    Lemma shallow_vcgen_fuel_soundness {Δ τ} (fuel : nat) (c : SepContract Δ τ) (body : Stm Δ τ) :
      Shallow.ValidContractWithFuel fuel c body ->
      ProgLog.ValidContract c body.
    Proof. apply vcgen_sound. Qed.

    (* Print Assumptions shallow_vcgen_soundnes. *)

  End Soundness.

End Soundness.

Module MakeShallowSoundness
  (Import GLOBAL : GlobalState)
  (Import SIG    : Signature GLOBAL)
  (Import PROG   : Program GLOBAL)
  (Import PLOG   : ProgramLogic GLOBAL SIG PROG)
  (Import EXEC   : ShallowExecOn GLOBAL SIG PROG PLOG).

  Include Soundness GLOBAL SIG PROG PLOG EXEC.

End MakeShallowSoundness.
