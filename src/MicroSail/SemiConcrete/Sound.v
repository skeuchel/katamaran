(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel                                          *)
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
     Program.Tactics
     ZArith.ZArith
     Strings.String
     Classes.Morphisms
     Classes.Morphisms_Prop
     Classes.Morphisms_Relations.

From Equations Require Import
     Equations.

From MicroSail Require Import
     Sep.Spec
     Sep.Logic
     Sep.Hoare
     Syntax
     Tactics
     SemiConcrete.Mutator
     Symbolic.Outcome.

Set Implicit Arguments.

Import CtxNotations.
Import EnvNotations.

Module Soundness
       (Import typekit : TypeKit)
       (Import termkit : TermKit typekit)
       (Import progkit : ProgramKit typekit termkit)
       (Import assertkit : AssertionKit typekit termkit progkit)
       (Import contractkit : SymbolicContractKit typekit termkit progkit assertkit)
       (Import heapkit : HeapKit typekit termkit progkit assertkit contractkit).
  Module MUT := SemiConcrete typekit termkit progkit assertkit contractkit.
  Import MUT.
  Module LOG := ProgramLogic typekit termkit progkit assertkit contractkit heapkit.
  Import LOG.

  Local Open Scope logic.

  Section Soundness.

    Notation "'scmutres_heap' r" := (scstate_heap (scmutres_state r)) (at level 10).
    Notation "'scmutres_localstore' r" := (scstate_localstore (scmutres_state r)) (at level 10).

    Context `{HL: IHeaplet L} {SLL: ISepLogicLaws L}.

    Definition inst_scchunk (c : SCChunk) : L :=
      match c with
      | scchunk_pred p vs => pred p vs
      | scchunk_ptsreg r v => ptsreg r v
      end.

    Definition inst_scheap : SCHeap -> L :=
      List.fold_right (fun c h => inst_scchunk c ✱ h) emp.
    Global Arguments inst_scheap !h.

    Lemma in_heap_extractions {h c1 h1} (hyp : List.In (c1 , h1) (heap_extractions h)) :
      inst_scheap h ⊣⊢s inst_scchunk c1 ✱ inst_scheap h1.
    Proof.
      revert c1 h1 hyp.
      induction h; cbn; intros.
      - contradict hyp.
      - destruct hyp as [hyp|hyp].
        + inversion hyp; subst.
          split; apply entails_refl.
        + cbn in *.
          apply List.in_map_iff in hyp.
          destruct hyp as [[c2 h2] [H1 H2]].
          inversion H1; subst; clear H1.
          apply IHh in H2; rewrite H2; clear IHh H2.
          rewrite sepcon_comm.
          rewrite sepcon_assoc.
          split; apply sepcon_entails; auto using entails_refl.
          apply sepcon_comm.
          apply sepcon_comm.
    Qed.

    Opaque env_tail.
    Opaque match_chunk_eqb.

    Local Ltac sound_inster :=
      match goal with
      | [ IH: outcome_satisfy (scmut_exec ?s _) _ |-
          outcome_satisfy (scmut_exec ?s _) _ ] =>
        refine (outcome_satisfy_monotonic _ _ IH); clear IH
      | [ IH: outcome_satisfy (scmut_consume _ ?a _) _ |-
          outcome_satisfy (scmut_consume _ ?a _) _ ] =>
        refine (outcome_satisfy_monotonic _ _ IH); clear IH
      | [ IH: outcome_satisfy (scmut_produce _ ?a _) _ |-
          outcome_satisfy (scmut_produce _ ?a _) _ ] =>
        refine (outcome_satisfy_monotonic _ _ IH); clear IH
      | [ IH: context[_ -> outcome_satisfy (scmut_exec ?s _) _] |-
          outcome_satisfy (scmut_exec ?s _) _ ] =>
        microsail_insterU (fail) IH; refine (outcome_satisfy_monotonic _ _ IH); clear IH
      | [ IH: outcome_satisfy ?o _ |-
          outcome_satisfy ?o _ ] =>
        refine (outcome_satisfy_monotonic _ _ IH); clear IH
      | [ IH: scmut_wp ?o _ _ |-
          scmut_wp ?o _ _ ] =>
        refine (scmut_monotonic o _ _ IH); clear IH;
        let v := fresh "v" in
        let δ := fresh "δ" in
        let h := fresh "h" in
        intros v [δ h]
      end.

    Lemma scmut_consume_chunk_sound {Γ} {δ1 : LocalStore Γ} {h1 : SCHeap} (c : SCChunk) (POST : LocalStore Γ -> L) :
      scmut_wp
        (scmut_consume_chunk c)
        (fun _ s => inst_scheap (scstate_heap s) ⊢ POST (scstate_localstore s))
        {| scstate_localstore := δ1; scstate_heap := h1 |} ->
      inst_scheap h1 ⊢ inst_scchunk c ✱ POST δ1.
    (* Proof. *)
    (*   cbn; intros HYP. *)
    (*   rewrite outcome_satisfy_bind, !outcome_satisfy_map_angelic_list, *)
    (*     outcome_satisfy_filter_angelic_list in HYP. *)
    (*   apply outcome_satisfy_angelic_list in HYP. *)
    (*   destruct HYP as [[c' h1'] [H1 [HYP Heq]]]; cbn in *; try discriminate. *)
    (*   apply (Bool.reflect_iff _ _ (match_chunk_eqb_spec _ _)) in Heq; subst c'. *)
    (*   apply in_heap_extractions in H1; rewrite H1; clear H1; cbn. *)
    (*   apply sepcon_entails. *)
    (*   apply entails_refl. *)
    (*   assumption. *)
    (* Qed. *)
    Admitted.

    Opaque scmut_consume_chunk.

    Lemma scmut_consume_sound {Γ Σ} {δ1 : LocalStore Γ} {h1 : SCHeap} {ι : SymInstance Σ} {asn : Assertion Σ} (POST : LocalStore Γ -> L) :
      scmut_wp
        (scmut_consume ι asn)
        (fun _ s => inst_scheap (scstate_heap s) ⊢ POST (scstate_localstore s))
        {| scstate_localstore := δ1; scstate_heap := h1 |} ->
      inst_scheap h1 ⊢ inst_assertion ι asn ✱ POST δ1.
    (* Proof. *)
    (*   revert ι δ1 h1 POST. induction asn; cbn; intros ι δ1 h1 POST HYP. *)
    (*   - destruct (inst_term ι b); cbn in *. *)
    (*     + rewrite <- sepcon_emp at 1. *)
    (*       rewrite sepcon_comm. *)
    (*       apply sepcon_entails. *)
    (*       apply entails_refl. *)
    (*       apply HYP. *)
    (*     + contradict HYP. *)
    (*   - contradict HYP. *)
    (*   - apply scmut_consume_chunk_sound in HYP. *)
    (*     now destruct c. *)
    (*   - destruct (inst_term ι b); auto. *)
    (*   - auto. *)
    (*   - unfold scmut_bind_right, scmut_bind in HYP. *)
    (*     rewrite outcome_satisfy_bind in HYP. *)
    (*     rewrite sepcon_assoc. *)
    (*     apply (IHasn1 ι δ1 h1 (fun δ => inst_assertion ι asn2 ✱ POST δ)); clear IHasn1. *)
    (*     sound_inster. *)
    (*     intros [? [δ2 h2]] HYP; cbn. *)
    (*     now apply (IHasn2 ι δ2 h2 POST). *)
    (*   - destruct HYP as [v HYP]. *)
    (*     apply (entails_trans (inst_scheap h1) (inst_assertion (env_snoc ι (ς , τ) v) asn ✱ POST δ1)). *)
    (*     + now apply IHasn. *)
    (*     + apply sepcon_entails. *)
    (*       apply lex_right with v, entails_refl. *)
    (*       apply entails_refl. *)
    (* Qed. *)
    Admitted.

    Lemma scmut_produce_sound {Γ Σ} {δ1 : LocalStore Γ} {h1 : SCHeap} {ι : SymInstance Σ} {asn : Assertion Σ} (POST : LocalStore Γ -> L) :
      scmut_wp
        (scmut_produce ι asn)
        (fun _ s => inst_scheap (scstate_heap s) ⊢ POST (scstate_localstore s))
        {| scstate_localstore := δ1; scstate_heap := h1 |} ->
      inst_scheap h1 ✱ inst_assertion ι asn ⊢ POST δ1.
    (* Proof. *)
    (*   revert ι δ1 h1 POST. induction asn; cbn; intros ι δ1 h1 POST HYP. *)
    (*   - destruct (inst_term ι b); cbn in *. *)
    (*     + rewrite <- (sepcon_emp (POST _)). *)
    (*       apply sepcon_entails. *)
    (*       apply HYP. *)
    (*       apply entails_refl. *)
    (*     + rewrite sepcon_comm. *)
    (*       apply wand_sepcon_adjoint. *)
    (*       apply lfalse_left. *)
    (*   - contradict HYP. *)
    (*   - rewrite sepcon_comm. *)
    (*     now destruct c. *)
    (*   - destruct (inst_term ι b); auto. *)
    (*   - auto. *)
    (*   - unfold scmut_bind_right, scmut_bind in HYP. *)
    (*     rewrite outcome_satisfy_bind in HYP. *)
    (*     rewrite <- sepcon_assoc. *)
    (*     apply wand_sepcon_adjoint. *)
    (*     apply (IHasn1 ι δ1 h1 (fun δ => inst_assertion ι asn2 -✱ POST δ)); clear IHasn1. *)
    (*     sound_inster. *)
    (*     intros [? [δ2 h2]] HYP; cbn. *)
    (*     apply wand_sepcon_adjoint. *)
    (*     now apply (IHasn2 ι δ2 h2 POST). *)
    (*   - rewrite sepcon_comm. *)
    (*     apply wand_sepcon_adjoint. *)
    (*     apply lex_left. intro v. *)
    (*     apply wand_sepcon_adjoint. *)
    (*     rewrite sepcon_comm. *)
    (*     now apply IHasn. *)
    (* Qed. *)
    Admitted.

    Lemma scmut_produce_sound' {Γ Σ} {δ1 : LocalStore Γ} {h1 : SCHeap} {ι : SymInstance Σ} {asn : Assertion Σ} (POST : LocalStore Γ -> L) :
      scmut_wp
        (scmut_produce ι asn)
        (fun _ s => inst_scheap (scstate_heap s) ⊢ POST (scstate_localstore s))
        {| scstate_localstore := δ1; scstate_heap := h1 |} ->
      inst_assertion ι asn ⊢ inst_scheap h1 -✱ POST δ1.
    Proof.
      intros. apply wand_sepcon_adjoint. rewrite sepcon_comm.
      now apply (scmut_produce_sound _ H).
    Qed.

    Lemma scmut_exec_sound {Γ σ} (s : Stm Γ σ) :
      forall (δ1 : LocalStore Γ) (h1 : SCHeap) (POST : Lit σ -> LocalStore Γ -> L),
        scmut_wp
          (scmut_exec s)
          (fun v2 s => inst_scheap (scstate_heap s) ⊢ POST v2 (scstate_localstore s))
          {| scstate_localstore := δ1; scstate_heap := h1 |} ->
        δ1 ⊢ ⦃ inst_scheap h1 ⦄ s ⦃ POST ⦄.
    (* Proof. *)
    (*   induction s; *)
    (*     unfold scmut_bind, scmut_bind_left, scmut_bind_right, scmut_push_local, *)
    (*       scmut_pop_local, scmut_pure; cbn in *; *)
    (*     repeat setoid_rewrite outcome_satisfy_bind; cbn in *; intros ? ? ? HYP. *)

    (*   - (* stm_lit *) *)
    (*     now apply rule_stm_lit. *)

    (*   - (* stm_exp *) *)
    (*     now apply rule_stm_exp. *)

    (*   - (* stm_let *) *)
    (*     eapply rule_consequence_left. *)
    (*     eapply rule_stm_let; intros; apply rule_wp. *)

    (*     apply lex_right with (inst_scheap h1). *)
    (*     apply land_right. *)
    (*     apply entails_refl. *)
    (*     apply lprop_right. *)
    (*     apply IHs1; clear IHs1. *)
    (*     sound_inster. *)
    (*     intros [v2 [δ2 h2]] HYP; cbn. *)

    (*     apply lex_right with (inst_scheap h2). *)
    (*     apply land_right. *)
    (*     apply entails_refl. *)
    (*     apply lprop_right. *)
    (*     now apply IHs2. *)

    (*   - (* stm_block *) *)
    (*     now apply rule_stm_block, IHs. *)

    (*   - (* stm_assign *) *)
    (*     now apply rule_stm_assign_backwards, IHs. *)

    (*   - (* stm_call *) *)
    (*     destruct (CEnv f) as [c|] eqn:Heq; cbn in HYP. *)
    (*     destruct c as [Σe δe req result ens] eqn:Heqc. *)
    (*     + destruct HYP as [ι [Heqs HYP]]. *)
    (*       unfold scmut_angelic, scmut_bind, scmut_pure in HYP; cbn in HYP. *)
    (*       repeat setoid_rewrite outcome_satisfy_bind in HYP; cbn in HYP. *)
    (*       repeat setoid_rewrite outcome_satisfy_bind in HYP; cbn in HYP. *)
    (*       assert (inst_scheap h1 ⊢ inst_assertion ι req ✱ (∀ v, inst_assertion (env_snoc ι (result,_) v) ens -✱ POST v δ1)). *)
    (*       { apply (scmut_consume_sound (fun δ => ∀ v, inst_assertion (env_snoc ι (result , σ) v) ens -✱ POST v δ)). *)
    (*         sound_inster. *)
    (*         intros [? [δ2 h2]] HYP; cbn. *)
    (*         apply lall_right; intro v. *)
    (*         specialize (HYP v). *)
    (*         now apply wand_sepcon_adjoint, scmut_produce_sound. *)
    (*       } *)
    (*       clear HYP. *)
    (*       eapply rule_consequence_left. *)
    (*       2: exact H. *)
    (*       rewrite sepcon_comm. *)
    (*       eapply rule_consequence_right. *)
    (*       apply rule_frame. *)
    (*       apply rule_stm_call_forwards with c. *)
    (*       congruence. *)
    (*       rewrite Heqc. *)
    (*       constructor. *)
    (*       apply Heqs. *)
    (*       cbn. intros. *)
    (*       apply wand_sepcon_adjoint. *)
    (*       apply lall_left with v. *)
    (*       apply wand_sepcon_adjoint. *)
    (*       rewrite sepcon_comm. *)
    (*       apply wand_sepcon_adjoint. *)
    (*       rewrite land_comm. *)
    (*       apply limpl_and_adjoint. *)
    (*       apply lprop_left; intro; subst δ1. *)
    (*       apply limpl_and_adjoint. *)
    (*       apply land_left2. *)
    (*       apply wand_sepcon_adjoint. *)
    (*       rewrite sepcon_comm. *)
    (*       apply wand_sepcon_adjoint. *)
    (*       apply entails_refl. *)
    (*     + contradict HYP. *)

    (*   - (* stm_call_frame *) *)
    (*     now apply rule_stm_call_frame, IHs. *)

    (*   - (* stm_call_external *) *)
    (*     cbn. *)
    (*     (* err.. need for assumptions about external calls? *) *)
    (*     admit. *)

    (*   - (* stm_if *) *)
    (*     apply rule_stm_if; apply rule_pull; intro Heval; rewrite Heval in *; auto. *)

    (*   - (* stm_seq *) *)
    (*     eapply rule_consequence_left. *)
    (*     eapply rule_stm_seq; intros; apply rule_wp. *)

    (*     apply lex_right with (inst_scheap h1). *)
    (*     apply land_right. *)
    (*     apply entails_refl. *)
    (*     apply lprop_right. *)
    (*     apply IHs1; clear IHs1. *)
    (*     sound_inster. *)
    (*     intros [v2 [δ2 h2]] HYP; cbn. *)

    (*     apply lex_right with (inst_scheap h2). *)
    (*     apply land_right. *)
    (*     apply entails_refl. *)
    (*     apply lprop_right. *)
    (*     now apply IHs2. *)

    (*   - (* stm_assert *) *)
    (*     eapply rule_consequence_right. *)
    (*     apply rule_stm_assert. *)
    (*     cbn; intros. *)
    (*     apply limpl_and_adjoint. *)
    (*     apply lprop_left; intros (? & ? & Heval); subst. *)
    (*     rewrite Heval in *; cbn in *. *)
    (*     now apply limpl_and_adjoint, land_left2. *)

    (*   - (* stm_fail *) *)
    (*     eapply rule_consequence_left. *)
    (*     apply rule_stm_fail. *)
    (*     apply ltrue_right. *)

    (*   - (* stm_match_list *) *)
    (*     apply rule_stm_match_list; cbn; intros; *)
    (*       apply rule_pull; intro Heval; rewrite Heval in HYP. *)
    (*     + now apply IHs1. *)
    (*     + unfold scmut_bind_left, scmut_bind in HYP; cbn in HYP. *)
    (*       repeat setoid_rewrite outcome_satisfy_bind in HYP; cbn in HYP. *)
    (*       now apply IHs2. *)

    (*   - (* stm_match_sum *) *)
    (*     apply rule_stm_match_sum; cbn; intros; *)
    (*       apply rule_pull; intro Heval; rewrite Heval in HYP. *)
    (*     + unfold scmut_bind_left, scmut_bind in HYP. *)
    (*       repeat setoid_rewrite outcome_satisfy_bind in HYP; cbn in HYP. *)
    (*       now apply IHs1. *)

    (*     + unfold scmut_bind_left, scmut_bind in HYP. *)
    (*       repeat setoid_rewrite outcome_satisfy_bind in HYP; cbn in HYP. *)
    (*       now apply IHs2. *)

    (*   - (* stm_match_pair *) *)
    (*     apply rule_stm_match_pair; cbn; intros; *)
    (*       apply rule_pull; intro Heval; rewrite Heval in HYP. *)
    (*     now apply IHs. *)

    (*   - (* stm_match_enum *) *)
    (*     now apply rule_stm_match_enum, H. *)

    (*   - (* stm_match_tuple *) *)
    (*     now apply rule_stm_match_tuple, IHs. *)

    (*   - (* stm_match_union *) *)
    (*     apply rule_stm_match_union'. *)
    (*     intros K. specialize (H K). *)
    (*     remember (alts K) as alt. *)
    (*     dependent elimination alt; cbn. *)
    (*     intros. *)
    (*     apply rule_pull. intro Heval. rewrite Heval, 𝑼_unfold_fold in HYP. *)
    (*     unfold scmut_bind_left, scmut_bind in HYP. *)
    (*     repeat setoid_rewrite outcome_satisfy_bind in HYP; cbn in HYP. *)
    (*     rewrite <- Heqalt in HYP. *)
    (*     now apply H. *)

    (*   - (* stm_match_record *) *)
    (*     now apply rule_stm_match_record, IHs. *)

    (*   - (* stm_read_register *) *)
    (*     destruct HYP as [v HYP]. *)
    (*     eapply rule_consequence_left. *)
    (*     apply (rule_stm_read_register_backwards (v := v)). *)
    (*     setoid_rewrite sepcon_comm in HYP. *)
    (*     setoid_rewrite wand_sepcon_adjoint in HYP. *)
    (*     now apply (scmut_consume_chunk_sound _ (fun δ => _ -✱ POST _ δ)) in HYP. *)

    (*   - (* stm_write_register *) *)
    (*     destruct HYP as [v HYP]. *)
    (*     eapply rule_consequence_left. *)
    (*     apply (rule_stm_write_register_backwards (v := v)). *)
    (*     setoid_rewrite sepcon_comm in HYP. *)
    (*     setoid_rewrite wand_sepcon_adjoint in HYP. *)
    (*     now apply (scmut_consume_chunk_sound _ (fun δ => _ -✱ POST _ δ)) in HYP. *)

    (*   - (* stm_bind *) *)
    (*     eapply rule_consequence_left. *)
    (*     eapply rule_stm_bind; intros; apply rule_wp. *)

    (*     apply lex_right with (inst_scheap h1). *)
    (*     apply land_right. *)
    (*     apply entails_refl. *)
    (*     apply lprop_right. *)
    (*     apply IHs; clear IHs. *)
    (*     sound_inster. *)
    (*     intros [v2 [δ2 h2]] HYP; cbn. *)

    (*     apply lex_right with (inst_scheap h2). *)
    (*     apply land_right. *)
    (*     apply entails_refl. *)
    (*     apply lprop_right. *)
    (*     now apply H. *)

    Admitted.

    Lemma scmut_exec_sound' {Γ σ} (s : Stm Γ σ) :
      forall (δ1 : LocalStore Γ) (h1 : SCHeap) (POST : Lit σ -> LocalStore Γ -> L),
        scmut_wp
          (scmut_exec s)
          (fun v2 s => inst_scheap (scstate_heap s) ⊢ POST v2 (scstate_localstore s))
          {| scstate_localstore := δ1; scstate_heap := h1 |} ->
        inst_scheap h1 ⊢ WP s POST δ1.
    Proof.
      cbn in *; intros.
      unfold WP.
      apply scmut_exec_sound in H.
      apply lex_right with (inst_scheap h1).
      apply land_right.
      reflexivity.
      now apply lprop_right.
    Qed.

    Opaque inst_localstore.

    Lemma scmut_contract_sound {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
      ValidContractSCMut c body ->
      ValidContract c body.
    Proof.
      unfold ValidContractSCMut, ValidContract.
      unfold inst_contract_localstore.
      destruct c as [Σ δΣ req result ens]; cbn; intros HYP ι.
      - specialize (HYP ι).
        remember (inst_localstore ι δΣ) as δ.
        eapply rule_consequence_left.
        apply rule_wp.
        apply entails_trans with
            (inst_scheap nil -✱ WP body (fun (v : Lit τ) (_ : LocalStore Δ) => inst_assertion (env_snoc ι (result,τ) v) ens) δ).
        apply scmut_produce_sound'.
        2: {
          rewrite <- sepcon_emp.
          apply wand_sepcon_adjoint.
          apply entails_refl.
        }
        sound_inster; cbn; intros HYP.
        apply scmut_exec_sound'.
        sound_inster; cbn; intros HYP.
        enough (inst_scheap h0 ⊢ inst_assertion (env_snoc ι (result,τ) v0) ens ✱ emp)
          by now rewrite sepcon_emp in H.
        change emp with ((fun _ => emp) δ1).
        apply (scmut_consume_sound (asn := ens)).
        sound_inster.
        destruct h1; cbn in *; intros.
        + apply entails_refl.
        + contradict H.
    Qed.

  End Soundness.

End Soundness.
