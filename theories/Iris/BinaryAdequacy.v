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

From Equations Require Import
     Equations Signature.
Require Import Equations.Prop.EqDec.

From stdpp Require finite gmap list.

From iris Require Import
     algebra.auth
     algebra.excl
     algebra.gmap
     base_logic.lib.fancy_updates
     base_logic.lib.gen_heap
     base_logic.lib.own
     bi.big_op
     bi.interface
     program_logic.adequacy
     program_logic.weakestpre
     proofmode.proofmode.

From Katamaran Require Import
     Iris.Base
     Iris.Instance
     Prelude
     Semantics
     Sep.Hoare
     Signature
     SmallStep.Step
     BinaryResources
     BinaryWeakestPre.

Import ctx.notations.
Import env.notations.

Set Implicit Arguments.

Module Type IrisAdeqParameters2
  (Import GLOBAL  : GlobalState)
  (IPleft  : IrisParameters GLOBAL)
  (IPright : IrisParameters GLOBAL)
  (Import IPP     : IrisParameters2 GLOBAL IPleft IPright).

  Parameter Inline memGpreS2 : gFunctors -> Set.
  Parameter memΣ2 : gFunctors.
  Parameter memΣ_GpreS2 : forall {Σ}, subG memΣ2 Σ -> memGpreS2 Σ.
  Parameter mem_res2 : forall `{mG : memGS2 Σ}, Memory -> Memory -> iProp Σ.

    (* Definition mem_state_interp `{sailG Σ} (μ : Z -> option Z) : iProp Σ := *)
    (*   (∃ memmap, gen_heap_ctx memmap ∗ *)
    (*      ⌜ map_Forall (fun (a : Z) v => μ a = Some v) memmap ⌝ *)
    (*   )%I. *)

  Parameter mem_init2 : forall `{mGS : memGpreS2 Σ} (μ1 μ2 : Memory),
                                         ⊢ |==> ∃ mG : memGS2 Σ, (mem_state_interp2 (mG := mG) μ1 μ2 ∗ mem_res2 (mG := mG) μ1 μ2)%I.

End IrisAdeqParameters2.

Module Type IrisAdequacy2
  (Import GLOBAL  : GlobalState)
  (Import SIG     : Signature GLOBAL)
  (Import PROG    : Program GLOBAL)
  (Import SEM     : Semantics GLOBAL PROG)
  (Import PLOG    : ProgramLogic GLOBAL SIG PROG)
  (Import IPre    : IrisPrelims GLOBAL PROG SEM)
  (IBleft         : IrisBase GLOBAL PROG SEM IPre)
  (IBright        : IrisBase GLOBAL PROG SEM IPre)
  (Import IB2     : IrisBase2 GLOBAL PROG SEM IPre IBleft IBright)
  (Import IAP2    : IrisAdeqParameters2 GLOBAL IBleft IBright IB2)
  (Import IPred2  : IrisPredicates2 GLOBAL SIG PROG SEM IPre IBleft IBright IB2)
  (Import IRules2 : IrisSignatureRules2 GLOBAL SIG PROG SEM PLOG IPre IBleft IBright IB2 IPred2).

  Import SmallStepNotations.

  Class sailGpreS2 Σ := SailGpreS2 { (* resources for the implementation side *)
                       sailGpresS_invGpreS2 :: invGpreS Σ; (* for fancy updates, invariants... *)

                       (* ghost variables for tracking state of registers *)
                       reg_pre_inG2_left :: inG Σ regUR;
                       reg_pre_inG2_right :: inG Σ regUR;

                       (* ghost variable for tracking state of memory cells *)
                       sailPreG_gen_memGpreS2 :: memGpreS2 Σ
                     }.

  #[local] Existing Instance sailGpresS_invGpreS2.

  Definition sailΣ2 : gFunctors := #[ memΣ2 ; invΣ ; GFunctor regUR; GFunctor regUR].

  #[local] Instance subG_sailGpreS {Σ} : subG sailΣ2 Σ -> sailGpreS2 Σ.
  Proof.
    intros.
    lazymatch goal with
    | H:subG ?xΣ _ |- _ => try unfold xΣ in H
    end.
    repeat match goal with
           | H:subG (gFunctors.app _ _) _ |- _ => apply subG_inv in H; destruct H
           end.
    split; eauto using memΣ_GpreS2, subG_invΣ.
    - clear s2. solve_inG.
    - clear s1. solve_inG.
 Qed.

  Lemma steps_to_erased {σ Γ γ μ δ} (s : Stm Γ σ) {γ' μ' δ' s'}:
    ⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', s' ⟩ ->
    rtc erased_step ([MkConf s δ]%list, (γ,μ)) ([MkConf s' δ']%list, (γ',μ')).
  Proof.
    induction 1; first done.
    refine (rtc_l _ _ _ _ _ IHSteps).
    exists nil.
    refine (step_atomic _ _ _ _ _ nil nil eq_refl eq_refl _).
    by eapply mk_prim_step.
  Qed.

  Lemma steps_to_nsteps {σ Γ γ μ δ} (s : Stm Γ σ) {γ' μ' δ' s'}:
    ⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', s' ⟩ ->
    exists n, language.nsteps n ([MkConf s δ]%list , (γ,μ)) [] ([MkConf s' δ']%list , (γ',μ')).
  Proof.
    induction 1.
    - exists 0. now constructor.
    - destruct IHSteps as [n steps].
      exists (S n).
      refine (language.nsteps_l _ _ _ _ [] _ _ steps).
      refine (step_atomic _ _ _ _ _ nil nil eq_refl eq_refl _).
      now eapply mk_prim_step.
  Qed.

  Lemma own_RegStore_to_map_reg_pointsTos `{sailGS2 Σ} {γ1 γ2 : RegStore} {l : list (sigT 𝑹𝑬𝑮)} :
    NoDup l ->
    ⊢ own (A := regUR) (inG0 := @reg_inG _ sailRegGS2_sailRegGS_left) (@reg_gv_name _ sailRegGS2_sailRegGS_left) (◯ list_to_map (K := SomeReg)
                         (fmap (fun x => match x with existT _ r =>
                                                     pair (existT _ r) (Excl (existT _ (read_register γ1 r)))
                                      end) l)) ∗
      own (A := regUR) (inG0 := @reg_inG _ sailRegGS2_sailRegGS_right) (@reg_gv_name _ sailRegGS2_sailRegGS_right) (◯ list_to_map (K := SomeReg)
                         (fmap (fun x => match x with existT _ r =>
                                                     pair (existT _ r) (Excl (existT _ (read_register γ2 r)))
                                      end) l))
    -∗
      [∗ list] x ∈ l,
        let (x0, r) := (x : sigT 𝑹𝑬𝑮) in reg_pointsTo2 r (read_register γ1 r) (read_register γ2 r).
  Proof.
    iIntros (nodups) "[Hregs1 Hregs2]".
    iInduction l as [|[x r]] "IH".
    - now iFrame.
    - rewrite big_sepL_cons. cbn.
      rewrite (insert_singleton_op (A := exclR (leibnizO SomeVal)) (list_to_map (_ <$> l))  (existT x r) (Excl (existT _ (read_register γ1 r)))).
      rewrite (insert_singleton_op (A := exclR (leibnizO SomeVal)) (list_to_map (_ <$> l))  (existT x r) (Excl (existT _ (read_register γ2 r)))).
      rewrite ?auth_frag_op.
      iPoseProof (own_op reg_gv_name with "Hregs1") as "[Hreg1 Hregs1]".
      iDestruct (own_op reg_gv_name with "Hregs2") as "[Hreg2 Hregs2]".
      iFrame.
      iApply ("IH" with "[%] [$Hregs1] [$Hregs2]").
      + refine (NoDup_cons_1_2 (existT x r) l nodups).
      + destruct (proj1 (NoDup_cons (existT x r) _) nodups) as [notin _].
        refine (not_elem_of_list_to_map_1 _ (existT x r) _).
        rewrite <-list_fmap_compose.
        rewrite (list_fmap_ext _ id).
        now rewrite list_fmap_id.
        now intros i [σ2 r2].
      + destruct (proj1 (NoDup_cons (existT x r) _) nodups) as [notin _].
        refine (not_elem_of_list_to_map_1 _ (existT x r) _).
        rewrite <-list_fmap_compose.
        rewrite (list_fmap_ext _ id).
        now rewrite list_fmap_id.
        now intros i [σ2 r2].
  Qed.

  Definition own_regstore2 `{sailGS2 Σ} (γ1 γ2 : RegStore) : iProp Σ :=
    [∗ list] _ ↦ x ∈ finite.enum (sigT 𝑹𝑬𝑮),
      match x with | existT _ r => reg_pointsTo2 r (read_register γ1 r) (read_register γ2 r) end.

  Inductive NSteps {Γ : PCtx} {σ : Ty} (γ1 : RegStore) (μ1 : Memory) (δ1 : CStore Γ) (s1 : Stm Γ σ) : RegStore -> Memory -> CStore Γ -> Stm Γ σ -> nat -> Prop :=
  | nstep_refl : NSteps γ1 μ1 δ1 s1 γ1 μ1 δ1 s1 0
  | nstep_trans {n} {γ2 γ3 : RegStore} {μ2 μ3 : Memory} {δ2 δ3 : CStore Γ} {s2 s3 : Stm Γ σ} :
      Step γ1 μ1 δ1 γ2 μ2 δ2 s1 s2 -> NSteps γ2 μ2 δ2 s2 γ3 μ3 δ3 s3 n -> NSteps γ1 μ1 δ1 s1 γ3 μ3 δ3 s3 (S n).

  Lemma nsteps_to_steps {Γ : PCtx} {σ : Ty} {γ1 γ2 : RegStore} {μ1 μ2 : Memory} {δ1 δ2 : CStore Γ} {s1 s2 : Stm Γ σ} {n} :
    NSteps γ1 μ1 δ1 s1 γ2 μ2 δ2 s2 n -> Steps γ1 μ1 δ1 s1 γ2 μ2 δ2 s2.
  Proof.
    induction 1; econstructor; eassumption.
  Qed.

  (* TODO: move following 3 to where stm_val_stuck is defined? *)
  Lemma final_val_and_fail_None : forall {Γ τ} (s : Stm Γ τ),
      Final s -> stm_to_val s = None -> stm_to_fail s = None -> False.
  Proof. intros ? ? s. by destruct s. Qed.

  Lemma is_not_final : forall {Γ τ} (s : Stm Γ τ),
      stm_to_val s = None ->
      stm_to_fail s = None ->
      ~ Final s.
  Proof. intros ? ? s ? ? ?. by destruct s. Qed.

  Lemma can_step : forall {Γ τ} (s : Stm Γ τ) γ μ δ,
      ~ Final s ->
      ∃ γ' μ' δ' s', ⟨ γ, μ, δ, s ⟩ ---> ⟨ γ', μ', δ', s' ⟩.
  Proof.
    intros ? ? s **.
    pose proof (progress s) as [|Hprogress];
      first intuition.
    by apply Hprogress.
  Qed.

  Lemma not_stuck_ever {Γ τ} :
    ∀ (e : expr (microsail_lang Γ τ)) σ,
      not_stuck e σ.
  Proof.
    intros [s δ] [γ μ]. unfold not_stuck. cbn. destruct (stm_to_val s) eqn:Es.
    - left. auto.
    - right. apply reducible_not_val. auto.
  Qed.

  Lemma wp2_strong_adequacy {Γ1 Γ2 τ} {s1 s1' : Stm Γ1 τ} (s2 : Stm Γ2 τ)
    {γ1 γ1' : RegStore} (γ2 : RegStore) {μ1 μ1' : Memory} (μ2 : Memory)
    {δ1 δ1' : CStore Γ1} (δ2 : CStore Γ2) {v1 : IVal τ}
    {Q : ∀ `{sailGS2 Σ}, IVal τ -> CStore Γ1 -> IVal τ -> CStore Γ2 -> iProp Σ}
    {φ : Prop}
    (Hsteps: ⟨ γ1, μ1, δ1, s1 ⟩ --->* ⟨ γ1', μ1', δ1', s1' ⟩)
    (Hval : stm_to_val s1' = Some v1) :
    (forall `{sailGS2 Σ},
        ⊢ ((mem_res2 μ1 μ2 ∗ own_regstore2 γ1 γ2 ={⊤}=∗ semWP2 δ1 δ2 s1 s2 Q)
           ∗ (∀ γ2' μ2' δ2' s2' v2,
               ⌜⟨ γ2, μ2, δ2, s2 ⟩ --->* ⟨ γ2', μ2', δ2', s2' ⟩⌝ -∗
               ⌜stm_to_val s2' = Some v2⌝ -∗
               Q v1 δ1' v2 δ2' -∗
               mem_state_interp2 μ1' μ2' ={⊤,∅}=∗ ⌜ φ ⌝)))%I ->
    φ.
  Proof.
    intros Hwp.
    destruct (steps_to_nsteps Hsteps) as [n steps].
    eapply (sbi.pure_soundness (PROP := uPredI (iResUR sailΣ2))).
    eapply (step_fupdN_soundness_gen _ HasLc n n).
    iIntros (Hinv) "Hlc".
    assert (regsmapv1 := RegStore_to_map_valid γ1).
    assert (regsmapv2 := RegStore_to_map_valid γ2).
    iMod (own_alloc (i := reg_pre_inG2_left) ((● RegStore_to_map γ1 ⋅ ◯ RegStore_to_map γ1 ) : regUR)) as (spec_name1) "[H1γ1 H2γ1]";
      first by apply auth_both_valid.
    iMod (own_alloc (i := reg_pre_inG2_right) ((● RegStore_to_map γ2 ⋅ ◯ RegStore_to_map γ2 ) : regUR)) as (spec_name2) "[H1γ2 H2γ2]";
      first by apply auth_both_valid.
    pose proof (memΣ_GpreS2 (Σ := sailΣ2) _) as mGS.
    iMod (mem_init2 (mGS := mGS) μ1 μ2) as (memG) "[Hmem Rmem]".
    set (regsG_left := {| reg_inG := @reg_pre_inG2_left sailΣ2 (@subG_sailGpreS sailΣ2 (subG_refl sailΣ2)); reg_gv_name := spec_name1 |}).
    set (regsG_right := {| reg_inG := @reg_pre_inG2_right sailΣ2 (@subG_sailGpreS sailΣ2 (subG_refl sailΣ2)); reg_gv_name := spec_name2 |}).
    set (sailG_left  := IBleft.SailGS Hinv regsG_left  (@memGS2_memGS_left _ memG)).
    set (sailG_right := IBright.SailGS Hinv regsG_right (@memGS2_memGS_right _ memG)).
    set (gs2 := SailGS2 Hinv (SailRegGS2 (@IBleft.sailGS_sailRegGS _ sailG_left) (@IBright.sailGS_sailRegGS _ sailG_right)) memG).
    iPoseProof (Hwp _ gs2) as "(Hwp & Hφ)".
    iSpecialize ("Hwp" with "[$Rmem H2γ1 H2γ2]").
    { iApply (own_RegStore_to_map_reg_pointsTos (l := finite.enum (sigT 𝑹𝑬𝑮))).
      eapply finite.NoDup_enum.
      iSplitL "H2γ1". iApply "H2γ1". iApply "H2γ2". }
    iMod "Hwp". rewrite /semWP2.
    rewrite mem_state_interp2_mem_inv. iDestruct "Hmem" as "(Hmem1 & Hmem2)".
    iSpecialize ("Hwp" with "[$Hmem2 H1γ2]").
    { now iApply own_RegStore_to_regs_inv. }
    iMod (IBleft.semWP_postcondition steps Hval with "[Hmem1 H1γ1] [Hlc] Hwp") as "H"; eauto.
    { iFrame "Hmem1".
      now iApply (@own_RegStore_to_regs_inv sailΣ2 (@IBleft.sailGS_sailRegGS sailΣ2 sailGS2_sailGS_left) γ1). }
    iAssert (|={∅}▷=>^n |={∅}=> ⌜φ⌝)%I with "[-]" as "H"; last first.
    { destruct n; [done|]. by iApply step_fupdN_S_fupd. }
    iApply (step_fupdN_wand with "H").
    iIntros "H". iMod "H".
    iDestruct "H" as "([Hreg1 Hmem1] & %γ22 & %μ22 & %δ2' & %s2' & %v2 & Hs2 & Hs2' & Hregs2 & Hmem2 & HQ)".
    iPoseProof (mem_state_interp2_mem_inv with "[$Hmem1 $Hmem2]") as "Hmem".
    now iMod ("Hφ" with "Hs2 Hs2' HQ Hmem").
  Qed.

  Lemma wp2_adequate {Γ1 Γ2 τ} (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ)
    {γ1 γ1' γ2 : RegStore} {μ1 μ1' μ2 : Memory}
    {δ1 δ1' : CStore Γ1} {δ2 : CStore Γ2} {v1 v2 : Val τ}
    {Q : ∀ `{sailGS2 Σ}, IVal τ -> CStore Γ1 -> IVal τ -> CStore Γ2 -> iProp Σ}
    {φ : IVal τ -> CStore Γ1 -> IVal τ -> CStore Γ2 -> Prop} :
    (∀ `{sailGS2 Σ}, ∀ v1 δ1 v2 δ2, Q v1 δ1 v2 δ2 -∗ ⌜φ v1 δ1 v2 δ2⌝) ->
    (∀ `{sailGS2 Σ}, ⊢ semWP2 δ1 δ2 s1 s2 Q) ->
    @adequate (microsail_lang Γ1 τ) NotStuck (MkConf s1 δ1) (γ1 , μ1)
             (λ v1 _, ∃ γ2' μ2' s2' v2' δ2',
                 ⟨ γ2, μ2, δ2, s2 ⟩ --->* ⟨ γ2', μ2', δ2', s2' ⟩
                 ∧ stm_to_val s2' = Some v2'
                 ∧ φ (valconf_val v1) (valconf_store v1) v2' δ2').
  Proof.
    intros H Hwp.
    apply (wp_adequacy sailΣ2 _).
    iIntros (Hinv ?).
    assert (regsmapv1 := RegStore_to_map_valid γ1).
    assert (regsmapv2 := RegStore_to_map_valid γ2).
    iMod (own_alloc (i := reg_pre_inG2_left) ((● RegStore_to_map γ1 ⋅ ◯ RegStore_to_map γ1 ) : regUR)) as (spec_name1) "[H1γ1 H2γ1]";
      first by apply auth_both_valid.
    iMod (own_alloc ((● RegStore_to_map γ2 ⋅ ◯ RegStore_to_map γ2 ) : regUR)) as (spec_name2) "[H1γ2 H2γ2]";
      first by apply auth_both_valid.
    pose proof (memΣ_GpreS2 (Σ := sailΣ2) _) as mGS.
    iMod (mem_init2 (mGS := mGS) μ1 μ2) as (memG) "[Hmem Rmem]".
    set (regsG_left := {| reg_inG := @reg_pre_inG2_left sailΣ2 (@subG_sailGpreS sailΣ2 (subG_refl sailΣ2)); reg_gv_name := spec_name1 |}).
    set (regsG_right := {| reg_inG := @reg_pre_inG2_right sailΣ2 (@subG_sailGpreS sailΣ2 (subG_refl sailΣ2)); reg_gv_name := spec_name2 |}).
    set (sailG_left  := IBleft.SailGS Hinv regsG_left  (@memGS2_memGS_left _ memG)).
    set (sailG_right := IBright.SailGS Hinv regsG_right (@memGS2_memGS_right _ memG)).
    set (gs2 := SailGS2 Hinv (SailRegGS2 (@IBleft.sailGS_sailRegGS _ sailG_left) (@IBright.sailGS_sailRegGS _ sailG_right)) memG).
    iExists (λ σ _, regs_inv (srGS := regsG_left) (σ.1) ∗ @IBleft.mem_state_interp _ (@memGS2_memGS_left _ memG) (σ.2))%I, _. cbn.
    iPoseProof (Hwp sailΣ2 gs2) as "H".
    rewrite mem_state_interp2_mem_inv.
    iDestruct "Hmem" as "($ & Hmem2)".
    iSplitR "H1γ2 H2γ2 Rmem Hmem2".
    - now iApply (@own_RegStore_to_regs_inv sailΣ2 regsG_left γ1).
    - rewrite /semWP2.
      iSpecialize ("H" with "[$Hmem2 H1γ2 H2γ2]").
      { now iApply own_RegStore_to_regs_inv. }
      iModIntro.
      rewrite /IBleft.semWP.
      iApply (wp_mono with "H").
      iIntros ([v1'' δ1'']) "(%γ22 & %μ22 & %δ2'' & %s2'' & %v2'' & %Hstep2' & %Hval & Hregs & Hmem & HQ)".
      iExists γ22, μ22, s2'', v2'', δ2''.
      repeat iSplitR; auto.
      now iApply H.
  Qed.

End IrisAdequacy2.
