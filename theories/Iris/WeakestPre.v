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

From iris Require Import
     algebra.auth
     algebra.excl
     algebra.gmap
     program_logic.adequacy
     program_logic.weakestpre
     proofmode.proofmode.

From Katamaran Require Import
     Prelude
     Semantics
     Iris.Resources.

Import ctx.notations.
Import env.notations.
Set Implicit Arguments.

Module Type IrisWeakestPre
  (Import B    : Base)
  (Import PROG : Program B)
  (Import SEM  : Semantics B PROG)
  (Import IPre : IrisPrelims B PROG SEM)
  (Import IP   : IrisParameters B)
  (Import IR   : IrisResources B PROG SEM IPre IP).

  Definition semWP {Σ} `{sG : sailGS Σ} [Γ τ] (δ : CStore Γ) (s : Stm Γ τ)
    (Q : Post Γ τ) : iProp Σ :=
    WP {| conf_stm := s; conf_store := δ |} {{ v, Q (valconf_val v) (valconf_store v) }}.
  Global Arguments semWP {Σ} {sG} [Γ] [τ] δ s%_exp Q%_I.

  Ltac fold_semWP :=
    first
      [ progress
          change_no_check
          (wp NotStuck top
              {| conf_stm := ?s; conf_store := ?δ |}
              (fun v => ?Q (valconf_val v) (valconf_store v)))
        with (semWP δ s Q)
      | progress
          change_no_check
          (wp NotStuck top
              {| conf_stm := ?s; conf_store := ?δ |}
              ?Q)
        with (semWP δ s (fun v δ' => Q (MkValConf _ v δ')));
        try (progress (cbn [valconf_val valconf_store]))
      ].

  Section WeakestPre.

    Context `{sG : sailGS Σ}.

    Lemma semWP_unfold [Γ τ] (δ : CStore Γ) (s : Stm Γ τ)
      (Q : Post Γ τ) :
      semWP δ s Q ⊣⊢
        match stm_to_val s with
        | Some v => |={⊤}=> Q v δ
        | None   => ∀ (γ1 : RegStore) (μ1 : Memory),
                       regs_inv γ1 ∗ mem_state_interp μ1 ={⊤,∅}=∗
                       (∀ (s2 : Stm Γ τ) (δ2 : CStore Γ) (γ2 : RegStore) (μ2 : Memory),
                          ⌜⟨ γ1, μ1, δ , s ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩⌝ ∗ £ 1 ={∅}▷=∗
                          |={∅,⊤}=> (regs_inv γ2 ∗ mem_state_interp μ2) ∗ semWP δ2 s2 Q)
        end.
    Proof.
      unfold semWP. rewrite wp_unfold. unfold wp_pre. cbn.
      destruct (stm_to_val s) eqn:Es; cbn; [easy|].
      apply bi.entails_anti_sym; iIntros "HYP".
      - iIntros (γ μ) "state_inv".
        iSpecialize ("HYP" $! (γ,μ) O nil nil O with "state_inv").
        iMod "HYP" as "[_ HYP]". iModIntro.
        iIntros (s' δ' γ' μ') "(%step & lc)".
        iSpecialize ("HYP" $! (MkConf s' δ') (γ',μ') nil
                       (mk_prim_step (MkConf _ _) step)).
        iMod ("HYP" with "lc") as "HYP". do 2 iModIntro. iMod "HYP". iModIntro.
        now iMod "HYP" as "[$ [$ _]]".
      - iIntros ([γ1 μ1] _ κ _ _) "state_inv".
        iSpecialize ("HYP" $! γ1 μ1 with "state_inv").
        iMod "HYP". iModIntro. iSplitR. iPureIntro. apply reducible_not_val; auto.
        iIntros (c' σ' efs H) "lc". inversion H as [γ γ' μ μ' δ' s' Hs]; subst.
        simpl in Hs.
        iSpecialize ("HYP" $! s' δ' γ' μ' with "[$lc]"); first now iPureIntro.
        iMod "HYP". do 2 iModIntro. iMod "HYP". iModIntro.
        iMod "HYP" as "($ & $)". now cbn.
    Qed.

    Lemma semWP_unfold_nolc [Γ τ] (s : Stm Γ τ)
      (Q : Post Γ τ) (δ : CStore Γ) :
        match stm_to_val s with
        | Some v => |={⊤}=> Q v δ
        | None   => ∀ (γ1 : RegStore) (μ1 : Memory),
                       regs_inv γ1 ∗ mem_state_interp μ1 ={⊤,∅}=∗
                       (∀ (s2 : Stm Γ τ) (δ2 : CStore Γ) (γ2 : RegStore) (μ2 : Memory),
                          ⌜⟨ γ1, μ1, δ , s ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩⌝ ={∅}▷=∗
                          |={∅,⊤}=> (regs_inv γ2 ∗ mem_state_interp μ2) ∗ semWP δ2 s2 Q)
        end ⊢ semWP δ s Q.
    Proof.
      rewrite semWP_unfold.
      destruct (stm_to_val s); first easy.
      iIntros "HYP" (γ1 μ1) "Hres".
      iMod ("HYP" with "Hres") as "HYP".
      iIntros "!>" (s2 δ2 γ2 μ2) "(%Hstep & Hcred)".
      iMod ("HYP" $! _ _ _ _ Hstep) as "HYP".
      repeat iModIntro. iMod "HYP". iMod "HYP".
      now iModIntro.
    Qed.

    Lemma semWP_mono [Γ τ] (s : Stm Γ τ) (P Q : Post Γ τ) (δ : CStore Γ) :
      ⊢ (semWP δ s P -∗ (∀ v δ, P v δ -∗ Q v δ) -∗ semWP δ s Q).
    Proof.
      unfold semWP. iIntros "WP PQ".
      iApply (wp_strong_mono with "WP"); auto.
      iIntros ([v δΓ]) "X"; cbn.
      by iApply "PQ".
    Qed.

    Lemma fupd_semWP {Γ τ} E (δ : CStore Γ) (s : Stm Γ τ) Φ :
      (|={E}=> semWP δ s Φ) ⊢ semWP δ s Φ.
    Proof.
      unfold semWP. iIntros "WP".
      iApply fupd_wp. iMod (fupd_mask_subseteq E) as "Hclose"; first auto.
      iMod "WP". iMod "Hclose" as "_". now iModIntro.
    Qed.

    Lemma semWP_fupd {Γ τ} (δ : CStore Γ) (s : Stm Γ τ) Φ :
      semWP δ s (λ v δ, |={⊤}=> Φ v δ) ⊢ semWP δ s Φ.
    Proof.
      unfold semWP. iIntros "WP".
      now iApply wp_fupd.
    Qed.

    Lemma semWP_val {Γ τ} (v : Val τ) (Q : Post Γ τ) (δ : CStore Γ) :
      semWP δ (stm_val τ v) Q ⊣⊢ (|={⊤}=> Q (inl v) δ).
    Proof. rewrite semWP_unfold. reflexivity. Qed.

    Lemma semWP_fail {Γ τ s} (Q : Post Γ τ) (δ : CStore Γ) :
      semWP δ (stm_fail _ s) Q ⊣⊢ (|={⊤}=> Q (inr s) δ).
    Proof. rewrite semWP_unfold. reflexivity. Qed.

    Lemma semWP_exp {Γ τ} (e : Exp Γ τ) :
      ⊢ ∀ (Q : Post Γ τ) (δ : CStore Γ),
          Q (inl (eval e δ)) δ -∗ semWP δ (stm_exp e) Q.
    Proof.
      iIntros (Q δ1) "P". rewrite <-semWP_unfold_nolc. cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro.
      iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      do 3 iModIntro. iMod "Hclose" as "_". iModIntro.
      iFrame "state_inv". by iApply semWP_val.
    Qed.

    Lemma semWP_block {Γ τ Δ} (δΔ : CStore Δ) (s : Stm (Γ ▻▻ Δ) τ) :
      ⊢ ∀ (Q : Post Γ τ) (δ : CStore Γ),
          semWP (δ ►► δΔ) s (fun v δ1 => Q v (env.drop Δ δ1)) -∗
          semWP δ (stm_block δΔ s) Q.
    Proof.
      iIntros (Q). iRevert (δΔ s). iLöb as "IH". iIntros (δΔ k δΓ) "WPk".
      rewrite (semWP_unfold _ (stm_block δΔ k)). cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2) "(%step & Hcred)". destruct (smallinvstep step); cbn.
      - rewrite !semWP_val. rewrite env.drop_cat. by iFrame.
      - rewrite !semWP_fail. rewrite env.drop_cat. by iFrame.
      - rewrite (semWP_unfold _ k). rewrite (stm_val_stuck H).
        iSpecialize ("WPk" $! γ1 μ1 with "state_inv").
        iMod "Hclose". iMod "WPk" as "WPk".
        iSpecialize ("WPk" $! _ _ _ _ with "[$Hcred]"); first easy.
        iMod "WPk". iModIntro. iModIntro. iModIntro.
        iMod "WPk". iMod "WPk" as "[$ wps]".
        by iApply "IH".
    Qed.

    Lemma semWP_call_frame {Γ τ Δ} (δΔ : CStore Δ) (s : Stm Δ τ) :
      ⊢ ∀ (Q : Post Γ τ) (δ : CStore Γ),
          semWP δΔ s (fun v _ => Q v δ) -∗
          semWP δ (stm_call_frame δΔ s) Q.
    Proof.
      iIntros (Q δΓ). iRevert (δΔ s). iLöb as "IH". iIntros (δΔ s) "WPs".
      rewrite (semWP_unfold _ (stm_call_frame δΔ s)). cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2) "(%step & Hcred)". destruct (smallinvstep step); cbn.
      - rewrite !semWP_val. by iFrame.
      - rewrite !semWP_fail. by iFrame.
      - rewrite (semWP_unfold _ s). rewrite (stm_val_stuck H).
        iSpecialize ("WPs" $! γ1 μ1 with "state_inv").
        iMod "Hclose". iMod "WPs".
        iSpecialize ("WPs" $! _ _ _ _ with "[$Hcred]"); first easy.
        iMod "WPs". iModIntro. iModIntro. iModIntro.
        iMod "WPs". iMod "WPs" as "[$ wps]".
        now iApply "IH".
    Qed.

    Lemma semWP_call_inline_later {Γ τ Δ} (f : 𝑭 Δ τ) (es : NamedEnv (Exp Γ) Δ) :
      ⊢ ∀ (Q : Post Γ τ) (δΓ : CStore Γ),
          ▷ semWP (evals es δΓ) (FunDef f) (fun vτ _ => Q vτ δΓ) -∗
          semWP δΓ (stm_call f es) Q.
    Proof.
      iIntros (Q δΓ) "wpbody". rewrite <-(semWP_unfold_nolc (stm_call f es)). cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      iModIntro. iModIntro. iModIntro. iMod "Hclose" as "_". iModIntro.
      iFrame "state_inv". by iApply semWP_call_frame.
    Qed.

    Lemma semWP_call_inline {Γ τ Δ} (f : 𝑭 Δ τ) (es : NamedEnv (Exp Γ) Δ) :
      ⊢ ∀ (Q : Post Γ τ) (δΓ : CStore Γ),
          semWP (evals es δΓ) (FunDef f) (fun vτ _ => Q vτ δΓ) -∗
          semWP δΓ (stm_call f es) Q.
    Proof. iIntros (Q δΓ) "wpbody". by iApply semWP_call_inline_later. Qed.

    Lemma semWP_bind {Γ τ σ} (s : Stm Γ σ) (k : Val σ → Stm Γ τ) :
      ⊢ ∀ (Q : Post Γ τ) (δ : CStore Γ),
          semWP δ s (fun v δ => semWP δ (lift_cnt k v) Q) -∗ semWP δ (stm_bind s k) Q.
    Proof.
      iIntros (Q). iRevert (s). iLöb as "IH". iIntros (s δ) "WPs".
      rewrite (semWP_unfold _ (stm_bind s k)). cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2) "(%step & Hcred)". destruct (smallinvstep step); cbn.
      - rewrite !semWP_val. do 3 iModIntro. iMod "Hclose". iMod "WPs". by iFrame.
      - rewrite !semWP_fail. do 3 iModIntro. iMod "Hclose". iMod "WPs". by iFrame.
      - rewrite (semWP_unfold _ s). rewrite (stm_val_stuck H).
        iSpecialize ("WPs" $! γ1 μ1 with "state_inv").
        iMod "Hclose". iMod "WPs".
        iSpecialize ("WPs" $! _ _ _ _ with "[$Hcred]"); first easy.
        iMod "WPs". iModIntro. iModIntro. iModIntro.
        iMod "WPs". iMod "WPs" as "[$ wps]".
        by iApply "IH".
    Qed.

    Lemma semWP_let {Γ τ x σ} (s : Stm Γ σ) (k : Stm (Γ ▻ x∷σ) τ) :
      ⊢ ∀ (Q : Post Γ τ) (δ : CStore Γ),
          semWP δ s (fun v1 δ1 => match v1 with
                                | inl v1 => semWP δ1.[x∷σ ↦ v1] k (fun v2 δ2 => Q v2 (env.tail δ2))
                                | inr m1 => semWP δ1 (of_ival (inr m1)) Q
                                end) -∗
          semWP δ (let: x ∷ σ := s in k) Q.
    Proof.
      iIntros (Q δΓ) "WPs". rewrite <-(semWP_unfold_nolc (stm_let x σ s k)). cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      do 3 iModIntro. iMod "Hclose" as "_". iModIntro. iFrame "state_inv".
      iApply semWP_bind. iApply (semWP_mono with "WPs"). iIntros ([v|m] δ) "wpk".
      - simpl. iApply (semWP_block [env].[_∷_ ↦ v]). iApply (semWP_mono with "wpk").
        clear. iIntros (? δ) "HQ". by destruct (env.view δ).
      - simpl. done.
    Qed.

    Lemma semWP_seq {Γ τ σ} (s : Stm Γ σ) (k : Stm Γ τ) :
      ⊢ ∀ (Q : Post Γ τ) (δ : CStore Γ),
          semWP δ s (λ v δ, match v with
                          | inl _ => semWP δ k Q
                          | inr m => semWP δ (of_ival (inr m)) Q
                          end) -∗ semWP δ (s;;k) Q.
    Proof.
      iIntros (Q δ) "WPs". rewrite <-(semWP_unfold_nolc (stm_seq s k)). cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      do 3 iModIntro. iMod "Hclose" as "_". iModIntro. iFrame "state_inv".
      iApply semWP_bind. iApply (semWP_mono with "WPs"). iIntros ([v|m] δ').
      - simpl. iIntros "$".
      - simpl. now iIntros "H".
    Qed.

    Lemma semWP_assertk {Γ τ} (e1 : Exp Γ ty.bool) (e2 : Exp Γ ty.string) (k : Stm Γ τ) :
      ⊢ ∀ (Q : Post Γ τ) (δ : CStore Γ),
          (⌜eval e1 δ = true⌝ → semWP δ k Q) -∗
          (⌜eval e1 δ = false⌝ → semWP δ (fail (eval e2 δ)) Q) -∗
          semWP δ (stm_assertk e1 e2 k) Q.
    Proof.
      iIntros (Q δ) "WPtrue WPfalse". rewrite <-(semWP_unfold_nolc (stm_assertk e1 e2 k)). cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      do 3 iModIntro. iMod "Hclose" as "_". iModIntro. iFrame "state_inv".
      destruct eval; [by iApply "WPtrue"|by iApply "WPfalse"].
    Qed.

    Lemma semWP_read_register {Γ τ} (reg : 𝑹𝑬𝑮 τ) :
      ⊢ ∀ (Q : Post Γ τ) (δ : CStore Γ),
          (∃ v : Val τ, reg_pointsTo reg v ∗ (reg_pointsTo reg v -∗ Q (inl v) δ)) -∗
          semWP δ (stm_read_register reg) Q.
    Proof.
      iIntros (Q δ) "[% [Hreg HP]]". rewrite <-semWP_unfold_nolc. cbn.
      iIntros (γ1 μ1) "[Hregs Hmem]".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro. iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      do 3 iModIntro. iMod "Hclose" as "_". iModIntro.
      iDestruct (@reg_valid with "Hregs Hreg") as %->.
      iSpecialize ("HP" with "Hreg"). iFrame "Hregs Hmem". by iApply semWP_val.
    Qed.

    Lemma semWP_write_register {Γ τ} (reg : 𝑹𝑬𝑮 τ) (e : Exp Γ τ) :
      ⊢ ∀ (Q : Post Γ τ) (δ : CStore Γ),
          (∃ v : Val τ, reg_pointsTo reg v ∗ (reg_pointsTo reg (eval e δ) -∗ Q (inl (eval e δ)) δ)) -∗
          semWP δ (stm_write_register reg e) Q.
    Proof.
      iIntros (Q δ) "[% [Hreg HP]]". rewrite <-semWP_unfold_nolc. cbn.
      iIntros (γ1 μ1) "[Hregs Hmem]".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iMod (reg_update γ1 reg v (eval e δ) with "Hregs Hreg") as "[Hregs Hreg]".
      iModIntro. iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      do 3 iModIntro. iMod "Hclose" as "_". iModIntro.
      iSpecialize ("HP" with "Hreg"). iFrame "Hregs Hmem". by iApply semWP_val.
    Qed.

    Lemma semWP_assign {Γ τ x} (xInΓ : x∷τ ∈ Γ) (s : Stm Γ τ) :
      ⊢ ∀ (Q : Post Γ τ) (δ : CStore Γ),
          semWP δ s (λ (a : IVal τ) (δ0 : CStore Γ), match a with
                                                   | inl a => Q (inl a) (δ0 ⟪ x ↦ a ⟫)
                                                   | inr m => Q (inr m) δ0
                                                   end) -∗
          semWP δ (stm_assign x s) Q.
    Proof.
      iIntros (Q). iRevert (s). iLöb as "IH". iIntros (s δ) "WPs".
      rewrite (semWP_unfold _ (stm_assign x s)). cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2) "(%step & Hcred)". destruct (smallinvstep step); cbn.
      - rewrite !semWP_val. by iFrame.
      - rewrite !semWP_fail. by iFrame.
      - rewrite (semWP_unfold _ s). rewrite (stm_val_stuck H).
        iSpecialize ("WPs" $! γ1 μ1 with "state_inv").
        iMod "Hclose". iMod "WPs".
        iSpecialize ("WPs" $! _ _ _ _ with "[$Hcred]"); first easy.
        iMod "WPs". iModIntro. iModIntro. iModIntro.
        iMod "WPs". iMod "WPs" as "[$ wps]".
        by iApply "IH".
    Qed.

    Lemma semWP_pattern_match {Γ τ σ} (s : Stm Γ σ) (pat : Pattern σ)
      (rhs : ∀ pc : PatternCase pat, Stm (Γ ▻▻ PatternCaseCtx pc) τ) :
      ⊢ ∀ (Q : Post Γ τ) (δ : CStore Γ),
      semWP δ s
        (fun vσ δ1 =>
           match vσ with
           | inl vσ =>
               let (pc,δpc) := pattern_match_val pat vσ in
               semWP (δ1 ►► δpc) (rhs pc)
                 (fun vτ δ2 => Q vτ (env.drop (PatternCaseCtx pc) δ2))
           | inr m => |={⊤}=> Q (inr m) δ1
           end) -∗
      semWP δ (stm_pattern_match s pat rhs) Q.
    Proof.
      iIntros (Q δΓ) "WPs". rewrite <-(semWP_unfold_nolc (stm_pattern_match s pat rhs)). cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      do 3 iModIntro. iMod "Hclose" as "_". iModIntro. iFrame "state_inv".
      iApply semWP_bind. iApply (semWP_mono with "WPs"). iIntros ([v|m] δ) "WPrhs".
      - simpl. destruct pattern_match_val as [pc δpc]. iApply (semWP_block δpc).
        iApply (semWP_mono with "WPrhs"). iIntros ([v'|m'] ?) "H"; simpl; auto.
      - simpl. now rewrite semWP_fail.
    Qed.

    Lemma semWP_foreign {Γ Δ τ} {f : 𝑭𝑿 Δ τ} {es : NamedEnv (Exp Γ) Δ} {Q δ} :
      ⊢ (∀ γ μ,
            (regs_inv γ ∗ mem_state_interp μ)
            ={⊤,∅}=∗
        (∀ res γ' μ' ,
          ⌜ ForeignCall f (evals es δ) res γ γ' μ μ' ⌝
           ={∅}▷=∗
           |={∅,⊤}=> (regs_inv γ' ∗ mem_state_interp μ') ∗
                      semWP δ (match res with inr v => stm_val _ v
                                       | inl s => stm_fail _ s
                             end) Q)) -∗
        semWP δ (stm_foreign f es) Q.
    Proof.
      iIntros "H". rewrite <-semWP_unfold_nolc. cbn. iIntros (γ1 μ1) "state_inv".
      iMod ("H" $! γ1 μ1 with "[$]") as "H". iModIntro.
      iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn. by iApply "H".
    Qed.

    Lemma semWP_debugk {Γ τ} (s : Stm Γ τ) :
      ⊢ ∀ Q δ, semWP δ s Q -∗ semWP δ (stm_debugk s) Q.
    Proof.
      iIntros (Q δ) "WPs". rewrite <-(semWP_unfold_nolc (stm_debugk s)). cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      do 3 iModIntro. iMod "Hclose" as "_". iModIntro. now iFrame "state_inv".
    Qed.

    Lemma semWP_lemmak {Γ τ} {Δ} (l : 𝑳 Δ) (es : NamedEnv (Exp Γ) Δ) (s : Stm Γ τ) :
      ⊢ ∀ Q δ, semWP δ s Q -∗ semWP δ (stm_lemmak l es s) Q.
    Proof.
      iIntros (Q δ) "WPs". rewrite <-(semWP_unfold_nolc (stm_lemmak l es s)). cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      do 3 iModIntro. iMod "Hclose" as "_". iModIntro. now iFrame "state_inv".
    Qed.

    Lemma semWP_step {Γ τ} {s1 s2 : Stm Γ τ} {γ1 γ2 : RegStore} {μ1 μ2 : Memory}
                     {δ1 δ2 : CStore Γ} {Q : Post Γ τ} :
      ⟨ γ1, μ1, δ1, s1 ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ ->
      regs_inv γ1 ∗ mem_state_interp μ1 -∗
      £ 1 -∗
      semWP δ1 s1 Q ={⊤,∅}=∗
      ▷ |={∅,⊤}=> (regs_inv γ2 ∗ mem_state_interp μ2) ∗ semWP δ2 s2 Q.
    Proof.
      iIntros (Hstep) "Hres Hlc Hwp".
      rewrite semWP_unfold.
      rewrite (stm_val_stuck Hstep).
      iMod ("Hwp" with "Hres [$Hlc]") as "H"; first eauto.
      iMod "H". iModIntro. iModIntro. now iMod "H".
    Qed.

    #[local] Lemma list_singleton_app_cons :
      ∀ {A} l1 l2 (a b : A), ([a] = l1 ++ b :: l2)%list -> a = b ∧ l1 = []%list ∧ l2 = []%list.
    Proof.
      intros A l1. induction l1 as [|e1 l1 IHl1]; simpl;
        intros l2 a b Happ.
      now inversion Happ.
      inversion Happ; subst.
      exfalso. eapply app_cons_not_nil. eauto.
    Qed.

    Lemma step_to_Step {Γ τ} {n : nat} {s1 s2 : Stm Γ τ} {γ1 γ2 : RegStore} {μ1 μ2 : Memory}
                     {δ1 δ2 : CStore Γ} κ :
      step ([MkConf s1 δ1]%list, (γ1, μ1)) κ ([MkConf s2 δ2]%list, (γ2, μ2)) ->
      ⟨ γ1, μ1, δ1, s1 ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩.
    Proof.
      intros H.
      destruct H as [[] [] [] [] ? t1 t2 Hρ1 Hρ2 Hprim].
      destruct Hprim as [? ? ? ? ? ? H]. cbn in H.
      inversion Hρ1; inversion Hρ2; subst.
      inversion Hρ1 as [Hl1]; inversion Hρ2 as [Hl2].
      apply list_singleton_app_cons in Hl1 as (Hl1 & -> & ->).
      apply list_singleton_app_cons in Hl2 as (Hl2 & ?).
      inversion_clear Hl1. inversion_clear Hl2.
      done.
    Qed.

    Lemma semWP_preservation {Γ τ} {n : nat} {s1 s2 : Stm Γ τ} {γ1 γ2 : RegStore} {μ1 μ2 : Memory}
                     {δ1 δ2 : CStore Γ} {Q : Post Γ τ} κ :
      language.nsteps n ([MkConf s1 δ1]%list , (γ1,μ1)) κ ([MkConf s2 δ2]%list , (γ2,μ2)) ->
      regs_inv γ1 ∗ mem_state_interp μ1 -∗
      £ n -∗
      semWP δ1 s1 Q ={⊤,∅}=∗
      |={∅}▷=>^n |={∅,⊤}=> (regs_inv γ2 ∗ mem_state_interp μ2) ∗ semWP δ2 s2 Q.
    Proof.
      revert s1 s2 γ1 γ2 μ1 μ2 δ1 δ2 Q κ.
      induction n as [|n IHn];
        intros s1 s2 γ1 γ2 μ1 μ2 δ1 δ2 Q κ;
        iIntros (Hstep) "Hres Hlc Hwp".
      - inversion_clear Hstep; iFrame "Hres Hwp".
        now iApply fupd_mask_subseteq.
      - inversion_clear Hstep.
        rewrite lc_succ. iDestruct "Hlc" as "[Hlc1 Hlc2]".
        destruct H as [? ? ? ? ? ? ? Heq ? Hprim].
        destruct Hprim.
        inversion Heq as [Heq']; apply list_singleton_app_cons in Heq' as (? & ? & ?); subst.
        simpl in *.
        iPoseProof (semWP_step with "Hres Hlc1 Hwp") as "H"; first eauto.
        iMod "H". iModIntro. iModIntro. iModIntro. iMod "H".
        iDestruct "H" as "(Hres & Hwp)".
        iApply (IHn with "Hres Hlc2 Hwp"); eauto.
    Qed.

    Lemma semWP_postcondition {Γ τ} {n : nat} {s1 s2 : Stm Γ τ} {γ1 γ2 : RegStore} {μ1 μ2 : Memory}
                     {δ1 δ2 : CStore Γ} {v : IVal τ} {Q : Post Γ τ} κ :
      language.nsteps n ([MkConf s1 δ1]%list , (γ1,μ1)) κ ([MkConf s2 δ2]%list , (γ2,μ2)) ->
      stm_to_val s2 = Some v ->
      regs_inv γ1 ∗ mem_state_interp μ1 -∗
      £ n -∗
      semWP δ1 s1 Q ={⊤,∅}=∗
      |={∅}▷=>^n |={∅,⊤}=> (regs_inv γ2 ∗ mem_state_interp μ2) ∗ Q v δ2.
    Proof.
      iIntros (Hstep Hs2) "Hres Hlc Hwp".
      iMod (semWP_preservation with "Hres Hlc Hwp") as "H"; first eauto.
      iModIntro. iApply (step_fupdN_wand with "H").
      iIntros "H". iMod "H" as "($ & H)".
      destruct (stm_to_val_Some_cases Hs2) as [(v' & -> & ->)|(m & -> & ->)].
      - now rewrite semWP_val.
      - now rewrite semWP_fail.
    Qed.

  End WeakestPre.

  Module wptactics.
    (* Keep the kits folded: Exp constructors carry them as arguments. *)
    Ltac kEval :=
      match goal with
      | |- environments.envs_entails ?ctx (semWP ?store ?s ?post) =>
          let s' := eval compute - [Val typedeclkit typedenotekit typedefkit] in s in
          let store' := eval compute - [Val typedeclkit typedenotekit typedefkit] in store in
          change_no_check (environments.envs_entails ctx (semWP store' s' post))
      end.

    Ltac kStep :=
      match goal with
      | |- environments.envs_entails ?ctx (semWP ?store ?stm ?post) =>
          match stm with
          | stm_val ?τ ?v => iApply semWP_val
          | stm_exp ?e => iApply (semWP_exp e)
          | stm_let ?x ?τ ?s1 ?s2 => iApply (semWP_let s1 s2)
          | stm_pattern_match ?scrut ?pat ?rhs =>
              iApply (semWP_pattern_match scrut pat rhs)
          | match ?x with _ => _ end => destruct x eqn:?
          end
      end.
  End wptactics.

End IrisWeakestPre.
