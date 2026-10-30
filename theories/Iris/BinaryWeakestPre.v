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
     Sep.Logic
     Signature
     SmallStep.Step
     BinaryResources.

Import ctx.notations.
Import env.notations.

Set Implicit Arguments.

(* The following three modules define the Iris instance of the program logic
   depending solely on the operational semantics (through IrisBase) and the
   user-defined predicates (in IrisPredicates), but without depending on a
   Specification module. The program logic rules of this subset are implemented
   in IrisSignatureRules, which is combined with IrisPredicates to form
   IrisInstance.

   This split allows us to use multiple different specifications with the same
   Iris model, so that the resulting triples can be combined. This is important
   particularly when combining specifications of universal contracts for unknown
   code with known code verifications, e.g. as in the RiscvPmp.BlockVerification
   proofs. *)

Module Type IrisPredicates2
  (Import GLOBAL : GlobalState)
  (Import SIG    : Signature GLOBAL)
  (Import PROG   : Program GLOBAL)
  (Import SEM    : Semantics GLOBAL PROG)
  (Import IPre   : IrisPrelims GLOBAL PROG SEM)
  (IBleft : IrisBase GLOBAL PROG SEM IPre)
  (IBright : IrisBase GLOBAL PROG SEM IPre)
  (Import IB     : IrisBase2 GLOBAL PROG SEM IPre IBleft IBright).
  Parameter luser_inst2 : forall `{sRG : sailRegGS2 Σ} `{invGS Σ} `{mG : memGS2 Σ} (p : 𝑯) (ts : Env Val (𝑯_Ty p)), iProp Σ.
  Parameter lduplicate_inst2 : forall `{sRG : sailRegGS2 Σ} `{invGS Σ} {mG : memGS2 Σ} (p : 𝑯) (ts : Env Val (𝑯_Ty p)),
      is_duplicable p = true ->
      luser_inst2 ts ⊢ luser_inst2 ts ∗ luser_inst2 ts.

End IrisPredicates2.

Module IrisBinaryWP
  (Import GLOBAL : GlobalState)
  (Import SIG    : Signature GLOBAL)
  (Import PROG   : Program GLOBAL)
  (Import SEM    : Semantics GLOBAL PROG)
  (Import IPre : IrisPrelims GLOBAL PROG SEM)
  (IBleft : IrisBase GLOBAL PROG SEM IPre)
  (IBright : IrisBase GLOBAL PROG SEM IPre)
  (Import IB2    : IrisBase2 GLOBAL PROG SEM IPre IBleft IBright)
  (Import IPred  : IrisPredicates2 GLOBAL SIG PROG SEM IPre IBleft IBright IB2).

  Section WithSailGS2.
    Context `{sG : sailGS2 Σ}.

    #[export] Program Instance PredicateDefIProp : PredicateDef (iProp Σ) :=
      {| lptsreg σ r v        := reg_pointsTo2 r v v;
        luser p ts           := luser_inst2 ts;
        lduplicate p ts Hdup := lduplicate_inst2 ts Hdup
      |}.

    (* Declare necessary OFE instances. Don't use them directly, they will be
     resolved when needed. *)
    Canonical Structure PCtxO     := leibnizO PCtx.
    Canonical Structure TyO       := leibnizO Ty.
    Canonical Structure CStoreO Γ := leibnizO (CStore Γ).
    Canonical Structure StmO Γ τ  := leibnizO (Stm Γ τ).
    Canonical Structure ValO τ    := leibnizO (Val τ).
    Canonical Structure IValO τ   := leibnizO (IVal τ).

    Definition Post2 Γ1 Γ2 τ :=
      IVal τ -> CStore Γ1 -> IVal τ -> CStore Γ2 -> iProp Σ.
    Canonical Structure Post2O Γ1 Γ2 τ := leibnizO (Post2 Γ1 Γ2 τ).

    Definition Wp2 Γ1 Γ2 τ :=
      CStore Γ1 -d> CStore Γ2 -d>
        Stm Γ1 τ -d> Stm Γ2 τ -d>
        Post2 Γ1 Γ2 τ -d>
        iProp Σ.

    (* IDEA: borrow idea of Atomic of Iris. When s1 and s2 are atomic, they are
           allowed to open the invariants and close them.
           Some useful resources to look at:
           - iris/program_logic/weakestpre.v > wp_atomic
           - iris/program_logic/atomic.v > atomic_wp_inv

           It might be that some restrictions that apply to wp2 are only
           exposed at the ISA level (for example, MMIO interactions ≡ effects)

           How does PMP come into play? Can we capture non-interferene of U-mode
           data through invariants? (I would assume so)
     *)
    Ltac f_equiv_more_arities := match goal with
                                 | H:_ ?f ?g |- ?R (?f ?x ?y ?z1) (?g ?x ?y ?z1) => solve [ simple apply H ]
                                 | H:_ ?f ?g |- ?R (?f ?x ?y ?z1 ?z2) (?g ?x ?y ?z1 ?z2) => solve [ simple apply H ]
                                 | H:_ ?f ?g |- ?R (?f ?x ?y ?z1 ?z2 ?z3) (?g ?x ?y ?z1 ?z2 ?z3) => solve [ simple apply H ]
                                 end.

    Ltac solve_contractive_more_arities := solve_proper_core ltac:(fun _ => first [ f_contractive | f_equiv | f_equiv_more_arities]).

    Import SmallStepNotations.

    Definition semWP2 {Γ1 Γ2 τ} : Wp2 Γ1 Γ2 τ :=
      let sG_left    := sailGS2_sailGS_left in
      let srGS_right := sailRegGS2_sailRegGS_right in
      let mG_right   := memGS2_memGS_right in
      (λ δ1 δ2 s1 s2 Q,
        ∀ γ21 μ21,
          regs_inv (srGS := srGS_right) γ21 ∗ IBright.mem_state_interp (mG := mG_right) μ21 -∗
            IBleft.semWP (sG := sG_left) δ1 s1 (λ v1 δ1',
              ∃ γ22 μ22 δ2' s2' v2,
                ⌜⟨ γ21, μ21, δ2, s2 ⟩ --->* ⟨ γ22, μ22, δ2', s2' ⟩⌝
                ∗ ⌜stm_to_val s2' = Some v2⌝
                ∗ regs_inv (srGS := srGS_right) γ22 ∗ IBright.mem_state_interp (mG := mG_right) μ22
                ∗ Q v1 δ1' v2 δ2'
          ))%I.

    Lemma semWP2_mono [Γ1 Γ2 τ] (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ)
      (Q1 Q2 : Post2 Γ1 Γ2 τ) (δ1 : CStore Γ1) (δ2 : CStore Γ2) :
      ⊢ semWP2 δ1 δ2 s1 s2 Q1 -∗ (∀ v1 δ1 v2 δ2, Q1 v1 δ1 v2 δ2 -∗ Q2 v1 δ1 v2 δ2) -∗ semWP2 δ1 δ2 s1 s2 Q2.
    Proof.
      iIntros "Hwp H". rewrite /semWP2.
      iIntros (γ21 μ21) "Hres". iSpecialize ("Hwp" with "Hres").
      iApply (IBleft.semWP_mono with "Hwp").
      iIntros (v1 δ1') "(%γ22 & %μ22 & %δ2' & %s2' & %v2 & Hk)".
      iExists γ22, μ22, δ2', s2', v2. iDestruct "Hk" as "($ & $ & $ & $ & HQ1)".
      by iApply ("H" with "HQ1").
    Qed.

    Lemma semWP2_val_1 {Γ1 Γ2 τ} (v1 : Val τ) (v2 : Val τ) (Q : Post2 Γ1 Γ2 τ) :
      ∀ δ1 δ2,
        (|={⊤}=> Q (inl v1) δ1 (inl v2) δ2) ⊢ semWP2 δ1 δ2 (stm_val τ v1) (stm_val τ v2) Q.
    Proof.
      iIntros (δ1 δ2) "HQ". rewrite /semWP2. iIntros (γ21 μ21) "Hres".
      rewrite IBleft.semWP_val. iMod "HQ". iModIntro.
      iExists γ21, μ21, δ2, (stm_val _ v2), (inl v2).
      iFrame "HQ Hres". iPureIntro. split. apply step_refl. auto.
    Qed.

    (* TODO: doesn't hold (resources!) *)
    Lemma semWP2_val {Γ1 Γ2 τ} (v1 : Val τ) (v2 : Val τ) (Q : Post2 Γ1 Γ2 τ) :
      forall δ1 δ2,
        semWP2 δ1 δ2 (stm_val τ v1) (stm_val τ v2) Q ⊣⊢ |={⊤}=> Q (inl v1) δ1 (inl v2) δ2.
    Abort.

    Lemma semWP2_fail {Γ1 Γ2 τ s1 s2} (Q : Post2 Γ1 Γ2 τ) :
      ∀ δ1 δ2,
        (|={⊤}=> Q (inr s1) δ1 (inr s2) δ2) ⊢ semWP2 δ1 δ2 (stm_fail _ s1) (stm_fail _ s2) Q. 
    Proof.
      iIntros (δ1 δ2) "HQ".
      rewrite /semWP2. iIntros (γ21 μ21) "Hres". iApply IBleft.semWP_fail.
      iMod "HQ". iModIntro. iExists γ21, μ21, δ2, (stm_fail _ s2), (inr s2).
      iSplitR. iPureIntro. apply step_refl.
      iSplitR. auto. iFrame "HQ Hres".
    Qed.

    Lemma fupd_semWP2 {Γ1 Γ2 τ} E (δA : CStore Γ1) (δB : CStore Γ2)
      (eA : Stm Γ1 τ) (eB : Stm Γ2 τ) Φ : 
      (|={E}=> semWP2 δA δB eA eB Φ) ⊢ semWP2 δA δB eA eB Φ.
    Proof.
      iIntros "WP". rewrite /semWP2. iIntros (γ21 μ21) "Hres".
      iApply (IBleft.fupd_semWP E). iMod "WP". iModIntro.
      by iApply "WP".
    Qed.

    Lemma semWP2_frame_l {Γ1 Γ2 τ} (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ)
      (δ1 : CStore Γ1) (δ2 : CStore Γ2) (POST : Post2 Γ1 Γ2 τ)
      (R : iProp Σ) :
      R ∗ semWP2 δ1 δ2 s1 s2 POST -∗
      semWP2 δ1 δ2 s1 s2 (λ v1 δ1 v2 δ2, R ∗ POST v1 δ1 v2 δ2).
    Proof.
      iIntros "(HR & H)". rewrite /semWP2. iIntros (γ21 μ21) "Hres".
      iSpecialize ("H" with "Hres"). iApply (IBleft.semWP_mono with "H").
      iIntros (v1 δ1') "(%γ22 & %μ22 & %δ2' & %s2' & %v2 & H)".
      iExists γ22, μ22, δ2', s2', v2. now iDestruct "H" as "($ & $ & $ & $ & $)".
    Qed.

    Ltac discriminate_step :=
      match goal with
      | H: ⟨ ?γ, ?μ, ?δ, stm_fail ?τ ?m ⟩ ---> ⟨ ?γ', ?μ', ?δ', ?s ⟩ |- _ =>
          inversion H
      | H: ⟨ ?γ, ?μ, ?δ, stm_val ?τ ?v ⟩ ---> ⟨ ?γ', ?μ', ?δ', ?s ⟩ |- _ =>
          inversion H
      end.

    Ltac close_later H :=
      iMod (fupd_mask_subseteq empty) as H; first set_solver.

    Ltac stm_val_fail_stuck :=
      repeat match goal with
        | H: ⟨ ?γ, ?μ, ?δ, ?s ⟩ ---> ⟨ ?γ', ?μ', ?δ', ?s' ⟩
          |- context[stm_to_val ?s] => rewrite (stm_val_stuck H)
        | H: ⟨ ?γ, ?μ, ?δ, ?s ⟩ ---> ⟨ ?γ', ?μ', ?δ', ?s' ⟩
          |- context[stm_to_fail ?s] => rewrite (stm_fail_stuck H)
        end.

    Lemma semWP2_exp {Γ1 Γ2 τ} (Φ : Post2 Γ1 Γ2 τ) eA eB δA δB :
      Φ (inl (eval eA δA)) δA (inl (eval eB δB)) δB ⊢ semWP2 δA δB (stm_exp eA) (stm_exp eB) Φ.
    Proof.
      iIntros "HΦ". rewrite /semWP2. iIntros (γ21 μ21) "Hres".
      iApply IBleft.semWP_exp. iExists γ21, μ21, δB, (stm_val _ (eval eB δB)), (inl (eval eB δB)).
      iFrame "HΦ Hres". iPureIntro. split; auto. eapply step_trans.
      constructor. apply step_refl.
    Qed.

    (* TODO: move somewhere else? *)
    Ltac semWP2_stuck_progress :=
      repeat match goal with
        | H: ⟨ ?γ1, ?μ1, ?δ1, ?s ⟩ ---> ⟨ ?γ2, ?μ2, ?δ2, ?s' ⟩
          |- context[stm_to_val ?s] =>
            rewrite (stm_val_stuck H)
        | H: ⟨ ?γ1, ?μ1, ?δ1, ?s ⟩ ---> ⟨ ?γ2, ?μ2, ?δ2, ?s' ⟩
          |- context[stm_to_fail ?s] =>
            rewrite (stm_fail_stuck H)
        end.

    Lemma not_final_expanded : ∀ {Γ τ} (s : Stm Γ τ),
        ~ Final s -> stm_to_val s = None ∧ stm_to_fail s = None.
    Proof.
      intros Γ τ s H; unfold Final in H; destruct s; auto; contradiction.
    Qed.

    Lemma semWP2_call_inline_later {Γ1 Γ2 τ Δ} (f1 f2 : 𝑭 Δ τ)
      (es1 : NamedEnv (Exp Γ1) Δ) (es2 : NamedEnv (Exp Γ2) Δ) :
      ⊢ ∀ (Q : Post2 Γ1 Γ2 τ) (δΓ1 : CStore Γ1) (δΓ2 : CStore Γ2),
          ▷ semWP2 (evals es1 δΓ1) (evals es2 δΓ2) (FunDef f1) (FunDef f2) (λ v1τ _ v2τ _, Q v1τ δΓ1 v2τ δΓ2) -∗
          semWP2 δΓ1 δΓ2 (stm_call f1 es1) (stm_call f2 es2) Q.
    Proof.
      iIntros (Q δΓ1 δΓ2) "H". rewrite /semWP2. iIntros (γ21 μ21) "Hres".
      iApply IBleft.semWP_call_inline_later. iModIntro. iSpecialize ("H" with "Hres").
      iApply (IBleft.semWP_mono with "H").
      iIntros (v1 δ1') "(%γ22 & %μ22 & %δ2' & %s2' & %v2 & %Hf2 & %Hval & H)".
      iExists γ22, μ22, δΓ2, (of_ival v2), v2.
      iFrame "H". iPureIntro. split; last apply stm_to_val_of_ival.
      eapply step_trans. constructor. eapply Steps_trans.
      apply (Steps_call_frame Hf2). rewrite (stm_to_val_eq Hval).
      destruct (stm_to_val_Some_cases Hval) as [(? & -> & ->)|(? & -> & ->)];
        simpl; eapply step_trans; constructor.
    Qed.

    Lemma semWP2_call_inline {Γ1 Γ2 τ Δ} (f1 f2 : 𝑭 Δ τ)
      (es1 : NamedEnv (Exp Γ1) Δ) (es2 : NamedEnv (Exp Γ2) Δ) :
      ⊢ ∀ (Q : Post2 Γ1 Γ2 τ) (δΓ1 : CStore Γ1) (δΓ2 : CStore Γ2),
          semWP2 (evals es1 δΓ1) (evals es2 δΓ2) (FunDef f1) (FunDef f2) (λ v1τ _ v2τ _, Q v1τ δΓ1 v2τ δΓ2) -∗
          semWP2 δΓ1 δΓ2 (stm_call f1 es1) (stm_call f2 es2) Q.
    Proof. iIntros (? ? ?) "?". by iApply semWP2_call_inline_later. Qed.

    Lemma semWP2_bind {Γ1 Γ2 τ σ} (s1 : Stm Γ1 σ) (s2 : Stm Γ2 σ)
      (k1 : Val σ -> Stm Γ1 τ) (k2 : Val σ → Stm Γ2 τ) (Q : Post2 Γ1 Γ2 τ)
      (δ1 : CStore Γ1) (δ2 : CStore Γ2) :
      semWP2 δ1 δ2 s1 s2 (λ v1 δ12 v2 δ22, semWP2 δ12 δ22 (IBleft.lift_cnt k1 v1) (IBleft.lift_cnt k2 v2) Q) ⊢
        semWP2 δ1 δ2 (stm_bind s1 k1) (stm_bind s2 k2) Q.
    Proof.
      iIntros "H". rewrite /semWP2. iIntros (γ21 μ21) "Hres".
      iSpecialize ("H" with "Hres"). iApply IBleft.semWP_bind.
      iApply (IBleft.semWP_mono with "H").
      iIntros (v1 δ1') "(%γ22 & %μ22 & %δ2' & %s2' & %v2 & %Hsteps & %Hval & Hregs & Hmem & H)".
      iSpecialize ("H" with "[$Hregs $Hmem]"). iApply (IBleft.semWP_mono with "H").
      iIntros (v1' δ1'') "(%γ23 & %μ23 & %δ2'' & %s2'' & %v2' & H)".
      iExists γ23, μ23, δ2'', (of_ival v2'), v2'.
      iDestruct "H" as "(%Hsteps' & %Hval' & $ & $ & $)".
      iPureIntro. split; last apply stm_to_val_of_ival.
      apply (Steps_trans (Steps_bind Hsteps)).
      destruct (stm_to_val_Some_cases Hval) as [(? & -> & ->)|(? & -> & ->)],
               (stm_to_val_Some_cases Hval') as [(? & -> & ->)|(? & -> & ->)];
        simpl in *; (eapply step_trans; [constructor|auto]).
    Qed.

    Lemma semWP2_block {Γ1 Γ2 τ Δ1 Δ2} (δΔ1 : CStore Δ1) (δΔ2 : CStore Δ2) (s1 : Stm (Γ1 ▻▻ Δ1) τ) (s2 : Stm (Γ2 ▻▻ Δ2) τ) :
      ⊢ ∀ (Q : Post2 Γ1 Γ2 τ) (δ1 : CStore Γ1) (δ2 : CStore Γ2),
          semWP2 (δ1 ►► δΔ1) (δ2 ►► δΔ2) s1 s2 (fun v1 δ21 v2 δ22 => Q v1 (env.drop Δ1 δ21) v2 (env.drop Δ2 δ22)) -∗
          semWP2 δ1 δ2 (stm_block δΔ1 s1) (stm_block δΔ2 s2) Q.
    Proof.
      iIntros (Q δ1 δ2) "H". rewrite /semWP2. iIntros (γ21 μ21) "Hres".
      iSpecialize ("H" with "Hres"). iApply IBleft.semWP_block.
      iApply (IBleft.semWP_mono with "H").
      iIntros (v1 δ1') "(%γ22 & %μ22 & %δ2' & %s2' & %v2 & %Hsteps & %Hval & Hregs & Hmem & H)".
      iExists γ22, μ22, (env.drop Δ2 δ2'), (of_ival v2), v2.
      iFrame "Hregs Hmem H". iPureIntro. split; last apply stm_to_val_of_ival.
      destruct (env.catView δ2'). apply (Steps_trans (Steps_block Hsteps)).
      rewrite env.drop_cat.
      destruct (stm_to_val_Some_cases Hval) as [(? & -> & ->)|(? & -> & ->)];
        simpl in *; (eapply step_trans; [constructor|auto]); constructor.
    Qed.

    Lemma semWP2_call_frame {Γ1 Γ2 τ Δ} (δ1Δ δ2Δ : CStore Δ) (s1 s2 : Stm Δ τ) :
      ⊢ ∀ (Q : Post2 Γ1 Γ2 τ) (δ1 : CStore Γ1) (δ2 : CStore Γ2),
          semWP2 δ1Δ δ2Δ s1 s2 (λ v1 _ v2 _, Q v1 δ1 v2 δ2) -∗
          semWP2 δ1 δ2 (stm_call_frame δ1Δ s1) (stm_call_frame δ2Δ s2) Q.
    Proof.
      iIntros (Q δ1 δ2) "Hk". rewrite /semWP2. iIntros (γ21 μ21) "Hres".
      iSpecialize ("Hk" with "Hres"). iApply IBleft.semWP_call_frame.
      iApply (IBleft.semWP_mono with "Hk").
      iIntros (v1 _) "(%γ22 & %μ22 & %δ2' & %s2' & %v2 & %Hsteps & %Hval & Hregs & Hmem & H)".
      iExists γ22, μ22, δ2, (of_ival v2), v2.
      iFrame "Hregs Hmem H". iPureIntro. split.
      - rewrite (stm_to_val_eq Hval) in Hsteps.
        eapply (Steps_trans (Steps_call_frame Hsteps)).
        destruct v2; eapply step_trans; simpl; constructor.
      - apply stm_to_val_of_ival.
    Qed.

    Lemma semWP2_let {Γ1 Γ2 τ x σ} (s1 : Stm Γ1 σ) (s2 : Stm Γ2 σ)
      (k1 : Stm (Γ1 ▻ x∷σ) τ) (k2 : Stm (Γ2 ▻ x∷σ) τ)
      (Q : Post2 Γ1 Γ2 τ) (δ1 : CStore Γ1) (δ2 : CStore Γ2) :
      ⊢ semWP2 δ1 δ2 s1 s2 (λ v1 δ12 v2 δ22, match v1, v2 with
                                             | inl v1, inl v2 => semWP2 δ12.[x∷σ ↦ v1] δ22.[x∷σ ↦ v2] k1 k2 (λ v12 δ13 v22 δ23, Q v12 (env.tail δ13) v22 (env.tail δ23))
                                             | inr m1, inl v2 => semWP2 δ12 δ22.[x∷σ ↦ v2] (stm_fail _ m1) k2 (λ v12 δ13 v22 δ23, Q v12 δ13 v22 (env.tail δ23))
                                             | inl v1, inr m2 => semWP2 δ12.[x∷σ ↦ v1] δ22 k1 (stm_fail _ m2) (λ v12 δ13 v22 δ23, Q v12 (env.tail δ13) v22 δ23)
                                             | inr m1, inr m2 => semWP2 δ12 δ22 (of_ival (inr m1)) (of_ival (inr m2)) Q 
                                             end) -∗
        semWP2 δ1 δ2 (let: x ∷ σ := s1 in k1)%exp (let: x ∷ σ := s2 in k2)%exp Q.
    Proof.
      iIntros "H". rewrite /semWP2. iIntros (γ21 μ21) "Hres".
      iSpecialize ("H" with "Hres"). iApply IBleft.semWP_let.
      iApply (IBleft.semWP_mono with "H").
      iIntros (v1 δ1') "(%γ22 & %μ22 & %δ2' & %s2' & %v2 & %Hsteps & %Hval & Hregs & Hmem & H)".
      destruct v1 as [v1|m1], v2 as [v2|m2].
      - iSpecialize ("H" with "[$Hregs $Hmem]"). iApply (IBleft.semWP_mono with "H").
        iIntros (v1' δ1'') "(%γ23 & %μ23 & %δ2'' & %s2'' & %v2' & %Hsteps' & %Hval' & Hregs & Hmem & H)".
        iExists γ23, μ23, (env.tail δ2''), (of_ival v2'), v2'.
        iFrame "Hregs Hmem H". iPureIntro. split; last apply stm_to_val_of_ival.
        destruct (env.view δ2'').
        eapply step_trans. constructor. apply (Steps_trans (Steps_bind Hsteps)).
        rewrite (stm_to_val_eq Hval') in Hsteps'.
        destruct (stm_to_val_Some_cases Hval) as [(? & -> & Hv2)|(? & -> & Hm2)];
          simpl in *; try discriminate.
        eapply step_trans. constructor. eapply Steps_trans.
        eapply Steps_block.
        assert (E.[x∷σ ↦ v] = E ►► [env].[x∷σ ↦ v]) as <- by reflexivity.
        cbn. inversion Hv2; subst. eassumption.
        destruct v2'; eapply step_trans; constructor.
      - iSpecialize ("H" with "[$Hregs $Hmem]"). iApply (IBleft.semWP_mono with "H").
        iIntros (v1' δ1'') "(%γ23 & %μ23 & %δ2'' & %s2'' & %v2' & %Hsteps' & %Hval' & Hregs & Hmem & H)".
        pose proof (stm_to_val_Some_inr Hval) as Hs2'.
        destruct v2' as [v2'|m2'].
        + rewrite (stm_to_val_Some_inl Hval') in Hsteps'.
          inversion Hsteps'. destruct (smallinvstep H).
        + iExists γ23, μ23, δ2'', (stm_fail _ m2'), (inr m2').
          iFrame "Hregs Hmem H".
          rewrite (stm_to_val_Some_inr Hval') in Hsteps'.
          iPureIntro. split; auto. eapply step_trans.
          constructor. apply (Steps_trans (Steps_bind Hsteps)).
          eapply step_trans. rewrite Hs2'. constructor. auto.
      - iSpecialize ("H" with "[$Hregs $Hmem]"). rewrite ?IBleft.semWP_fail. iMod "H".
        iModIntro.
        iDestruct "H" as "(%γ23 & %μ23 & %δ2'' & %s2'' & %v2' & %Hsteps' & %Hval' & Hregs & Hmem & H)".
        pose proof (stm_to_val_Some_inl Hval) as Hs2'.
        iExists γ23, μ23, (env.tail δ2''), (of_ival v2'), v2'.
        destruct (env.view δ2'').
        iFrame "Hregs Hmem H". iPureIntro. split; last apply stm_to_val_of_ival.
        eapply step_trans. constructor. apply (Steps_trans (Steps_bind Hsteps)).
        destruct (stm_to_val_Some_cases Hval) as [(? & -> & Hv2)|(? & -> & Hm2)],
                 (stm_to_val_Some_cases Hval') as [(? & -> & Hv2')|(? & -> & Hm2')];
          simpl in *; (eapply step_trans; [constructor|auto]);
          try discriminate.
        + eapply Steps_trans. eapply Steps_block. cbn.
          assert (E.[x∷σ ↦ v] = E ►► [env].[x∷σ ↦ v]) as <- by reflexivity.
          inversion Hv2; subst. eassumption. eapply step_trans.
          constructor. subst. simpl. apply step_refl.
        + eapply Steps_trans. eapply Steps_block. cbn.
          assert (E.[x∷σ ↦ v] = E ►► [env].[x∷σ ↦ v]) as <- by reflexivity.
          inversion Hv2; subst. eassumption. eapply step_trans.
          constructor. subst. simpl. apply step_refl.
      - pose proof (stm_to_val_Some_inr Hval) as Hs2'. simpl.
        iSpecialize ("H" with "[$Hregs $Hmem]"). rewrite ?IBleft.semWP_fail.
        iMod "H" as "(%γ23 & %μ23 & %δ2'' & %s2'' & %v2' & %Hsteps' & %Hval' & Hregs & Hmem & H)".
        iModIntro. iExists γ23, μ23, δ2'', s2'', v2'. iFrame.
        iPureIntro. split; auto. eapply step_trans. constructor.
        apply (Steps_trans (Steps_bind Hsteps)). rewrite Hs2'. eapply step_trans.
        apply st_bind_fail. auto.
    Qed.

    Lemma semWP2_seq {Γ1 Γ2 τ σ} (s1 : Stm Γ1 σ) (s2 : Stm Γ2 σ)
      (k1 : Stm Γ1 τ) (k2 : Stm Γ2 τ) :
      ⊢ ∀ (Q : Post2 Γ1 Γ2 τ) (δ1 : CStore Γ1) (δ2 : CStore Γ2),
          semWP2 δ1 δ2 s1 s2 (λ v1 δ21 v2 δ22,
              match v1, v2 with
              | inr m1, inr m2 => semWP2 δ21 δ22 (of_ival (inr m1)) (of_ival (inr m2)) Q
              | inr m1, inl v2 => semWP2 δ21 δ22 (of_ival (inr m1)) k2 Q
              | inl v1, inr m2 => semWP2 δ21 δ22 k1 (of_ival (inr m2)) Q
              | inl v1, inl v2 => semWP2 δ21 δ22 k1 k2 Q
              end) -∗
          semWP2 δ1 δ2 (s1;;k1)%exp (s2;;k2)%exp Q.
    Proof.
      iIntros (Q δ1 δ2) "H". rewrite /semWP2. iIntros (γ21 μ21) "Hres".
      iSpecialize ("H" with "Hres"). iApply IBleft.semWP_seq.
      iApply (IBleft.semWP_mono with "H"). iIntros (v1 δ1') "(%γ22 & %μ22 & %δ2' & %s2' & %v2 & %Hsteps & %Hval & Hregs & Hmem & H)".
      destruct v1 as [v1|m1], v2 as [v2|m2].
      - iSpecialize ("H" with "[$Hregs $Hmem]"). iApply (IBleft.semWP_mono with "H").
        iIntros (v1' δ1'') "(%γ23 & %μ23 & %δ2'' & %s2'' & %v2' & %Hsteps' & %Hval' & Hregs & Hmem & H)".
        iExists γ23, μ23, δ2'', (of_ival v2'), v2'. iFrame "Hregs Hmem H".
        iPureIntro. split; last apply stm_to_val_of_ival.
        rewrite (stm_to_val_eq Hval') in Hsteps'.
        eapply step_trans. constructor. apply (Steps_trans (Steps_bind Hsteps)).
        eapply step_trans. rewrite (stm_to_val_Some_inl Hval). constructor. auto.
      - iSpecialize ("H" with "[$Hregs $Hmem]"). iApply (IBleft.semWP_mono with "H").
        iIntros (v1' δ1'') "(%γ23 & %μ23 & %δ2'' & %s2'' & %v2' & %Hsteps' & %Hval' & Hregs & Hmem & H)".
        iExists γ23, μ23, δ2'', (of_ival v2'), v2'. iFrame "Hregs Hmem H".
        iPureIntro. split; last apply stm_to_val_of_ival.
        rewrite (stm_to_val_eq Hval') in Hsteps'.
        rewrite (stm_to_val_Some_inr Hval) in Hsteps.
        eapply step_trans. constructor. apply (Steps_trans (Steps_bind Hsteps)).
        eapply step_trans. constructor. auto.
      - iSpecialize ("H" with "[$Hregs $Hmem]"). rewrite ?IBleft.semWP_fail. iMod "H".
        iModIntro.
        iDestruct "H" as "(%γ23 & %μ23 & %δ2'' & %s2'' & %v2' & %Hsteps' & %Hval' & Hregs & Hmem & H)".
        iExists γ23, μ23, δ2'', (of_ival v2'), v2'. iFrame "Hregs Hmem H".
        iPureIntro. split; last apply stm_to_val_of_ival.
        rewrite (stm_to_val_eq Hval') in Hsteps'.
        rewrite (stm_to_val_Some_inl Hval) in Hsteps.
        eapply step_trans. constructor. apply (Steps_trans (Steps_bind Hsteps)).
        eapply step_trans. constructor. auto.
      - iSpecialize ("H" with "[$Hregs $Hmem]"). rewrite ?IBleft.semWP_fail.
        iMod "H" as "(%γ23 & %μ23 & %δ2'' & %s2'' & %v2' & %Hsteps' & %Hval' & Hregs & Hmem & H)".
        iModIntro. iExists γ23, μ23, δ2'', s2'', v2'.
        iFrame "Hregs Hmem H". iPureIntro; split; auto.
        rewrite (stm_to_val_eq Hval) in Hsteps. eapply step_trans. constructor.
        apply (Steps_trans (Steps_bind Hsteps)). simpl. eapply step_trans.
        constructor. auto.
    Qed.

    Lemma semWP2_assertk {Γ1 Γ2 τ} (e11 : Exp Γ1 ty.bool) (e21 : Exp Γ2 ty.bool)
      (e12 : Exp Γ1 ty.string) (e22 : Exp Γ2 ty.string) (k1 : Stm Γ1 τ) (k2 : Stm Γ2 τ) :
      ⊢ ∀ (Q : Post2 Γ1 Γ2 τ) (δ1 : CStore Γ1) (δ2 : CStore Γ2),
          (⌜eval e11 δ1 = true⌝ → ⌜eval e21 δ2 = true⌝ → semWP2 δ1 δ2 k1 k2 Q) -∗
          (⌜eval e11 δ1 = false⌝ → ⌜eval e21 δ2 = true⌝ → semWP2 δ1 δ2 (stm_fail _ (eval e12 δ1)) k2 Q) -∗
          (⌜eval e11 δ1 = true⌝ → ⌜eval e21 δ2 = false⌝ → semWP2 δ1 δ2 k1 (stm_fail _ (eval e22 δ2)) Q) -∗
          (⌜eval e11 δ1 = false⌝ → ⌜eval e21 δ2 = false⌝ → semWP2 δ1 δ2 (stm_fail _ (eval e12 δ1)) (stm_fail _ (eval e22 δ2)) Q) -∗
          semWP2 δ1 δ2 (stm_assertk e11 e12 k1) (stm_assertk e21 e22 k2) Q.
    Proof.
      iIntros (Q δ1 δ2) "Htt Hft Htf Hff". rewrite /(semWP2 _ _ (stm_assertk _ _ _)).
      iIntros (γ21 μ21) "Hres". destruct (eval e11 δ1) eqn:Ee11, (eval e21 δ2) eqn:Ee21.
      - iClear "Hft Htf Hff". iSpecialize ("Htt" with "[] []"); auto.
        rewrite /semWP2. iSpecialize ("Htt" with "Hres").
        iApply (IBleft.semWP_assertk with "[Htt]").
        + iIntros (_). iApply (IBleft.semWP_mono with "Htt").
          iIntros (v1 δ1') "(%γ22 & %μ22 & %δ2' & %k2' & %v2 & %Hsteps & %Hk2' & Hregs & Hmem & H)".
          iExists γ22, μ22, δ2', (of_ival v2), v2. iFrame "Hregs Hmem H".
          iPureIntro. split; last apply stm_to_val_of_ival.
          eapply step_trans. constructor. rewrite Ee21.
          rewrite (stm_to_val_eq Hk2') in Hsteps. auto.
        + iIntros (Hcon). rewrite Hcon in Ee11. discriminate.
      - iClear "Htt Hft Hff". iSpecialize ("Htf" with "[] []"); auto.
        rewrite /semWP2. iSpecialize ("Htf" with "Hres").
        iApply (IBleft.semWP_assertk with "[Htf]").
        + iIntros (_). iApply (IBleft.semWP_mono with "Htf").
          iIntros (v1 δ1') "(%γ22 & %μ22 & %δ2' & %k2' & %v2 & %Hsteps & %Hk2' & Hregs & Hmem & H)".
          iExists γ22, μ22, δ2', (of_ival v2), v2. iFrame "Hregs Hmem H".
          iPureIntro. split; last apply stm_to_val_of_ival.
          eapply step_trans. constructor. rewrite Ee21.
          rewrite (stm_to_val_eq Hk2') in Hsteps. auto.
        + iIntros (Hcon). rewrite Hcon in Ee11. discriminate.
      - iClear "Htt Htf Hff". iSpecialize ("Hft" with "[] []"); auto.
        rewrite /semWP2. iSpecialize ("Hft" with "Hres").
        iApply (IBleft.semWP_assertk with "[] [Hft]").
        + iIntros (Hcon). rewrite Hcon in Ee11. discriminate.
        + iIntros (_). iApply (IBleft.semWP_mono with "Hft").
          iIntros (v1 δ1') "(%γ22 & %μ22 & %δ2' & %k2' & %v2 & %Hsteps & %Hk2' & Hregs & Hmem & H)".
          iExists γ22, μ22, δ2', (of_ival v2), v2. iFrame "Hregs Hmem H".
          iPureIntro. split; last apply stm_to_val_of_ival.
          eapply step_trans. constructor. rewrite Ee21.
          rewrite (stm_to_val_eq Hk2') in Hsteps. auto.
      - iClear "Htt Htf Hft". iSpecialize ("Hff" with "[] []"); auto.
        rewrite /semWP2. iSpecialize ("Hff" with "Hres").
        iApply (IBleft.semWP_assertk with "[] [Hff]").
        + iIntros (Hcon). rewrite Hcon in Ee11. discriminate.
        + iIntros (_). iApply (IBleft.semWP_mono with "Hff").
          iIntros (v1 δ1') "(%γ22 & %μ22 & %δ2' & %k2' & %v2 & %Hsteps & %Hk2' & Hregs & Hmem & H)".
          iExists γ22, μ22, δ2', (of_ival v2), v2. iFrame "Hregs Hmem H".
          iPureIntro. split; last apply stm_to_val_of_ival.
          eapply step_trans. constructor. rewrite Ee21.
          rewrite (stm_to_val_eq Hk2') in Hsteps. auto.
    Qed.

    Lemma semWP2_read_register {Γ1 Γ2 τ} (reg : 𝑹𝑬𝑮 τ) :
      ⊢ ∀ (Q : Post2 Γ1 Γ2 τ) (δ1 : CStore Γ1) (δ2 : CStore Γ2),
          (∃ v1 v2 : Val τ, reg_pointsTo2 reg v1 v2 ∗ (reg_pointsTo2 reg v1 v2 -∗ Q (inl v1) δ1 (inl v2) δ2)) -∗
          semWP2 δ1 δ2 (stm_read_register reg) (stm_read_register reg) Q.
    Proof.
      iIntros (Q δ1 δ2) "(%v1 & %v2 & (Hptsto1 & Hptsto2) & Hk)". rewrite /semWP2.
      iIntros (γ21 μ21) "(Hreg & Hmem)". iApply IBleft.semWP_read_register. iExists v1.
      iFrame "Hptsto1". iIntros "Hptsto1".
      iExists γ21, μ21, δ2, (stm_val _ (read_register γ21 reg)), (inl (read_register γ21 reg)).
      iDestruct (reg_valid with "Hreg Hptsto2") as %H. rewrite H.
      iSpecialize ("Hk" with "[$Hptsto1 $Hptsto2]"). iFrame "Hk Hreg Hmem".
      iPureIntro. split; last reflexivity.
      eapply step_trans. constructor. rewrite H. apply step_refl.
    Qed.

    Lemma semWP2_write_register {Γ1 Γ2 τ} (reg : 𝑹𝑬𝑮 τ) (e1 : Exp Γ1 τ) (e2 : Exp Γ2 τ) :
      ⊢ ∀ (Q : Post2 Γ1 Γ2 τ) (δ1 : CStore Γ1) (δ2 : CStore Γ2),
          (∃ v1 v2 : Val τ, reg_pointsTo2 reg v1 v2 ∗ (reg_pointsTo2 reg (eval e1 δ1) (eval e2 δ2) -∗ Q (inl (eval e1 δ1)) δ1 (inl (eval e2 δ2)) δ2)) -∗
          semWP2 δ1 δ2 (stm_write_register reg e1) (stm_write_register reg e2) Q.
    Proof.
      iIntros (Q δ1 δ2) "(%v1 & %v2 & (Hptsto1 & Hptsto2) & Hk)". rewrite /semWP2.
      iIntros (γ21 μ21) "(Hreg & Hmem)". iApply (IBleft.fupd_semWP ⊤).
      iMod (reg_update γ21 reg v2 (eval e2 δ2) with "Hreg Hptsto2") as "[Hreg Hptsto2]".
      iModIntro. iApply IBleft.semWP_write_register. iExists v1.
      iFrame "Hptsto1". iIntros "Hptsto1".
      iExists (write_register γ21 reg (eval e2 δ2)), μ21, δ2, (stm_val _ (eval e2 δ2)), (inl (eval e2 δ2)).
      iSpecialize ("Hk" with "[$Hptsto1 $Hptsto2]"). iFrame "Hk Hmem Hreg".
      iPureIntro. split; last reflexivity. eapply step_trans. constructor.
      apply step_refl.
    Qed.

    Lemma semWP2_assign {Γ1 Γ2 τ x} (xInΓ1 : x∷τ ∈ Γ1) (xInΓ2 : x∷τ ∈ Γ2)
      (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ) :
      ⊢ ∀ (Q : Post2 Γ1 Γ2 τ) (δ1 : CStore Γ1) (δ2 : CStore Γ2),
          semWP2 δ1 δ2 s1 s2 (λ v1 δ21 v2 δ22,
              match v1, v2 with
              | inl v1, inl v2 => Q (inl v1) (δ21 ⟪ x ↦ v1 ⟫) (inl v2) (δ22 ⟪ x ↦ v2 ⟫)
              | inl v1, inr m2 => Q (inl v1) (δ21 ⟪ x ↦ v1 ⟫) v2 δ22
              | inr m1, inl v2 => Q v1 δ21 (inl v2) (δ22 ⟪ x ↦ v2 ⟫)
              | inr m1, inr m2 => Q v1 δ21 v2 δ22
              end) -∗
          semWP2 δ1 δ2 (stm_assign x s1) (stm_assign x s2) Q.
    Proof.
      iIntros (Q δ1 δ2) "H". rewrite /semWP2. iIntros (γ21 μ21) "Hres".
      iSpecialize ("H" with "Hres"). iApply IBleft.semWP_assign.
      iApply (IBleft.semWP_mono with "H").
      iIntros (v1 δ1') "(%γ22 & %μ22 & %δ2' & %s2' & %v2 & %Hs2' & %Hval & H)".
      destruct v1 as [v1|m1], v2 as [v2|m2]; iExists γ22, μ22.
      - iExists (δ2' ⟪ x ↦ v2 ⟫), s2', (inl v2). iFrame "H".
        iPureIntro. split; auto. eapply (Steps_trans (Steps_assign Hs2')).
        rewrite (stm_to_val_Some_inl Hval). eapply step_trans. constructor.
        apply step_refl.
      - iExists δ2', s2', (inr m2). iFrame "H".
        iPureIntro. split; auto. eapply (Steps_trans (Steps_assign Hs2')).
        rewrite (stm_to_val_Some_inr Hval). eapply step_trans. constructor.
        apply step_refl.
      - iExists (δ2' ⟪ x ↦ v2 ⟫), s2', (inl v2). iFrame "H".
        iPureIntro. split; auto. eapply (Steps_trans (Steps_assign Hs2')).
        rewrite (stm_to_val_Some_inl Hval). eapply step_trans. constructor.
        apply step_refl.
      - iExists δ2', s2', (inr m2). iFrame "H".
        iPureIntro. split; auto. eapply (Steps_trans (Steps_assign Hs2')).
        rewrite (stm_to_val_Some_inr Hval). eapply step_trans. constructor.
        apply step_refl.
    Qed.

    Lemma semWP2_pattern_match {Γ1 Γ2 τ σ} (s1 : Stm Γ1 σ) (s2 : Stm Γ2 σ) (pat : Pattern σ)
      (rhs1 : ∀ pc : PatternCase pat, Stm (Γ1 ▻▻ PatternCaseCtx pc) τ)
      (rhs2 : ∀ pc : PatternCase pat, Stm (Γ2 ▻▻ PatternCaseCtx pc) τ) :
      ⊢ ∀ (Q : Post2 Γ1 Γ2 τ) (δ1 : CStore Γ1) (δ2 : CStore Γ2),
          semWP2 δ1 δ2 s1 s2
            (λ vσ1 δ12 vσ2 δ22,
              match vσ1, vσ2 with
              | inl vσ1, inl vσ2 =>
                  let (pc1,δpc1) := pattern_match_val pat vσ1 in
                  let (pc2,δpc2) := pattern_match_val pat vσ2 in
                  semWP2 (δ12 ►► δpc1) (δ22 ►► δpc2) (rhs1 pc1) (rhs2 pc2)
                    (λ vτ1 δ21 vτ2 δ22, Q vτ1 (env.drop (PatternCaseCtx pc1) δ21) vτ2 (env.drop (PatternCaseCtx pc2) δ22))
              | inr mσ1, inl vσ2 =>
                  let (pc2,δpc2) := pattern_match_val pat vσ2 in
                  semWP2 δ12 (δ22 ►► δpc2) (stm_fail _ mσ1) (rhs2 pc2)
                    (λ vτ1 δ21 vτ2 δ22, Q vτ1 δ21 vτ2 (env.drop (PatternCaseCtx pc2) δ22))
              | inl vσ1, inr mσ2 =>
                  let (pc1,δpc1) := pattern_match_val pat vσ1 in
                  semWP2 (δ12 ►► δpc1) δ22 (rhs1 pc1) (stm_fail _ mσ2)
                    (λ vτ1 δ21 vτ2 δ22, Q vτ1 (env.drop (PatternCaseCtx pc1) δ21) vτ2 δ22)
              | inr mσ1, inr mσ2 =>
                  semWP2 δ12 δ22 (stm_fail _ mσ1) (stm_fail _ mσ2) Q
              end
            ) -∗
          semWP2 δ1 δ2 (stm_pattern_match s1 pat rhs1) (stm_pattern_match s2 pat rhs2) Q.
    Proof.
      iIntros (Q δ1 δ2) "H". rewrite /semWP2. iIntros (γ21 μ21) "Hres".
      iSpecialize ("H" with "Hres"). iApply IBleft.semWP_pattern_match.
      iApply (IBleft.semWP_mono with "H").
      iIntros (v1 δ1') "(%γ22 & %μ22 & %δ2' & %s2' & %v2 & %Hs2' & %Hval & Hreg & Hmem & H)".
      destruct v1 as [v1|m1];
        first destruct (pattern_match_val pat v1) eqn:Ev1;
        destruct v2 as [v2|m2];
        try destruct (pattern_match_val pat v2) eqn:Ev2.
      - iSpecialize ("H" with "[$Hreg $Hmem]"). iApply (IBleft.semWP_mono with "H").
        iIntros (v1' δ1'') "(%γ23 & %μ23 & %δ2'' & %s2'' & %v2' & %Hs2'' & %Hval' & Hreg & Hmem & HQ)".
        iExists γ23, μ23, (env.drop (PatternCaseCtx _) δ2''), (of_ival v2'), v2'.
        iFrame "HQ Hreg Hmem". iPureIntro. destruct (env.catView δ2'').
        split; last apply stm_to_val_of_ival.
        eapply step_trans. constructor. eapply Steps_trans. apply (Steps_bind Hs2').
        rewrite (stm_to_val_eq Hval') in Hs2''.
        destruct (stm_to_val_Some_cases Hval) as [(? & -> & Heq)|(? & -> & Heq)];
          last inversion Heq.
        eapply step_trans. constructor. inversion Heq; subst.
        rewrite Ev2. apply (Steps_trans (Steps_block Hs2'')).
        destruct (stm_to_val_Some_cases Hval') as [(? & -> & ->)|(? & -> & ->)];
          simpl; eapply step_trans; try constructor; rewrite env.drop_cat;
          apply step_refl.
      - iSpecialize ("H" with "[$Hreg $Hmem]"). iApply (IBleft.semWP_mono with "H").
        iIntros (v1' δ1'') "(%γ23 & %μ23 & %δ2'' & %s2'' & %v2' & %Hs2'' & %Hval' & Hreg & Hmem & HQ)".
        iExists γ23, μ23, δ2'', (of_ival v2'), v2'.
        iFrame "HQ Hreg Hmem". iPureIntro.
        split; last apply stm_to_val_of_ival.
        eapply step_trans. constructor. eapply (Steps_trans (Steps_bind Hs2')).
        rewrite (stm_to_val_Some_inr Hval). eapply step_trans. constructor.
        rewrite <- (stm_to_val_eq Hval'). auto.
      - iSpecialize ("H" with "[$Hreg $Hmem]"). rewrite IBleft.semWP_fail.
        iMod "H" as "(%γ23 & %μ23 & %δ2'' & %s2'' & %v2' & %Hs2'' & %Hval' & Hreg & Hmem & HQ)".
        iModIntro.
        iExists γ23, μ23, (env.drop (PatternCaseCtx _) δ2''), (of_ival v2'), v2'.
        iFrame "HQ Hreg Hmem". iPureIntro.
        split; last apply stm_to_val_of_ival.
        destruct (env.catView δ2'').
        eapply step_trans. constructor. eapply (Steps_trans (Steps_bind Hs2')).
        rewrite (stm_to_val_Some_inl Hval). eapply step_trans. constructor.
        rewrite Ev2. eapply (Steps_trans (Steps_block Hs2'')).
        destruct (stm_to_val_Some_cases Hval') as [(? & -> & ->)|(? & -> & ->)];
          simpl; eapply step_trans; try constructor; rewrite env.drop_cat;
          apply step_refl.
      - iSpecialize ("H" with "[$Hreg $Hmem]"). rewrite IBleft.semWP_fail.
        iMod "H" as "(%γ23 & %μ23 & %δ2'' & %s2'' & %v2' & %Hs2'' & %Hval' & Hreg & Hmem & HQ)".
        iModIntro.
        iExists γ23, μ23, δ2'', (of_ival v2'), v2'.
        iFrame "HQ Hreg Hmem". iPureIntro.
        split; last apply stm_to_val_of_ival.
        eapply step_trans. constructor. eapply (Steps_trans (Steps_bind Hs2')).
        rewrite (stm_to_val_Some_inr Hval). eapply step_trans. constructor.
        rewrite <- (stm_to_val_eq Hval'). auto.
    Qed.

    Lemma semWP2_foreign {Γ1 Γ2 Δ τ} {f1 f2 : 𝑭𝑿 Δ τ}
      {es1 : NamedEnv (Exp Γ1) Δ} {es2 : NamedEnv (Exp Γ2) Δ} {Q δ1 δ2} :
      let srGS_left  := sailRegGS2_sailRegGS_left in
      let mG_left    := memGS2_memGS_left in
      let srGS_right := sailRegGS2_sailRegGS_right in
      let mG_right   := memGS2_memGS_right in
      ⊢ (∀ γ1 μ1,
            (@regs_inv _ srGS_left γ1 ∗ @IBleft.mem_state_interp _ mG_left μ1)
            ={⊤,∅}=∗
              (∀ res1 γ1' μ1',
                   ⌜ForeignCall f1 (evals es1 δ1) res1 γ1 γ1' μ1 μ1'⌝
                   ={∅}▷=∗
                     |={∅,⊤}=>
                 (@regs_inv _ srGS_left γ1' ∗ @IBleft.mem_state_interp _ mG_left μ1')
                       ∗  (∀ γ2 μ2,
                           (@regs_inv _ srGS_right γ2 ∗ @IBright.mem_state_interp _ mG_right μ2) ={⊤,∅}=∗
                               (∀ res2 γ2' μ2',
                                 ⌜ForeignCall f2 (evals es2 δ2) res2 γ2 γ2' μ2 μ2'⌝ ={∅,⊤}=∗
                                                                                             (@regs_inv _ srGS_right γ2' ∗ @IBright.mem_state_interp _ mG_right μ2')
                                   ∗ semWP2 δ1 δ2 (match res1 with inr v => stm_val _ v
                                                                 | inl s => stm_fail _ s
                                                   end)
                                                  (match res2 with inr v => stm_val _ v
                                                                 | inl s => stm_fail _ s
                                                   end) Q)))) -∗
        semWP2 δ1 δ2 (stm_foreign f1 es1) (stm_foreign f2 es2) Q.
    Proof.
      simpl. iIntros "H". rewrite /semWP2. iIntros (γ2 μ2) "Hres2".
      iApply IBleft.semWP_foreign. iIntros (γ1 μ1) "Hres1".
      iMod ("H" with "Hres1") as "H". iIntros "!>" (res1 γ1' μ1' Hf1).
      iMod ("H" $! _ _ _ Hf1) as "H". iModIntro. iModIntro. iMod "H".
      iModIntro. iMod "H". iModIntro. iDestruct "H" as "($ & H)".
      destruct res1 as [v1|msg1].
      - rewrite IBleft.semWP_fail. iApply (@IBright.semTWP_Steps _ sailGS2_sailGS_right with "Hres2").
        iApply IBright.semTWP_foreign. iIntros (γ2' μ2') "Hres2".
        iMod ("H" with "Hres2") as "H". iIntros "!>" (res2 γ2'' μ2'' Hf2).
        iMod ("H" $! _ _ _ Hf2) as "H". iDestruct "H" as "(Hres2 & H)".
        iSpecialize ("H" with "Hres2"). rewrite IBleft.semWP_fail. iMod "H". iModIntro.
        iDestruct "H" as "(%γ22 & %μ22 & %δ2' & %s2' & %v2 & %Hstep & %Hval & Hreg & Hmem & HQ)".
        destruct res2 as [v2'|msg2];
          inversion Hstep; subst;
          try match goal with
            | H: context[⟨ _, _, _, stm_val _ _ ⟩ ---> ⟨ _, _, _, _ ⟩] |- _ =>
                inversion H
            | H: context[⟨ _, _, _, stm_fail _ _ ⟩ ---> ⟨ _, _, _, _ ⟩] |- _ =>
                inversion H
            end;
          simpl in Hval; inversion Hval; subst.
        + rewrite IBright.semTWP_fail. now iFrame.
        + rewrite IBright.semTWP_val. now iFrame.
      - rewrite IBleft.semWP_val. iApply (@IBright.semTWP_Steps _ sailGS2_sailGS_right with "Hres2").
        iApply IBright.semTWP_foreign. iIntros (γ2' μ2') "Hres2".
        iMod ("H" with "Hres2") as "H". iIntros "!>" (res2 γ2'' μ2'' Hf2).
        iMod ("H" $! _ _ _ Hf2) as "H". iDestruct "H" as "(Hres2 & H)".
        iSpecialize ("H" with "Hres2"). rewrite IBleft.semWP_val. iMod "H". iModIntro.
        iDestruct "H" as "(%γ22 & %μ22 & %δ2' & %s2' & %v2 & %Hstep & %Hval & Hreg & Hmem & HQ)".
        destruct res2 as [v2'|msg2];
          inversion Hstep; subst;
          try match goal with
            | H: context[⟨ _, _, _, stm_val _ _ ⟩ ---> ⟨ _, _, _, _ ⟩] |- _ =>
                inversion H
            | H: context[⟨ _, _, _, stm_fail _ _ ⟩ ---> ⟨ _, _, _, _ ⟩] |- _ =>
                inversion H
            end;
          simpl in Hval; inversion Hval; subst.
        + rewrite IBright.semTWP_fail. now iFrame.
        + rewrite IBright.semTWP_val. now iFrame.
    Qed.

    Lemma semWP2_debugk {Γ1 Γ2 τ} (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ) :
      ⊢ ∀ Q δ1 δ2, semWP2 δ1 δ2 s1 s2 Q -∗ semWP2 δ1 δ2 (stm_debugk s1) (stm_debugk s2) Q.
    Proof.
      iIntros (Q δ1 δ2) "H". rewrite /semWP2. iIntros (γ21 μ21) "Hres".
      iSpecialize ("H" with "Hres"). iApply IBleft.semWP_debugk.
      iApply (IBleft.semWP_mono with "H").
      iIntros (v1 δ1') "(%γ22 & %μ22 & %δ2' & %s2' & %v2 & %Hs2' & %Hval & H)".
      iExists γ22, μ22, δ2', s2', v2. iFrame "H". iPureIntro. split; auto.
      eapply step_trans. constructor. assumption.
    Qed.

    Lemma semWP2_lemmak {Γ1 Γ2 τ} {Δ} (l1 l2 : 𝑳 Δ) (es1 : NamedEnv (Exp Γ1) Δ)
      (es2 : NamedEnv (Exp Γ2) Δ) (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ) :
      ⊢ ∀ Q δ1 δ2, semWP2 δ1 δ2 s1 s2 Q -∗ semWP2 δ1 δ2 (stm_lemmak l1 es1 s1) (stm_lemmak l2 es2 s2) Q.
    Proof.
      iIntros (Q δ1 δ2) "H". rewrite /semWP2. iIntros (γ21 μ21) "Hres".
      iSpecialize ("H" with "Hres"). iApply IBleft.semWP_lemmak.
      iApply (IBleft.semWP_mono with "H").
      iIntros (v1 δ1') "(%γ22 & %μ22 & %δ2' & %s2' & %v2 & %Hs2' & %Hval & H)".
      iExists γ22, μ22, δ2', s2', v2. iFrame "H". iPureIntro. split; auto.
      eapply step_trans. constructor. assumption.
    Qed.

    Lemma semWP2_focus {Γ1 Γ2 τ} {s1 : Stm Γ1 τ} {s2 : Stm Γ2 τ} :
      ⊢ ∀ Q1 Q2 Q δ1 δ2,
          @IBleft.semTWP _ sailGS2_sailGS_left _ _ δ1 s1 Q1 -∗
          @IBright.semTWP _ sailGS2_sailGS_right _ _ δ2 s2 Q2 -∗
          (∀ v1 δ1 v2 δ2, Q1 v1 δ1 ∗ Q2 v2 δ2 -∗ Q v1 δ1 v2 δ2) -∗
          semWP2 δ1 δ2 s1 s2 Q.
    Proof.
      iIntros (Q1 Q2 Q δ1 δ2) "HTWP1 HTWP2 H". rewrite /semWP2.
      iIntros (γ21 μ21) "Hres". iApply IBleft.semWP_fupd.
      iPoseProof (IBleft.semTWP_semWP with "HTWP1") as "HWP1".
      iPoseProof (IBright.semTWP_Steps with "[Hres] HTWP2") as "H2".
      { iDestruct "Hres" as "($ & $)". }
      iApply (IBleft.semWP_mono with "HWP1"). iIntros (v1 δ1') "HQ1".
      iMod "H2" as "(%γ22 & %μ22 & %δ2' & %s2' & %v2 & %Hstep & %Hs2' & Hreg & Hmem & HQ2)".
      iModIntro. iExists γ22, μ22, δ2', (of_ival v2), v2. iFrame "Hreg Hmem".
      iDestruct ("H" with "[$HQ1 $HQ2]") as "$". iPureIntro.
      split; last apply stm_to_val_of_ival. rewrite (stm_to_val_eq Hs2') in Hstep.
      auto.
    Qed.

    Lemma semWP2_focus_seq {Γ1 Γ2 τ} {s1 : Stm Γ1 τ} {s2 : Stm Γ2 τ} :
      ⊢ ∀ Q δ1 δ2,
          @IBleft.semTWP _ sailGS2_sailGS_left _ _ δ1 s1 (λ v1 δ1,
              @IBright.semTWP _ sailGS2_sailGS_right _ _ δ2 s2
                (λ v2 δ2, Q v1 δ1 v2 δ2)) -∗
          semWP2 δ1 δ2 s1 s2 Q.
    Proof.
      iIntros (Q δ1 δ2) "H". rewrite /semWP2. iIntros (γ21 μ21) "Hres".
      iApply IBleft.semWP_fupd.
      iPoseProof (IBleft.semTWP_semWP with "H") as "H". iApply (IBleft.semWP_mono with "H").
      iIntros (v1 δ1') "H". now iApply (IBright.semTWP_Steps with "[Hres] H").
    Qed.

    Lemma semWP2_anaglyph {Γ1 Γ2 τ} {s1 : Stm Γ1 τ} {s2 : Stm Γ2 τ} :
      ⊢ ∀ Q δ1 δ2,
          @IBleft.semWP _ sailGS2_sailGS_left _ _ δ1 s1 (λ v1 δ1,
              @IBright.semTWP _ sailGS2_sailGS_right _ _ δ2 s2
                      (λ v2 δ2, Q v1 δ1 v2 δ2)) -∗
          semWP2 δ1 δ2 s1 s2 Q.
    Proof.
      iIntros (Q δ1 δ2) "H". rewrite /semWP2. iIntros (γ21 μ21) "Hres".
      iApply IBleft.semWP_fupd.
      iApply (IBleft.semWP_mono with "H"). iIntros (v1 δ1') "H".
      now iApply (IBright.semTWP_Steps with "[Hres] H").
    Qed.

    Lemma semWP2_step_left {Γ1 Γ2 τ} {s1 s1' : Stm Γ1 τ} {s2 : Stm Γ2 τ}
      {γ1 γ1' γ2 : RegStore} {μ1 μ1' μ2 : Memory} {δ1 δ1' : CStore Γ1}
      {δ2 : CStore Γ2} {Q : Post2 Γ1 Γ2 τ} :
      ⟨ γ1, μ1, δ1, s1 ⟩ ---> ⟨ γ1', μ1', δ1', s1' ⟩ ->
      regs_inv2 γ1 γ2 ∗ mem_state_interp2 μ1 μ2 -∗
      £ 1 -∗
      semWP2 δ1 δ2 s1 s2 Q ={⊤,∅}=∗
                                    ▷ |={∅,⊤}=> (@regs_inv _ sailRegGS2_sailRegGS_left γ1' ∗ @IBleft.mem_state_interp _ memGS2_memGS_left μ1')
                  ∗ @IBleft.semWP _ sailGS2_sailGS_left _ _ δ1' s1' (λ (v1 : IVal τ) (δ1'0 : CStore Γ1),
                    ∃ (γ22 : RegStore) (μ22 : Memory) (δ2' : CStore Γ2) (s2' : Stm Γ2 τ) (v2 : IVal τ),
                      ⌜⟨ γ2, μ2, δ2, s2 ⟩ --->* ⟨ γ22, μ22, δ2', s2' ⟩⌝
                        ∗ ⌜stm_to_val s2' = Some v2⌝ ∗ @regs_inv _ sailRegGS2_sailRegGS_right γ22 ∗ @IBright.mem_state_interp _ memGS2_memGS_right μ22 ∗ Q v1 δ1'0 v2 δ2').
    Proof.
      iIntros (Hstep) "([Hreg1 Hreg2] & Hmem) Hlc Hwp".
      rewrite /semWP2.
      iDestruct (mem_state_interp2_mem_inv with "Hmem") as "[Hmem1 Hmem2]".
      iSpecialize ("Hwp" with "[$Hreg2 $Hmem2]").
      iApply (IBleft.semWP_step Hstep with "[Hreg1 Hmem1] [Hlc] Hwp"); eauto.
      iFrame "Hreg1 Hmem1".
    Qed.

    Lemma semWP2_seq_left {Γ1 Γ2 τ σ} (s1 : Stm Γ1 σ) (k1 : Stm Γ1 τ) (s2 : Stm Γ2 τ) :
      ⊢ ∀ (Q : Post2 Γ1 Γ2 τ) (δ1 : CStore Γ1) (δ2 : CStore Γ2),
          @IBleft.semWP _ sailGS2_sailGS_left _ _ δ1 s1 (λ v1 δ1',
              match v1 with
              | inl _  => semWP2 δ1' δ2 k1 s2 Q
              | inr m1 => semWP2 δ1' δ2 (of_ival (inr m1)) s2 Q
              end) -∗
          semWP2 δ1 δ2 (s1;;k1)%exp s2 Q.
    Proof.
      iIntros (Q δ1 δ2) "H". rewrite /semWP2. iIntros (γ21 μ21) "Hres".
      iApply IBleft.semWP_seq. iApply (IBleft.semWP_mono with "H").
      iIntros ([v1|m1] δ1') "H"; iApply ("H" with "Hres").
    Qed.

    Lemma semWP2_seq_right {Γ1 Γ2 τ σ} (s1 : Stm Γ1 τ) (s2 : Stm Γ2 σ) (k2 : Stm Γ2 τ) :
      ⊢ ∀ (Q : Post2 Γ1 Γ2 τ) (δ1 : CStore Γ1) (δ2 : CStore Γ2),
          @IBright.semTWP _ sailGS2_sailGS_right _ _ δ2 s2 (λ v2 δ2',
              match v2 with
              | inl _  => semWP2 δ1 δ2' s1 k2 Q
              | inr m2 => semWP2 δ1 δ2' s1 (of_ival (inr m2)) Q
              end) -∗
          semWP2 δ1 δ2 s1 (s2;;k2)%exp Q.
    Proof.
      iIntros (Q δ1 δ2) "H". rewrite /semWP2. iIntros (γ21 μ21) "Hres".
      iApply (IBleft.fupd_semWP ⊤).
      iMod (IBright.semTWP_Steps with "[Hres] H")
        as "(%γ22 & %μ22 & %δ2' & %s2' & %v2 & %Hsteps & %Hval & Hregs & Hmem & H)".
      { iDestruct "Hres" as "($ & $)". }
      iModIntro.
      destruct v2 as [v2|m2].
      - iSpecialize ("H" with "[$Hregs $Hmem]"). iApply (IBleft.semWP_mono with "H").
        iIntros (v1 δ1') "(%γ23 & %μ23 & %δ2'' & %s2'' & %v2' & %Hsteps' & %Hval' & Hregs & Hmem & H)".
        iExists γ23, μ23, δ2'', s2'', v2'. iFrame "Hregs Hmem H".
        iPureIntro. split; last done.
        rewrite (stm_to_val_Some_inl Hval) in Hsteps.
        eapply step_trans. constructor. apply (Steps_trans (Steps_bind Hsteps)).
        eapply step_trans. constructor. auto.
      - iSpecialize ("H" with "[$Hregs $Hmem]"). iApply (IBleft.semWP_mono with "H").
        iIntros (v1 δ1') "(%γ23 & %μ23 & %δ2'' & %s2'' & %v2' & %Hsteps' & %Hval' & Hregs & Hmem & H)".
        iExists γ23, μ23, δ2'', s2'', v2'. iFrame "Hregs Hmem H".
        iPureIntro. split; last done.
        rewrite (stm_to_val_Some_inr Hval) in Hsteps.
        eapply step_trans. constructor. apply (Steps_trans (Steps_bind Hsteps)).
        eapply step_trans. constructor. auto.
    Qed.

    Lemma semWP2_call_inline_left {Γ1 Γ2 τ Δ} (f : 𝑭 Δ τ)
      (es : NamedEnv (Exp Γ1) Δ) (s2 : Stm Γ2 τ) :
      ⊢ ∀ (Q : Post2 Γ1 Γ2 τ) (δ1 : CStore Γ1) (δ2 : CStore Γ2),
          semWP2 (evals es δ1) δ2 (FunDef f) s2 (λ v1 _ v2 δ2', Q v1 δ1 v2 δ2') -∗
          semWP2 δ1 δ2 (stm_call f es) s2 Q.
    Proof.
      iIntros (Q δ1 δ2) "H". rewrite /semWP2. iIntros (γ21 μ21) "Hres".
      iApply IBleft.semWP_call_inline. iApply ("H" with "Hres").
    Qed.

    Lemma semWP2_call_inline_right {Γ1 Γ2 τ Δ} (f : 𝑭 Δ τ)
      (s1 : Stm Γ1 τ) (es : NamedEnv (Exp Γ2) Δ) :
      ⊢ ∀ (Q : Post2 Γ1 Γ2 τ) (δ1 : CStore Γ1) (δ2 : CStore Γ2),
          semWP2 δ1 (evals es δ2) s1 (FunDef f) (λ v1 δ1' v2 _, Q v1 δ1' v2 δ2) -∗
          semWP2 δ1 δ2 s1 (stm_call f es) Q.
    Proof.
      iIntros (Q δ1 δ2) "H". rewrite /semWP2. iIntros (γ21 μ21) "Hres".
      iSpecialize ("H" with "Hres").
      iApply (IBleft.semWP_mono with "H").
      iIntros (v1 δ1') "(%γ22 & %μ22 & %δ2' & %s2' & %v2 & %Hf2 & %Hval & H)".
      iExists γ22, μ22, δ2, (of_ival v2), v2.
      iFrame "H". iPureIntro. split; last apply stm_to_val_of_ival.
      eapply step_trans. constructor. eapply Steps_trans.
      apply (Steps_call_frame Hf2). rewrite (stm_to_val_eq Hval).
      destruct (stm_to_val_Some_cases Hval) as [(? & -> & ->)|(? & -> & ->)];
        simpl; eapply step_trans; constructor.
    Qed.

  End WithSailGS2.
End IrisBinaryWP.

Module Type IrisSignatureRules2
  (Import GLOBAL : GlobalState)
  (Import SIG    : Signature GLOBAL)
  (Import PROG   : Program GLOBAL)
  (Import SEM    : Semantics GLOBAL PROG)
  (Import PLOG   : ProgramLogic GLOBAL SIG PROG)
  (Import IPre   : IrisPrelims GLOBAL PROG SEM)
  (IBleft : IrisBase GLOBAL PROG SEM IPre)
  (IBright : IrisBase GLOBAL PROG SEM IPre)
  (Import IB2    : IrisBase2 GLOBAL PROG SEM IPre IBleft IBright)
  (Import IPred  : IrisPredicates2 GLOBAL SIG PROG SEM IPre IBleft IBright IB2).

  Module Export IWP := IrisBinaryWP GLOBAL SIG PROG SEM IPre IBleft IBright IB2 IPred.

  Section WithSailGS2.
  Context `{sG : sailGS2 Σ}.

Section Soundness.

  Context {SPEC : Specification}.

  Definition semTriple {Γ τ} (δ : CStore Γ)
             (PRE : iProp Σ) (s : Stm Γ τ) (POST : Val τ -> CStore Γ -> iProp Σ) : iProp Σ :=
    PRE -∗
    semWP2 δ δ s s (λ v1 δ1 v2 δ2, ⌜v1 = v2⌝ ∗ ⌜δ1 = δ2⌝ ∗
                                   match v1 with
                                   | inl v1 => POST v1 δ1
                                   | inr m => if fail_rule_pre then True%I else False%I
                                   end)%I.
  (* always modality needed? perhaps not because sail not higher-order? *)
  Global Arguments semTriple {Γ} {τ} δ PRE%_I s%_exp POST%_I.

  Definition ValidLemma {Δ} (lem : Lemma Δ) : Prop :=
    match lem with
      {| lemma_logic_variables := Σ;
         lemma_patterns        := θΔ;
         lemma_precondition    := req;
         lemma_postcondition   := ens;
      |} =>
      forall (ι : Valuation Σ),
        ⊢ asn.interpret req ι -∗
          asn.interpret ens ι
    end.

  Lemma iris_rule_consequence {Γ σ} {δ : CStore Γ}
        {P P'} {Q Q' : Val σ -> CStore Γ -> iProp Σ} {s : Stm Γ σ} :
        (P ⊢ P') -> (forall v δ', Q' v δ' ⊢ Q v δ') ->
        semTriple δ P' s Q' -∗ semTriple δ P s Q.
  Proof.
    iIntros (PP QQ) "Htriple P".
    iApply (semWP2_mono with "[Htriple P]").
    - iApply "Htriple".
      now iApply PP.
    - iIntros (v1 δ1 v2 δ2) "(-> & -> & Q')".
      case_match; auto.
      iPoseProof (QQ with "Q'") as "Q"; auto.
  Qed.

  Lemma iris_rule_frame {Γ σ} {δ : CStore Γ}
        (R P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ) (s : Stm Γ σ) :
        (⊢ semTriple δ P s Q -∗ semTriple δ (R ∗ P) s (fun v δ' => R ∗ Q v δ'))%I.
  Proof.
    iIntros "Htriple [HR HP]".
    iSpecialize ("Htriple" with "HP").
    iPoseProof (semWP2_frame_l with "[HR Htriple]") as "Hwp".
    { iSplitL "HR". iExact "HR". iExact "Htriple". }
    iApply (semWP2_mono with "Hwp").
    iIntros ([] ? ? ?) "(R & <- & $ & H)"; auto.
    now iFrame "R H".
  Qed.

  Lemma iris_rule_pull {σ Γ} (δ : CStore Γ) (s : Stm Γ σ)
        (P : iProp Σ) (Q : Prop) (R : Val σ -> CStore Γ -> iProp Σ) :
        (⊢ (⌜ Q ⌝ -∗ semTriple δ P s R) -∗ semTriple δ (P ∧ bi_pure Q) s R).
  Proof.
    iIntros "QP [P %]".
    by iApply "QP".
  Qed.

  Lemma iris_rule_exist {σ Γ} (δ : CStore Γ)
        (s : Stm Γ σ) {A : Type} {P : A -> iProp Σ}
        {Q : Val σ -> CStore Γ -> iProp Σ} :
        ⊢ ((∀ x, semTriple δ (P x) s Q) -∗ semTriple δ (∃ x, P x) s Q).
  Proof.
    iIntros "Htriple [% P]".
    by iApply "Htriple".
  Qed.

  Lemma iris_rule_stm_val {Γ} (δ : CStore Γ)
        {τ : Ty} {v : Val τ}
        {P : iProp Σ} {Q : Val τ -> CStore Γ -> iProp Σ} :
        ⊢ ((P -∗ Q v δ)%I -∗ semTriple δ P (stm_val τ v) Q).
  Proof.
    iIntros "PQ P".
    iApply semWP2_val_1.
    iSpecialize ("PQ" with "P").
    iModIntro; by iFrame.
  Qed.

  Lemma iris_rule_stm_exp {Γ} (δ : CStore Γ)
        {τ : Ty} {e : Exp Γ τ}
        {P : iProp Σ} {Q : Val τ -> CStore Γ -> iProp Σ} :
        ⊢ ((P -∗ Q (eval e δ) δ) -∗ semTriple δ P (stm_exp e) Q).
  Proof.
    iIntros "PQ P".
    iApply semWP2_exp.
    iSpecialize ("PQ" with "P").
    now iFrame.
  Qed.

  Lemma iris_rule_stm_let {Γ} (δ : CStore Γ)
        (x : PVar) (σ τ : Ty) (s : Stm Γ σ) (k : Stm (Γ ▻ x∷σ) τ)
        (P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ)
        (R : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P s Q -∗
            (∀ (v : Val σ) (δ' : CStore Γ),
               semTriple (env.snoc δ' (x∷σ) v) (Q v δ') k (fun v δ'' => R v (env.tail δ''))) -∗
               semTriple δ P (let: x := s in k) R).
  Proof.
    iIntros "Hs Hk P".
    iApply semWP2_let.
    iSpecialize ("Hs" with "P").
    iApply (semWP2_mono with "Hs").
    iIntros (v1 δ1 v2 δ2) "(<- & <- & Q)".
    destruct v1 as [v1|m1].
    - iSpecialize ("Hk" $! v1 δ1 with "Q").
      iApply (semWP2_mono with "Hk").
      iIntros (? ? ? ?) "(<- & <- & R)".
      by iFrame "R".
    - simpl. iApply semWP2_fail. auto.
  Qed.

  Lemma iris_rule_stm_block {Γ} (δ : CStore Γ)
        (Δ : PCtx) (δΔ : CStore Δ)
        (τ : Ty) (k : Stm (Γ ▻▻ Δ) τ)
        (P : iProp Σ) (R : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple (δ ►► δΔ) P k (fun v δ'' => R v (env.drop Δ δ'')) -∗
            semTriple δ P (stm_block δΔ k) R).
  Proof.
    iIntros "Hk P". iApply semWP2_block. iSpecialize ("Hk" with "P").
    iApply (semWP2_mono with "Hk"). iIntros (? ? ? ?) "(<- & <- & R)".
    by iFrame "R".
  Qed.

  Lemma iris_rule_stm_seq {Γ} (δ : CStore Γ)
        (τ : Ty) (s1 : Stm Γ τ) (σ : Ty) (s2 : Stm Γ σ)
        (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) (R : Val σ -> CStore Γ -> iProp Σ) :
    ⊢ semTriple δ P s1 Q -∗
      (∀ v δ', semTriple δ' (Q v δ') s2 R) -∗
      semTriple δ P (s1 ;; s2) R.
  Proof.
    iIntros "Hs Hk P". iApply semWP2_seq. iSpecialize ("Hs" with "P").
    iApply (semWP2_mono with "Hs"). iIntros (v1 δ1 v2 δ2) "(<- & <- & Q)".
    destruct v1 as [v1|m1]; simpl.
    - now iSpecialize ("Hk" with "Q").
    - destruct fail_rule_pre; auto; now iApply semWP2_fail.
  Qed.

  Lemma iris_rule_stm_assertk {Γ τ} (δ : CStore Γ)
        (e1 : Exp Γ ty.bool) (e2 : Exp Γ ty.string) (k : Stm Γ τ)
                      (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
    ⊢ (⌜eval e1 δ = true⌝ -∗ semTriple δ P k Q) -∗
      (if fail_rule_pre then True else ⌜eval e1 δ ≠ false⌝) -∗
      semTriple δ P (stm_assertk e1 e2 k) Q.
  Proof.
    iIntros "Hk Hf P". destruct (eval e1 δ) eqn:Ee1.
    - iSpecialize ("Hk" with "[] P"); auto.
      iApply (semWP2_assertk with "[Hk]"); iIntros (H1e H2e);
        try (rewrite H1e in H2e, Ee1; discriminate);
        auto.
    - iApply semWP2_assertk;
        iIntros (H1 H2); rewrite Ee1 in H1, H2; try discriminate.
      destruct fail_rule_pre.
      + now iApply semWP2_fail.
      + by iDestruct "Hf" as "%Hf".
  Qed.

  Lemma iris_rule_stm_fail {Γ} (δ : CStore Γ)
    (τ : Ty) (s : Val ty.string) :
    forall {Q : Val τ -> CStore Γ -> iProp Σ},
      ⊢ semTriple δ (if fail_rule_pre then True else False) (stm_fail τ s) Q.
  Proof.
    iIntros (Q) "H".
    destruct fail_rule_pre; auto.
    now iApply semWP2_fail.
  Qed.

  Lemma iris_rule_stm_read_register {Γ} (δ : CStore Γ)
        {σ : Ty} (r : 𝑹𝑬𝑮 σ) (v : Val σ) :
    ⊢ (semTriple δ (lptsreg r v) (stm_read_register r)
         (λ v' δ', ⌜δ' = δ⌝ ∧ ⌜v' = v⌝ ∧ lptsreg r v)).
  Proof.
    iIntros "H". iApply semWP2_read_register. iExists v, v.
    iFrame. iIntros "H". repeat iSplit; auto.
  Qed.

  Lemma iris_rule_stm_write_register {Γ} (δ : CStore Γ)
        {σ : Ty} (r : 𝑹𝑬𝑮 σ) (w : Exp Γ σ)
                              (Q : Val σ -> CStore Γ -> iProp Σ)
                              (v : Val σ) :
        ⊢ semTriple δ (lptsreg r v) (stm_write_register r w)
            (λ v' δ',
              ⌜δ' = δ⌝ ∧ ⌜v' = eval w δ⌝ ∧ lptsreg r v').
  Proof.
    iIntros "H". iApply semWP2_write_register. iExists v, v.
    iFrame. iIntros "H". repeat iSplit; auto.
  Qed.

  Lemma iris_rule_stm_assign {Γ} (δ : CStore Γ)
        (x : PVar) (σ : Ty) (xIn : x∷σ ∈ Γ) (s : Stm Γ σ)
        (P : iProp Σ) (R : Val σ -> CStore Γ -> iProp Σ) :
    ⊢ (semTriple δ P s (fun v δ' => R v (@env.update _ _ _ δ' (x∷_) _ v)) -∗
           semTriple δ P (stm_assign x s) R).
  Proof.
    iIntros "Hk P". iApply semWP2_assign. iSpecialize ("Hk" with "P").
    iApply (semWP2_mono with "Hk"). iIntros (? ? ? ?) "(<- & <- & R)".
    destruct v1 as [v1|m1]; auto.
  Qed.

  Lemma iris_rule_stm_bind {Γ} (δ : CStore Γ)
        {σ τ : Ty} (s : Stm Γ σ) (k : Val σ -> Stm Γ τ)
        (P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ)
        (R : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P s Q -∗
           (∀ (v__σ : Val σ) (δ' : CStore Γ),
               semTriple δ' (Q v__σ δ') (k v__σ) R) -∗
           semTriple δ P (stm_bind s k) R).
  Proof.
    iIntros "trips tripk P".
    iSpecialize ("trips" with "P").
    iApply semWP2_bind.
    iApply (semWP2_mono with "trips").
    iIntros (v1 δ1 v2 δ2) "(<- & <- & HR)".
    destruct v1 as [v1|m1].
    - now iApply ("tripk" with "HR").
    - destruct fail_rule_pre; auto.
      now iApply semWP2_fail.
  Qed.

  Lemma iris_rule_stm_call_inline_later
    {Γ} (δΓ : CStore Γ)
    {Δ σ} (f : 𝑭 Δ σ) (es : NamedEnv (Exp Γ) Δ)
    (P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ) :
    ⊢ ▷ semTriple (evals es δΓ) P (FunDef f) (fun v _ => Q v δΓ) -∗
      semTriple δΓ P (stm_call f es) Q.
  Proof.
    iIntros "Hk P". iApply semWP2_call_inline_later. iModIntro.
    iSpecialize ("Hk" with "P"). iApply (semWP2_mono with "Hk").
    iIntros (? ? ? ?) "(<- & <- & Q)". now iFrame "Q".
  Qed.

  Lemma iris_rule_stm_call_inline
    {Γ} (δΓ : CStore Γ)
    {Δ σ} (f : 𝑭 Δ σ) (es : NamedEnv (Exp Γ) Δ)
    (P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ) :
    ⊢ semTriple (evals es δΓ) P (FunDef f) (fun v _ => Q v δΓ) -∗
      semTriple δΓ P (stm_call f es) Q.
  Proof.
    iIntros "Hk". now iApply iris_rule_stm_call_inline_later.
  Qed.

  Lemma iris_rule_stm_debugk
    {Γ τ} (δ : CStore Γ) (k : Stm Γ τ)
    (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
    ⊢ (semTriple δ P k Q -∗
       semTriple δ P (stm_debugk k) Q).
  Proof.
    iIntros "Hk P". iApply semWP2_debugk. iApply ("Hk" with "P").
  Qed.

  Lemma iris_rule_noop {Γ σ} {δ : CStore Γ}
        {P} {Q : Val σ -> CStore Γ -> iProp Σ} {s : Stm Γ σ} :
    stm_to_val s = None ->
    (forall {s' γ γ' μ μ' δ'}, ⟨ γ, μ, δ, s ⟩ ---> ⟨ γ', μ', δ', s' ⟩ ->
                            (γ' = γ) /\ (μ' = μ) /\ (δ' = δ) /\
                              (forall {γ2 μ2} {δ2 : CStore Γ}, ⟨ γ2, μ2, δ2, s ⟩ ---> ⟨ γ2, μ2, δ2, s' ⟩) /\
                            ((exists v, s' = stm_val _ v) \/ (exists msg, s' = stm_fail _ msg))) ->
    (∀ v, P ={⊤}=∗ Q v δ) -∗
                 semTriple δ P s Q.
  Proof.
    iIntros (Hnv Hnoop) "HPQ HP". rewrite /semWP2. iIntros (γ21 μ21) "(Hreg2 & Hmem2)".
    rewrite <-IBleft.semWP_unfold_nolc. rewrite Hnv. iIntros (γ11 μ11) "Hres1".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iIntros "!>" (s12 δ12 γ12 μ12 Hs).
    destruct (Hnoop _ _ _ _ _ _ Hs) as (-> & -> & -> & Hs2 & [[v ->]|[msg ->]]).
    - do 3 iModIntro. iMod "Hclose" as "_".
      iFrame. iModIntro. iApply IBleft.semWP_val.
      iExists γ21, μ21, δ, (of_ival (inl v)), (inl v).
      iMod ("HPQ" $! v with "HP") as "$". repeat iModIntro.
      iFrame "Hreg2 Hmem2". repeat iSplit; auto. iPureIntro. eapply step_trans.
      apply Hs2. apply step_refl.
    - do 3 iModIntro. iMod "Hclose" as "_". iFrame "Hres1".
      iModIntro. iApply IBleft.semWP_fail.
      repeat iModIntro. iExists γ21, μ21, δ, (of_ival (inr msg)), (inr msg).
      iFrame "Hreg2 Hmem2". repeat iSplit; auto. iPureIntro.
      eapply step_trans. apply Hs2. simpl. apply step_refl.
  Abort.

  Lemma iris_rule_stm_pattern_match {Γ τ σ} (δΓ : CStore Γ)
    (s : Stm Γ σ) (pat : Pattern σ)
    (rhs : ∀ pc : PatternCase pat, Stm (Γ ▻▻ PatternCaseCtx pc) τ)
    (P : iProp Σ) (Q : Val σ → CStore Γ → iProp Σ) (R : Val τ → CStore Γ → iProp Σ) :
    ⊢ semTriple δΓ P s Q -∗
      (∀ pc δpc δΓ1,
                semTriple (δΓ1 ►► δpc) (Q (pattern_match_val_reverse pat pc δpc) δΓ1) (rhs pc)
                  (λ vτ (δ' : CStore (Γ ▻▻ PatternCaseCtx pc)), R vτ (env.drop (PatternCaseCtx pc) δ'))) -∗
      semTriple δΓ P (stm_pattern_match s pat rhs) R.
  Proof.
    iIntros "Hs Hk P". iApply semWP2_pattern_match. iSpecialize ("Hs" with "P").
    iApply (semWP2_mono with "Hs"). iIntros (v1 δ1 v2 δ2) "(<- & <- & Q)".
    destruct v1 as [v1|m1].
    - destruct (pattern_match_val pat v1) as [pc δpc] eqn:Ev1.
      iSpecialize ("Hk" $! pc δpc δ1 with "[Q]").
      { change (pattern_match_val_reverse pat pc δpc) with
          (pattern_match_val_reverse' pat (existT pc δpc)).
        rewrite <- Ev1. now rewrite pattern_match_val_inverse_left. }
      iApply (semWP2_mono with "Hk"). iIntros (? ? ? ?) "(<- & <- & R)".
      now iFrame "R".
    - destruct fail_rule_pre; auto.
      now iApply semWP2_fail.
  Qed.

  Definition ValidContractSemCurried {Δ σ} (body : Stm Δ σ) (contract : SepContract Δ σ) : iProp Σ :=
    match contract with
    | MkSepContract _ _ ctxΣ θΔ pre result post =>
      Sep.Logic.Forall (fun (ι : Valuation ctxΣ) =>
        semTriple (inst θΔ ι) (asn.interpret pre ι) body
                  (fun v δ' => asn.interpret post (env.snoc ι (result∷σ) v)))
    end.

  (* Uses projections rather than a match, so that using it for a concrete
     contract does not unfold the contract. *)
  Definition ValidContractSem {Δ σ} (body : Stm Δ σ) (contract : SepContract Δ σ) : iProp Σ :=
    ∀ (ι : Valuation (sep_contract_logic_variables contract)),
      semTriple (inst (sep_contract_localstore contract) ι)
        (asn.interpret (sep_contract_precondition contract) ι) body
        (λ v δ, asn.interpret (sep_contract_postcondition contract)
                  (env.snoc ι (sep_contract_result contract∷σ) v)).

  Definition ValidContractForeign {Δ τ} (contract : SepContract Δ τ) (f : 𝑭𝑿 Δ τ) : Prop :=
    forall Γ (es : NamedEnv (Exp Γ) Δ) (δ : CStore Γ),
      match contract with
      | MkSepContract _ _ Σ' θΔ req result ens =>
        forall (ι : Valuation Σ'),
        evals es δ = inst θΔ ι ->
        ⊢ semTriple δ (asn.interpret req ι) (stm_foreign f es)
          (λ v δ', asn.interpret ens (env.snoc ι (result∷τ) v) ∗ bi_pure (δ' = δ))
      end.

  Definition valid_contract_curry {Δ σ} (body : Stm Δ σ) (contract : SepContract Δ σ) :
    ValidContractSem body contract ⊣⊢ ValidContractSemCurried body contract.
  Proof.
    destruct contract as [lvars δ req res ens]; cbn.
    now rewrite Forall_forall.
  Qed.

End Soundness.
End WithSailGS2.

End IrisSignatureRules2.
