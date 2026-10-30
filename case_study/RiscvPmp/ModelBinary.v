(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel, Dominique Devriese, Sander Huyghebaert  *)
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
     Program.Tactics
     Lists.List.
From Katamaran Require Import
     Bitvector
     Environment
     Iris.BinaryInstance
     Program
     Semantics
     Sep.Hoare
     RiscvPmp.PmpCheck
     RiscvPmp.Machine
     RiscvPmp.Logic
     RiscvPmp.Contracts
     RiscvPmp.Model
     RiscvPmp.IrisModel
     RiscvPmp.IrisModelBinary
     RiscvPmp.IrisInstance
     RiscvPmp.IrisInstanceBinary
     RiscvPmp.Sig.
From Equations Require Import
     Equations.

From iris.base_logic Require lib.gen_heap lib.iprop.
From iris.base_logic Require Export invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac.
From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import string_ident proofmode.

Set Implicit Arguments.
Import ListNotations.
Import bv.notations.

Import RiscvPmpProgram.
Import RiscvPmpSignature.

Ltac destruct_syminstance ι :=
  repeat
    match type of ι with
    | Env _ (ctx.snoc _ (MkB ?s _)) =>
        string_to_ident_cps s
          ltac:(fun id =>
                  let fr := fresh id in
                  destruct (env.view ι) as [ι fr];
                  destruct_syminstance ι)
    | Env _ ctx.nil => destruct (env.view ι)
    | _ => idtac
    end.


Module Type RiscvPmpModel2
  (Import RVPCOM : RiscvPmpIrisBaseCommon)
  (RVPBASEl : RiscvPmpIrisBase LeftOrRightLeft RVPCOM)
  (RVPPREDl : RiscvPmpIrisInstancePredicates LeftOrRightLeft RVPCOM RVPBASEl)
  (RVPINSTl : RiscvPmpIrisInstance LeftOrRightLeft RVPCOM RVPBASEl RVPPREDl)
  (RVPBASEr : RiscvPmpIrisBase LeftOrRightRight RVPCOM)
  (RVPPREDr : RiscvPmpIrisInstancePredicates LeftOrRightRight RVPCOM RVPBASEr)
  (RVPINSTr : RiscvPmpIrisInstance LeftOrRightRight RVPCOM RVPBASEr RVPPREDr)
  (Import RVPBASE2 : RiscvPmpIrisBase2 RVPCOM RVPBASEl RVPBASEr)
  (Import RVPPRED2 : RiscvPmpIrisInstancePredicates2 RVPCOM RVPBASEl RVPPREDl RVPBASEr RVPPREDr RVPBASE2)
  (Import RVPADEQ2 : RiscvPmpIrisAdeqParams2 RVPCOM RVPBASEl RVPBASEr RVPBASE2)
  (Import RVPINST2 : RiscvPmpIrisInstance2 RVPCOM RVPBASEl RVPPREDl RVPBASEr RVPPREDr RVPBASE2 RVPPRED2 RVPADEQ2).
  Import RiscvPmpSignature.
  Import RiscvPmpSpecification.
  Import RiscvPmpProgram.

  Include IrisInstanceWithContracts2 RiscvPmpGlobalState RiscvPmpSignature RiscvPmpProgram
    RiscvPmpSemantics RiscvPmpProgramLogic
    RVPCOM RVPBASEl RVPBASEr RVPBASE2 RVPADEQ2 RVPINST2.

  Section ForeignProofs.
    Context `{sg : sailGS2 Σ}.

    #[export] Existing Instance sailGS2_invGS.
    #[export] Existing Instance sailGS2_regGS2.
    #[export] Existing Instance sailGS2_memGS.

    Local Instance hmemGS2 : memGS2 Σ := sailGS2_memGS.

    Ltac eliminate_prim_step Heq :=
      let f := fresh "f" in
      match goal with
      | H: RiscvPmpSemantics.Step _ _ _ _ _ _ _ _ |- _ =>
          dependent elimination H as [RiscvPmpSemantics.st_foreign _ _ f];
          rewrite Heq in f;
          cbn in f;
          dependent elimination f;
          cbn
      end.


    Lemma interp_ptstomem_exists_intro (bytes : nat) :
      ⊢ ∀ (paddr : Addr) (w : bv (bytes * byte)),
          interp_ptstomem (mG := sailGS2_memGS) paddr w -∗
                                                           ∃ (w : bv (bytes * byte)), interp_ptstomem (mG := sailGS2_memGS) paddr w.
    Proof. auto. Qed.

    Definition sailGS2_sailGS_left `{sailGS2 Σ} : RVPBASEl.sailGS Σ :=
      RVPBASEl.SailGS sailGS2_invGS sailRegGS2_sailRegGS_left (memGS2_memGS_left (mG := sailGS2_memGS)).

    Definition sailGS2_sailGS_right `{sailGS2 Σ} : RVPBASEr.sailGS Σ :=
      RVPBASEr.SailGS sailGS2_invGS sailRegGS2_sailRegGS_right (memGS2_memGS_right (mG := sailGS2_memGS)).

    Lemma pmp_entries_ptsto : ∀ (entries : list PmpEntryCfg),
        ⊢ interp_pmp_entries entries -∗
          ∃ (cfg0 : Pmpcfg_ent) (addr0 : Addr) (cfg1 : Pmpcfg_ent) (addr1 : Addr),
            ⌜entries = [(cfg0, addr0); (cfg1, addr1)]⌝ ∗
            reg_pointsTo21 pmp0cfg cfg0 ∗ reg_pointsTo21 pmpaddr0 addr0 ∗
            reg_pointsTo21 pmp1cfg cfg1 ∗ reg_pointsTo21 pmpaddr1 addr1.
    Proof.
      iIntros (entries) "H".
      destruct entries as [|[cfg0 addr0] [|[cfg1 addr1] [|]]] eqn:?; try done.
      repeat iExists _.
      now iFrame.
    Qed.

    Lemma interp_pmpentries_dedup : ∀ (entries : list PmpEntryCfg),
        interp_pmp_entries entries ⊣⊢
          RVPPREDl.interp_pmp_entries (H := sailRegGS2_sailRegGS_left) entries ∗
          RVPPREDr.interp_pmp_entries (H := sailRegGS2_sailRegGS_right) entries.
    Proof.
      iIntros (entries).
      destruct entries as [|[cfg0 addr0] [|[cfg1 addr1] [|]]] eqn:?; cbn;
      try (iSplit; iIntros; now destruct H).
      iSplit.
      - iIntros "([$ $] & [$ $] & [$ $] & [$ $])".
      - iIntros "(($ & $ & $ & $) & ($ & $ & $ & $))".
    Qed.

    Lemma read_ram_sound (bytes : nat) :
      ValidContractForeign (sep_contract_read_ram bytes) (read_ram bytes).
    Proof.
      intros Γ es δ ι Heq. cbn. destruct_syminstance ι. cbn.
      iIntros "(HmemL & HmemR)". cbn in *. iApply semWP2_foreign.
      iIntros (? ?) "(Hreg & %memmapL & Hmem & %HmapL & Htr & Hpw)".
      iPoseProof (RVPINSTl.fun_read_ram_works (sr := sailGS2_sailGS_left) HmapL with "[$HmemL $Hmem]") as "%eq_fun_read_ram_l".
      iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
      iIntros (res1 ? ? Hf1). rewrite Heq in Hf1. cbn in Hf1.
      inversion Hf1; subst. iIntros "!> !> !>". iMod "Hclose" as "_". iModIntro.
      iFrame "Hreg Hmem Htr Hpw". iSplitR; first by iPureIntro.
      iIntros (? ?) "(Hreg & %memmapR & Hmem & %HmapR & Htr & Hpw)".
      iPoseProof (RVPINSTr.fun_read_ram_works (sr := sailGS2_sailGS_right) HmapR with "[$HmemR $Hmem]") as "%eq_fun_read_ram_r".
      iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
      iIntros (res2 ? ? Hf2). rewrite Heq in Hf2. cbn in Hf2.
      inversion Hf2; subst. iMod "Hclose" as "_". iModIntro.
      iFrame "Hreg Hmem Htr Hpw". iSplitR; first by iPureIntro.
      iApply semWP2_val_1. rewrite eq_fun_read_ram_r. now iFrame "HmemL HmemR".
    Qed.

    Lemma write_ram_sound (bytes : nat) :
      ValidContractForeign (sep_contract_write_ram bytes) (write_ram bytes).
    Proof.
      intros Γ es δ ι Heq. cbn. destruct_syminstance ι. cbn.
      iIntros "(%v & HmemL & HmemR)". cbn in *. iApply semWP2_foreign.
      iIntros (? ?) "(Hreg & %memmapL & Hmem & %HmapL & Htr & Hpw)".
      iMod (RVPINSTl.fun_write_ram_works (sr := sailGS2_sailGS_left) with "[$HmemL $Hmem $Htr $Hpw]") as "(Hmem & HmemL)"; first done.
      iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
      iIntros (res1 ? ? Hf1). rewrite Heq in Hf1. cbn in Hf1.
      inversion Hf1; subst. iIntros "!> !> !>". iMod "Hclose" as "_". iModIntro.
      iFrame "Hreg Hmem".
      iIntros (? ?) "(Hreg & %memmapR & Hmem & %HmapR & Htr & Hpw)".
      iMod (RVPINSTr.fun_write_ram_works  (sr := sailGS2_sailGS_right) with "[$HmemR $Hmem $Htr $Hpw]") as "(Hmem & HmemR)"; first done.
      iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
      iIntros (res2 ? ? Hf2). rewrite Heq in Hf2. cbn in Hf2.
      inversion Hf2; subst. iMod "Hclose" as "_". iModIntro. iFrame "Hreg Hmem".
      iApply semWP2_val_1. now iFrame "HmemL HmemR".
    Qed.

    Lemma decode_sound :
      ValidContractForeign sep_contract_decode decode.
    Proof.
      intros Γ es δ ι Heq. cbn. destruct_syminstance ι. cbn.
      iIntros "_". cbn in *. iApply semWP2_foreign. iIntros (? ?) "Hres1".
      iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
      iIntros (res1 ? ? Hf1). rewrite Heq in Hf1. cbn in Hf1.
      inversion Hf1; subst. iFrame "Hres1". iIntros "!> !> !>".
      iMod "Hclose" as "_". iModIntro.
      iIntros (? ?) "Hres2". iMod (fupd_mask_subseteq empty) as "Hclose"; auto.
      iModIntro. iIntros (res2 ? ? Hf2). rewrite Heq in Hf2. cbn in Hf2.
      inversion Hf2; subst. iFrame "Hres2". iMod "Hclose" as "_". iModIntro.
      destruct (pure_decode _).
      - now iApply semWP2_fail.
      - now iApply semWP2_val_1.
    Qed.

    Lemma mmio_read_sound `(H: restrict_bytes bytes) :
     ValidContractForeign (sep_contract_mmio_read H) (mmio_read H).
    Proof.
      intros Γ es δ ι Heq. destruct_syminstance ι. cbn.
      now iIntros "[%HFalse _]".
    Qed.

    Lemma mmio_write_sound `(H: restrict_bytes bytes) :
     ValidContractForeign (sep_contract_mmio_write H) (mmio_write H).
    Proof.
      intros Γ es δ ι Heq. destruct_syminstance ι. cbn.
      now iIntros "[%HFalse _]".
    Qed.

    (* NOTE: duplicate of the same lemma in the unary iris instance (IrisInstance.v). *)
    Lemma interp_addr_access_app base width width':
      interp_addr_access liveAddrs mmioAddrs base (width + width') ⊣⊢
      interp_addr_access liveAddrs mmioAddrs base width ∗ interp_addr_access liveAddrs mmioAddrs (base + bv.of_nat width) width'.
    Proof.
      unfold interp_addr_access.
      rewrite Nat2Z.inj_add bv.seq_add ?bv.of_Z_nat ?big_sepL_app //; lia.
    Qed.

    (* NOTE: duplicate of the same lemma in the unary iris instance (IrisInstance.v). *)
    Lemma interp_addr_access_cons base width:
      interp_addr_access liveAddrs mmioAddrs base (S width) ⊣⊢
      interp_addr_access_byte liveAddrs mmioAddrs base ∗ interp_addr_access liveAddrs mmioAddrs (base + bv.of_nat 1) width.
    Proof. rewrite <-Nat.add_1_l.
           rewrite interp_addr_access_app.
           unfold interp_addr_access, interp_addr_access_byte.
           by rewrite bv.seq_one big_sepL_singleton.
    Qed.

    (* NOTE: duplicate of the same lemma in the unary iris instance (IrisInstance.v). *)
    Lemma interp_pmp_within_mmio_spec {entries m p} (paddr : Addr) bytes :
      (bv.unsigned paddr + Z.of_nat bytes < 2 ^ Z.of_nat xlenbits)%Z ->
      Pmp_access paddr (bv.of_nat bytes) entries m p →
      interp_pmp_addr_access liveAddrs mmioAddrs entries m -∗
      ⌜bool_decide (withinMMIO paddr bytes) = false%nat⌝.
    Proof.
      iIntros (Hrep Hpmp) "Hint".
      destruct bytes as [|bytes]. (* No induction needed: disproving one location suffices. *)
      - rewrite bool_decide_eq_false. iPureIntro. intros [? _]. lia.
      - rewrite interp_pmp_addr_inj_extr; eauto.
        iDestruct "Hint" as "[Hint _]".
        iDestruct (interp_addr_access_cons with "Hint") as "[Hfirst _]".
        unfold interp_addr_access_byte.
        case_decide; auto.
        iPureIntro.
        rewrite bool_decide_eq_false. intros ?%withinMMIO_elem_of_base.
        congruence.
    Qed.

    (* NOTE: duplicate of the same lemma in the unary model (Model.v). *)
    Lemma interp_pmp_fun_within_mmio_spec {entries m p} (paddr : Addr) bytes:
      Pmp_access paddr (bv.of_nat bytes) entries m p →
      interp_pmp_addr_access liveAddrs mmioAddrs entries m -∗
      ⌜fun_within_mmio bytes paddr = false%nat⌝.
    Proof.
      iIntros (Hpmp) "Hint". rewrite /fun_within_mmio.
      rewrite bool_decide_and andb_false_iff.
      destruct (decide (bv.unsigned paddr + Z.of_nat bytes < 2 ^ Z.of_nat xlenbits)%Z) as [Hlt | Hnlt].
      - iDestruct (interp_pmp_within_mmio_spec with "Hint") as "->"; eauto.
      - iPureIntro. right.
        by rewrite bool_decide_false.
    Qed.

    Lemma within_mmio_sound `(H: restrict_bytes bytes) :
     ValidContractForeign (@sep_contract_within_mmio bytes H) (within_mmio H).
    Proof.
      intros Γ es δ ι Heq. destruct_syminstance ι. cbn in *.
      iIntros "(Hcurp & Hpmp & Hpmpa & [%acc [%Hpmp _]])".
      iApply semWP2_foreign. iIntros (? ?) "(Hregs & % & Hmem & %HmapL & Htr & Hpw)".
      iPoseProof (interp_pmp_fun_within_mmio_spec with "Hpmpa") as "%HnotmmioL"; first eauto.
      iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
      iIntros (res1 ? ? Hf1). rewrite Heq in Hf1. cbn in Hf1.
      inversion Hf1; subst. iFrame "Hregs Hmem Htr Hpw". iIntros "!> !> !>".
      iMod "Hclose" as "_". iModIntro.
      iSplitR; first auto. iIntros (? ?) "(Hregs & % & Hmem & %HmapR & Htr & Hpw)".
      iPoseProof (interp_pmp_fun_within_mmio_spec with "Hpmpa") as "%HnotmmioR"; first eauto.
      iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
      iIntros (res2 ? ? Hf2). rewrite Heq in Hf2. cbn in Hf2.
      inversion Hf2; subst. iFrame "Hregs Hmem Htr Hpw". iMod "Hclose" as "_".
      iModIntro. iSplitR; auto. iApply semWP2_val_1.
      iFrame "Hpmp Hpmpa Hcurp". now iPureIntro.
    Qed.

    Lemma externalWorldUpdates_sound :
      ValidContractForeign sep_contract_externalWorldUpdates externalWorldUpdates.
    Proof.
      intros Γ es δ ι Heq. destruct_syminstance ι. cbn.
      iIntros "[Hmip1 Hmip2]".
      iApply semWP2_foreign.
      iIntros (γ μ) "(Hregs1 & Hmem)".
      iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
      iIntros (res γ' μ' Hfc). do 3 iModIntro.
      rewrite Heq in Hfc; cbn in Hfc; unfold fun_externalWorldUpdates in Hfc.
      (* destruct state_tra_world_updates as (vmip' , s') eqn:Hstwu. *)
      inversion Hfc; subst.
      iMod (reg_update γ mip vmip _ with "Hregs1 Hmip1") as "[Hregs1 Hmip1]".
      iMod "Hclose" as "_". iModIntro.
      iFrame "Hregs1 Hmem".
      iIntros (γ2 μ2) "[Hregs2 Hmem2]".
      iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
      iIntros (res2 γ2' μ2' Hfc2).
      rewrite Heq in Hfc2; cbn in Hfc2; unfold fun_externalWorldUpdates in Hfc2.
      inversion Hfc2; subst.
      iMod "Hclose" as "_".
      iMod (reg_update γ2 mip vmip _ with "Hregs2 Hmip2") as "[Hregs2 Hmip2]".
      iModIntro.
      iFrame "Hregs2 Hmem2".
      iApply semWP2_val_1.
      now iModIntro; iFrame.
    Qed.

    Lemma powered_on_sound :
      ValidContractForeign sep_contract_powered_on powered_on.
    Proof.
      intros Γ es δ ι Heq. destruct_syminstance ι. cbn.
      now iIntros "[%HFalse _]".
    Qed.

    Lemma foreignSem : ForeignSem.
    Proof.
      intros Δ τ f; destruct f; cbn;
        eauto using read_ram_sound, write_ram_sound, decode_sound,
                    mmio_read_sound, mmio_write_sound, within_mmio_sound,
                    externalWorldUpdates_sound, powered_on_sound.
    Qed.
  End ForeignProofs.

  Section LemProofs.
    Context `{sg : sailGS2 Σ}.

    Import IrisInstance.

    Lemma interp_gprs_split (exclude : gset (Reg ty_xlenbits)) :
      interp_gprs exclude ⊢
        @RVPPREDl.interp_gprs _ sailRegGS2_sailRegGS_left exclude
        ∗ @RVPPREDr.interp_gprs _ sailRegGS2_sailRegGS_right exclude.
    Proof.
      unfold interp_gprs, RVPPREDl.interp_gprs, RVPPREDr.interp_gprs.
      remember (elements (GPRS ∖ exclude)) as l eqn:El.
      assert (Hdup: NoDup l) by (subst; apply NoDup_elements).
      assert (Hl: list_to_set l = GPRS ∖ exclude) by (subst; apply list_to_set_elements_L).
      rewrite <- Hl.
      rewrite ?big_sepS_list_to_set; auto.
      clear El Hdup Hl.
      iInduction l as [|gpr gprs] "IH";
        iIntros "H"; simpl; auto.
      iDestruct "H" as "((% & $ & $) & H)".
      iApply ("IH" with "H").
    Qed.

    Lemma open_gprs_sound :
      ValidLemma RiscvPmpSpecification.lemma_open_gprs.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      rewrite (gprs_equiv env.nil). cbn. iIntros. iFrame.
    Qed.

    Lemma close_gprs_sound :
      ValidLemma RiscvPmpSpecification.lemma_close_gprs.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      rewrite (gprs_equiv env.nil). cbn. iIntros. iFrame.
    Qed.

    Lemma open_ptsto_instr_sound :
      ValidLemma RiscvPmpSpecification.lemma_open_ptsto_instr.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      now iIntros.
    Qed.

    Lemma close_ptsto_instr_sound :
      ValidLemma RiscvPmpSpecification.lemma_close_ptsto_instr.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      now iIntros.
    Qed.

    Lemma open_pmp_entries_sound :
      ValidLemma RiscvPmpSpecification.lemma_open_pmp_entries.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      iIntros "H".
      iPoseProof (pmp_entries_ptsto with "H") as "(% & % & % & % & -> & Hpmp0cfg & Hpmpaddr0 & Hpmp1cfg & Hpmpaddr1)".
      repeat iExists _.
      now iFrame "Hpmp0cfg Hpmp1cfg Hpmpaddr0 Hpmpaddr1".
    Qed.

    Lemma close_pmp_entries_sound :
      ValidLemma RiscvPmpSpecification.lemma_close_pmp_entries.
    Proof. intros ι; destruct_syminstance ι; cbn; auto. Qed.

    Lemma minAddr_le_ule : forall (addr : Addr),
      (Z.of_N minAddr <= bv.unsigned addr)%Z <-> bv.of_N minAddr <=ᵘ addr.
    Proof.
      intros. by rewrite bv.ule_iff_unsigned_le.
    Qed.

    Lemma maxAddr_le_ule : forall (addr : Addr) (bytes : nat),
        (bv.unsigned addr + Z.of_nat bytes < 2 ^ Z.of_nat xlenbits)%Z ->
         (bv.unsigned addr + Z.of_nat bytes <= Z.of_N maxAddr)%Z -> addr + bv.of_nat bytes <=ᵘ bv.of_N maxAddr.
    Proof.
      intros addr bytes Hrep H. pose proof (bv.unsigned_bounds addr).
      rewrite bv.ule_iff_unsigned_le -bv.unsigned_add_small -bv.of_Z_nat -bv.unsigned_of_Z_small;
        change (bv.unsigned (bv.of_N maxAddr)) with (Z.of_N maxAddr); lia.
    Qed.

    Lemma in_liveAddrs : forall (addr : Addr),
        (bv.of_N minAddr <=ᵘ addr) ->
        (addr <ᵘ bv.of_N maxAddr) ->
        addr ∈ liveAddrs.
    Proof.
      unfold liveAddrs, maxAddr.
      intros addr Hmin%bv.ule_iff_unsigned_le Hmax%bv.ult_iff_unsigned_lt.
      apply bv.elem_of_seq_bounds; first done.
      change (bv.unsigned (bv.of_N ?x)) with (Z.of_N x) in *; lia.
    Qed.

    Opaque minAddr.
    Opaque lenAddr.
    Opaque xlenbits.

    Lemma in_liveAddrs_split : forall (addr : Addr) (bytes : nat),
        (bv.unsigned addr + Z.of_nat bytes < 2 ^ Z.of_nat xlenbits)%Z ->
        (bv.of_N minAddr <=ᵘ addr) ->
        (addr + (bv.of_nat bytes) <=ᵘ bv.of_N maxAddr) ->
        exists l1 l2, liveAddrs = l1 ++ (bv.seq addr (Z.of_nat bytes)  ++ l2).
    Proof.
      intros addr bytes Hrep Hmin%bv.ule_iff_unsigned_le Hmax%bv.ule_iff_unsigned_le.
      pose proof (bv.unsigned_bounds addr).
      rewrite -bv.unsigned_add_small -bv.of_Z_nat -bv.unsigned_of_Z_small in Hmax; [|lia..].
      apply bv.seq_sub_list; unfold maxAddr in *;
        change (bv.unsigned (bv.of_N ?x)) with (Z.of_N x) in *; lia.
    Qed.

    Lemma N_of_nat_lt_S : forall w n,
        (N.of_nat (S n) < bv.exp2 w)%N ->
        (N.of_nat n < bv.exp2 w)%N.
    Proof. lia. Qed.

    (* TODO: better name! *)
    Lemma bv_ule_base : forall {n} (base a b max : bv n),
        (bv.unsigned base + bv.unsigned a < 2 ^ Z.of_nat n)%Z ->
        b <=ᵘ a ->
        base + a <=ᵘ max ->
        base + b <=ᵘ max.
    Proof.
      intros n base a b max Hn Hba Hmax.
      apply bv.ule_trans with (y := base + a); last done.
      rewrite bv.ule_iff_unsigned_le in Hba.
      rewrite bv.ule_iff_unsigned_le -!bv.unsigned_add_small; lia.
    Qed.

    Lemma big_sepL_pure_impl (bytes : nat) :
        ∀ (paddr : Addr)
            (entries : list PmpEntryCfg) (p : Privilege) p0,
            (Pmp_access paddr (bv.of_nat bytes) entries p p0) ->
            (bv.unsigned paddr + Z.of_nat bytes < 2 ^ Z.of_nat xlenbits)%Z ->
            (Z.of_nat bytes < 2 ^ Z.of_nat xlenbits)%Z ->
            ⊢ (([∗ list] offset ∈ bv.seq paddr (Z.of_nat bytes),
               ⌜∃ p0, Pmp_access offset%bv
                        (bv.of_nat 1) entries p p0⌝ -∗
                        ∃ w : Byte, interp_ptsto (mG := sailGS2_memGS) offset w)
              ∗-∗
              (⌜∃ p0, Pmp_access paddr (bv.of_nat bytes) entries p p0⌝ -∗
                        [∗ list] offset ∈ bv.seq paddr (Z.of_nat bytes),
                 ∃ w : Byte, interp_ptsto (mG := sailGS2_memGS) offset w))%I.
    Proof.
      pose proof xlenbits_pos.
      iInduction bytes as [|bytes] "IHbytes"; iIntros (paddr pmp p p0 Hpmp Hrep Hbytes) "".
      { now iSimpl; iSplit; iIntros. }
      iSplit; iIntros "H".
      - iIntros "[%acc %Haccess]".
        simpl.
        rewrite Nat2Z.inj_succ bv.seq_succ; last lia.
        rewrite big_sepL_cons.
        iDestruct "H" as "[Hb Hbs]".
        iSplitL "Hb".
        iApply ("Hb" with "[%]").
        exists acc.
        assert (Htmp: (N.of_nat 1 < bv.exp2 xlenbits)%N) by lia.
        rewrite (@bv.unsigned_of_Z_small xlenbits (Z.of_nat (S bytes))) ?bv.of_Z_nat in Hrep; last lia.
        refine (pmp_access_reduced_width Hrep (bv.ult_nat_S_zero Htmp) (bv.ule_nat_one_S (n := bytes) Htmp ltac:(lia)) Haccess).
        destruct bytes; first by simpl. (* we need to know a bit more about bytes to finish this case *)
        iSimpl in "Hbs".
        apply pmp_access_addr_S_width_pred in Haccess; try lia.
        rewrite bv.add_comm in Haccess.
        iApply ("IHbytes" $! (bv.one + paddr) pmp p acc Haccess with "[%] [%] Hbs"); try lia.
        rewrite -bv.unsigned_succ_small; lia.
        now iExists acc.
        rewrite -bv.of_Z_nat -bv.unsigned_of_Z_small; lia.
      - iSpecialize ("H" $! (ex_intro _ _ Hpmp)).
        rewrite Nat2Z.inj_succ bv.seq_succ; last lia.
        iDestruct "H" as "[Hw H]"; fold seq.
        simpl.
        iSplitL "Hw"; auto.
        destruct bytes; first now simpl.
        apply pmp_access_addr_S_width_pred in Hpmp; auto.
        rewrite bv.add_comm in Hpmp.
        iApply ("IHbytes" $! (bv.one + paddr) pmp p p0 Hpmp with "[%] [%]"); auto; try lia.
        rewrite -bv.unsigned_succ_small; lia.
        rewrite -bv.of_Z_nat -bv.unsigned_of_Z_small; lia.
    Qed.

    Lemma extract_pmp_ptsto_sound (bytes : nat) :
      ValidLemma (RiscvPmpSpecification.lemma_extract_pmp_ptsto bytes).
    Proof.
      intros ι; destruct_syminstance ι; cbn - [liveAddrs].
      iIntros "[Hmem [[%Hlemin _] [[%Hlemax _] [%Hpmp _]]]]".
      unfold interp_pmp_addr_access_without,
        interp_pmp_addr_access,
        interp_ptsto,
        MemVal, Word.
      assert (bv.unsigned paddr + Z.of_nat bytes < 2 ^ Z.of_nat xlenbits)%Z.
      { pose proof maxAddr_rep.
        change (bv.unsigned paddr) with (@bv.unsigned xlenbits paddr) in *. lia. }
      iDestruct (interp_pmp_addr_inj_extr with "Hmem") as "[Hmemwo Hia]"; eauto.
      iFrame.
      iApply interp_addr_access_extr; last iFrame; eauto.
    Qed.

    Lemma return_pmp_ptsto_sound (bytes : nat) :
      ValidLemma (RiscvPmpSpecification.lemma_return_pmp_ptsto bytes).
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      iIntros "[Hwithout Hptsto]".
      iDestruct (interp_addr_access_inj with "Hptsto") as "Hacc".
      unfold interp_pmp_addr_access_without.
      iApply ("Hwithout" with "Hacc").
    Qed.

    Lemma close_mmio_write_sound (imm : bv 12) (width : WordWidth):
      ValidLemma (RiscvPmpSpecification.lemma_close_mmio_write imm width).
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      now iIntros.
    Qed.

    Lemma lemSem : LemmaSem.
    Proof.
      intros Δ []; cbn - [ValidLemma];
        eauto using open_gprs_sound, close_gprs_sound, open_ptsto_instr_sound, close_ptsto_instr_sound, open_pmp_entries_sound,
        close_pmp_entries_sound, extract_pmp_ptsto_sound, return_pmp_ptsto_sound, close_mmio_write_sound.
    Qed.
  End LemProofs.

End RiscvPmpModel2.
