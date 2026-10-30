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
     Iris.Instance
     Iris.Base
     Program
     Semantics
     Sep.Hoare
     RiscvPmp.PmpCheck
     RiscvPmp.Machine
     RiscvPmp.Logic
     RiscvPmp.Contracts
     RiscvPmp.IrisModel
     RiscvPmp.IrisInstance
     RiscvPmp.Sig
     RiscvPmp.trace.
From Equations Require Import
     Equations.

From iris.base_logic Require lib.gen_heap lib.iprop.
From iris.base_logic Require Export invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac.
From iris.program_logic Require Import weakestpre total_weakestpre adequacy.
From iris.program_logic Require lifting.
From iris.program_logic Require total_lifting.
From iris.proofmode Require Import string_ident proofmode.

Set Implicit Arguments.
Import ListNotations.
Import bv.notations.

Import RiscvPmpProgram.
Import RiscvPmpSignature.
(* Import RiscvPmpIrisInstancePredicates. *)

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

Module Type RiscvPmpModel
  (LOR : LeftOrRight)
  (Import RVPCOM : RiscvPmpIrisBaseCommon)
  (Import RVPBASE : RiscvPmpIrisBase LOR RVPCOM)
  (Import RVPPRED : RiscvPmpIrisInstancePredicates LOR RVPCOM RVPBASE)
  (Import RVPINST : RiscvPmpIrisInstance LOR RVPCOM RVPBASE RVPPRED).
  Import RiscvPmpSpecification.

  Include IrisInstanceWithContracts RiscvPmpGlobalState RiscvPmpSignature RiscvPmpProgram
    RiscvPmpSemantics RiscvPmpProgramLogic RVPCOM RVPBASE RVPINST.

  Section ForeignProofs.
    Context `{sg : sailGS Σ} {rG : trivGS Σ}.

    Lemma read_ram_sound (bytes : nat) :
      TValidContractForeign (sep_contract_read_ram bytes) (read_ram bytes).
    Proof.
      intros Γ es δ ι Heq. destruct_syminstance ι. cbn in *.
      iIntros "H". iApply semTWP_foreign.
      iIntros (? ?) "(Hregs & % & Hmem & %Hmap & Htr & Hpw)".
      iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
      iIntros (res ? ? Hf). rewrite Heq in Hf. cbn in Hf. inversion Hf; subst.
      iMod "Hclose" as "_". iModIntro.
      iPoseProof (fun_read_ram_works Hmap with "[$H $Hmem]") as "%eq_fun_read_ram".
      iPoseProof (mem_state_interp_not_modified $! Hmap with "Hmem Htr Hpw") as "Hmem".
      iFrame "Hregs Hmem". iApply semTWP_val. now iFrame "H".
    Qed.

    Lemma write_ram_sound (bytes : nat) :
      TValidContractForeign (sep_contract_write_ram bytes) (write_ram bytes).
    Proof.
      intros Γ es δ ι Heq. destruct_syminstance ι. cbn in *.
      iIntros "[%w H]". iApply semTWP_foreign.
      iIntros (? ?) "(Hregs & % & Hmem & %Hmap & Htr & Hpw)".
      iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
      iIntros (res ? ? Hf). rewrite Heq in Hf. cbn in Hf. inversion Hf; subst.
      iMod "Hclose" as "_".
      iMod (fun_write_ram_works with "[$H $Hmem $Htr $Hpw]") as "[$ H]"; auto.
      rewrite semTWP_val. now iFrame "Hregs H".
    Qed.

    Lemma mmio_read_sound `(H: restrict_bytes bytes) :
      TValidContractForeign (sep_contract_mmio_read H) (mmio_read H).
    Proof.
      intros Γ es δ ι Heq. destruct_syminstance ι. cbn.
      now iIntros "[%HFalse _]".
    Qed.


    Lemma mmio_write_sound `(H: restrict_bytes bytes) :
      TValidContractForeign (sep_contract_mmio_write H) (mmio_write H).
    Proof.
      intros Γ es δ ι Heq. destruct_syminstance ι. cbn.
      now iIntros "[%HFalse _]".
    Qed.

    Lemma interp_pmp_fun_within_mmio_spec {entries m p} (paddr : Addr) bytes :
      Pmp_access paddr (bv.of_nat bytes) entries m p →
      interp_pmp_addr_access liveAddrs mmioAddrs entries m -∗
      ⌜fun_within_mmio bytes paddr = false⌝.
    Proof.
      iIntros (Hpmp) "Hint". rewrite /fun_within_mmio.
      rewrite bool_decide_and andb_false_iff.
      destruct (decide (bv.unsigned paddr + Z.of_nat bytes < 2 ^ Z.of_nat xlenbits)%Z) as [Hlt | Hnlt].
      - iDestruct (interp_pmp_within_mmio_spec with "Hint") as "->"; eauto.
      - iPureIntro. right. by rewrite bool_decide_false.
    Qed.

    Lemma within_mmio_sound `(H: restrict_bytes bytes) :
      TValidContractForeign (@sep_contract_within_mmio bytes H) (within_mmio H).
    Proof.
      intros Γ es δ ι Heq. destruct_syminstance ι. cbn in *.
      iIntros "(Hcurp & Hpmp & Hpmpa & [%acc [%Hpmp _]])".
      iApply semTWP_foreign. iIntros (? ?) "[Hregs [% (Hmem & %Hmap & Htr & Hpw)]]".
      iPoseProof (interp_pmp_fun_within_mmio_spec with "Hpmpa") as "%Hnotmmio"; first eauto.
      iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
      iIntros (res ? ? Hf). iMod "Hclose" as "_". iModIntro.
      rewrite Heq in Hf. cbn in Hf. inversion Hf; subst.
      iFrame "Hregs Hmem Htr Hpw". iSplitR; auto. iApply semTWP_val.
      now iFrame "Hcurp Hpmp Hpmpa".
    Qed.

    Lemma decode_sound :
      TValidContractForeign sep_contract_decode decode.
    Proof.
      intros Γ es δ ι Heq. destruct_syminstance ι. cbn.
      iIntros "_". cbn in *. iApply semTWP_foreign.
      iIntros (? ?) "(Hregs & Hmem)".
      iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
      iIntros (res ? ? Hf). rewrite Heq in Hf. cbn in Hf. inversion Hf; subst.
      iMod "Hclose" as "_". iModIntro. iFrame "Hregs Hmem".
      destruct (pure_decode _).
      - now iApply semTWP_fail.
      - now iApply semTWP_val.
    Qed.

    Lemma externalWorldUpdates_sound :
      TValidContractForeign sep_contract_externalWorldUpdates externalWorldUpdates.
    Proof.
      intros Γ es δ ι Heq. destruct_syminstance ι. cbn.
      iIntros "Hmip". cbn in *. iApply semTWP_foreign.
      iIntros (? ?) "(Hregs & Hmem)".
      iMod (fupd_mask_subseteq empty) as "Hclose"; auto.
      iModIntro.
      iIntros (res ? ? Hf). rewrite Heq in Hf. cbn in Hf.
      inversion Hf; subst.
      iMod (reg_update γ mip vmip _ with "Hregs Hmip") as "[Hregs Hmip]".
      iMod "Hclose" as "_". iModIntro. iFrame "Hregs Hmem".
      iApply semTWP_val.
      now iFrame "Hmip".
    Qed.

    Lemma powered_on_sound :
      TValidContractForeign sep_contract_powered_on powered_on.
    Proof.
      intros Γ es δ ι Heq. destruct_syminstance ι. cbn.
      now iIntros "[%HFalse _]".
    Qed.

    Lemma TforeignSem : TForeignSem.
    Proof.
      intros Δ τ f; destruct f; cbn - [TValidContractForeign];
        eauto using read_ram_sound, write_ram_sound, mmio_read_sound, mmio_write_sound, within_mmio_sound, decode_sound, externalWorldUpdates_sound, powered_on_sound.
    Qed.

    Lemma foreignSem : ForeignSem.
    Proof. apply (TForeignSem_ForeignSem TforeignSem). Qed.
  End ForeignProofs.

  Section LemProofs.
    Context `{sg : sailGS Σ, rG : trivGS Σ}.

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
      rewrite pmp_entries_ptsto.
      iIntros "(% & % & % & % & -> & e1 & e2 & e3 & e4)".
      repeat iExists _.
      now iFrame "e1 e2 e3 e4".
    Qed.

    Lemma close_pmp_entries_sound :
      ValidLemma RiscvPmpSpecification.lemma_close_pmp_entries.
    Proof. intros ι; destruct_syminstance ι; cbn; auto. Qed.

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

    Lemma close_mmio_write_sound (imm : bv 12) (width : WordWidth) :
      ValidLemma (RiscvPmpSpecification.lemma_close_mmio_write imm width).
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      now iIntros.
    Qed.

    (* Lemma close_mmio_write_mem (imm : bv 12) (width : WordWidth): *)
    (*   ValidLemma (RiscvPmpSpecification.lemma_close_mmio_write_mem imm width). *)
    (* Proof. *)
    (*   intros ι; destruct_syminstance ι; cbn. *)
    (*   now iIntros. *)
    (* Qed. *)

    Lemma lemSem : LemmaSem.
    Proof.
      intros Δ []; cbn - [ValidLemma];
        eauto using open_gprs_sound, close_gprs_sound, open_ptsto_instr_sound, close_ptsto_instr_sound, open_pmp_entries_sound, close_pmp_entries_sound, extract_pmp_ptsto_sound, return_pmp_ptsto_sound, close_mmio_write_sound.
    Qed.
  End LemProofs.
End RiscvPmpModel.
