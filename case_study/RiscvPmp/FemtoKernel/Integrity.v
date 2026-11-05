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
     ZArith.ZArith
     Lists.List
     Strings.String.
From Katamaran Require Import
     Base
     Bitvector
     Notations
     SmallStep.Step
     RiscvPmp.BlockVer.Spec
     RiscvPmp.BlockVer.TotalVerifier
     RiscvPmp.IrisModel
     RiscvPmp.IrisInstance
     RiscvPmp.Machine
     RiscvPmp.Sig
     RiscvPmp.Contracts
     RiscvPmp.LoopVerification
     RiscvPmp.Everything
     RiscvPmp.UnaryAdequacy
     RiscvPmp.FemtoKernel.Kernel
     RiscvPmp.FemtoKernel.BlockVerification.
From iris.base_logic Require lib.gen_heap lib.iprop invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac big_op.
From iris.program_logic Require weakestpre adequacy.
From iris.proofmode Require string_ident proofmode.
From stdpp Require namespaces.

Import RiscvPmpProgram.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.
Import ListNotations.
Open Scope ctx_scope.

Module inv := invariants.

Import iris.program_logic.weakestpre.
Import iris.proofmode.proofmode.

Import Contracts.
Import Assembly.
Import ArchState (ArchState).

Import RVPCOM.
Import RVPV2.
Import RVPINST2.
Import RVPBASE2.
Import RVPPRED2.

Local Opaque femtokernel_init_gen.

(* Integrity of the FemtoKernel: a single execution of the FemtoKernel, together
   with arbitrary (unknown) U-mode code, only ever produces MMIO events that
   satisfy mmio_pred. This is a unary result: it uses the unary (left) Iris
   instance and unary adequacy.

   The unary block contracts of the FemtoKernel use the writePending ghost
   state for the observable MMIO write (nothingPending before the write,
   written after). Without a second execution to resynchronize with, we use the
   phantom execution of RVPADEQl: we carry its resources around in the
   universal contract (as part of R), and resynchronize with phantom_resync. *)
Section Integrity.
  Import RVPCOM.
  Import RVPBASEl.
  Import RVPPREDl.
  Import RVPINSTl.
  Import RiscvPmpSemantics.SmallStepNotations.

  #[local] Existing Instance Instance.trivTrivGS.

  #[local] Instance sailGS_mcMemGS2 `{sG : RVPBASEl.sailGS Σ} : mcMemGS2 Σ :=
    RVPBASEl.sailGS_memGS.

  Section WithUnarySailGS.
    Context `{sG : RVPBASEl.sailGS Σ}.

    #[local] Notation "r '↦ᵣ' v" := (reg_pointsTo r v) (at level 70).
    #[local] Notation asn_interpret := (@asn.interpret _ (UnaryPredicateDefIProp__l sG) _).

    (* The resource that is threaded through the universal contract: the
       phantom execution's resources (RVPADEQl.phantom_res), together with
       this execution's nothingPending and power token. *)
    Definition phantom_res : iProp Σ := nothingPending ∗ powered_tok true ∗ RVPADEQl.phantom_res.

    Lemma loop_pre_WP_loop (archstate : ArchState) :
      LoopVerificationl.loop_pre phantom_res archstate ⊢ WP_loop.
    Proof.
      iIntros "H".
      iApply (semWP_mono with "[H]").
      { iApply (LoopVerificationl.valid_semTriple_loop with "H"). }
      by iIntros.
    Qed.

    Definition femtokernel_safe_shared_pre (addr : N) (b : Block) : iProp Σ :=
      RVPTVl.exec_instructions_prologue (bv.of_N addr) (filter_AST b) ∗
        (∃ v, mscratch ↦ᵣ v) ∗
        interp_pmp_addr_access liveAddrs mmioAddrs femto_pmpentries User.

    Lemma femtokernel_handler_exit_safe (archstate : ArchState) (vmie : Val ty_Minterrupts) (Hmpp : ArchState.mpp (ArchState.mstate archstate) ≠ Machine) :
      ⊢ femtokernel_safe_shared_pre handler_exit_addr femtokernel_handler_exit ∗
        asn_interpret femtokernel_handler_exit_pre (csrs_valuation archstate vmie).["a" ∷ ty_xlenbits ↦ bv.of_N handler_exit_addr] ∗
        interp_gprs ∅ ∗
        phantom_res ∗
        ▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
             ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
             LoopVerificationl.M_Trap (femto_archstate priv ms ss pc) -∗ phantom_res -∗ WP_loop)
        -∗
        WP_loop.
    Proof.
      iIntros "((Hpro & [%vmscratch Hmscratch] & HaccU) & Hpre & Hgprs & HR & Htrap)".
      iPoseProof (contract_femtohandler_exit_verified__l (bv.of_N handler_exit_addr) archstate vmie) as "Htrip".
      iApply (RVPTVl.WP_loop_semTripleBlock with "Hpro [Hpre] Htrip"); first iExact "Hpre".
      iIntros (an) "(Hpost & Hpc & Hinstrs & Hnpc)".
      iDestruct "Hpost" as "((Hcurpriv & Hmtvec & Hmcause & Hmip & Hmie & Hmepc & Hsepc & Hscause & Hsscratch & Hstvec & Hmideleg & Hmedeleg & Hpmp) & Hmstatus & [%Han _])"; cbn - [interp_ptstomem] in *.
      iAssert (interp_pmp_addr_access liveAddrs mmioAddrs femto_pmpentries (ArchState.mpp (ArchState.mstate archstate))) with "[HaccU]" as "Hacc".
      { assert (Hmpp' : ArchState.mpp (ArchState.mstate archstate) = User ∨ ArchState.mpp (ArchState.mstate archstate) = Supervisor)
          by (destruct (ArchState.mpp (ArchState.mstate archstate)); auto; congruence).
        destruct Hmpp' as [Heq|Heq]; rewrite Heq; first iExact "HaccU".
        by iApply interp_pmp_addr_access_s_u_eq. }
      iApply (loop_pre_WP_loop (femto_return_archstate archstate vmscratch an)).
      unfold LoopVerificationl.loop_pre.
      iSplitR "HR Htrap Hinstrs".
      { unfold LoopVerificationl.Step_pre; cbn.
        iFrame "Hacc Hgprs Hpmp Hmie Hmip Hcurpriv Hpc Hnpc Hmtvec Hstvec Hmstatus Hmepc Hsepc Hmideleg Hmedeleg Hmscratch Hmcause Hsscratch Hscause".
        auto. }
      iFrame "HR".
      iSplitR.
      { iIntros "!> [H' _]". iDestruct (LoopVerificationl.M_CSRMod_machine with "H'") as %Heq.
        cbn in Heq. contradiction. }
      iSplitL "Htrap Hinstrs".
      { iIntros "!> [H' HR]". iApply ("Htrap" $! (ArchState.mpp (ArchState.mstate archstate)) with "[//] Hinstrs H' HR"). }
      iSplitR.
      { iIntros "!> [H' _]". iDestruct (LoopVerificationl.MRET_machine with "H'") as %Heq.
        cbn in Heq. contradiction. }
      iIntros "!> [H' _]". iDestruct (LoopVerificationl.SRET_machine with "H'") as %Heq.
      cbn in Heq. contradiction.
    Qed.

    (* Run the dispatch block and, depending on the secret, the is_zero or
       not_zero block, which both perform the observable write. *)
    Lemma femtokernel_dispatch_path (vx1 vx5 secret : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
      let ι__csrs := csrs_valuation archstate vmie in
      ⊢ femto_inv_mmio -∗
        RVPTVl.exec_instructions_prologue (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) -∗
        asn_interpret femtokernel_handler_dispatch_pre
          (ι__csrs ►► [env].["x1" ∷ ty_xlenbits ↦ vx1].["secret" ∷ ty_xlenbits ↦ secret]
                   ►► [env].["a" ∷ ty_xlenbits ↦ bv.of_N handler_dispatch_addr]) -∗
        nothingPending -∗
        x5 ↦ᵣ vx5 -∗
        ptsto_instrs (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) -∗
        ptsto_instrs (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) -∗
        (∀ x1 x5 a an,
           asn_interpret femtokernel_handler_ack_post
             (ι__csrs ►► [env].["x1" ∷ ty_xlenbits ↦ x1].["x5" ∷ ty_xlenbits ↦ x5].["secret" ∷ ty_xlenbits ↦ secret]
                      ►► [env].["a" ∷ ty_xlenbits ↦ a].["an" ∷ ty_xlenbits ↦ an]) -∗
           pc ↦ᵣ an -∗
           (∃ v, nextpc ↦ᵣ v) -∗
           ptsto_instrs (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) -∗
           ptsto_instrs (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) -∗
           ptsto_instrs (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) -∗
           WP_loop) -∗
        WP_loop.
    Proof.
      iIntros (ι__csrs) "#Hinv Hpro Hpre Hnp Hx5 Hnz Hiz Hk".
      iPoseProof (contract_femtohandler_dispatch_verified__l vx1 secret (bv.of_N handler_dispatch_addr) archstate vmie) as "Htrip".
      iApply (RVPTVl.WP_loop_semTripleBlock with "Hpro [Hpre] Htrip"); first iExact "Hpre".
      iIntros (an) "(Hpost & Hpc & Hcode & Hnpc)".
      iEval (cbn - [interp_ptstomem]) in "Hpost".
      iDestruct "Hpost" as "(Hshared & Hmstatus & Han & Hx1 & Hdata)".
      case_match; iDestruct "Han" as "[%Han _]"; cbn in Han; subst an.
      - (* The secret is zero: is_zero block. *)
        iPoseProof (contract_femtohandler_is_zero_verified__l secret vx5 secret (bv.of_N handler_is_zero_addr) archstate vmie) as "Htrip'".
        iApply (RVPTVl.WP_loop_semTripleBlock with "[Hpc Hiz Hnpc] [Hshared Hmstatus Hnp Hx1 Hx5 Hdata] Htrip'").
        + iFrame "Hpc Hiz Hnpc".
        + cbn - [interp_ptstomem].
          iFrame "Hinv Hmstatus Hnp Hx1 Hx5 Hdata".
          repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
          repeat iSplit; try iPureIntro; try done; by vm_compute.
        + iIntros (an') "(Hpost & Hpc & Hcode' & Hnpc)".
          iApply ("Hk" with "Hpost Hpc Hnpc Hcode Hnz Hcode'").
      - (* The secret is not zero: not_zero block. *)
        iPoseProof (contract_femtohandler_not_zero_verified__l secret vx5 secret (bv.of_N handler_not_zero_addr) archstate vmie) as "Htrip'".
        iApply (RVPTVl.WP_loop_semTripleBlock with "[Hpc Hnz Hnpc] [Hshared Hmstatus Hnp Hx1 Hx5 Hdata] Htrip'").
        + iFrame "Hpc Hnz Hnpc".
        + cbn - [interp_ptstomem].
          iFrame "Hinv Hmstatus Hnp Hx1 Hx5 Hdata".
          repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
          repeat iSplit; try iPureIntro; try done; by vm_compute.
        + iIntros (an') "(Hpost & Hpc & Hcode' & Hnpc)".
          iApply ("Hk" with "Hpost Hpc Hnpc Hcode Hcode' Hiz").
    Qed.

    Lemma femtokernel_handler_dispatch_safe (vx1 secret : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) (Hmpp : ArchState.mpp (ArchState.mstate archstate) ≠ Machine) :
      ⊢ femto_inv_mmio -∗
        femtokernel_safe_shared_pre handler_dispatch_addr femtokernel_handler_dispatch ∗
        asn_interpret femtokernel_handler_dispatch_pre
          (csrs_valuation archstate vmie ►► [env].["x1" ∷ ty_xlenbits ↦ vx1].["secret" ∷ ty_xlenbits ↦ secret]
                                         ►► [env].["a" ∷ ty_xlenbits ↦ bv.of_N handler_dispatch_addr]) ∗
        interp_gprs {[x1]} ∗
        phantom_res ∗
        ptsto_instrs (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) ∗
        ptsto_instrs (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) ∗
        ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) ∗
        ▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
           ptsto_instrs (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) -∗
           ptsto_instrs (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) -∗
           ptsto_instrs (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) -∗
           interp_ptstomem (bv.of_N data_addr) secret -∗
           ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
           LoopVerificationl.M_Trap (femto_archstate priv ms ss pc) -∗ phantom_res -∗ WP_loop)
        -∗
        WP_loop.
    Proof.
      iIntros "#Hinv ((Hpro & Hmscratch & HaccU) & Hpre & Hgprs & (Hnp & Hpow & Hph) & Hhnz & Hhiz & Hhexit & Hk)".
      iPoseProof (interp_gprs_with_excluded_gen {[x1]} (exclude2 := {[x5]}) with "Hgprs") as "(Hregs & Hgprs)";
        try solve_subseteq.
      reduce_big_sepS_big_sepL.
      iDestruct "Hregs" as "([%vx5 Hx5] & _)".
      subst l; clear Hl Hdup.
      iApply (femtokernel_dispatch_path vx1 vx5 secret archstate vmie
                with "Hinv Hpro Hpre Hnp Hx5 Hhnz Hhiz").
      iIntros (x1v x5v a an) "Hpost Hpc Hnpc Hcode Hhnz Hhiz".
      iEval (cbn - [interp_ptstomem]) in "Hpost".
      iDestruct "Hpost" as "(Hshared & Hmstatus & [%Han _] & Hx1 & Hx5 & Hdata & Hw)"; subst an.
      (* Resynchronize with the phantom execution after the observable write. *)
      iApply (fupd_semWP ⊤).
      iMod (RVPADEQl.phantom_resync bytes_per_word with "Hinv Hph Hw") as "[Hph Hnp]"; first solve_ndisj.
      iModIntro.
      iAssert (interp_gprs ∅) with "[Hgprs Hx1 Hx5]" as "Hgprs".
      { iApply (interp_gprs_with_excluded (exclude := {[x1; x5]})); try solve_subseteq.
        iFrame "Hgprs".
        reduce_big_sepS_big_sepL.
        iFrame "Hx1 Hx5". by cbn. }
      iAssert (▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
                 ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
                 LoopVerificationl.M_Trap (femto_archstate priv ms ss pc) -∗ phantom_res -∗ WP_loop))%I
        with "[Hk Hcode Hhnz Hhiz Hdata]" as "Hk".
      { iIntros "!>" (priv ms ss pc Hpriv) "Hhexit Htrap HR".
        iApply ("Hk" with "[//] Hcode Hhnz Hhiz Hdata Hhexit Htrap HR"). }
      iApply (femtokernel_handler_exit_safe _ _ Hmpp).
      iFrame "Hpc Hhexit Hnpc Hmscratch HaccU Hmstatus Hgprs Hk Hinv Hnp Hpow Hph"; cbn - [interp_ptstomem].
      repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
      now iPureIntro.
    Qed.

    Lemma femtokernel_handler_secret_write_safe (vx1 secret : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) (Hmpp : ArchState.mpp (ArchState.mstate archstate) ≠ Machine) :
      ⊢ femto_inv_mmio -∗
        femtokernel_safe_shared_pre handler_secret_write_addr femtokernel_handler_secret_write ∗
        asn_interpret femtokernel_handler_secret_write_pre
          (csrs_valuation archstate vmie ►► [env].["x1" ∷ ty_xlenbits ↦ vx1].["secret" ∷ ty_xlenbits ↦ secret]
                                         ►► [env].["a" ∷ ty_xlenbits ↦ bv.of_N handler_secret_write_addr]) ∗
        interp_gprs {[x1]} ∗
        phantom_res ∗
        ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) ∗
        ▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
           ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) -∗
           interp_ptstomem (bv.of_N data_addr) secret -∗
           ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
           LoopVerificationl.M_Trap (femto_archstate priv ms ss pc) -∗ phantom_res -∗ WP_loop)
        -∗
        WP_loop.
    Proof.
      iIntros "#Hinv ((Hpro & Hmscratch & HaccU) & Hpre & Hgprs & HR & Hhexit & Htrap)".
      iPoseProof (contract_femtohandler_secret_write_verified__l vx1 secret (bv.of_N handler_secret_write_addr) archstate vmie) as "Htrip".
      iApply (RVPTVl.WP_loop_semTripleBlock with "Hpro [Hpre] Htrip"); first iExact "Hpre".
      iIntros (an) "(Hpost & Hpc & Hinstrs & Hnpc)".
      iEval (cbn - [interp_ptstomem]) in "Hpost".
      iDestruct "Hpost" as "(Hshared & Hmstatus & [%Han _] & Hx1 & Hdata)".
      iAssert (interp_gprs ∅) with "[Hgprs Hx1]" as "Hgprs".
      { iApply (interp_gprs_with_excluded (exclude := {[x1]})); try solve_subseteq.
        iFrame "Hgprs".
        reduce_big_sepS_big_sepL.
        iFrame "Hx1". by cbn. }
      iAssert (▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
                 ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
                 LoopVerificationl.M_Trap (femto_archstate priv ms ss pc) -∗ phantom_res -∗ WP_loop))%I
        with "[Htrap Hinstrs Hdata]" as "Htrap".
      { iIntros "!>" (priv ms ss pc Hpriv) "Hhexit' Htrap' HR".
        iApply ("Htrap" with "[//] Hinstrs Hdata Hhexit' Htrap' HR"). }
      iApply (femtokernel_handler_exit_safe _ _ Hmpp).
      rewrite Han.
      iFrame "Hpc Hhexit Hnpc Hmscratch HaccU Hmstatus Hgprs Htrap Hinv HR"; cbn - [interp_ptstomem].
      repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
      now iPureIntro.
    Qed.

    (* The shutdown check, followed by either powering off the machine, or by
       the secret write. *)
    Lemma femtokernel_handler_shutdown_check_safe (vx1 vx5 vx10 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) (Hmpp : ArchState.mpp (ArchState.mstate archstate) ≠ Machine) :
      ⊢ femto_inv_mmio -∗
        femtokernel_safe_shared_pre handler_shutdown_check_addr femtokernel_handler_shutdown_check ∗
        asn_interpret femtokernel_handler_shutdown_check_pre
          (csrs_valuation archstate vmie ►► [env].["x1" ∷ ty_xlenbits ↦ vx1].["x5" ∷ ty_xlenbits ↦ vx5].["x10" ∷ ty_xlenbits ↦ vx10]
                                         ►► [env].["a" ∷ ty_xlenbits ↦ bv.of_N handler_shutdown_check_addr]) ∗
        interp_gprs {[x1; x5; x10]} ∗
        (∃ v : Val ty_xlenbits, interp_ptstomem (bv.of_N data_addr) v) ∗
        phantom_res ∗
        ptsto_instrs (bv.of_N handler_shutdown_addr) (filter_AST femtokernel_handler_shutdown) ∗
        ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) ∗
        ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) ∗
        ▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
           ptsto_instrs (bv.of_N handler_shutdown_check_addr) (filter_AST femtokernel_handler_shutdown_check) -∗
           ptsto_instrs (bv.of_N handler_shutdown_addr) (filter_AST femtokernel_handler_shutdown) -∗
           ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) -∗
           (∃ v : Val ty_xlenbits, interp_ptstomem (bv.of_N data_addr) v) -∗
           ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
           LoopVerificationl.M_Trap (femto_archstate priv ms ss pc) -∗ phantom_res -∗ WP_loop)
        -∗
        WP_loop.
    Proof.
      iIntros "#Hinv ((Hpro & Hmscratch & HaccU) & Hpre & Hgprs & Hdata & HR & Hhshutdown & Hhsecret & Hhexit & Hk)".
      iPoseProof (contract_femtohandler_shutdown_check_verified__l vx1 vx5 vx10 (bv.of_N handler_shutdown_check_addr) archstate vmie) as "Htrip".
      iApply (RVPTVl.WP_loop_semTripleBlock with "Hpro [Hpre] Htrip"); first iExact "Hpre".
      iIntros (an) "(Hpost & Hpc & Hinstrs & Hnpc)".
      iEval (cbn - [interp_ptstomem]) in "Hpost".
      iDestruct "Hpost" as "(Hshared & Hmstatus & Han & Hx1 & Hx5 & Hx10)".
      case_match; iDestruct "Han" as "[-> _]".
      - (* Power off the machine. *)
        iDestruct "HR" as "(Hnp & Hpow & Hph)".
        iPoseProof (contract_femtohandler_shutdown_verified__l (bv.of_N handler_shutdown_addr) archstate vmie) as "Htrip'".
        iApply (RVPTVl.WP_loop_semTripleBlock with "[Hpc Hhshutdown Hnpc] [Hshared Hmstatus Hx5 Hnp Hpow] Htrip'").
        + iFrame "Hpc Hhshutdown Hnpc".
        + cbn - [interp_ptstomem].
          iFrame "Hinv Hmstatus Hx5 Hnp Hpow".
          repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
          repeat iSplit; try iPureIntro; try done; by vm_compute.
        + iIntros (an') "(Hpost & _)".
          iEval (cbn) in "Hpost". iDestruct "Hpost" as "(_ & Hoff)".
          unfold WP_loop.
          iApply (semWP_fun_loop_off with "[Hoff]"); [iExact "Hoff" | by iIntros].
      - (* Perform the secret write. *)
        iAssert (interp_gprs {[x1]}) with "[Hgprs Hx5 Hx10]" as "Hgprs".
        { iApply (interp_gprs_with_excluded_gen {[x1]} (exclude2 := {[x5; x10]})); try solve_subseteq.
          iFrame "Hgprs".
          reduce_big_sepS_big_sepL.
          iFrame "Hx5 Hx10". by cbn. }
        iDestruct "Hdata" as "(%secret & Hdata)".
        iAssert (▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
                   ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) -∗
                   interp_ptstomem (bv.of_N data_addr) (secret : Val ty_xlenbits) -∗
                   ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
                   LoopVerificationl.M_Trap (femto_archstate priv ms ss pc) -∗ phantom_res -∗ WP_loop))%I
          with "[Hk Hinstrs Hhshutdown]" as "Hksecret".
        { iIntros "!>" (priv ms ss pc Hpriv) "Hhsecret Hdata Hhexit Htrap HR".
          iApply ("Hk" with "[//] Hinstrs Hhshutdown Hhsecret [Hdata] Hhexit Htrap HR").
          by iExists _. }
        iApply (femtokernel_handler_secret_write_safe _ secret _ _ Hmpp with "Hinv"); cbn - [interp_ptstomem].
        iFrame "Hhsecret Hpc Hnpc Hmscratch HaccU Hmstatus Hgprs Hhexit Hx1 Hdata HR Hksecret".
        repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
        repeat iSplit; try iPureIntro; try done; by vm_compute.
    Qed.

    Lemma femtokernel_handler_entry_safe (x5_val x10_val : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) (Hmpp : ArchState.mpp (ArchState.mstate archstate) ≠ Machine) :
      ⊢ femto_inv_mmio -∗
        femtokernel_safe_shared_pre handler_entry_addr femtokernel_handler_entry ∗
        asn_interpret femtokernel_handler_entry_pre
          (csrs_valuation archstate vmie ►► [env].["x5" ∷ ty_xlenbits ↦ x5_val].["x10" ∷ ty_xlenbits ↦ x10_val]
                                         ►► [env].["a" ∷ ty_xlenbits ↦ bv.of_N handler_entry_addr]) ∗
        interp_gprs {[ x1; x5; x10 ]} ∗
        (∃ v, x1 ↦ᵣ v) ∗
        (∃ v : Val ty_xlenbits, interp_ptstomem (bv.of_N data_addr) v) ∗
        phantom_res ∗
        ptsto_instrs (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) ∗
        ptsto_instrs (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) ∗
        ptsto_instrs (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) ∗
        ptsto_instrs (bv.of_N handler_shutdown_check_addr) (filter_AST femtokernel_handler_shutdown_check) ∗
        ptsto_instrs (bv.of_N handler_shutdown_addr) (filter_AST femtokernel_handler_shutdown) ∗
        ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) ∗
        ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit)
        -∗
        WP_loop.
    Proof.
      iIntros "#Hinv".
      iLöb as "IH" forall (x5_val x10_val archstate vmie Hmpp).
      iIntros "((Hpro & Hmscratch & HaccU) & Hpre & Hgprs & Hx1 & Hdata & HR & Hhdispatch & Hhnotzero & Hhiszero & Hhcheck & Hhshutdown & Hhsecret & Hhexit)".
      (* When the adversary traps back into the handler, we are back at the
         start of this lemma (with possibly different CSR values). *)
      iAssert (▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
                 ptsto_instrs_handler ∗ (∃ v : Val ty_xlenbits, interp_ptstomem (bv.of_N data_addr) v) -∗
                 LoopVerificationl.M_Trap (femto_archstate priv ms ss pc) -∗ phantom_res -∗ WP_loop))%I with "[]" as "#Hk".
      { iIntros "!>" (priv ms ss pc Hpriv) "(Hhandler & Hdata) Htrap HR".
        iDestruct "Hhandler" as "(Hhentry & Hhdispatch & Hhnotzero & Hhiszero & Hhcheck & Hhshutdown & Hhsecret & Hhexit)".
        assert (HU : User ≠ Machine) by auto.
        iPoseProof (LoopVerificationl.M_Trap_SU_irrelevant (femto_archstate priv ms ss pc) (femto_archstate User ms ss pc)
                      Hpriv HU eq_refl with "Htrap") as "Htrap".
        unfold LoopVerificationl.M_Trap, LoopVerificationl.transition; cbn.
        iDestruct "Htrap" as "(HaccU & Hgprs & Hpmp & [%vmie' Hmie] & Hmip & Hcurpriv & Hpc & Hnpc & Hmtvec & [%vstvec Hstvec] & [%vspp [%vmpie [%vspie [%vsie [%vmpp (Hmstatus & [%Hmpp' _])]]]]] & [%vmepc Hmepc] & [%vsepc Hsepc] & Hmideleg & Hmedeleg & [%vmscratch Hmscratch] & [%vmcause Hmcause] & [%vsscratch Hsscratch] & [%vscause Hscause])".
        iPoseProof (interp_gprs_with_excluded (exclude := {[x1;x5;x10]}) with "Hgprs") as "(Hregs & Hgprs)";
          try solve_subseteq.
        reduce_big_sepS_big_sepL.
        iDestruct "Hregs" as "([% Hx5] & Hx1 & [% Hx10] & _)".
        iApply ("IH" $! _ _
                  (femto_handler_archstate vmpp vmpie vmcause vmscratch vmepc (ArchState.mkSState vstvec (MkSstatus vspp vspie vsie) vscause vsscratch vsepc)) vmie' with "[//]").
        cbn - [interp_ptstomem].
        iFrame "Hhentry Hpc Hnpc Hmscratch HaccU Hcurpriv Hmtvec Hmcause Hmip Hmie Hmepc Hsepc Hscause Hsscratch Hstvec Hmideleg Hmedeleg Hpmp Hinv Hmstatus Hgprs Hx5 Hx10 Hx1 Hdata HR Hhdispatch Hhnotzero Hhiszero Hhcheck Hhshutdown Hhsecret Hhexit".
        auto. }
      iPoseProof (contract_femtohandler_entry_verified__l x5_val x10_val (bv.of_N handler_entry_addr) archstate vmie) as "Htrip".
      iApply (RVPTVl.WP_loop_semTripleBlock with "Hpro [Hpre] Htrip"); first iExact "Hpre".
      iIntros (an) "(Hpost & Hpc & Hinstrs & Hnpc)".
      iDestruct "Hpost" as "((Hcurpriv & Hmtvec & Hmcause & Hmip & Hmie & Hmepc & Hsepc & Hscause & Hsscratch & Hstvec & Hmideleg & Hmedeleg & Hpmp) & Hmstatus & Han & Hx5 & Hx10)"; cbn - [interp_ptstomem].
      iDestruct "Hx1" as "[%vx1 Hx1]".
      case_match; cbn - [interp_ptstomem];
        iDestruct "Han" as "[-> _]".
      - (* Dispatch on the secret. *)
        iAssert (interp_gprs {[ x1; x5 ]}) with "[Hgprs Hx10]" as "Hgprs".
        { iApply (interp_gprs_with_excluded_gen {[x1; x5]} (exclude2 := {[x10]}));
            try solve_subseteq.
          iFrame "Hgprs".
          reduce_big_sepS_big_sepL.
          now iFrame "Hx10". }
        iAssert (interp_gprs {[ x1 ]}) with "[Hgprs Hx5]" as "Hgprs".
        { iApply (interp_gprs_with_excluded_gen {[x1]} (exclude2 := {[x5]}));
            try solve_subseteq.
          iFrame "Hgprs".
          reduce_big_sepS_big_sepL.
          now iFrame "Hx5". }
        iDestruct "Hdata" as "(%secret & Hdata)".
        iAssert (▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
                   ptsto_instrs (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) -∗
                   ptsto_instrs (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) -∗
                   ptsto_instrs (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) -∗
                   interp_ptstomem (bv.of_N data_addr) (secret : Val ty_xlenbits) -∗
                   ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
                   LoopVerificationl.M_Trap (femto_archstate priv ms ss pc) -∗ phantom_res -∗ WP_loop))%I
          with "[Hinstrs Hhcheck Hhshutdown Hhsecret]" as "Hkdispatch".
        { iIntros "!>" (priv ms ss pc Hpriv) "Hhdispatch Hhnotzero Hhiszero Hdata Hhexit Htrap HR".
          iApply ("Hk" with "[//] [Hinstrs Hhdispatch Hhnotzero Hhiszero Hhcheck Hhshutdown Hhsecret Hhexit Hdata] Htrap HR").
          iSplitR "Hdata"; last by iExists _.
          iFrame "Hinstrs Hhdispatch Hhnotzero Hhiszero Hhcheck Hhshutdown Hhsecret Hhexit". }
        iApply (femtokernel_handler_dispatch_safe _ _ _ _ Hmpp with "Hinv").
        iFrame "Hkdispatch"; cbn - [interp_ptstomem].
        iFrame "Hhdispatch Hpc Hnpc Hmscratch HaccU Hcurpriv Hmtvec Hmcause Hmip Hmie Hmepc Hsepc Hscause Hsscratch Hstvec Hmideleg Hmedeleg Hpmp Hinv Hmstatus Hgprs Hhnotzero Hhiszero Hhexit Hx1 Hdata HR";
          repeat iSplitR; auto.
      - (* Check for a shutdown request. *)
        iAssert (▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
                   ptsto_instrs (bv.of_N handler_shutdown_check_addr) (filter_AST femtokernel_handler_shutdown_check) -∗
                   ptsto_instrs (bv.of_N handler_shutdown_addr) (filter_AST femtokernel_handler_shutdown) -∗
                   ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) -∗
                   (∃ v : Val ty_xlenbits, interp_ptstomem (bv.of_N data_addr) v) -∗
                   ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
                   LoopVerificationl.M_Trap (femto_archstate priv ms ss pc) -∗ phantom_res -∗ WP_loop))%I
          with "[Hinstrs Hhdispatch Hhnotzero Hhiszero]" as "Hkcheck".
        { iIntros "!>" (priv ms ss pc Hpriv) "Hhcheck Hhshutdown Hhsecret Hdata Hhexit Htrap HR".
          iApply ("Hk" with "[//] [Hinstrs Hhdispatch Hhnotzero Hhiszero Hhcheck Hhshutdown Hhsecret Hhexit Hdata] Htrap HR").
          iFrame "Hinstrs Hhdispatch Hhnotzero Hhiszero Hhcheck Hhshutdown Hhsecret Hhexit Hdata". }
        iApply (femtokernel_handler_shutdown_check_safe vx1 _ x10_val _ _ Hmpp with "Hinv").
        iFrame "Hkcheck"; cbn - [interp_ptstomem].
        iFrame "Hhcheck Hpc Hnpc Hmscratch HaccU Hcurpriv Hmtvec Hmcause Hmip Hmie Hmepc Hsepc Hscause Hsscratch Hstvec Hmideleg Hmedeleg Hpmp Hinv Hmstatus Hgprs Hx1 Hx5 Hx10 Hdata HR Hhshutdown Hhsecret Hhexit";
          repeat iSplitR; auto.
    Qed.

    Lemma femtokernel_handler_safe :
      ⊢ femto_inv_mmio -∗
        ∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
          ptsto_instrs_handler ∗ (∃ v : Val ty_xlenbits, interp_ptstomem (bv.of_N data_addr) v) -∗
          LoopVerificationl.M_Trap (femto_archstate priv ms ss pc) -∗ phantom_res -∗ WP_loop.
    Proof.
      iIntros "#Hinv" (priv ms ss pc Hpriv) "(Hhandler & Hdata) Htrap HR".
      iDestruct "Hhandler" as "(Hhentry & Hhdispatch & Hhnotzero & Hhiszero & Hhcheck & Hhshutdown & Hhsecret & Hhexit)".
      (* Traps from S-mode look the same as traps from U-mode *)
      assert (HU : User ≠ Machine) by auto.
      iPoseProof (LoopVerificationl.M_Trap_SU_irrelevant (femto_archstate priv ms ss pc) (femto_archstate User ms ss pc)
                    Hpriv HU eq_refl with "Htrap") as "Htrap".
      unfold LoopVerificationl.M_Trap, LoopVerificationl.transition; cbn.
      iDestruct "Htrap" as "(HaccU & Hgprs & Hpmp & [%vmie Hmie] & Hmip & Hcurpriv & Hpc & Hnpc & Hmtvec & [%vstvec Hstvec] & [%vspp [%vmpie [%vspie [%vsie [%vmpp (Hmstatus & [%Hmpp _])]]]]] & [%vmepc Hmepc] & [%vsepc Hsepc] & Hmideleg & Hmedeleg & [%vmscratch Hmscratch] & [%vmcause Hmcause] & [%vsscratch Hsscratch] & [%vscause Hscause])".
      iPoseProof (interp_gprs_with_excluded (exclude := {[x1;x5;x10]}) with "Hgprs") as "(Hregs & Hgprs)";
        try solve_subseteq.
      reduce_big_sepS_big_sepL.
      iDestruct "Hregs" as "([% Hx5] & Hx1 & [% Hx10] & _)".
      iApply (femtokernel_handler_entry_safe _ _
                (femto_handler_archstate vmpp vmpie vmcause vmscratch vmepc (ArchState.mkSState vstvec (MkSstatus vspp vspie vsie) vscause vsscratch vsepc)) vmie Hmpp with "Hinv").
      cbn - [interp_ptstomem].
      iFrame "Hhentry Hpc Hnpc Hmscratch HaccU Hcurpriv Hmtvec Hmcause Hmip Hmie Hmepc Hsepc Hscause Hsscratch Hstvec Hmideleg Hmedeleg Hpmp Hinv Hmstatus Hgprs Hx5 Hx10 Hx1 Hdata HR Hhdispatch Hhnotzero Hhiszero Hhcheck Hhshutdown Hhsecret Hhexit".
      auto.
    Qed.

    Lemma memAdv_pmpPolicy :
      (ptstoSthL advAddrs ⊢
         interp_pmp_addr_access liveAddrs mmioAddrs femto_pmpentries User)%I.
    Proof.
      iIntros "Hadv".
      unfold interp_pmp_addr_access.
      rewrite <-(big_sepL_filter).
      unfold ptstoSthL.
      rewrite -> (big_opL_permutation _ _ _ allAddr_filter_advAddr).
      iApply (big_sepL_mono with "Hadv"). iIntros (? ? Hsom) "Hptsto".
      unfold interp_addr_access_byte.
      apply list_elem_of_lookup_2, adv_is_live in Hsom.
      repeat case_decide; auto.
      iPureIntro. eapply mmio_ram_False; eauto.
    Qed.

    Lemma femtokernel_manualStep :
      ⊢ (∃ mpp mpie mie, mstatus ↦ᵣ {| MPP := mpp; SPP := User; MPIE := mpie; SPIE := false; MIE := mie; SIE := false |}) ∗
        (mtvec ↦ᵣ (bv.of_N handler_entry_addr)) ∗
        (∃ v, mcause ↦ᵣ v) ∗
        (∃ v, mip ↦ᵣ v) ∗ (∃ v, mie ↦ᵣ v) ∗
        (∃ v, mscratch ↦ᵣ v) ∗
        (∃ v, mepc ↦ᵣ v) ∗
        (∃ v, scause ↦ᵣ v) ∗
        (∃ v, sscratch ↦ᵣ v) ∗
        (∃ v, sepc ↦ᵣ v) ∗
        (∃ v, stvec ↦ᵣ v) ∗
        mideleg ↦ᵣ Minterrupts_zero ∗
        medeleg ↦ᵣ Medeleg_zero ∗
        cur_privilege ↦ᵣ User ∗
        interp_gprs ∅ ∗
        interp_pmp_entries femto_pmpentries ∗
        femto_inv_mmio ∗
        (pc ↦ᵣ (bv.of_N adv_addr)) ∗
        (∃ v, nextpc ↦ᵣ v) ∗
        ptsto_instrs_handler ∗
        (∃ v : Val ty_xlenbits, interp_ptstomem (bv.of_N data_addr) v) ∗
        ptstoSthL advAddrs ∗
        phantom_res
        -∗
        WP_loop.
    Proof.
      iIntros "((%mpp & %mpie & %mie & Hmst) & Hmtvec & [%vmcause Hmcause] & Hmip & Hmie & [%vmscratch Hmscratch] & [%vmepc Hmepc] & [%vscause Hscause] & [%vsscratch Hsscratch] & [%vsepc Hsepc] & [%vstvec Hstvec] & Hmideleg & Hmedeleg & Hcurpriv & Hgprs & Hpmpcfg & #Hmmio & Hpc & Hnpc & Hhandler & Hdata & Hmemadv & HR)".
      iApply (loop_pre_WP_loop
                    (femto_adv_archstate mpp mpie mie vmcause vmscratch vmepc vstvec vscause vsscratch vsepc)).
      unfold LoopVerificationl.loop_pre.
      iSplitR "Hhandler Hdata HR".
      - unfold LoopVerificationl.Step_pre.
        cbn - [ptstoSthL interp_ptstomem].
        iFrame "Hgprs Hpmpcfg Hmie Hmip Hcurpriv Hpc Hnpc Hmtvec Hstvec Hmst Hmepc Hsepc Hmideleg Hmedeleg Hmscratch Hsscratch Hmcause Hscause".
        iSplitR; first auto.
        by iApply memAdv_pmpPolicy.
      - iFrame "HR".
        iSplitR.
        { iIntros "!> [H' _]". iDestruct (LoopVerificationl.M_CSRMod_machine with "H'") as %Heq.
          cbn in Heq; discriminate Heq. }
        iSplitL "Hhandler Hdata".
        { iIntros "!> [H' HR]".
          iApply (femtokernel_handler_safe with "Hmmio [] [$Hhandler $Hdata] H' HR").
          iPureIntro; discriminate. }
        iSplitR.
        { iIntros "!> [H' _]". iDestruct (LoopVerificationl.MRET_machine with "H'") as %Heq.
          cbn in Heq; discriminate Heq. }
        iIntros "!> [H' _]". iDestruct (LoopVerificationl.SRET_machine with "H'") as %Heq.
        cbn in Heq; discriminate Heq.
    Qed.

    Lemma femtokernel_init_safe (archstate : ArchState) (vmie : Val ty_Minterrupts) :
      ⊢ RVPTVl.exec_instructions_prologue (bv.of_N init_addr) (filter_AST femtokernel_init_gen)
        ∗ ptsto_instrs_handler
        ∗ ptstoSthL advAddrs
        ∗ asn_interpret femtokernel_init_pre (csrs_valuation archstate vmie ►► [env] ►► [env].["a" ∷ ty_xlenbits ↦ bv.of_N init_addr])
        ∗ interp_gprs {[x1]}
        ∗ (∃ v : Val ty_xlenbits, interp_ptstomem (bv.of_N data_addr) v)
        ∗ (∃ v, mscratch ↦ᵣ v)
        ∗ (∃ v : Val ty_scause, scause ↦ᵣ v)
        ∗ (∃ v : Val ty_xlenbits, sscratch ↦ᵣ v)
        ∗ (∃ v : Val ty_xlenbits, sepc ↦ᵣ v)
        ∗ (∃ v : Val ty_xlenbits, stvec ↦ᵣ v)
        ∗ femto_inv_mmio
        ∗ phantom_res
          -∗
          WP_loop.
    Proof.
      iIntros "(Hpro & Hhandler & Hadv & Hpre & Hgprs & Hdata & Hmscratch & Hscause & Hsscratch & Hsepc & Hstvec & #Hmem & HR)".
      iPoseProof (contract_femtoinit_verified__l (bv.of_N init_addr) archstate vmie) as "Htrip".
      iApply (RVPTVl.WP_loop_semTripleBlock with "Hpro [Hpre] Htrip"); first iExact "Hpre".
      iIntros (an) "(Hpost & Hepi)".
      cbn - [asn_regs_ptsto interp_pmp_entries].
      iDestruct "Hpost" as "([-> _] & Hmtvec & Hmcause & Hmip & Hmie & Hmepc & Hmstatus & Hmideleg & Hmedeleg & Hcurpriv & Hx1 & Hpmpentries)".
      iAssert (interp_gprs ∅) with "[Hgprs Hx1]" as "Hgprs".
      { iApply (interp_gprs_with_excluded (exclude := {[x1]}));
          try solve_subseteq.
        reduce_big_sepS_big_sepL.
        iFrame "Hgprs".
        iFrame "Hx1". by cbn. }
      iDestruct "Hepi" as "(Hpc & Hinstrs & Hnpc)".
      rewrite ?bv.add_zero_l.
      iApply (femtokernel_manualStep with "[$Hmstatus $Hmtvec $Hmcause $Hmip $Hmie $Hmscratch $Hmepc $Hscause $Hsscratch $Hsepc $Hstvec $Hmideleg $Hmedeleg $Hcurpriv $Hgprs $Hpmpentries $Hmem $Hpc $Hnpc $Hhandler $Hdata $Hadv $HR]").
    Qed.
  End WithUnarySailGS.

  (* Integrity: starting from a memory that contains the FemtoKernel and whose
     MMIO trace satisfies mmio_pred, every reachable state still has a trace
     satisfying mmio_pred. Note that U-mode code is arbitrary. *)
  Lemma femtokernel_endToEnd {γ γ' : RegStore} {μ μ' : Memory}
        {δ δ' : CStore [ctx]} {s' : Stm [ctx] ty.unit} (secret : Val ty_xlenbits) :
    mem_has_femtokernel μ secret ->
    mmio_pred bytes_per_word (memory_trace μ) ->
    fun_powered_on μ = true -> (* The machine starts powered on *)
    femto_init_regs γ ->
    ⟨ γ, μ, δ, fun_loop ⟩ --->* ⟨ γ', μ', δ', s' ⟩ ->
    mmio_pred bytes_per_word (memory_trace μ').
  Proof.
    intros μfk μpred μon
      (γmstatus & γcurpriv & γpmp0cfg & γpmpaddr0 & γpmp1cfg & γpmpaddr1 & γpc & γmideleg & γmedeleg) steps.
    refine (RVPADEQUACYl.adequacy_gen (Q := fun _ _ _ _ => True%I) _ steps _).
    iIntros (Σ sG mGS) "(Hmem & Hregs)".
    iDestruct "Hmem" as "(Hmem & Hfrag & Hnpa & Hnp & Hpw & Hfrago & Hnpao & Hph)".
    iPoseProof (femtokernel_splitMemory with "Hmem") as "(Hinit & Hhandler & Hdata & Hadv)"; try eassumption.
    iPoseProof (intro_ptstoSthL with "Hadv") as "Hadv".
    (* Allocate the shared invariant, with the phantom execution in sync. *)
    iMod (inv.inv_alloc femto_inv_mmio_ns ⊤
            (∃ t, side_inv bytes_per_word mc_ghGS2_left t ∗ side_inv bytes_per_word mc_ghGS2_right t)
           with "[Hfrag Hnpa Hfrago Hnpao]") as "#Hinv".
    { iNext. iExists (filter_adv_observable (memory_trace μ)).
      rewrite inv_mmio_body_own_other.
      iSplitL "Hfrag Hnpa".
      - iExists _. iFrame "Hfrag". iSplitR; first done. iLeft. by iFrame "Hnpa".
      - iExists _. iFrame "Hfrago". iSplitR; first done. iLeft. by iFrame "Hnpao". }
    iModIntro.
    iSplitL.
    - destruct (nenv.view δ).
      iApply (femtokernel_init_safe
                (femto_init_archstate γ)
                (read_register γ mie)
                with "[-]").
      #[local] Opaque ptsto_instrs. (* Avoid spinning because code is unfolded *)
      iEval (rewrite μon) in "Hpw".
      iFrame "Hinit Hhandler Hadv Hinv Hnp Hpw Hph Hdata".
      unfold RVPADEQUACYl.own_regstore. cbn - [interp_gprs].
      rewrite γmstatus γcurpriv γpmp0cfg γpmpaddr0 γpmp1cfg γpmpaddr1 γpc γmideleg γmedeleg.
      iDestruct "Hregs" as "(Hpc & Hnpc & Hmstatus & Hmie & Hmip & Hmideleg & Hmedeleg & Hmtvec & Hmscratch & Hmepc & Hmcause & Hstvec & Hsscratch & Hsepc & Hscause & Hcp & Hx1 & Hregs)".
      iFrame "Hpc Hnpc Hmstatus Hmie Hmip Hmideleg Hmedeleg Hmtvec Hmscratch Hmepc Hmcause Hstvec Hsscratch Hsepc Hscause Hcp Hx1".
      iDestruct "Hregs" as "(Hx2 & Hx3 & Hx4 & Hx5 & Hx6 & Hx7 & Hx8 & Hx9 & Hx10 & Hx11 & Hx12 & Hx13 & Hx14 & Hx15 & Hx16 & Hx17 & Hx18 & Hx19 & Hx20 & Hx21 & Hx22 & Hx23 & Hx24 & Hx25 & Hx26 & Hx27 & Hx28 & Hx29 & Hx30 & Hx31 & Hp0 & Hp1 & Ha0 & Ha1 & _)".
      iFrame "Hp0 Hp1 Ha0 Ha1".
      iSplitR; first (iPureIntro; split; [by vm_compute | done]).
      unfold interp_gprs; reduce_big_sepS_big_sepL; cbn.
      iFrame.
    - iIntros "Hmem".
      iInv "Hinv" as ">(%t & Hsides)" "_".
      rewrite inv_mmio_body_own_other.
      iDestruct "Hsides" as "[(%ts & Hf & %Hpred & _) _]".
      iDestruct "Hmem" as "(%memmap & _ & _ & Htr & _)".
      iDestruct (trace.trace_full_frag_eq with "Htr Hf") as %->.
      iApply fupd_mask_intro; first set_solver.
      now iIntros "_".
  Qed.

End Integrity.
