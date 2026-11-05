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
     Lists.List.
From Katamaran Require Import
     Bitvector
     Environment
     Iris.Instance
     Iris.Base
     Program
     Semantics
     Sep.Hoare
     Sep.Logic
     MicroSail.ShallowExecutor
     MicroSail.ShallowSoundness
     MicroSail.RefineExecutor
     MicroSail.Soundness
     RiscvPmp.Machine
     RiscvPmp.Logic
     RiscvPmp.PmpCheck
     RiscvPmp.Sig
     RiscvPmp.IrisModel
     RiscvPmp.IrisModelBinary
     RiscvPmp.IrisInstance
     RiscvPmp.IrisInstanceBinary
     RiscvPmp.ModelBinary
     RiscvPmp.Contracts
     RiscvPmp.LoopVerification.

From iris.base_logic Require lib.gen_heap lib.iprop.
From iris.base_logic Require Export invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac.
From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import string_ident proofmode.

Set Implicit Arguments.
Import ListNotations.
Import PmpCheck.

Module Type LoopVerificationBinary
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
  (Import RVPINST2 : RiscvPmpIrisInstance2 RVPCOM RVPBASEl RVPPREDl RVPBASEr RVPPREDr RVPBASE2 RVPPRED2 RVPADEQ2)
  (Import RVPMOD2 : RiscvPmpModel2 RVPCOM RVPBASEl RVPPREDl RVPINSTl RVPBASEr RVPPREDr RVPINSTr RVPBASE2 RVPPRED2 RVPADEQ2 RVPINST2).

  Import RiscvPmpSpecification.
  Import RiscvPmpProgram.
  Import RiscvPmpValidContracts.
  Import RiscvPmpProgramLogic.ProgLog.
  Import RiscvPmpShallowSoundness.
  Import RiscvPmpSymbolicSoundness.

  Import RiscvPmpSignature.

  Import ArchState (ArchState, archstate_valuation, archstate_update_pc).

  Section Loop.
    Context `{sg : sailGS2 Σ}.

    Definition step_sem_contract :=
      Eval cbn  in ValidContractSemCurried fun_step sep_contract_step.

    Definition Step_pre (archstate : ArchState) : iProp Σ :=
      asn.interpret (sep_contract_precondition sep_contract_step) (archstate_valuation archstate).

    Local Notation "r '↦' val" := (reg_pointsTo21 r val) (at level 70).
    (* Some Iris Proof Mode tactics like (iFrame) try very hard to solve some
       goals. Unfortunately that can result in definitions being unfolded.
       For example the [frame_instances.frame_big_sepL_cons] instance for the
       [Frame] typeclass will look for [IsCons liveAddrs _ _] which will unfold
       [liveAddrs] because the concrete value can indeed be unified with [cons].
       We make liveAddrs opaque to prevent this.
     *)
    Local Opaque liveAddrs.

    Definition PmpEntry : Set := Pmpcfg_ent * Z.
    Definition PtstosPred : Type := Privilege -> Privilege -> Z -> Z -> list PmpEntry -> list PmpEntry -> Privilege -> Z -> Z -> iProp Σ.

    Section TransitionTargets.
      (* Interpret the disjunct of a transition target with some ArchState. In
         case the disjuncts were not found, we simply use True. *)
      Definition transition (t : TransitionTarget) (archstate : ArchState) : iProp Σ :=
        match disjuncts with
        | Some ds => asn.interpret (ds t) (nenv.snoc (archstate_valuation archstate) (_∷ty.unit) tt)
        | None    => True
        end.

      Definition Execution (archstate : ArchState) : iProp Σ :=
        transition TT_Execution archstate.
      Definition M_CSRMod (archstate : ArchState) : iProp Σ :=
        transition TT_M_CSRMod archstate.
      Definition M_Trap (archstate : ArchState) : iProp Σ :=
        transition TT_M_Trap archstate.
      Definition MRET (archstate : ArchState) : iProp Σ :=
        transition TT_MRET archstate.
      Definition SRET (archstate : ArchState) : iProp Σ :=
        transition TT_SRET archstate.

      (* Step_post is not a "TransitionTarget" but simply groups the possibilities
         back together using disjunction. *)
      Definition Step_post (archstate : ArchState) : iProp Σ :=
        Execution archstate
        ∨ M_CSRMod archstate
        ∨ M_Trap archstate
        ∨ MRET archstate
        ∨ SRET archstate.

    End TransitionTargets.

    Definition semTriple_step : iProp Σ :=
      (∀ (archstate : ArchState),
          semTriple nenv.nil (Step_pre archstate)
                    (FunDef step)
                    (fun _ _ => Step_post archstate))%I.

    Definition semTriple_init_model : iProp Σ :=
      semTriple nenv.nil
                ((∃ p, reg_pointsTo21 cur_privilege p) ∗ (∃ es, interp_pmp_entries es))%I
                (FunDef init_model)
                (fun _ _ => reg_pointsTo21 cur_privilege Machine ∗ (∃ es, interp_pmp_entries es))%I.

    Lemma valid_step_contract : ⊢ ValidContractSem fun_step sep_contract_step.
    Proof.
      iApply (sound $! _ _ step).
      exact foreignSem.
      exact lemSem.
      unfold ValidContractCEnv.
      intros.
      pose (ValidContracts f H) as Hc.
      destruct Hc as [fuel Hc].
      apply shallow_vcgen_fuel_soundness with (fuel := fuel).
      now apply symbolic_vcgen_fuel_soundness.
    Qed.

    Lemma valid_init_model_contract : ⊢ ValidContractSem fun_init_model sep_contract_init_model.
    Proof.
      iApply (sound $! _ _ init_model).
      exact foreignSem.
      exact lemSem.
      unfold ValidContractCEnv.
      intros.
      pose (ValidContracts f H) as Hc.
      destruct Hc as [fuel Hc].
      apply shallow_vcgen_fuel_soundness with (fuel := fuel).
      now apply symbolic_vcgen_fuel_soundness.
    Qed.

    Import env.notations.

    Lemma valid_step_semTriple :
      ⊢ semTriple_step.
    Proof.
      iIntros (archstate) "H".
      iApply (semWP2_mono with "[-]").
      iApply (valid_step_contract with "H").
      iIntros ([[]|e1] δ1 v2 δ2) "(<- & <- & H)"; last auto.
      iSplit; first done. iSplit; first done. iExact "H".
    Qed.

    Lemma init_model_iprop : ⊢ semTriple_init_model.
    Proof.
      iApply (@iris_rule_consequence _ _ _ _ _ nenv.nil
               ((∃ p : Privilege, cur_privilege ↦ p) ∗
                (∃ es : list PmpEntryCfg, interp_pmp_entries es))
               _ _ _ fun_init_model _ _)%I.
      iApply valid_init_model_contract.
      Unshelve.
      cbn.
      iIntros "(Hcp & Hin)".
      iSplitL "Hcp"; iAssumption.
      cbn.
      iIntros (v δ) "H".
      iDestruct "H" as "([-> _] & Hcp & Hpmp)".
      iFrame "Hcp Hpmp".
      constructor.
    Qed.

    Lemma transition_update_pc (t : TransitionTarget) (a : ArchState) (pc : Xlenbits) :
      transition t (archstate_update_pc a pc) ⊣⊢ transition t a.
    Proof.
      destruct a as [m ? ? ?].
      unfold archstate_update_pc, transition.
      destruct t, m; reflexivity.
    Qed.

    Lemma M_CSRMod_machine (a : ArchState) :
      M_CSRMod a ⊢ ⌜ArchState.m a = Machine⌝.
    Proof.
      destruct a.
      unfold M_CSRMod, transition; cbn.
      now iIntros "(_ & _ & _ & [%Heq _] & _)".
    Qed.

    Lemma MRET_machine (a : ArchState) :
      MRET a ⊢ ⌜ArchState.m a = Machine⌝.
    Proof.
      destruct a.
      unfold MRET, transition; cbn.
      now iIntros "(_ & _ & _ & [%Heq _] & _)".
    Qed.

    Lemma SRET_machine (a : ArchState) :
      SRET a ⊢ ⌜ArchState.m a = Machine⌝.
    Proof.
      destruct a.
      unfold SRET, transition; cbn.
      now iIntros "(_ & _ & _ & [%Heq _] & _)".
    Qed.

    (* For a trap from S/U-mode, it is irrelevant which of S/U-mode it was:
       only the M-mode state matters (not the S-mode state or the pc). *)
    Lemma M_Trap_SU_irrelevant (a a' : ArchState) :
      ArchState.m a ≠ Machine -> ArchState.m a' ≠ Machine ->
      ArchState.mstate a = ArchState.mstate a' ->
      M_Trap a ⊢ M_Trap a'.
    Proof.
      destruct a as [m ? ? ?], a' as [m' ? ? ?]; cbn; intros Hm Hm' <-.
      unfold M_Trap, transition; cbn.
      iIntros "(Hpaa & H)".
      iSplitL "Hpaa"; first by iApply (interp_pmp_addr_access_not_machine with "Hpaa").
      destruct m, m'; try contradiction; auto.
    Qed.

    (* Parameterized by an iProp R that is maintained at each step of the loop.
       This gives some flexibility when doing known code verification, where we
       can hand off some knowledge that will not be violated (or invalidated)
       by unknown code when invoking the universal contract. *)
    (* Both executions are powered on (powered2 true) whenever control is in
       the loop, which lets both executions agree on the power check at the
       start of every iteration. *)
    Definition loop_pre (R : iProp Σ) (archstate : ArchState) : iProp Σ :=
      (Step_pre archstate ∗
       R ∗
       powered2 true ∗
       ▷ (M_CSRMod archstate ∗ R ∗ powered2 true -∗ WP2_loop R) ∗
       ▷ (M_Trap archstate ∗ R ∗ powered2 true -∗ WP2_loop R) ∗
       ▷ (MRET archstate ∗ R ∗ powered2 true -∗ WP2_loop R) ∗
       ▷ (SRET archstate ∗ R ∗ powered2 true -∗ WP2_loop R))%I.

    Definition semTriple_loop : iProp Σ :=
      (∀ (R : iProp Σ) (archstate : ArchState),
          loop_pre R archstate -∗ WP2_loop R)%I.

    Lemma valid_semTriple_loop : ⊢ semTriple_loop.
    Proof.
      iLöb as "H".
      iIntros (R archstate) "(HStep & HR & [Hpl Hpr] & HM_CSRMod & HM_Trap & HMRET & HSRET)".
      unfold WP2_loop at 2.
      iApply (semWP2_fun_loop with "Hpl Hpr").
      iIntros "Hpl Hpr" (Γon1 Γon2 δon1 δon2).
      iApply (semWP2_seq (call step) (call step) (call loop) (call loop)).
      iApply semWP2_call_inline_later.
      iApply (semWP2_mono with "[HStep]").
      iApply (valid_step_semTriple with "HStep").
      iModIntro.
      iIntros ([v|e] δ1 v2 δ2) "(<- & <- & HRes)";
        last (iApply semWP2_fail; iModIntro; by iFrame "HR").
      iDestruct "HRes" as "[HRes | [HRes | [HRes | [HRes | HRes]]]]";
        iApply (semWP2_call_inline loop _).
      - iDestruct "HRes" as "(Hacc & Hgprs & Hpmp & Hmie & Hmip & (%i' & Hpc & Hnpc) & Hmtvec & Hmepc & Hmideleg & Hmedeleg & Hmscratch & Hmcause & [HRes | HRes])".
        + (* Normal execution in M-mode (only pc changed) *)
          iDestruct "HRes" as "([%Hm _] & Hcp & Hstvec & Hmstatus & Hsepc & Hsscratch & Hscause)".
          cbn in Hm.
          iApply (semWP2_mono with "[-]").
          { iApply ("H" $! R (archstate_update_pc archstate i')).
            unfold loop_pre, M_CSRMod, M_Trap, MRET, SRET.
            iSplitR "HR Hpl Hpr HM_CSRMod HM_Trap HMRET HSRET".
            { unfold Step_pre; cbn.
              rewrite ?Hm.
              now iFrame "Hacc Hgprs Hpmp Hmie Hmip Hcp Hpc Hnpc Hmtvec Hstvec Hmstatus Hmepc Hsepc Hmideleg Hmedeleg Hmscratch Hmcause Hsscratch Hscause". }
            rewrite !transition_update_pc.
            iFrame "HR Hpl Hpr HM_CSRMod HM_Trap HMRET HSRET". }
          iIntros (? ? ? ?) "(<- & _ & $)"; auto.
        + (* S/U-mode: still in S/U-mode, the privilege and S-mode state may have changed *)
          iDestruct "HRes" as "([%Hm _] & [%m' (Hcp & [%Hm' _] & [%stvec' Hstvec] & [%spp' [%spie' [%sie' Hmstatus]]] & [%sepc' Hsepc] & [%sscratch' Hsscratch] & [%scause' Hscause])])".
          cbn in Hm, Hm'.
          iPoseProof (interp_pmp_addr_access_not_machine _ _ _ Hm Hm' with "Hacc") as "Hacc".
          destruct archstate as [? ms ? ?].
          iApply (semWP2_mono with "[-]").
          { iApply ("H" $! R (ArchState.mkArchState m' ms (ArchState.mkSState stvec' (MkSstatus spp' spie' sie') scause' sscratch' sepc') i')).
            iSplitR "HR Hpl Hpr HM_CSRMod HM_Trap HMRET HSRET".
            { unfold Step_pre; cbn.
              now iFrame "Hacc Hgprs Hpmp Hmie Hmip Hcp Hpc Hnpc Hmtvec Hstvec Hmstatus Hmepc Hsepc Hmideleg Hmedeleg Hmscratch Hmcause Hsscratch Hscause". }
            iFrame "HR Hpl Hpr".
            iSplitL "HM_CSRMod".
            { iIntros "!> [H' _]". iDestruct (M_CSRMod_machine with "H'") as %Heq.
              cbn in Heq. contradiction. }
            iSplitL "HM_Trap".
            { iIntros "!> (H' & HR & HP)". iApply "HM_Trap".
              iSplitR "HR HP"; last iFrame "HR HP".
              by iApply (M_Trap_SU_irrelevant with "H'"). }
            iSplitL "HMRET".
            { iIntros "!> [H' _]". iDestruct (MRET_machine with "H'") as %Heq.
              cbn in Heq. contradiction. }
            iIntros "!> [H' _]". iDestruct (SRET_machine with "H'") as %Heq.
            cbn in Heq. contradiction. }
          iIntros (? ? ? ?) "(<- & _ & $)"; auto.
      - iSpecialize ("HM_CSRMod" with "[$HRes $HR $Hpl $Hpr]").
        iApply (semWP2_mono with "HM_CSRMod").
        iIntros (? ? ? ?) "(<- & _ & $)"; auto.
      - iSpecialize ("HM_Trap" with "[$HRes $HR $Hpl $Hpr]").
        iApply (semWP2_mono with "HM_Trap").
        iIntros (? ? ? ?) "(<- & _ & $)"; auto.
      - iSpecialize ("HMRET" with "[$HRes $HR $Hpl $Hpr]").
        iApply (semWP2_mono with "HMRET").
        iIntros (? ? ? ?) "(<- & _ & $)"; auto.
      - iSpecialize ("HSRET" with "[$HRes $HR $Hpl $Hpr]").
        iApply (semWP2_mono with "HSRET").
        iIntros (? ? ? ?) "(<- & _ & $)"; auto.
    Qed.
  End Loop.
End LoopVerificationBinary.
