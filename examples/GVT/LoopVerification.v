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
     MicroSail.ShallowExecutor
     MicroSail.ShallowSoundness
     MicroSail.RefineExecutor
     MicroSail.Soundness
     RiscvPmp.Machine
     RiscvPmp.GVT.Logic
     RiscvPmp.GVT.Sig
     RiscvPmp.GVT.IrisModel
     RiscvPmp.GVT.IrisInstance
     RiscvPmp.GVT.Model
     RiscvPmp.iostate
     RiscvPmp.GVT.Contracts.

From iris.base_logic Require lib.gen_heap lib.iprop.
From iris.base_logic Require Export invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac.
From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import string_ident proofmode.

Set Implicit Arguments.
Import ListNotations.
Import RiscvPmpSpecification.
Import RiscvPmpProgram.
Import RiscvPmpIrisPrelims RiscvPmpIrisBase.
Import RiscvPmpModel2.
Import RiscvPmpIrisInstance.
Import RiscvPmpValidContracts.
Import RiscvPmpIrisInstancePredicates.

Import RiscvPmpSignature.
Import RiscvPmpProgramLogic.

(* The step contract at the type of step. An abbreviation rather than a
   definition, so that every use is the same term: converting between two
   names for the contract can make Rocq unfold it. *)
#[local] Abbreviation sep_contract_step :=
  (@RiscvPmpSpecification.sep_contract_step ty.unit ctx.nil).

(* ArchState defines a record that contains all logic variables we will need for the
   LoopVerification. These are based on the logic variables of the step contract,
   as the loop is of the form: step();; loop(). *)
Module ArchState.
  Import env.notations.

  Record MState :=
    mkMState
      { mtvec      : Xlenbits
      ; pmpentries : list (Pmpcfg_ent * Xlenbits)
      ; mpp        : Privilege
      ; mcause     : Xlenbits
      ; mscratch   : Xlenbits
      ; mepc       : Xlenbits
      ; mpie       : bool
      ; mie        : bool
      ; mideleg    : Minterrupts
      ; medeleg    : RMedeleg
      }.

  Record SState :=
    mkSState
      { stvec    : Xlenbits
      ; spp      : Privilege
      ; scause   : Xlenbits
      ; sscratch : Xlenbits
      ; sepc     : Xlenbits
      ; spie     : bool
      ; sie      : bool
      }.

  Record ArchState :=
    mkArchState
      { m      : Privilege
      ; mstate : MState
      ; sstate : SState
      ; pc     : Xlenbits
      }.

  Definition archstate_valuation (archstate : ArchState) : Valuation (sep_contract_logic_variables sep_contract_step) :=
    let ms := mstate archstate in
    let ss := sstate archstate in
    [env].["m"∷ty.enum privilege ↦ m archstate].["mtvec"∷ty.bvec 32 ↦ mtvec ms]
    .["stvec"∷ty.bvec 32 ↦ stvec ss]
    .["pmpentries"∷ty.list (ty.prod (ty.record rpmpcfg_ent) (ty.bvec 32)) ↦ pmpentries ms]
    .["mpp"∷ty.enum privilege ↦ mpp ms].["spp"∷ty.enum privilege ↦ spp ss]
    .["pc"∷ty.bvec 32 ↦ pc archstate].["mcause"∷ty.bvec 32 ↦ mcause ms]
    .["mscratch"∷ty.bvec 32 ↦ mscratch ms].["mepc"∷ty.bvec 32 ↦ mepc ms]
    .["scause"∷ty.bvec 32 ↦ scause ss].["sscratch"∷ty.bvec 32 ↦ sscratch ss]
    .["sepc"∷ty.bvec 32 ↦ sepc ss].["mpie"∷ty.bool ↦ mpie ms]
    .["spie"∷ty.bool ↦ spie ss].["mie"∷ty.bool ↦ mie ms]
    .["sie"∷ty.bool ↦ sie ss]
    .["mideleg"∷ty_Minterrupts ↦ mideleg ms]
    .["medeleg"∷ty_Medeleg ↦ medeleg ms].

  Definition archstate_update_pc (archstate : ArchState) (pc' : Xlenbits) : ArchState :=
    mkArchState (m archstate) (mstate archstate) (sstate archstate) pc'.

  Definition archstate_update_m (archstate : ArchState) (m' : Privilege) : ArchState :=
    mkArchState m' (mstate archstate) (sstate archstate) (pc archstate).
End ArchState.

(* We only import the record type and the valuation conversion function.
   Record fields will need the qualified name, for example: ArchState.mepc to access
   the mepc value. This avoids naming conflicts with the registers. *)
Import ArchState (ArchState, archstate_valuation, archstate_update_pc, archstate_update_m).

Section Loop.
  Context `{sg : sailGS Σ} {rG : iostateG IOState Σ}.
  Definition step_sem_contract :=
    Eval simpl in ValidContractSemCurried fun_step sep_contract_step.

  (* Some Iris Proof Mode tactics like (iFrame) try very hard to solve some
     goals. Unfortunately that can result in definitions being unfolded.
     For example the [frame_instances.frame_big_sepL_cons] instance for the
     [Frame] typeclass will look for [IsCons liveAddrs _ _] which will unfold
     [liveAddrs] because the concrete value can indeed be unified with [cons].
     We make liveAddrs opaque to prevent this.
   *)
  Local Opaque liveAddrs.

  (* TODO: remove? Never used? *)
  Definition PmpEntry : Set := Pmpcfg_ent * Z.
  Definition PtstosPred : Type := Privilege -> Privilege -> Z -> Z -> list PmpEntry -> list PmpEntry -> Privilege -> Z -> Z -> iProp Σ.

  (* For the LoopVerification, we always start with a precondition that needs to
     satisfy the precondition of the step function. We directly interpret this
     from the contract definition of step. *)
  Definition Step_pre (archstate : ArchState) : iProp Σ :=
    asn.interpret (sep_contract_precondition sep_contract_step) (archstate_valuation archstate).

  Local Notation "r '↦' val" := (reg_pointsTo r val) (at level 70).

  Section TransitionTargets.
    (* TransitionTargets defines all targets which we can transition to during
       execution of the machine. These corresponds to the individual disjuncts
       of the postcondition of the step function. *)
    Inductive TransitionTarget :=
    | TT_Execution
    | TT_M_CSRMod
    | TT_M_Trap
    | TT_MRET
    | TT_SRET.

    Definition Disjunct := Assertion (ctx.snoc (sep_contract_logic_variables sep_contract_step) (sep_contract_result sep_contract_step∷ty.unit)).

    (* We define an extract function that returns the disjunct of every
       transition target, or None in case the pattern used doesn't match. *)
    Definition disjuncts : option (TransitionTarget -> Disjunct) :=
      match sep_contract_postcondition sep_contract_step with
      | asn.or exe (asn.or m_csrmod (asn.or m_trap (asn.or mret sret))) =>
          Some (fun t => match t with
                         | TT_Execution => exe
                         | TT_M_CSRMod  => m_csrmod
                         | TT_M_Trap    => m_trap
                         | TT_MRET      => mret
                         | TT_SRET      => sret
                         end)
      | _ => None
      end.

    (* This lemma is a sanity check, if it fails, it most likely means the
       step function was updated so that there are more/less disjuncts and
       the pattern of the disjuncts definition wasn't updated accordingly. *)
    Lemma extract_disjuncts_should_work : disjuncts ≠ None.
    Proof. by simpl. Qed.

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
              ((∃ p, reg_pointsTo cur_privilege p) ∗ (∃ es, interp_pmp_entries es))%I
              (FunDef init_model)
              (fun _ _ => reg_pointsTo cur_privilege Machine ∗ (∃ es, interp_pmp_entries es))%I.

  Lemma valid_step_contract : ⊢ ValidContractSem fun_step sep_contract_step.
  Proof.
    iApply (sound $! _ _ step).
    exact foreignSem.
    exact lemSem.
    unfold ProgLog.ValidContractCEnv.
    intros Δ τ f c H.
    destruct (ValidContracts f H) as [fuel Hc].
    apply RiscvPmpShallowSoundness.shallow_vcgen_fuel_soundness with (fuel := fuel).
    now apply RiscvPmpSymbolicSoundness.symbolic_vcgen_fuel_soundness.
  Qed.

  Lemma valid_init_model_contract : ⊢ ValidContractSem fun_init_model sep_contract_init_model.
  Proof.
    iApply (sound $! _ _ init_model).
    exact foreignSem.
    exact lemSem.
    unfold ProgLog.ValidContractCEnv.
    intros Δ τ f c H.
    destruct (ValidContracts f H) as [fuel Hc].
    apply RiscvPmpShallowSoundness.shallow_vcgen_fuel_soundness with (fuel := fuel).
    now apply RiscvPmpSymbolicSoundness.symbolic_vcgen_fuel_soundness.
  Qed.

  Import env.notations.

  Lemma valid_step_semTriple :
    ⊢ semTriple_step.
  Proof.
    iIntros (archstate) "H".
    iApply (semWP_mono with "[-]").
    iApply (valid_step_contract with "H").
    iIntros ([[]|e] _); last auto.
    iIntros "H". iExact "H".
  Time Qed.

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
    iIntros (? ?) "(_ & Hcp & Hin)".
    iSplitL "Hcp"; iAssumption.
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

  Definition loop_pre (archstate : ArchState) : iProp Σ :=
    (Step_pre archstate ∗
     ▷ (M_CSRMod archstate -∗ WP_loop) ∗
     ▷ (M_Trap archstate -∗ WP_loop) ∗
     ▷ (MRET archstate -∗ WP_loop) ∗
     ▷ (SRET archstate -∗ WP_loop))%I.

  Definition semTriple_loop : iProp Σ :=
    (∀ (archstate : ArchState),
        semTriple nenv.nil (loop_pre archstate)
                  (FunDef loop)
                  (fun _ _ => True))%I.

  Lemma valid_semTriple_loop : ⊢ semTriple_loop.
  Proof.
    iLöb as "H".
    iIntros (archstate) "(HStep & HM_CSRMod & HM_Trap & HMRET & HSRET)".
    iApply semWP_fun_loop. iSplit; last by cbn. iIntros (Γon δon).
    iApply (semWP_seq (call step) (call loop)).
    iApply semWP_call_inline_later.
    iApply (semWP_mono with "[HStep]").
    iApply (valid_step_semTriple with "HStep").
    iModIntro.
    iIntros ([v|e] δ); last (iIntros "_"; by rewrite semWP_fail);
      iIntros "[HRes | [HRes | [HRes | [HRes | HRes]]]]";
      iApply (semWP_call_inline loop _).
    - iDestruct "HRes" as "(Hacc & Hgprs & Hpmp & Hmie & Hmip & (%i' & Hpc & Hnpc) & Hmtvec & Hmepc & Hmideleg & Hmedeleg & Hmscratch & Hmcause & [HRes | HRes])".
      + (* Normal execution in M-mode (only pc changed) *)
        iDestruct "HRes" as "([%Hm _] & Hcp & Hstvec & Hmstatus & Hsepc & Hsscratch & Hscause)".
        cbn in Hm.
        iApply ("H" $! (archstate_update_pc archstate i')).
        unfold loop_pre, M_CSRMod, M_Trap, MRET, SRET.
        iSplitR "HM_CSRMod HM_Trap HMRET HSRET".
        { unfold Step_pre; cbn.
          rewrite ?Hm.
          now iFrame "Hacc Hgprs Hpmp Hmie Hmip Hcp Hpc Hnpc Hmtvec Hstvec Hmstatus Hmepc Hsepc Hmideleg Hmedeleg Hmscratch Hmcause Hsscratch Hscause". }
        rewrite !transition_update_pc.
        iFrame "HM_CSRMod HM_Trap HMRET HSRET".
      + (* S/U-mode: still in S/U-mode, the privilege and S-mode state may have changed *)
        iDestruct "HRes" as "([%Hm _] & [%m' (Hcp & [%Hm' _] & [%stvec' Hstvec] & [%spp' [%spie' [%sie' Hmstatus]]] & [%sepc' Hsepc] & [%sscratch' Hsscratch] & [%scause' Hscause])])".
        cbn in Hm, Hm'.
        iPoseProof (interp_pmp_addr_access_not_machine _ _ _ Hm Hm' with "Hacc") as "Hacc".
        destruct archstate as [? ms ? ?].
        iApply ("H" $! (ArchState.mkArchState m' ms (ArchState.mkSState stvec' spp' scause' sscratch' sepc' spie' sie') i')).
        iSplitR "HM_CSRMod HM_Trap HMRET HSRET".
        { unfold Step_pre; cbn.
          now iFrame "Hacc Hgprs Hpmp Hmie Hmip Hcp Hpc Hnpc Hmtvec Hstvec Hmstatus Hmepc Hsepc Hmideleg Hmedeleg Hmscratch Hmcause Hsscratch Hscause". }
        iSplitL "HM_CSRMod".
        { iIntros "!> H'". iDestruct (M_CSRMod_machine with "H'") as %Heq.
          cbn in Heq. contradiction. }
        iSplitL "HM_Trap".
        { iIntros "!> H'". iApply "HM_Trap". by iApply (M_Trap_SU_irrelevant with "H'"). }
        iSplitL "HMRET".
        { iIntros "!> H'". iDestruct (MRET_machine with "H'") as %Heq.
          cbn in Heq. contradiction. }
        iIntros "!> H'". iDestruct (SRET_machine with "H'") as %Heq.
        cbn in Heq. contradiction.
    - iSpecialize ("HM_CSRMod" with "HRes").
      iApply (semWP_mono with "HM_CSRMod").
      iIntros ([] ?); auto.
    - iSpecialize ("HM_Trap" with "HRes").
      iApply (semWP_mono with "HM_Trap").
      iIntros ([] ?); auto.
    - iSpecialize ("HMRET" with "HRes").
      iApply (semWP_mono with "HMRET").
      iIntros ([] ?); auto.
    - iSpecialize ("HSRET" with "HRes").
      iApply (semWP_mono with "HSRET").
      iIntros ([] ?); auto.
  Qed.
End Loop.
