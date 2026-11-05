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
     Strings.String
     Lists.List.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Iris.Instance
     Iris.Base
     Notations
     Bitvector
     Sep.Hoare
     MicroSail.ShallowExecutor
     MicroSail.ShallowSoundness
     MicroSail.SymbolicExecutor
     MicroSail.RefineExecutor
     MicroSail.Soundness
     RiscvPmp.PmpCheck
     RiscvPmp.IrisModel
     RiscvPmp.IrisModelBinary
     RiscvPmp.IrisInstance
     RiscvPmp.IrisInstanceBinary
     RiscvPmp.Machine
     RiscvPmp.Logic
     RiscvPmp.Sig
     RiscvPmp.Contracts
     RiscvPmp.BlockVer.Spec
     RiscvPmp.BlockVer.TotalVerifier.
From Katamaran Require RiscvPmp.ModelBinary.

Import RiscvPmpProgram.
Import RiscvPmpProgramLogic.
Import RiscvPmpBlockVerifSpec.
Import ListNotations.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.


Module BinaryBlockVerifier
  (Import RVPCOM : RiscvPmpIrisBaseCommon)
  (RVPBASEl : RiscvPmpIrisBase LeftOrRightLeft RVPCOM)
  (RVPPREDl : RiscvPmpIrisInstancePredicates LeftOrRightLeft RVPCOM RVPBASEl)
  (RVPINSTl : RiscvPmpIrisInstance LeftOrRightLeft RVPCOM RVPBASEl RVPPREDl)
  (RVPCONTRl : RiscvPmpIrisInstanceWithContracts LeftOrRightLeft RVPCOM RVPBASEl RVPPREDl RVPINSTl)
  (RVPTVl : RiscvPmpBlockVerifTotalVerifier LeftOrRightLeft RVPCOM RVPBASEl RVPPREDl RVPINSTl RVPCONTRl)
  (RVPBASEr : RiscvPmpIrisBase LeftOrRightRight RVPCOM)
  (RVPPREDr : RiscvPmpIrisInstancePredicates LeftOrRightRight RVPCOM RVPBASEr)
  (RVPINSTr : RiscvPmpIrisInstance LeftOrRightRight RVPCOM RVPBASEr RVPPREDr)
  (RVPCONTRr : RiscvPmpIrisInstanceWithContracts LeftOrRightRight RVPCOM RVPBASEr RVPPREDr RVPINSTr)
  (RVPTVr : RiscvPmpBlockVerifTotalVerifier LeftOrRightRight RVPCOM RVPBASEr RVPPREDr RVPINSTr RVPCONTRr)
  (Import RVPBASE2 : RiscvPmpIrisBase2 RVPCOM RVPBASEl RVPBASEr)
  (Import RVPPRED2 : RiscvPmpIrisInstancePredicates2 RVPCOM RVPBASEl RVPPREDl RVPBASEr RVPPREDr RVPBASE2)
  (Import RVPADEQ2 : RiscvPmpIrisAdeqParams2 RVPCOM RVPBASEl RVPBASEr RVPBASE2)
  (Import RVPINST2 : RiscvPmpIrisInstance2 RVPCOM RVPBASEl RVPPREDl RVPBASEr RVPPREDr RVPBASE2 RVPPRED2 RVPADEQ2).
  Import iris.base_logic.lib.iprop iris.proofmode.proofmode.

  Module Import BinaryBlockVerifierNotations.
    Notation "a '↦' t" := (reg_pointsTo21 a t) (at level 70).
    Notation "a '↦ₘ' t" := (interp_ptsto a t) (at level 70).
  End BinaryBlockVerifierNotations.

  Section WithSailGS2.
    Context {Σ} {GS : sailGS2 Σ}.

    (* Main difference with interp_ptsto_instr is that we get two existentials
       with this definition, instead of a single one. The two existentials work
       better when we split the verification into two unary ones (each will
       produce/require its own existentials too). *)
    Definition ptsto_instr (a : Val ty_xlenbits) (instr : AST) : iProp Σ :=
      @RVPCOM.interp_ptsto_instr _ memGS_left a instr
      ∗ @RVPCOM.interp_ptsto_instr _ memGS_right a instr.

    Fixpoint ptsto_instrs (a : Val ty_xlenbits) (instrs : list AST) : iProp Σ :=
      match instrs with
      | cons inst insts => (ptsto_instr a inst ∗ ptsto_instrs (bv.add a bv_instrsize) insts)%I
      | nil => True%I
      end.

    Lemma ptsto_instrs_equiv {a : Val ty_xlenbits} {instrs : list AST} :
      ptsto_instrs a instrs ⊣⊢
        @RVPCOM.ptsto_instrs _ memGS_left a instrs
        ∗ @RVPCOM.ptsto_instrs _ memGS_right a instrs.
    Proof.
      revert a.
      iInduction instrs as [|instr instrs] "IH";
        cbn; auto.
      iIntros (a). iSplit.
      - iIntros "([Hl Hr] & Hinstrs)".
        iDestruct ("IH" with "Hinstrs") as "[$ $]".
        iFrame "Hl Hr".
      - iIntros "([Hl Hinstrsl] & [Hr Hinstrsr])".
        iDestruct ("IH" with "[$Hinstrsl $Hinstrsr]") as "$".
        iFrame "Hl Hr".
    Qed.

    Definition exec_instructions_prologue (a : Val ty_xlenbits) (l : list AST) : iProp Σ :=
      pc ↦ a ∗
      ptsto_instrs a l ∗
      ∃ v, nextpc ↦ v.

    Definition exec_instructions_epilogue (a an : Val ty_xlenbits) (l : list AST) : iProp Σ :=
      pc ↦ an ∗
      ptsto_instrs a l ∗
      ∃ v, nextpc ↦ v.

    (* The binary counterparts of RVPTVl.exec_instruction_prologue and
       RVPTVl.exec_instruction_epilogue. We cannot interpret those assertions
       in the binary program logic, as the binary interpretation of ptstoinstr
       requires the same instruction word on both sides, but we only care about
       having the same decoding of those words (again, ptsto_instr above vs interp_ptsto_instr!). *)
    Definition exec_instruction_prologue (i : AST) (a : Val ty_xlenbits) : iProp Σ :=
      reg_pointsTo2 pc a a ∗
      ptsto_instr a i ∗
      ∃ an, reg_pointsTo2 nextpc an an.
    Definition exec_instruction_epilogue (i : AST) (a an : Val ty_xlenbits) : iProp Σ :=
      reg_pointsTo2 pc an an ∗
      ptsto_instr a i ∗
      reg_pointsTo2 nextpc an an.

    Fixpoint step_n (instrs : list AST) (ainstr apc : Val ty_xlenbits) (POST : Val ty_xlenbits -> iProp Σ) : iProp Σ :=
      match instrs with
      | []   => POST apc
      | i :: instrs =>
          ⌜ainstr = apc⌝
          ∗ (exec_instruction_prologue i ainstr -∗
               semWP2 [env] [env] fun_step fun_step
                 (λ v1 δ1 v2 δ2, ⌜v1 = v2⌝ ∗ ⌜δ1 = δ2⌝ ∗
                     match v1 with
                     | inl v =>
                         ∃ na, exec_instruction_epilogue i ainstr na
                               ∗ step_n instrs (bv.add ainstr bv_instrsize) na POST
                     | inr _ =>
                       if fail_rule_pre
                       then True
                       else False
                      end)%I)
      end.

    Lemma step_n_mono {instrs : list AST} {a apc : Val ty_xlenbits} {POST1 POST2 : Val ty_xlenbits -> iProp Σ} :
      step_n instrs a apc POST1 -∗
      (∀ an, POST1 an -∗ POST2 an) -∗
      step_n instrs a apc POST2.
    Proof.
      revert a apc.
      iInduction instrs as [|instr instrs]; iIntros (a apc) "H HPOSTS".
      - cbn. now iApply "HPOSTS".
      - cbn. iDestruct "H" as "(<- & H)". iSplitR; first auto.
        iIntros "Hpro". iSpecialize ("H" with "Hpro").
        iApply (semWP2_mono with "H").
        iIntros ([] ? ? ?) "(<- & <- & H)"; auto.
        iDestruct "H" as "(%na & $ & H)".
        repeat iSplitR; auto.
        iApply ("IHinstrs" with "H HPOSTS").
    Qed.

    Definition stepTriple (l : list AST) (a apc : Val ty_xlenbits)
      (PRE : Val ty_xlenbits -> iProp Σ) (POST : Val ty_xlenbits -> Val ty_xlenbits -> iProp Σ) : iProp Σ :=
      PRE a -∗
        step_n l a apc (POST a).

    Definition semTripleBlock (PRE : Val ty_xlenbits -> iProp Σ) (a : Val ty_xlenbits) (instrs : list AST) (POST : Val ty_xlenbits -> Val ty_xlenbits -> iProp Σ) : iProp Σ :=
      stepTriple instrs a a PRE POST.

    Lemma WP2_loop_step_once {R : iProp Σ} : ∀ POST,
      powered2 true -∗
      semWP2 [env] [env] fun_step fun_step (λ v1 δ1 v2 δ2, ⌜v1 = v2⌝ ∗ ⌜δ1 = δ2⌝ ∗ POST v1 δ1 v2 δ2) -∗
      (∀ v1 δ1 v2 δ2, POST v1 δ1 v2 δ2 -∗ powered2 true -∗ match v1 with inl _ => WP2_loop R | inr _ => R end) -∗
      WP2_loop R.
    Proof.
      iIntros (POST) "[Hpl Hpr] H Hk".
      unfold WP2_loop at 2.
      iApply (semWP2_fun_loop with "Hpl Hpr").
      iIntros "Hpl Hpr" (Γon1 Γon2 δon1 δon2).
      iApply semWP2_seq.
      iApply semWP2_call_inline_later. simpl. iModIntro.
      iApply (semWP2_mono with "H").
      iIntros (? ? [] δ2) "(-> & -> & H)".
      - iApply semWP2_call_inline.
        iSpecialize ("Hk" with "H [$Hpl $Hpr]").
        iApply (semWP2_mono with "Hk").
        iIntros (? ? ? ?) "(<- & _ & $)"; auto.
      - iApply semWP2_fail. iSpecialize ("Hk" with "H [$Hpl $Hpr]").
        iModIntro. iFrame "Hk". auto.
    Qed.

    Lemma WP2_loop_semTripleBlock_later {R : iProp Σ} : ∀ PRE a instr instrs POST,
      powered2 true -∗
      (exec_instructions_prologue a (instr :: instrs)) -∗
      (PRE a) -∗
      semTripleBlock PRE a (instr :: instrs) POST -∗
      ▷ (∀ an, POST a an ∗ exec_instructions_epilogue a an (instr :: instrs) ∗ powered2 true -∗ WP2_loop R) -∗
      WP2_loop R.
    Proof.
      iIntros (PRE a instr instrs).
      iRevert (PRE a instr).
      iInduction instrs as [|i instrs] "IH";
        iIntros (PRE a instr POST) "[Hpl Hpr] Hpro HPRE Htrip Hk".
      - cbn. iDestruct ("Htrip" with "HPRE") as "(_ & Htrip)".
        iSpecialize ("Htrip" with "[Hpro]").
        { cbn. iDestruct "Hpro" as "($ & [$ _] & $)". }
        unfold WP2_loop at 2.
        iApply (semWP2_fun_loop with "Hpl Hpr").
        iIntros "Hpl Hpr" (Γon1 Γon2 δon1 δon2).
        iApply semWP2_seq.
        iApply semWP2_call_inline_later.
        iModIntro.
        iApply (semWP2_mono with "Htrip").
        iIntros ([] ? ? ?) "(<- & <- & H)"; auto.
        iDestruct "H" as "(%na & (Hpc & Hinstr & Hnpc) & Htrip)".
        iApply semWP2_call_inline.
        iSpecialize ("Hk" with "[$Htrip $Hpc $Hnpc $Hinstr $Hpl $Hpr]").
        iApply (semWP2_mono with "Hk").
        iIntros (? ? ? ?) "(<- & _ & $)"; auto.
      - cbn. iDestruct ("Htrip" with "HPRE") as "(_ & Htrip)". fold step_n.
        iDestruct "Hpro" as "(Hpc & Hinstrs & Hnpc)"; cbn.
        iDestruct "Hinstrs" as "(Hinstr & Hinstrs)".
        iSpecialize ("Htrip" with "[$Hpc $Hinstr $Hnpc]").
        unfold WP2_loop at 4.
        iApply (semWP2_fun_loop with "Hpl Hpr").
        iIntros "Hpl Hpr" (Γon1 Γon2 δon1 δon2).
        iApply semWP2_seq.
        iApply semWP2_call_inline_later.
        iModIntro.
        iApply (semWP2_mono with "Htrip").
        iIntros ([] ? ? ?) "(<- & <- & H)"; auto.
        iDestruct "H" as "(%na & (Hpc & Hinstr & Hnpc) & Htrip)".
        iApply semWP2_call_inline.
        iDestruct "Htrip" as "(<- & Htrip)".
        iSpecialize ("IH" $! (λ _, True)%I (bv.add a bv_instrsize) i (λ _, POST a) with "[$Hpl $Hpr] [$Hpc $Hinstrs $Hnpc] [] [Htrip] [Hinstr Hk]");
          first auto.
        + iIntros "_".
          iSplitR; first auto. fold step_n.
          iExact "Htrip".
        + iModIntro.
          iIntros (an) "(HPOST & Hepi & Hpow)".
          iApply ("Hk" with "[$HPOST $Hinstr $Hepi $Hpow]").
        + iApply (semWP2_mono with "IH").
          iIntros (? ? ? ?) "(<- & _ & $)"; auto.
    Qed.

    (* A block of a single instruction that powers off both machines: after
       the power check that precedes the instruction, the instruction consumes
       the power tokens `powered2 true` and produces `powered2 false`. Compare
       with [WP2_loop_semTripleBlock], where the block leaves the tokens alone. *)
    Lemma WP2_loop_semTripleBlock_power_off {R : iProp Σ} : ∀ PRE a instr POST,
      powered2 true -∗
      (exec_instructions_prologue a [instr]) -∗
      (PRE a) -∗
      semTripleBlock (λ a, PRE a ∗ powered2 true) a [instr] (λ a an, POST a an ∗ powered2 false) -∗
      ▷ (∀ an, POST a an ∗ exec_instructions_epilogue a an [instr] ∗ powered2 false -∗ WP2_loop R) -∗
      WP2_loop R.
    Proof.
      iIntros (PRE a instr POST) "[Hpl Hpr] Hpro HPRE Htrip Hk".
      unfold WP2_loop at 2.
      iApply (semWP2_fun_loop with "Hpl Hpr").
      iIntros "Hpl Hpr" (Γon1 Γon2 δon1 δon2).
      cbn. iDestruct ("Htrip" with "[$HPRE $Hpl $Hpr]") as "(_ & Htrip)".
      iSpecialize ("Htrip" with "[Hpro]").
      { cbn. iDestruct "Hpro" as "($ & [$ _] & $)". }
      iApply semWP2_seq.
      iApply semWP2_call_inline_later.
      iModIntro.
      iApply (semWP2_mono with "Htrip").
      iIntros ([] ? ? ?) "(<- & <- & H)"; auto.
      iDestruct "H" as "(%na & (Hpc & Hinstr & Hnpc) & Htrip & Hoff)".
      iApply semWP2_call_inline.
      iSpecialize ("Hk" with "[$Htrip $Hpc $Hnpc $Hinstr $Hoff]").
      iApply (semWP2_mono with "Hk").
      iIntros (? ? ? ?) "(<- & _ & $)"; auto.
    Qed.

    Lemma WP2_loop_semTripleBlock {R : iProp Σ} : ∀ PRE a instrs POST,
      powered2 true -∗
      (exec_instructions_prologue a instrs) -∗
      (PRE a) -∗
      semTripleBlock PRE a instrs POST -∗
      (∀ an, POST a an ∗ exec_instructions_epilogue a an instrs ∗ powered2 true -∗ WP2_loop R) -∗
      WP2_loop R.
    Proof.
      iIntros (PRE a [|instr instrs] POST) "Hpow Hpro HPRE Htrip Hk".
      - cbn. iSpecialize ("Htrip" with "HPRE").
        iApply ("Hk" with "[$Htrip $Hpro $Hpow]").
      - now iApply (WP2_loop_semTripleBlock_later with "Hpow Hpro HPRE Htrip").
    Qed.

    Lemma step_n_focus (instrs : list AST) (ainstr apc : Val ty_xlenbits) (POST1 POST2 POST : Val ty_xlenbits -> iProp Σ) :
      @RVPTVl.step_n _ sailGS2_sailGS_left instrs ainstr apc POST1 -∗
      @RVPTVr.step_n _ sailGS2_sailGS_right instrs ainstr apc POST2 -∗
      (∀ na1 na2, POST1 na1 ∗ POST2 na2 -∗ ⌜na1 = na2⌝ ∗ POST na1) -∗
      step_n instrs ainstr apc POST.
    Proof.
      revert ainstr apc.
      iInduction instrs as [|instr instrs] "IH";
        iIntros (ainstr apc) "H1 H2 HPOST".
      - cbn. now iDestruct ("HPOST" with "[$H1 $H2]") as "(_ & $)".
      - cbn.
        iDestruct "H1" as "(<- & H1)".
        iDestruct "H2" as "($ & H2)".
        iIntros "([Hpc1 Hpc2] & [Hinstr1 Hinstr2] & (%npc & Hnpc1 & Hnpc2))".
        iSpecialize ("H1" with "[$Hpc1 $Hinstr1 $Hnpc1]").
        iSpecialize ("H2" with "[$Hpc2 $Hinstr2 $Hnpc2]").
        iApply (semWP2_focus with "H1 H2").
        iIntros ([v1|] δ1 [v2|] δ2) "(H1 & H2)"; auto.
        destruct v1, v2, (nenv.view δ1), (nenv.view δ2).
        repeat iSplitR; auto.
        destruct instrs as [|instr' instrs].
        + cbn.
          iDestruct "H1" as "(%na' & (Hpc1 & Hinstr1 & Hnpc1) & HPOST1)".
          iDestruct "H2" as "(% & (Hpc2 & Hinstr2 & Hnpc2) & HPOST2)".
          iDestruct ("HPOST" with "[$HPOST1 $HPOST2]") as "(<- & HPOST)".
          iExists na'. now iFrame "Hpc1 Hpc2 Hinstr1 Hinstr2 Hnpc1 Hnpc2 HPOST".
        + iDestruct "H1" as "(% & (Hpc1 & Hinstr1 & Hnpc1) & <- & H1)".
          iDestruct "H2" as "(% & (Hpc2 & Hinstr2 & Hnpc2) & <- & H2)".
          iExists (bv.add ainstr bv_instrsize).
          iFrame "Hpc1 Hpc2 Hinstr1 Hinstr2 Hnpc1 Hnpc2".
          iApply ("IH" with "[$H1] [$H2]"); auto.
    Qed.

    Lemma WP2_loop_step_left {R : iProp Σ} :
      powered_left true -∗
      @RVPBASEl.semTWP _ sailGS2_sailGS_left _ _ [env] fun_step
        (λ v _, match v with inl _ => powered_left true -∗ WP2_loop R | inr _ => False end) -∗ (* We cannot end up with a fail due to the fail logic for the BlockVer *)
      WP2_loop R.
    Proof.
      iIntros "Hp H". unfold WP2_loop at 2.
      iApply (semWP2_fun_loop_left with "Hp").
      iIntros "Hp" (Γon δon).
      iApply semWP2_seq_left. iApply RVPBASEl.semWP_call_inline.
      iApply RVPBASEl.semTWP_semWP. iApply (RVPBASEl.semTWP_mono with "H").
      iIntros ([v|m] δ) "H"; cbn; last done.
      iApply semWP2_call_inline_left.
      iSpecialize ("H" with "Hp").
      iApply (semWP2_mono with "H").
      iIntros (? δ1 ? δ2) "($ & _ & $)". now destruct (nenv.view δ1), (nenv.view δ2).
    Qed.

    Lemma WP2_loop_step_right {R : iProp Σ} :
      powered_right true -∗
      @RVPBASEr.semTWP _ sailGS2_sailGS_right _ _ [env] fun_step
        (λ v _, match v with inl _ => powered_right true -∗ WP2_loop R | inr _ => False end) -∗ (* We cannot end up with a fail due to the fail logic for the BlockVer *)
      WP2_loop R.
    Proof.
      iIntros "Hp H". unfold WP2_loop at 2.
      iApply (semWP2_fun_loop_right with "Hp").
      iIntros "Hp" (Γon δon).
      iApply semWP2_seq_right. iApply RVPBASEr.semTWP_call_inline.
      iApply (RVPBASEr.semTWP_mono with "H").
      iIntros ([v|m] δ) "H"; cbn; last done.
      iApply semWP2_call_inline_right.
      iSpecialize ("H" with "Hp").
      iApply (semWP2_mono with "H").
      iIntros (? δ1 ? δ2) "($ & _ & $)". now destruct (nenv.view δ1), (nenv.view δ2).
    Qed.

    (* Like the unary epilogue of a single execution, but remembering that
       nextpc equals pc. This is needed to recombine both executions after they
       ran asynchronously. *)
    Definition exec_instructions_epilogue_unary (srGS : sailRegGS Σ) (mG : mcMemGS Σ)
      (a an : Val ty_xlenbits) (l : list AST) : iProp Σ :=
      @reg_pointsTo _ srGS _ pc an ∗
      @RVPCOM.ptsto_instrs _ mG a l ∗
      @reg_pointsTo _ srGS _ nextpc an.

    Lemma WP2_loop_step_n_left {R : iProp Σ} (instr : AST) (instrs : list AST) (a apc : Val ty_xlenbits)
      (POST : Val ty_xlenbits -> iProp Σ) :
      powered_left true -∗
      @RVPTVl.exec_instructions_epilogue _ sailGS2_sailGS_left a apc (instr :: instrs) -∗
      @RVPTVl.step_n _ sailGS2_sailGS_left (instr :: instrs) a apc POST -∗
      (∀ an, POST an ∗ exec_instructions_epilogue_unary sailRegGS2_sailRegGS_left memGS_left a an (instr :: instrs) ∗ powered_left true -∗ WP2_loop R) -∗
      WP2_loop R.
    Proof.
      iInduction instrs as [|i instrs] "IH" forall (instr a apc POST);
        iIntros "Hp Hpro Htrip Hk"; cbn;
        iDestruct "Htrip" as "(<- & Htrip)";
        iDestruct "Hpro" as "(Hpc & (Hinstr & Hinstrs) & Hnpc)";
        iSpecialize ("Htrip" with "[$Hpc $Hinstr $Hnpc]");
        iApply (WP2_loop_step_left with "Hp");
        iApply (RVPBASEl.semTWP_mono with "Htrip");
        iIntros ([v|m] δ) "H"; cbn; try done;
        iDestruct "H" as "(%na & (Hpc & Hinstr & Hnpc) & Htrip)";
        iIntros "Hp".
      - iApply ("Hk" with "[$Htrip $Hpc $Hinstr $Hnpc $Hp]").
      - iApply ("IH" with "Hp [$Hpc $Hinstrs Hnpc] Htrip [Hinstr Hk]").
        + by iExists _.
        + iIntros (an) "(HPOST & (Hpc & Hinstrs & Hnpc) & Hp)".
          iApply ("Hk" with "[$HPOST $Hpc $Hinstr $Hinstrs $Hnpc $Hp]").
    Qed.

    Lemma WP2_loop_step_n_right {R : iProp Σ} (instr : AST) (instrs : list AST) (a apc : Val ty_xlenbits)
      (POST : Val ty_xlenbits -> iProp Σ) :
      powered_right true -∗
      @RVPTVr.exec_instructions_epilogue _ sailGS2_sailGS_right a apc (instr :: instrs) -∗
      @RVPTVr.step_n _ sailGS2_sailGS_right (instr :: instrs) a apc POST -∗
      (∀ an, POST an ∗ exec_instructions_epilogue_unary sailRegGS2_sailRegGS_right memGS_right a an (instr :: instrs) ∗ powered_right true -∗ WP2_loop R) -∗
      WP2_loop R.
    Proof.
      iInduction instrs as [|i instrs] "IH" forall (instr a apc POST);
        iIntros "Hp Hpro Htrip Hk"; cbn;
        iDestruct "Htrip" as "(<- & Htrip)";
        iDestruct "Hpro" as "(Hpc & (Hinstr & Hinstrs) & Hnpc)";
        iSpecialize ("Htrip" with "[$Hpc $Hinstr $Hnpc]");
        iApply (WP2_loop_step_right with "Hp");
        iApply (RVPBASEr.semTWP_mono with "Htrip");
        iIntros ([v|m] δ) "H"; cbn; try done;
        iDestruct "H" as "(%na & (Hpc & Hinstr & Hnpc) & Htrip)";
        iIntros "Hp".
      - iApply ("Hk" with "[$Htrip $Hpc $Hinstr $Hnpc $Hp]").
      - iApply ("IH" with "Hp [$Hpc $Hinstrs Hnpc] Htrip [Hinstr Hk]").
        + by iExists _.
        + iIntros (an) "(HPOST & (Hpc & Hinstrs & Hnpc) & Hp)".
          iApply ("Hk" with "[$HPOST $Hpc $Hinstr $Hinstrs $Hnpc $Hp]").
    Qed.

    Lemma WP2_loop_semTripleBlock_left {R : iProp Σ} : ∀ PRE a instrs POST,
      instrs ≠ []%list →
      ⊢ powered_left true -∗
        @RVPTVl.exec_instructions_prologue _ sailGS2_sailGS_left a instrs -∗
        PRE a -∗
        @RVPTVl.semTripleBlock _ sailGS2_sailGS_left PRE a instrs POST -∗
        (∀ an, POST a an ∗ exec_instructions_epilogue_unary sailRegGS2_sailRegGS_left memGS_left a an instrs ∗ powered_left true -∗ WP2_loop R) -∗
        WP2_loop R.
    Proof.
      iIntros (PRE a [|instr instrs] POST Hne) "Hp Hpro HPRE Htrip Hk"; first done.
      iApply (WP2_loop_step_n_left with "Hp Hpro [Htrip HPRE] Hk").
      by iApply "Htrip".
    Qed.

    Lemma WP2_loop_semTripleBlock_right {R : iProp Σ} : ∀ PRE a instrs POST,
      instrs ≠ []%list →
      ⊢ powered_right true -∗
        @RVPTVr.exec_instructions_prologue _ sailGS2_sailGS_right a instrs -∗
        PRE a -∗
        @RVPTVr.semTripleBlock _ sailGS2_sailGS_right PRE a instrs POST -∗
        (∀ an, POST a an ∗ exec_instructions_epilogue_unary sailRegGS2_sailRegGS_right memGS_right a an instrs ∗ powered_right true -∗ WP2_loop R) -∗
        WP2_loop R.
    Proof.
      iIntros (PRE a [|instr instrs] POST Hne) "Hp Hpro HPRE Htrip Hk"; first done.
      iApply (WP2_loop_step_n_right with "Hp Hpro [Htrip HPRE] Hk").
      by iApply "Htrip".
    Qed.

  End WithSailGS2.
End BinaryBlockVerifier.
