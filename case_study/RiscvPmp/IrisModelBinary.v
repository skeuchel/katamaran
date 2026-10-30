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

From Katamaran Require Import
     Bitvector
     Environment
     RiscvPmp.trace
     Iris.Base
     Iris.BinaryResources
     RiscvPmp.Machine
     RiscvPmp.IrisModel
     RiscvPmp.IrisInstance.
From iris.base_logic Require Import lib.gen_heap
  invariants.
From iris.proofmode Require Import proofmode.
From stdpp Require namespaces.
Module ns := stdpp.namespaces.

Set Implicit Arguments.

Import RiscvPmpProgram.

(* Instantiate the Iris framework solely using the operational semantics. At
   this point we do not commit to a set of contracts nor to a set of
   user-defined predicates. *)
Module Type RiscvPmpIrisBase2
  (Import RVPCOM : RiscvPmpIrisBaseCommon)
  (RVPBASEl : RiscvPmpIrisBase LeftOrRightLeft RVPCOM)
  (RVPBASEr : RiscvPmpIrisBase LeftOrRightRight RVPCOM)
  <: IrisBase2 RiscvPmpGlobalState RiscvPmpProgram RiscvPmpSemantics RVPCOM RVPBASEl RVPBASEr.

  (* Defines the memory ghost state. *)
  Section RiscvPmpIrisParams2.
    Import bv.

    Definition memGS2 : gFunctors -> Set := mcMemGS2.
    Existing Class memGS2.
    Definition memGS_left : forall `{mG : memGS2 Σ}, mcMemGS Σ := @mc_ghGS2_left.
    Definition memGS_right : forall `{mG : memGS2 Σ}, mcMemGS Σ := @mc_ghGS2_right.
    Definition memGS2_memGS_left `{mG : memGS2 Σ} : RVPBASEl.memGS Σ := mG.
    Definition memGS2_memGS_right `{mG : memGS2 Σ} : RVPBASEr.memGS Σ := mG.
    Definition mem_state_interp2 : forall {Σ}, memGS2 Σ -> Memory -> Memory -> iProp Σ :=
      fun {Σ} hG μ1 μ2 =>
        (RVPBASEl.mem_state_interp hG μ1 ∗ RVPBASEr.mem_state_interp hG μ2
        )%I.
    Lemma mem_state_interp2_mem_inv :
      forall `{mG : memGS2 Σ} (μ1 μ2 : Memory),
        mem_state_interp2 mG μ1 μ2 ⊣⊢ RVPBASEl.mem_state_interp mG μ1 ∗ RVPBASEr.mem_state_interp mG μ2.
    Proof. by unfold mem_state_interp2. Qed.

    Definition memGS2_gtGS2_left `{mG : memGS2 Σ} : traceG Trace Σ :=
      @mc_gtGS _ memGS_left.
    Definition memGS2_gtGS2_right `{mG : memGS2 Σ} : traceG Trace Σ :=
      @mc_gtGS _ memGS_right.
    Definition memGS2_wpGS2_left `{mG : memGS2 Σ} : writePendingG Σ :=
      @mc_wpGS _ memGS_left.
    Definition memGS2_wpGS2_right `{mG : memGS2 Σ} : writePendingG Σ :=
      @mc_wpGS _ memGS_right.

    (* (* DOMI: this lemma needs the two written_auth chunks as additional arguments and return the two nothingPending_auth chunks as additional results, see nothingPending_written in IrisModel.v *) *)
    (* Lemma written_nothingPending2 `{memGS2 Σ} e : *)
    (*   @written _ memGS2_wpGS2_left e ∗ @written _ memGS2_wpGS2_right e ==∗ *)
    (*   @nothingPending _ memGS2_wpGS2_left ∗ @nothingPending _ memGS2_wpGS2_right. *)
    (* Proof. *)
    (* Admitted. *)

  End RiscvPmpIrisParams2.

  Include IrisResources2 RiscvPmpGlobalState RiscvPmpProgram RiscvPmpSemantics RVPCOM RVPBASEl RVPBASEr.
End RiscvPmpIrisBase2.
