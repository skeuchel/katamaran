(******************************************************************************)
(* Copyright (c) 2026 Steven Keuchel, Dominique Devriese, Sander Huyghebaert  *)
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
     Base
     Bitvector
     Iris.Instance
     Iris.Base
     RiscvPmp.trace
     RiscvPmp.Base
     RiscvPmp.Machine
     RiscvPmp.IrisModel
     RiscvPmp.IrisInstance
     RiscvPmp.Logic
     RiscvPmp.Sig
     RiscvPmp.Everything.

From iris.base_logic Require Import invariants lib.iprop lib.gen_heap.
From iris.proofmode Require Import proofmode.

Set Implicit Arguments.
Import bv.notations.

(* Adequacy for a single (unary) execution.

   The unary Iris instances share their memory ghost state (mcMemGS2) and the
   MMIO invariant with a second execution, so that the binary verification can
   reuse unary contracts. For a unary end-to-end result there is no second
   execution. We allocate a "phantom" second execution instead, which only
   consists of ghost state: a trace and a writePending state. Owning the
   phantom's resources lets a unary proof resynchronize the shared invariant
   after an observable write on its own (see phantom_resync). *)
Module Type RiscvPmpIrisAdeqParams
  (Import LOR : LeftOrRight)
  (Import RVPCOM : RiscvPmpIrisBaseCommon)
  (Import RVPBASE : RiscvPmpIrisBase LOR RVPCOM)
<: IrisAdeqParameters RiscvPmpGlobalState RVPBASE.

  Definition memGpreS : gFunctors -> Set := RVPCOM.memGpreS.
  Definition memΣ : gFunctors := RVPCOM.memΣ.
  Definition memΣ_GpreS : forall {Σ}, subG memΣ Σ -> memGpreS Σ := @RVPCOM.memΣ_GpreS.

  Section Phantom.
    Context {Σ : gFunctors} {mG : mcMemGS2 Σ}.

    (* The resources of the phantom execution that are not part of the shared
       invariant. *)
    Definition phantom_res : iProp Σ :=
      (∃ t, @tr_auth _ _ (@mc_gtGS _ otherInstance) t) ∗
      @nothingPending _ (@mc_wpGS _ otherInstance).

    (* Besides the resources of this execution, we hand out the parts of the
       phantom execution that go into the shared invariant (which is allocated
       by the end-to-end proof), and the phantom's remaining resources. *)
    Definition mem_res : Memory -> iProp Σ :=
      fun μ => (([∗ list] a' ∈ liveAddrs, pointsto a' (DfracOwn 1) (memory_ram μ a')) ∗
               tr_frag (memory_trace μ) ∗
               nothingPending_auth ∗
               nothingPending ∗
               powered (fun_powered_on μ) ∗
               @tr_frag _ _ (@mc_gtGS _ otherInstance) (memory_trace μ) ∗
               @nothingPending_auth _ (@mc_wpGS _ otherInstance) ∗
               phantom_res
            )%I.
  End Phantom.

  Lemma initMemMap_works μ : map_Forall (λ (a : Addr) (v : MemVal), memory_ram μ a = v) (initMemMap μ).
  Proof.
    unfold initMemMap.
    rewrite map_Forall_to_list.
    rewrite Forall_forall.
    intros (a , v).
    rewrite elem_of_map_to_list.
    intros el.
    apply elem_of_list_to_map_2 in el.
    apply list_elem_of_In in el.
    apply in_map_iff in el.
    by destruct el as (a' & <- & _).
  Qed.

  Lemma mem_init `{gHP : memGpreS Σ} (μ : Memory) :
    ⊢ |==> ∃ mG : memGS Σ, (mem_state_interp mG μ ∗ mem_res (mG := mG) μ)%I.
  Proof.
    unfold memGpreS, RVPCOM.memGpreS in gHP.
    pose (memmap := initMemMap μ).
    iMod (gen_heap_init (L := Addr) (V := MemVal) memmap) as (gH) "[Hinv [Hmapsto _]]".
    iMod (trace_alloc (memory_trace μ)) as (gT) "[Hauth Hfrag]".
    iMod writePending_alloc as (gP) "[HauthPend HfragPend]".
    iMod (powered_alloc (fun_powered_on μ)) as (gW) "[HauthPow HfragPow]".
    (* The phantom execution only needs a trace and a writePending state. *)
    iMod (gen_heap_init (L := Addr) (V := MemVal) ∅) as (gHo) "_".
    iMod (trace_alloc (memory_trace μ)) as (gTo) "[Hautho Hfrago]".
    iMod writePending_alloc as (gPo) "[HauthPendo HfragPendo]".
    iMod (powered_alloc (fun_powered_on μ)) as (gWo) "_".
    iModIntro.
    iExists (if leftOrRight
             then McMemGS2 (McMemGS gH gT gP gW) (McMemGS gHo gTo gPo gWo)
             else McMemGS2 (McMemGS gHo gTo gPo gWo) (McMemGS gH gT gP gW)).
    iPoseProof (big_sepM_list_to_map with "Hmapsto") as "Hm".
    { eapply NoDup_liveAddrs. }
    change (map ?f liveAddrs) with (fmap f liveAddrs).
    rewrite big_sepL_fmap.
    unfold mem_state_interp, mem_res, phantom_res, otherInstance, leftOrRightInstance.
    destruct leftOrRight; cbn [mc_ghGS2_left mc_ghGS2_right mc_ghGS mc_gtGS mc_wpGS mc_pwGS];
      iFrame "Hinv Hauth Hfrag HauthPend HfragPend HauthPow HfragPow Hfrago HauthPendo HfragPendo Hm";
      (iSplitR; [iPureIntro; apply initMemMap_works | by iExists _]).
  Qed.

  (* The first adversary-observable event of a trace satisfying mmio_pred
     satisfies the event predicate, and is kept by the observability filter. *)
  Lemma filter_adv_observable_head width ts e t :
    mmio_pred width ts -> filter_adv_observable ts = e :: t ->
    event_pred width e ∧ ∀ ts', filter_adv_observable (e :: ts') = e :: filter_adv_observable ts'.
  Proof.
    intros Hpred Hfilter.
    assert (Hin : List.In e (filter_adv_observable ts)) by (rewrite Hfilter; now left).
    unfold filter_adv_observable in Hin.
    apply List.filter_In in Hin as [Hin Hobs].
    split.
    - by eapply List.Forall_forall.
    - intros ts'. unfold filter_adv_observable. cbn. by rewrite Hobs.
  Qed.

  Section Resync.
    Context `{invGS Σ} {mG : mcMemGS2 Σ}.

    (* After an observable write, this execution is one event ahead of the
       phantom execution. Using the phantom's resources, we let the phantom
       perform the same write, which resynchronizes both executions. *)
    Lemma phantom_resync (width : nat) (e : Event) E :
      ↑femto_inv_mmio_ns ⊆ E ->
      interp_inv_mmio width -∗
      phantom_res -∗
      written e ={E}=∗
      phantom_res ∗ nothingPending.
    Proof.
      iIntros (HE) "#Hinv [[%to Hautho] Hnpo] Hw".
      iInv "Hinv" as ">(%t & Hsides)" "Hclose".
      rewrite inv_mmio_body_own_other.
      iDestruct "Hsides" as "[(%ts & Hfrag & %Hpred & Hown) (%tso & Hfrago & %Hpredo & Hother)]".
      iDestruct "Hown" as "[[_ Ha] | (%e' & %Ht & Ha)]".
      { iDestruct (nothingPending_auth_written with "Ha Hw") as "[]". }
      iDestruct (written_auth_written with "Ha Hw") as %->.
      iDestruct "Hother" as "[[%Hto Hao] | (%e'' & _ & Hao)]";
        last by iDestruct (written_auth_nothingPending with "Hao Hnpo") as "[]".
      destruct (filter_adv_observable_head Hpred Ht) as [He Hcons].
      iDestruct (trace_full_frag_eq with "Hautho Hfrago") as %->.
      iMod (trace_update _ (e :: tso) with "[$Hautho $Hfrago]") as "[Hautho Hfrago]".
      iMod (written_nothingPending with "[$Ha $Hw]") as "[Ha $]".
      iMod ("Hclose" with "[Hfrag Ha Hfrago Hao]") as "_".
      { iExists (e :: t). rewrite inv_mmio_body_own_other.
        iSplitL "Hfrag Ha".
        - iExists ts. iFrame "Hfrag". iSplitR; first done.
          iLeft. by iFrame "Ha".
        - iExists (e :: tso). iFrame "Hfrago".
          iSplitR; first (iPureIntro; by constructor).
          iLeft. iFrame "Hao". by rewrite Hcons Hto. }
      iModIntro. iFrame "Hnpo". by iExists _.
    Qed.
  End Resync.

End RiscvPmpIrisAdeqParams.

Module RVPADEQl : RiscvPmpIrisAdeqParams LeftOrRightLeft RVPCOM RVPBASEl.
  Include RiscvPmpIrisAdeqParams LeftOrRightLeft RVPCOM RVPBASEl.
End RVPADEQl.

Module RVPADEQUACYl : IrisAdequacy RiscvPmpGlobalState RiscvPmpSignature RiscvPmpProgram
                        RiscvPmpSemantics RiscvPmpProgramLogic RVPCOM RVPBASEl RVPADEQl RVPINSTl RVPINSTl.
  Include IrisAdequacy RiscvPmpGlobalState RiscvPmpSignature RiscvPmpProgram
    RiscvPmpSemantics RiscvPmpProgramLogic RVPCOM RVPBASEl RVPADEQl RVPINSTl RVPINSTl.
End RVPADEQUACYl.
