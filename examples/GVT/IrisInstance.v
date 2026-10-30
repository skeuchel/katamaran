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
     Base
     Hoare
     Bitvector
     Iris.Instance
     Iris.Base
     Syntax.Predicates
     RiscvPmp.Base
     RiscvPmp.PmpCheck
     RiscvPmp.Machine
     RiscvPmp.GVT.Logic
     RiscvPmp.GVT.IrisModel
     RiscvPmp.GVT.trace
     RiscvPmp.iostate
     RiscvPmp.GVT.Sig.

From iris.base_logic Require Import invariants lib.iprop lib.gen_heap.
From iris.proofmode Require Import proofmode.
From stdpp Require namespaces.
Module ns := stdpp.namespaces.

Set Implicit Arguments.
Import bv.notations.

Module RiscvPmpIrisAdeqParameters <: IrisAdeqParameters RiscvPmpGlobalState RiscvPmpIrisBase.
  (* Pull in the definition of the LanguageMixin and register ghost state. *)
  Import RiscvPmpIrisPrelims RiscvPmpIrisBase.

  Class mcMemPreGS Σ := {
      mc_ghPreGS :: gen_heapGpreS Addr MemVal Σ;
      mc_gtPreGS :: trace_preG Trace Σ;
      mc_gsPreGS :: iostate_preG IOState Σ;
    }.
  #[export] Existing Instance mc_ghPreGS.
  #[export] Existing Instance mc_gtPreGS.
  #[export] Existing Instance mc_gsPreGS.

  Definition memGpreS : gFunctors -> Set := mcMemPreGS.
  Definition memΣ : gFunctors := #[gen_heapΣ Addr MemVal ; tracePreΣ Trace ; iostatePreΣ IOState].

  Lemma NoDup_liveAddrs : NoDup liveAddrs.
  Proof. exact Base.NoDup_liveAddrs. Qed.

  #[global] Arguments liveAddrs : simpl never.

  Definition initMemMap μ := (list_to_map (map (fun a => (a , memory_ram μ a)) liveAddrs) : gmap Addr MemVal).

  Definition memΣ_GpreS : forall {Σ}, subG memΣ Σ -> memGpreS Σ.
  Proof. intros. solve_inG. Defined.

  (* mem_res is the predicate representing full ownership of the entire memory
   * which is given to the verifier in the adequacy lemma.
   *)
  Definition mem_res `{hG : mcMemGS Σ} : Memory -> iProp Σ :=
    fun μ => (([∗ list] a' ∈ liveAddrs, pointsto a' (DfracOwn 1) (memory_ram μ a')) ∗ tr_frag1 (memory_trace μ))%I.

  Definition iost_res `{hG : mcMemGS Σ} {rG : iostateG IOState Σ} : IOState -> iProp Σ :=
    fun σ => (st_auth1 σ )%I.

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

  Lemma big_sepM_list_to_map {Σ} {A B : Type} `{Countable A} {l : list A} {f : A -> B} (F : A -> B -> iProp Σ) :
    NoDup l ->
    ([∗ map] l↦v ∈ (list_to_map (map (λ a : A, (a, f a)) l)), F l v)
      ⊢
      [∗ list] v ∈ l, F v (f v).
  Proof.
    intros ndl.
    induction ndl.
    - now iIntros "_".
    - cbn.
      rewrite big_sepM_insert.
      + iIntros "[$ Hrest]".
        now iApply IHndl.
      + apply not_elem_of_list_to_map_1.
        change (fmap fst ?l) with (map fst l).
        now rewrite map_map map_id.
  Qed.

  Lemma mem_init `{gHP : !mcMemPreGS Σ} (μ : Memory) :
    ⊢ |==> ∃ mG : mcMemGS Σ, (mem_state_interp mG μ ∗ mem_res μ)%I.
  Proof.
    pose (memmap := initMemMap μ).
    iMod (gen_heap_init (L := Addr) (V := MemVal) memmap) as (gH) "[Hinv [Hmapsto _]]".
    iMod (trace_alloc (memory_trace μ)) as (gT) "[Htrauth Htrfrag]".
    iModIntro.
    iExists (McMemGS gH gT).
    iSplitL "Hinv Htrauth".
    - iExists memmap.
      iFrame.
      iPureIntro.
      apply initMemMap_works.
    - unfold mem_res, initMemMap in *. iFrame.
        iApply (big_sepM_list_to_map (f := memory_ram μ) (fun a v => pointsto a (DfracOwn 1) v) with "[$]").
        eapply NoDup_liveAddrs.
  Qed.

End RiscvPmpIrisAdeqParameters.

Module RiscvPmpIrisInstancePredicates.
  Import RiscvPmpIrisPrelims RiscvPmpIrisBase.
  Import RiscvPmpProgram.

  Definition addr_inc (x : bv 32) (n : nat) : bv 32 :=
    bv.add x (bv.of_nat n).

  Fixpoint get_byte {width : nat} (offset : nat) : bv (width * byte) -> Byte :=
    match width with
    | O   => fun _ => bv.zero
    | S w =>
        fun bytes =>
          let (byte, bytes) := bv.appView byte (w * byte) bytes in
          match offset with
          | O        => byte
          | S offset => get_byte offset bytes
          end
    end.

  Definition s__init : IOState := SGo.

  (* Tut: Note, trace is kept in reverse order *)
  Inductive mmio_trace_state_pred: Trace -> IOState -> Prop :=
  | Tnil : mmio_trace_state_pred [] s__init
  | Tcons  : forall e tl s s', impl_mmio_event_prot e s s' ->
                         mmio_trace_state_pred tl s ->
                         mmio_trace_state_pred (e :: tl) s'.

  Lemma difference_commute_gset {A} `{Countable A} (X Y Z : gset A) :
    (X ∖ Y) ∖ Z = (X ∖ Z) ∖ Y.
  Proof.
    apply set_eq.
    intros x.
    rewrite ?elem_of_difference.
    split.
    - intros ([HX HY] & HZ).
      repeat split; auto.
    - intros ([HX HZ] & HY).
      repeat split; auto.
  Qed.

  Lemma list_to_set_subseteq : ∀ {A : Type} {HEqDecision : EqDecision A}
                                 {HCountable : Countable A} (l1 l2 : list A),
      (list_to_set l1 : gset A) ⊆ list_to_set l2 <-> l1 ⊆ l2.
  Proof.
    intros ? ? ? l1 l2.
    rewrite ?elem_of_subseteq.
    split; intros Hl e He.
    - rewrite <- (@elem_of_list_to_set _ (gset _) _ _ _ _ _).
      rewrite <- (@elem_of_list_to_set _ (gset _) _ _ _ _ _) in He.
      now apply Hl.
    - apply elem_of_list_to_set.
      apply elem_of_list_to_set in He. auto.
  Qed.

  Lemma list_to_set_cons_subseteq {A : Type} `{Countable A} (y : A) (Y : list A) (X : gset A) :
    NoDup (y :: Y) ->
    list_to_set (y :: Y) ⊆ X -> list_to_set Y ⊆ (X ∖ {[y]}).
  Proof.
    intros Hdup Hsub.
    remember Hdup as HyY. clear HeqHyY.
    rewrite NoDup_cons in HyY.
    destruct HyY as [Hy HY].
    cbn in Hsub.
    rewrite union_subseteq in Hsub.
    destruct Hsub as [HyX Hsub].
    intros x Hx.
    apply elem_of_difference; split.
    - now apply Hsub.
    - intros Helem.
      apply elem_of_singleton in Helem; subst.
      rewrite elem_of_list_to_set in Hx.
      contradiction.
  Qed.

  Lemma big_sepS_delete_multi_list :
    ∀ {Σ} {A : Type} {EqDecision0 : EqDecision A} {H : Countable A} (Φ : A → iProp Σ)
      (X : gset A) (Y : list A),
      NoDup Y ->
      list_to_set Y ⊆ X ->
      ([∗ set] x ∈ X, Φ x) ⊣⊢ ([∗ list] y ∈ Y, Φ y) ∗ ([∗ set] x ∈ (X ∖ list_to_set Y), Φ x).
  Proof.
    intros ? ? ? ? Φ X Y.
    revert X.
    iInduction Y as [|y Y] "IH";
      iIntros (X Hdup Hsub).
    - cbn. rewrite difference_empty_L.
      iSplit.
      iIntros "$".
      iIntros "(_ & $)".
    - iSplit.
      + iIntros "H".
        remember Hsub as Hsub' eqn:Heq. clear Heq.
        cbn in Hsub.
        rewrite union_subseteq in Hsub.
        destruct Hsub as (Hy & Hsub).
        rewrite <- elem_of_subseteq_singleton in Hy.
        cbn.
        iPoseProof (big_sepS_delete _ _ y Hy with "H") as "($ & H)".
        rewrite <- difference_difference_l_L.
        apply list_to_set_cons_subseteq in Hsub'; auto.
        apply NoDup_cons in Hdup. destruct Hdup as [HyY Hdup].
        iSpecialize ("IH" $! (X ∖ {[ y ]}) Hdup Hsub').
        now iApply "IH".
      + iIntros "(HY & HX)".
        cbn. iDestruct "HY" as "(Hy & HY)".
        rewrite <- difference_difference_l_L.
        rewrite difference_commute_gset.
        iPoseProof (@big_sepS_delete_2 _ _ _ _ _ _ _ with "Hy HX") as "H".
        apply NoDup_cons in Hdup.
        destruct Hdup as [HyY Hdup].
        cbn in Hsub. rewrite union_subseteq in Hsub.
        destruct Hsub as [HyX Hsub].
        iApply ("IH" $! _ Hdup Hsub).
        iFrame "HY H".
  Qed.

  Lemma big_sepS_delete_multi :
    ∀ {Σ} {A : Type} {EqDecision0 : EqDecision A} {H : Countable A} (Φ : A → iProp Σ)
      (X : gset A) (Y : gset A),
      Y ⊆ X ->
      ([∗ set] x ∈ X, Φ x) ⊣⊢ ([∗ set] y ∈ Y, Φ y) ∗ ([∗ set] x ∈ (X ∖ Y), Φ x).
  Proof.
    intros ? ? ? ? Φ X Y Hsub.
    remember (elements Y) as l eqn:El.
    assert (Hdup: NoDup l) by (subst; apply NoDup_elements).
    assert (Hl: list_to_set l = Y) by (subst; apply list_to_set_elements_L).
    assert (Hsub': list_to_set l ⊆ X) by (now rewrite Hl).
    iSplit.
    - iIntros "H".
      iPoseProof (big_sepS_delete_multi_list _ Hdup Hsub' with "H") as "H".
      rewrite Hl. iDestruct "H" as "(H & $)".
      rewrite <- Hl.
      now iApply big_sepS_list_to_set.
    - iIntros "(HY & HX)".
      iApply (big_sepS_delete_multi_list _ Hdup Hsub').
      rewrite Hl. iFrame "HX".
      rewrite <- Hl.
      now iApply big_sepS_list_to_set.
  Qed.

  Lemma NoDup_reg_convert_to_idx (l : list (Reg ty_xlenbits)) :
    NoDup l ->
    NoDup (omap reg_convert_to_idx l).
  Proof.
    induction l as [|r l IH]; cbn; intros Hdup; try constructor.
    apply NoDup_cons in Hdup. destruct Hdup as [Hr Hdup].
    specialize (IH Hdup).
    destruct (reg_convert_to_idx r) as [rid|] eqn:E; auto.
    apply NoDup_cons. split; auto.
    intros Helem.
    apply list_elem_of_omap in Helem.
    destruct Helem as (? & Hin & Heq).
    pose proof (reg_convert_to_idx_Some_inj _ _ E Heq) as ?; subst.
    apply (Hr Hin).
  Qed.

  Section WithMemory.
    Context {Σ : gFunctors} {mG : mcMemGS Σ}.

    (* TODO: change back to words instead of bytes... might be an easier first version
             and most likely still convenient in the future *)
    Definition interp_ptsto (addr : Addr) (b : Byte) : iProp Σ :=
      pointsto addr (DfracOwn 1) b ∗ ⌜¬ withinMMIO addr 1⌝.
    Definition ptstoSth : Addr -> iProp Σ := fun a => (∃ w, interp_ptsto a w)%I.
    Definition ptstoSthL : list Addr -> iProp Σ :=
      fun addrs => ([∗ list] k↦a ∈ addrs, ptstoSth a)%I.

    Definition interp_ptstomem' {width : nat} (addr : Addr) (bytes : bv (width * byte)) : iProp Σ :=
      [∗ list] offset ∈ seq 0 width,
        interp_ptsto (addr + bv.of_nat offset) (get_byte offset bytes).
    Fixpoint interp_ptstomem {width : nat} (addr : Addr) : bv (width * byte) -> iProp Σ :=
      match width with
      | O   => fun _ => True
      | S w =>
          fun bytes =>
            let (byte, bytes) := bv.appView byte (w * byte) bytes in
            interp_ptsto addr byte ∗ interp_ptstomem (bv.one + addr) bytes
      end%I.
    Global Arguments interp_ptstomem {width} addr v : simpl never.

    Definition femto_inv_mmio_ns : ns.namespace := (ns.ndot ns.nroot "inv_mmio").
    Definition interp_inv_mmio `{invGS Σ} (width : nat) : iProp Σ :=
      inv femto_inv_mmio_ns (∃ t, tr_frag1 t).
    Definition interp_mmio_trace_state_inv `{invGS Σ, iostateG IOState Σ} : iProp Σ :=
      inv femto_inv_mmio_ns (∃ (s : IOState) (t : Trace) , tr_frag1 t ∗ st_auth1 s ∗ ⌜mmio_trace_state_pred t s⌝).

    Definition interp_mmio_ptsto (addr : Addr) (b : Byte) : iProp Σ :=
      pointsto addr (DfracOwn 1) b ∗ ⌜withinMMIO addr 1⌝.
    Definition interp_mmio_ptstommio' {width : nat} (addr : Addr) (bytes : bv (width * byte)) : iProp Σ :=
      [∗ list] offset ∈ seq 0 width,
        interp_mmio_ptsto (addr + bv.of_nat offset) (get_byte offset bytes).
    Fixpoint interp_mmio_ptstommio {width : nat} (addr : Addr) : bv (width * byte) -> iProp Σ :=
      match width with
      | O   => fun _ => True
      | S w =>
          fun bytes =>
            let (byte, bytes) := bv.appView byte (w * byte) bytes in
            interp_mmio_ptsto addr byte ∗ interp_mmio_ptstommio (bv.one + addr) bytes
      end%I.
    Global Arguments interp_mmio_ptstommio {width} addr v : simpl never.

    Definition interp_mmio_state_checked_read `{invGS Σ} {width : nat} (addr : Addr) (bytes : bv (width * byte)) (s s': bv iostate_bits)  : iProp Σ :=
      ⌜withinMMIO addr width⌝ ∗
                ⌜let e := {| event_type := IORead;  event_addr := addr;  event_nbbytes := width;  event_contents := bytes |}
          in  impl_mmio_event_prot e (bv2s s) (bv2s s')⌝.

    Definition interp_mmio_state_checked_write `{invGS Σ} {width : nat} (addr : Addr) (bytes : bv (width * byte)) (s s': bv iostate_bits)  : iProp Σ :=
      ⌜withinMMIO addr width⌝ ∗
      ⌜let e := {| event_type := IOWrite;  event_addr := addr;  event_nbbytes := width ;  event_contents := bytes |}
      in  impl_mmio_event_prot e (bv2s s) (bv2s s')⌝.

    (* Current protocol state is: *)
    Definition interp_mmio_state_pred `{iostateG IOState Σ} (s : bv iostate_bits) : iProp Σ :=
      st_frag1 (bv2s s).


    Definition femto_inv_ro_ns : ns.namespace := (ns.ndot ns.nroot "inv_ro").
    Definition interp_ptstomem_readonly `{invGS Σ} {width : nat} (addr : Addr) (b : bv (width * byte)) : iProp Σ :=
      inv femto_inv_ro_ns (interp_ptstomem addr b).


    Section WithAddrs.
      Variable (live_addrs mmio_addrs : list Addr).

      (* Universal contract for single byte/`width` bytes after PMP checks *)
      Definition interp_addr_access_byte (a : Addr) : iProp Σ :=
        if decide (a ∈ mmio_addrs) then False%I (* Creates a proof obligation that the adversary cannot access MMIO. TODO: Change this to a trace filter to grant the adversary access to MMIO *)
        else if decide (a ∈ live_addrs) then ptstoSth a
             else True%I. (* Could be `False` as well *)
      Definition interp_addr_access (base : Addr) (width : nat): iProp Σ :=
        [∗ list] a ∈ bv.seq base (Z.of_nat width), interp_addr_access_byte a.

      Definition interp_pmp_addr_access (entries : list PmpEntryCfg) (m : Privilege) : iProp Σ :=
        [∗ list] a ∈ all_addrs,
          (⌜∃ p, Pmp_access a (bv.of_nat 1) entries m p⌝ -∗ interp_addr_access_byte a)%I.

      Lemma interp_pmp_addr_access_s_u_eq (entries : list PmpEntryCfg) :
        interp_pmp_addr_access entries User ⊣⊢ interp_pmp_addr_access entries Supervisor.
      Proof.
        iSplit; iApply big_sepL_mono; iIntros (k addr Hk) "H [%p %Hpmp]";
          iApply "H"; iExists p; iPureIntro; unfold Pmp_access, Gen_Pmp_access in *.
        - now rewrite pmp_check_aux_s_u_eq.
        - now rewrite pmp_check_aux_s_u_eq in Hpmp.
      Qed.

      Lemma interp_pmp_addr_access_not_machine (entries : list PmpEntryCfg) (m m' : Privilege) :
        m ≠ Machine -> m' ≠ Machine ->
        interp_pmp_addr_access entries m ⊢ interp_pmp_addr_access entries m'.
      Proof.
        intros Hm Hm'; destruct m, m'; try congruence;
          by rewrite ?interp_pmp_addr_access_s_u_eq.
      Qed.

      Definition interp_pmp_addr_access_without (addr : Addr) (width : nat)  (entries : list PmpEntryCfg) (m : Privilege) : iProp Σ :=
        (@interp_addr_access addr width -∗ interp_pmp_addr_access entries m)%I.
    End WithAddrs.

    (* TODO: introduce constant for nr of word bytes (replace 4) *)
    Definition interp_ptsto_instr (addr : Addr) (instr : AST) : iProp Σ :=
      (∃ v, @interp_ptstomem 4 addr v ∗ ⌜ pure_decode v = inr instr ⌝)%I.
  End WithMemory.

  Section WithSailGS.
    Context `{sailRegGS Σ} `{invGS Σ}.

    Definition interp_gprs (exclude : gset (Reg ty_xlenbits)) : iProp Σ :=
      [∗ set] r ∈ GPRS ∖ exclude,
        (∃ v, reg_pointsTo r v)%I.

    Lemma list_to_set_list_difference : ∀ {A : Type} `{Countable A} (l1 l2 : list A),
      (list_to_set (list_difference l1 l2) : gset A) = list_to_set l1 ∖ list_to_set l2.
    Proof.
      intros ? ? ? l1 l2. apply set_eq. revert l2.
      induction l1 as [|e1 l1 IHl1];
        intros l2 e; simpl; split; intros He.
      - inversion He.
      - apply elem_of_difference in He.
        now destruct He as [He _].
      - case_match.
        + rewrite difference_union_distr_l_L.
          apply elem_of_union_r.
          now apply IHl1.
        + cbn in *.
          rewrite difference_union_distr_l_L.
          apply elem_of_union in He.
          destruct He as [He|He].
          * apply elem_of_union_l.
            apply elem_of_difference.
            split; auto.
            rewrite elem_of_list_to_set.
            apply elem_of_singleton in He.
            now subst.
          * apply elem_of_union_r.
            now apply IHl1.
      - rewrite elem_of_difference in He.
        destruct He as [Hl1 Hl2].
        case_match.
        + apply IHl1.
          apply elem_of_union in Hl1.
          destruct Hl1 as [He|He].
          * apply elem_of_singleton in He. subst.
            rewrite elem_of_list_to_set in Hl2. contradiction.
          * now apply elem_of_difference.
        + simpl. apply elem_of_union.
          apply elem_of_union in Hl1.
          destruct Hl1 as [He|He].
          * now left.
          * right. apply IHl1.
            now apply elem_of_difference.
    Qed.

    Lemma interp_gprs_with_excluded `{sailGS Σ} (exclude : gset (Reg ty_xlenbits)) :
      exclude ⊆ GPRS ->
      ([∗ set] r ∈ exclude, ∃ v, reg_pointsTo r v) ∗ interp_gprs exclude ⊣⊢ interp_gprs ∅.
    Proof.
      intros Hsub.
      unfold interp_gprs.
      rewrite difference_empty_L.
      iApply bi.wand_iff_sym.
      now iApply big_sepS_delete_multi.
    Qed.





    Definition PmpEntryCfg : Set := Pmpcfg_ent * Xlenbits.

    Definition interp_pmp_entries (entries : list PmpEntryCfg) : iProp Σ :=
      match entries with
      | (cfg0, addr0) :: (cfg1, addr1) :: [] =>
          reg_pointsTo pmp0cfg cfg0 ∗
          reg_pointsTo pmpaddr0 addr0 ∗
          reg_pointsTo pmp1cfg cfg1 ∗
          reg_pointsTo pmpaddr1 addr1
      | _ => False
      end.
  End WithSailGS.
End RiscvPmpIrisInstancePredicates.

Module RiscvPmpIrisInstance <:
  IrisInstance RiscvPmpGlobalState RiscvPmpSignature RiscvPmpProgram RiscvPmpSemantics
    RiscvPmpProgramLogic RiscvPmpIrisPrelims RiscvPmpIrisBase.
  Import RiscvPmpIrisPrelims RiscvPmpIrisBase.
  Import RiscvPmpProgram.
  Import RiscvPmpIrisInstancePredicates.

  #[global] Notation "a '↦ₘ' t" := (interp_ptsto a t) (at level 70).

  Section RiscvPmpIrisPredicates.

    Import env.notations.
    Definition resGS := iostateG IOState.

    Equations(noeqns) luser_inst `{sailRegGS Σ, invGS Σ, mcMemGS Σ, iostateG IOState Σ}
      (p : Predicate) (ts : Env Val (𝑯_Ty p)) : iProp Σ :=
    | pmp_entries               | [ v ]                => interp_pmp_entries v
    | pmp_addr_access           | [ entries; m ]       => interp_pmp_addr_access liveAddrs mmioAddrs entries m
    | pmp_addr_access_without bytes | [ addr; entries; m ] => interp_pmp_addr_access_without liveAddrs mmioAddrs addr bytes entries m
    | gprs                      | _                    => interp_gprs ∅ (* For the Universal Contract verification we always need all GPRs, hence the empty exclude list *)
    | ptsto                     | [ addr; w ]          => interp_ptsto addr w
    | ptsto_one _               | [ addr; w ]          => False (* Unary instance has no support for different execution predicates *)
    | ptstomem_readonly _       | [ addr; w ]          => interp_ptstomem_readonly addr w
    | inv_mmio bytes            | _                    => interp_inv_mmio bytes
    | mmio_ptsto                | [ addr; w ]          => interp_mmio_ptsto addr w
    | mmio_ptstommio _          | [ addr; bs ]         => interp_mmio_ptstommio addr bs
    | mmio_state _              | [s] (* [unit] *)     => interp_mmio_state_pred s (* We have ownership over st *)
    | mmio_state_trace bytes    | [env] (* [unit] *)   => interp_mmio_trace_state_inv (* Given st and tr state_prot is satisfied *)
    | mmio_state_checked_read _ | [addr; w; s; s'] => interp_mmio_state_checked_read addr w s s'
    | mmio_state_checked_write _ | [addr; w; s; s'] => interp_mmio_state_checked_write addr w s s'
    | encodes_instr             | [ code; instr ]      => ⌜pure_decode code = inr instr ⌝%I
    | ptstomem _                | [ addr; bs]          => interp_ptstomem addr bs
    | ptstoinstr                | [ addr; instr ]      => interp_ptsto_instr addr instr.

    Ltac destruct_pmp_entries :=
      repeat match goal with
      | x : Val ty_pmpentry |- _ =>
          destruct x; auto
      | x : Val (ty.list ty_pmpentry) |- _ =>
          destruct x; auto
      | x : list (Val ty_pmpentry) |- _ =>
          destruct x; auto
      end.

    Definition lduplicate_inst `{sailRegGS Σ, invGS Σ, mcMemGS Σ, iostateG IOState Σ} :
      forall (p : Predicate) (ts : Env Val (𝑯_Ty p)),
        is_duplicable p = true ->
        (luser_inst p ts) ⊢ (luser_inst p ts ∗ luser_inst p ts).
    Proof.
      destruct p; intros ts Heq; try discriminate Heq;
        clear Heq; cbn in *; env.destroy ts; cbn; destruct_pmp_entries; auto.
    Qed.

  End RiscvPmpIrisPredicates.

  Section RiscVPmpIrisInstanceProofs.
    Context `{sr : sailRegGS Σ} `{igs : invGS Σ} `{mG : mcMemGS Σ}.

    (* Note that the condition on overflow is required: some illegal set-ups are accepted by `pmp_match_addr` as it does not track overflow, and shrinking those might make the output go from match to no match. *)
    Lemma pmp_match_addr_reduced_width (bytes w : Xlenbits) :
      forall paddr rng,
        (bv.unsigned paddr + bv.unsigned bytes < 2 ^ Z.of_nat xlenbits)%Z ->
        bv.zero <ᵘ w ->
        w <=ᵘ bytes ->
        pmp_match_addr paddr bytes rng = PMP_Match ->
        pmp_match_addr paddr w rng = PMP_Match.
    Proof.
      destruct rng as [[lo hi]|]; last by simpl.
      rewrite !pmp_match_addr_match.
      solve_bv.
    Qed.

    Lemma pmp_match_addr_reduced_width_no_match (bytes w : Xlenbits) :
      forall paddr rng,
      (bv.unsigned paddr + bv.unsigned bytes < 2 ^ Z.of_nat xlenbits)%Z ->
      w <=ᵘ bytes ->
      pmp_match_addr paddr bytes rng = PMP_NoMatch ->
      pmp_match_addr paddr w rng = PMP_NoMatch.
    Proof.
      intros paddr [[lo hi]|] Hass Hle; last by simpl.
      rewrite !pmp_match_addr_nomatch.
      intros [|Hcond]; try discriminate. right. intros ? ? Hinv.
      specialize (Hcond _ _ Hinv). inversion Hinv.
      solve_bv.
    Qed.

    Lemma pmp_match_entry_reduced_width (bytes w : Xlenbits) :
      forall paddr cfg p hi lo,
        (bv.unsigned paddr + bv.unsigned bytes < 2 ^ Z.of_nat xlenbits)%Z ->
        bv.zero <ᵘ w ->
        w <=ᵘ bytes ->
        pmp_match_entry paddr bytes p cfg hi lo = PMP_Success ->
        pmp_match_entry paddr w p cfg hi lo = PMP_Success.
    Proof.
      unfold pmp_match_entry.
      intros.
      destruct (pmp_match_addr paddr bytes _) eqn:E; try discriminate.
      apply pmp_match_addr_reduced_width with (w := w) in E; auto.
      now rewrite E.
    Qed.

    Lemma pmp_match_entry_reduced_width_continue (bytes w : Xlenbits) :
      forall paddr cfg p hi lo,
        (bv.unsigned paddr + bv.unsigned bytes < 2 ^ Z.of_nat xlenbits)%Z ->
        w <=ᵘ bytes ->
        pmp_match_entry paddr bytes p cfg hi lo = PMP_Continue ->
        pmp_match_entry paddr w p cfg hi lo = PMP_Continue.
    Proof.
      unfold pmp_match_entry.
      intros.
      destruct (pmp_match_addr paddr bytes _) eqn:E; try discriminate.
      apply pmp_match_addr_reduced_width_no_match with (w := w) in E; auto.
      now rewrite E.
    Qed.

    Lemma pmp_check_aux_access_reduced_width (bytes w : Xlenbits) :
      forall paddr lo entries p acc,
        (bv.unsigned paddr + bv.unsigned bytes < 2 ^ Z.of_nat xlenbits)%Z ->
        bv.zero <ᵘ w ->
        w <=ᵘ bytes ->
        pmp_check_aux paddr bytes lo entries p acc = true ->
        pmp_check_aux paddr w lo entries p acc = true.
    Proof.
      intros paddr lo entries p acc Hrep H0w Hle H.
      generalize dependent lo.
      induction entries as [|[cfg0 hi] es IHentries];
        intros;
        first now simpl in *.
      cbn in *.
      destruct (pmp_match_entry paddr bytes _ _ _ _) eqn:E; last done.
      - apply pmp_match_entry_reduced_width with (w := w) in E; auto.
        now rewrite E.
      - apply pmp_match_entry_reduced_width_continue with (w := w) in E; auto.
        rewrite E.
        unfold pmp_check_aux in IHentries.
        now apply IHentries.
    Qed.

    Lemma pmp_check_access_reduced_width (bytes w : Xlenbits) :
      forall paddr entries p acc,
        (bv.unsigned paddr + bv.unsigned bytes < 2 ^ Z.of_nat xlenbits)%Z ->
        bv.zero <ᵘ w ->
        w <=ᵘ bytes ->
        pmp_check paddr bytes entries p acc = true ->
        pmp_check paddr w entries p acc = true.
    Proof.
      unfold pmp_check; intros;
        apply pmp_check_aux_access_reduced_width with (bytes := bytes); auto.
    Qed.

    Lemma pmp_access_reduced_width (bytes w : Xlenbits) :
      forall paddr pmp p acc ,
        (bv.unsigned paddr + bv.unsigned bytes < 2 ^ Z.of_nat xlenbits)%Z ->
        bv.zero <ᵘ w ->
        w <=ᵘ bytes ->
        Pmp_access paddr bytes pmp p acc ->
        Pmp_access paddr w pmp p acc.
    Proof.
      unfold Pmp_access, Gen_Pmp_access; intros;
        apply pmp_check_aux_access_reduced_width with (bytes := bytes); auto.
    Qed.

    Lemma pmp_match_addr_addr_S_width_pred (bytes : nat) : forall paddr rng res,
        (0 < @bv.unsigned xlenbits (bv.of_nat bytes))%Z ->
        (bv.unsigned paddr + Z.of_nat (S bytes) < 2 ^ Z.of_nat xlenbits)%Z ->
        res = PMP_NoMatch ∨ res = PMP_Match ->
        pmp_match_addr paddr (bv.of_nat (S bytes)) rng = res ->
        pmp_match_addr (paddr + bv.one) (bv.of_nat bytes) rng = res.
    Proof.
      intros paddr rng res Hb Hrep.
      destruct rng as [[lo hi]|]; subst; auto.
      intros [Hres|Hres]; subst.
      - rewrite !pmp_match_addr_nomatch. intros [|Hcond]; first discriminate. right.
        intros ? ? Hspec. specialize (Hcond _ _ Hspec). solve_bv.
      - rewrite !pmp_match_addr_match. solve_bv.
    Qed.

    Lemma pmp_match_entry_addr_S_width_pred_success (bytes : nat) : forall paddr p cfg lo hi,
        (0 < @bv.unsigned xlenbits (bv.of_nat bytes))%Z ->
        (bv.unsigned paddr + Z.of_nat (S bytes) < 2 ^ Z.of_nat xlenbits)%Z ->
        pmp_match_entry paddr (bv.of_nat (S bytes)) p cfg lo hi = PMP_Success ->
        pmp_match_entry (paddr + bv.one) (bv.of_nat bytes) p cfg lo hi = PMP_Success.
    Proof.
      intros paddr p cfg lo hi Hb Hrep.
      unfold pmp_match_entry.
      intros H.
      destruct (pmp_match_addr paddr _ _) eqn:E;
        apply pmp_match_addr_addr_S_width_pred in E;
        auto;
        try now rewrite E.
      discriminate H.
    Qed.

    Lemma pmp_match_entry_addr_S_width_pred_continue (bytes : nat) : forall paddr p cfg lo hi,
        (0 < @bv.unsigned xlenbits (bv.of_nat bytes))%Z ->
        (bv.unsigned paddr + Z.of_nat (S bytes) < 2 ^ Z.of_nat xlenbits)%Z ->
        pmp_match_entry paddr (bv.of_nat (S bytes)) p cfg lo hi = PMP_Continue ->
        pmp_match_entry (paddr + bv.one) (bv.of_nat bytes) p cfg lo hi = PMP_Continue.
    Proof.
      intros paddr p cfg lo hi Hb Hrep.
      unfold pmp_match_entry.
      intros H.
      destruct (pmp_match_addr paddr _ _) eqn:E;
        apply pmp_match_addr_addr_S_width_pred in E;
        auto;
        try now rewrite E.
      discriminate H.
    Qed.

    Lemma pmp_check_aux_addr_S_width_pred (bytes : nat) : forall paddr lo entries p acc,
        (0 < @bv.unsigned xlenbits (bv.of_nat bytes))%Z ->
        (bv.unsigned paddr + Z.of_nat (S bytes) < 2 ^ Z.of_nat xlenbits)%Z ->
        pmp_check_aux paddr (bv.of_nat (S bytes)) lo entries p acc = true ->
        pmp_check_aux (paddr + bv.one) (bv.of_nat bytes) lo entries p acc = true.
    Proof.
      intros paddr lo entries p acc Hb Hrep.
      generalize dependent lo.
      induction entries as [|[cfg0 hi] entries IHentries];
        intros;
        first now simpl in *.
      unfold pmp_check_aux.
      unfold pmp_check_aux in H.
      simpl in *.
      destruct (pmp_match_entry paddr _ _ cfg0 _ _) eqn:Ecfg0; auto.
      apply pmp_match_entry_addr_S_width_pred_success in Ecfg0; auto.
      now rewrite Ecfg0.
      apply pmp_match_entry_addr_S_width_pred_continue in Ecfg0; auto.
      rewrite Ecfg0.
      now apply IHentries.
    Qed.

    Lemma pmp_access_addr_S_width_pred (bytes : nat) : forall paddr lo entries p acc,
        (0 < @bv.unsigned xlenbits (bv.of_nat bytes))%Z ->
        (bv.unsigned paddr + Z.of_nat (S bytes) < 2 ^ Z.of_nat xlenbits)%Z ->
        Gen_Pmp_access paddr (bv.of_nat (S bytes)) lo entries p acc ->
        Gen_Pmp_access (paddr + bv.one) (bv.of_nat bytes) lo entries p acc.
    Proof.
      intros paddr lo pmp p acc Hb Hrep.
      unfold Gen_Pmp_access.
      now apply pmp_check_aux_addr_S_width_pred.
    Qed.

    Lemma gen_pmp_access_shift (bytes shift: nat) paddr lo entries p acc:
        (0 < @bv.unsigned xlenbits (bv.of_nat bytes))%Z ->
        (bv.unsigned paddr + Z.of_nat (bytes + shift) < 2 ^ Z.of_nat xlenbits)%Z ->
        Gen_Pmp_access paddr (bv.of_nat (bytes + shift)) lo entries p acc ->
        Gen_Pmp_access (paddr + bv.of_nat shift) (bv.of_nat bytes) lo entries p acc.
    Proof.
      intros Hzero. generalize dependent paddr.
      induction shift; intros paddr Hrep Hacc.
      - rewrite bv.add_zero_r. rewrite Nat.add_0_r in Hacc. auto.
      - rewrite Nat.add_succ_r in Hacc,Hrep.
        rewrite Nat2Z.inj_succ in Hrep.
        apply pmp_access_addr_S_width_pred in Hacc; try solve_bv.
        apply IHshift in Hacc.
          + rewrite bv.of_nat_S bv.add_assoc. apply Hacc.
          + solve_bv.
    Qed.

    Lemma pmp_access_shift (bytes shift: nat) paddr entries p acc:
        (0 < @bv.unsigned xlenbits (bv.of_nat bytes))%Z ->
        (bv.unsigned paddr + Z.of_nat (bytes + shift) < 2 ^ Z.of_nat xlenbits)%Z ->
        Pmp_access paddr (bv.of_nat (bytes + shift)) entries p acc ->
        Pmp_access (paddr + bv.of_nat shift) (bv.of_nat bytes) entries p acc.
    Proof. apply gen_pmp_access_shift. Qed.

    (* Use `seq` to get rid of conditions on width *)
    (* TODO: intermediate lemma without seq that does shift + restrict? *)
    Lemma pmp_seq_restrict base width k y entries m p:
      (bv.unsigned base + Z.of_nat width < 2 ^ Z.of_nat xlenbits)%Z →
      bv.seq base (Z.of_nat width) !! k = Some y →
      Pmp_access base (bv.of_nat width) entries m p →
      Pmp_access y (bv.of_nat 1) entries m p.
    Proof.
      intros Hrep [-> Hk]%bv.lookup_seq Hacc.
      apply (pmp_access_reduced_width (w := bv.of_nat (1%nat + k))) in Hacc; try solve_bv.
      apply pmp_access_shift in Hacc; [exact Hacc|..]; solve_bv.
    Qed.

    Lemma addr_in_all_addrs (a : Addr): a ∈ all_addrs.
    Proof.
      rewrite all_addrs_eq.
      pose proof (bv.unsigned_bounds a).
      apply bv.elem_of_seq_bounds; rewrite bv.unsigned_zero; lia.
    Qed.

    Local Lemma to_nat_mono (a b : N) : (a < b)%N → N.to_nat a < N.to_nat b.
    Proof. lia. Qed.
    Lemma in_allAddrs_split (addr : Addr) (bytes : nat) :
      (bv.unsigned addr + Z.of_nat bytes < 2 ^ Z.of_nat xlenbits)%Z ->
      exists l1 l2, all_addrs = l1 ++ (bv.seq addr (Z.of_nat bytes)  ++ l2).
    Proof. intros Hrep. rewrite all_addrs_eq.
           pose proof (bv.unsigned_bounds addr).
           apply bv.seq_sub_list; rewrite bv.unsigned_zero; lia.
    Qed.

    Lemma ptstoSthL_app {l1 l2} : (ptstoSthL (l1 ++ l2) ⊣⊢ ptstoSthL l1 ∗ ptstoSthL l2)%I.
    Proof. eapply big_sepL_app. Qed.

    Lemma ptstomem_bv_app :
      forall {n} (a : Addr) (b : bv byte) (bs : bv (n * byte)),
        @interp_ptstomem _ _ (S n)%nat a (bv.app b bs)
        ⊣⊢
        (interp_ptsto a b ∗ interp_ptstomem (bv.one + a) bs).
    Proof. intros; unfold interp_ptstomem; now rewrite bv.appView_app. Qed.

    Lemma pmp_entries_ptsto : ∀ (entries : list PmpEntryCfg),
        interp_pmp_entries entries ⊣⊢
          ∃ (cfg0 : Pmpcfg_ent) (addr0 : Addr) (cfg1 : Pmpcfg_ent) (addr1 : Addr),
            ⌜entries = [(cfg0, addr0); (cfg1, addr1)]⌝ ∗
            reg_pointsTo pmp0cfg cfg0 ∗ reg_pointsTo pmpaddr0 addr0 ∗
            reg_pointsTo pmp1cfg cfg1 ∗ reg_pointsTo pmpaddr1 addr1.
    Proof.
      intros entries; iSplit; iIntros  "H".
      - unfold interp_pmp_entries.
        destruct entries as [|[cfg0 addr0] [|[cfg1 addr1] [|]]] eqn:?; try done.
        repeat iExists _.
        now iFrame.
     -  iDestruct "H" as "(% & % & % & % & -> & ? & ? & ? & ?)"; iFrame.
    Qed.

    Lemma interp_ptstomem_exists_intro (bytes : nat) :
      ⊢ ∀ (paddr : Addr) (w : bv (bytes * byte)),
          interp_ptstomem paddr w -∗
          ∃ (w : bv (bytes * byte)), interp_ptstomem paddr w.
    Proof. auto. Qed.

    Lemma interp_ptstomem_big_sepS (bytes : nat) (paddr : Addr):
      (∃ (w : bv (bytes * byte)), interp_ptstomem paddr w) ⊣⊢
        ptstoSthL (bv.seq paddr (Z.of_nat bytes)).
    Proof.
      generalize dependent paddr.
      iInduction bytes as [|bytes] "IHbytes"; iIntros (paddr).
      - unfold ptstoSthL. unshelve auto. exact bv.zero.
      - rewrite Nat2Z.inj_succ bv.seq_succ; last lia.
        rewrite (app_comm_cons []) ptstoSthL_app.
        iDestruct ("IHbytes" $! (bv.one + paddr)) as "[IHL IHR]".
        iSplit.
        *  iIntros "[%w H]".
           destruct (bv.appView byte (bytes * byte) w) as [b bs].
           rewrite ptstomem_bv_app.
           iDestruct "H" as "[Hb Hbs]".
           iSplitL "Hb".
           + cbn. iSplit; [by iExists _ | auto].
           + iApply "IHL"; by iExists _.
        * iIntros "[[[%b Hhd] _] Htl]".
          iDestruct ("IHR" with "Htl") as "[%btl Htl]".
          iExists (bv.app b btl).
          rewrite ptstomem_bv_app. iFrame.
    Qed.

    Lemma interp_addr_access_app base width width':
      interp_addr_access liveAddrs mmioAddrs base (width + width') ⊣⊢
      interp_addr_access liveAddrs mmioAddrs base width ∗ interp_addr_access liveAddrs mmioAddrs (base + bv.of_nat width) width'.
    Proof.
      unfold interp_addr_access.
      rewrite Nat2Z.inj_add bv.seq_add ?bv.of_Z_nat ?big_sepL_app //; lia.
    Qed.

    Lemma interp_addr_access_cons base width:
      interp_addr_access liveAddrs mmioAddrs base (S width) ⊣⊢
      interp_addr_access_byte liveAddrs mmioAddrs base ∗ interp_addr_access liveAddrs mmioAddrs (base + bv.of_nat 1) width.
    Proof. rewrite <-Nat.add_1_l.
           rewrite interp_addr_access_app.
           unfold interp_addr_access, interp_addr_access_byte.
           by rewrite bv.seq_one big_sepL_singleton.
    Qed.

    Lemma interp_addr_access_single base:
      interp_addr_access liveAddrs mmioAddrs base 1 ⊣⊢
      interp_addr_access_byte liveAddrs mmioAddrs base.
    Proof. rewrite interp_addr_access_cons.
           iSplit; iIntros "H"; [iDestruct "H" as "[H _]"|]; iFrame.
           unfold interp_addr_access. now cbn.
    Qed.

    (* Induction does not work here due to shape of `interp_pmp_addr_access_without`*)
    Lemma interp_pmp_addr_inj_extr {entries m p} base width :
      (bv.unsigned base + Z.of_nat width < 2 ^ Z.of_nat xlenbits)%Z →
      Pmp_access base (bv.of_nat width) entries m p →
      (interp_pmp_addr_access liveAddrs mmioAddrs entries m ⊣⊢
      (interp_addr_access liveAddrs mmioAddrs base width ∗ interp_pmp_addr_access_without liveAddrs mmioAddrs base width entries m))%I.
    Proof.
      intros Hrep Hpmp.
      (* Discharge easy direction *)
      iSplit ; last (iIntros "[H Hcont]"; by iApply "Hcont").
      unfold interp_pmp_addr_access_without, interp_pmp_addr_access.
      (* Hard direction: create `interp_addr_access` from scratch *)
      unfold interp_pmp_addr_access.
      pose proof (in_allAddrs_split base width Hrep) as [l1 [l2 Hall]]. rewrite Hall.
      rewrite !big_sepL_app.
      iIntros "(Hlow & Hia & Hhigh)".
      iSplitL "Hia".
      - iApply (big_sepL_mono with "Hia"). iIntros (? ? ?) "Hyp".
        iApply "Hyp". iPureIntro.
        eexists; eapply pmp_seq_restrict; eauto.
      - iIntros "Hia". iFrame.
        iDestruct (big_sepL_mono with "Hia") as "Hia"; last iFrame.
        now iIntros.
      Qed.

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

    (* Bidirectional version of the Iris lemma *)
    Lemma big_sepL_mono_iff {PROP : bi} {A : Type} (Φ Ψ : nat → A → PROP) (l : list A) :
    (∀ k y, l !! k = Some y → Φ k y ⊣⊢ Ψ k y) →
    ([∗ list] k ↦ y ∈ l, Φ k y) ⊣⊢ [∗ list] k ↦ y ∈ l, Ψ k y.
    Proof.
      intros Hiff.
      iSplit; iApply big_sepL_mono; iIntros; iApply Hiff; auto.
    Qed.

    (* Use knowledge of RAM to extract byte *)
    Lemma interp_addr_access_byte_extr  base :
      base ∈ liveAddrs ->
      (interp_addr_access_byte liveAddrs mmioAddrs base ⊢
      ptstoSth base).
    Proof.
      intros (* Hpmp *) Hlive.
      unfold interp_addr_access_byte, ptstoSth, interp_ptsto.
      repeat case_decide; auto; iIntros; by exfalso.
    Qed.

    (* Inserting a byte is always possible *)
    Lemma interp_addr_access_byte_inj base :
       ptstoSth base -∗ interp_addr_access_byte liveAddrs mmioAddrs base.
    Proof.
      unfold interp_addr_access_byte, ptstoSth, interp_ptsto.
      iIntros "HFalse". iDestruct "HFalse" as (?) "[Hmapsto %HFalse]".
      case_decide.
      - by rewrite withinMMIO_one in HFalse.
      - case_decide; auto.
    Qed.

    (* Use knowledge of RAM to extract range *)
    Lemma interp_addr_access_extr base width :
      (Z.of_N minAddr ≤ bv.unsigned base)%Z →
      (bv.unsigned base + Z.of_nat width ≤ Z.of_N maxAddr)%Z →
      (bv.unsigned base + Z.of_nat width < 2 ^ Z.of_nat xlenbits)%Z →
      interp_addr_access liveAddrs mmioAddrs base width ⊢
      (∃ (w : bv (width * byte)), interp_ptstomem base w).
    Proof.
      intros HminOK HmaxOK Hrep.
      rewrite interp_ptstomem_big_sepS.
      unfold interp_addr_access, ptstoSthL.
      iApply big_sepL_mono.
      iIntros (? y Hseq) "//".
      iApply interp_addr_access_byte_extr.
      eapply bv.seq_subseteq, list_elem_of_lookup_2, Hseq; unfold maxAddr in *;
        change (bv.unsigned (bv.of_N minAddr)) with (Z.of_N minAddr); lia.
    Qed.

    (* Inserting a range is always possible *)
    Lemma interp_addr_access_inj base width:
      (∃ (w : bv (width * byte)), interp_ptstomem base w) ⊢
      interp_addr_access liveAddrs mmioAddrs base width.
    Proof.
      iIntros "Hint".
      rewrite interp_ptstomem_big_sepS.
      unfold interp_addr_access, ptstoSthL.
      iApply big_sepL_mono; last auto.
      iIntros (? y Hseq) "/=".
      iApply interp_addr_access_byte_inj.
    Qed.

    (* TODO: This lemma is not a special case of the above, because of strange semantics of `Pmp_access`*)
    Lemma interp_pmp_addr_access_without_0 {entries m} base :
      interp_pmp_addr_access liveAddrs mmioAddrs entries m ⊣⊢ interp_pmp_addr_access_without liveAddrs mmioAddrs base 0 entries m.
    Proof. unfold interp_pmp_addr_access_without, interp_addr_access.
           iSplit; iIntros "H".
           - now iIntros "_".
           - now iApply "H".
    Qed.

  End RiscVPmpIrisInstanceProofs.


  Include IrisSignatureRules RiscvPmpGlobalState RiscvPmpSignature RiscvPmpProgram
    RiscvPmpSemantics RiscvPmpProgramLogic RiscvPmpIrisPrelims RiscvPmpIrisBase.
  Include IrisAdequacy RiscvPmpGlobalState RiscvPmpSignature RiscvPmpProgram
    RiscvPmpSemantics RiscvPmpProgramLogic RiscvPmpIrisPrelims RiscvPmpIrisBase RiscvPmpIrisAdeqParameters.

  Lemma gprs_equiv `{sailGS Σ, iostateG IOState Σ} : ∀ {Σ} (ι : Valuation Σ) (exclude : gset (Reg ty_xlenbits)),
      interp_gprs exclude ⊣⊢
        asn.interpret (asn_regs_ptsto exclude) ι.
  Proof.
    iIntros (? ι exclude).
    unfold interp_gprs, asn_regs_ptsto, asn_and_regs.
    remember (elements (GPRS ∖ exclude)) as l eqn:El.
    assert (Hdup: NoDup l) by (subst; apply NoDup_elements).
    assert (Hl: list_to_set l = GPRS ∖ exclude) by (subst; apply list_to_set_elements_L).
    rewrite <- Hl.
    rewrite big_sepS_list_to_set; last auto.
    clear El Hdup Hl.
    iInduction l as [|gpr gprs] "IH";
      iSplit; iIntros "H"; simpl; auto.
    - iDestruct "H" as "($ & H)".
      now iApply ("IH" with "H").
    - iDestruct "H" as "($ & H)".
      now iApply ("IH" with "H").
  Qed.

End RiscvPmpIrisInstance.
