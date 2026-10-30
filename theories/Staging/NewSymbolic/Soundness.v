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

From Katamaran Require Import
     Prelude
     Signature
     Program
     Sep.Hoare
     Symbolic.Worlds
     Staging.NewShallow.Executor
     Staging.NewSymbolic.Executor.

Import ctx.notations.
Import env.notations.

Set Implicit Arguments.

(* Soundness of the new symbolic executor with respect to the new shallow
   executor, instantiated with the predicate transformer monad over an
   arbitrary separation logic [L]. *)
Module Type NewSymbolicSoundness
  (Import B    : Base)
  (Import SIG  : Signature B)
  (Import PROG : Program B)
  (Import PLOG : ProgramLogic B SIG PROG)
  (SHAL : NewShallowExecOn B SIG PROG PLOG)
  (SYMB : NewSymbolicExecOn B SIG PROG PLOG).

  Import ModalNotations.
  Import SymProp.
  Import logicalrelation logicalrelation.notations.
  Import LogicalSoundness.
  Import proofmode.
  Import iris.proofmode.environments.
  Import iris.proofmode.proofmode.
  Import RSolve.

  #[local] Arguments SHAL.CPureSpec.purespecm : simpl never.
  #[local] Arguments SHAL.CPureSpec.heapspecm : simpl never.
  #[local] Arguments SYMB.spurespecm_sheapspec : simpl never.
  #[local] Arguments SYMB.sheapspecm_sheapspec : simpl never.
  #[local] Arguments SYMB.SStackT.spurespecm_sstackt : simpl never.
  #[local] Arguments SYMB.SStackT.sheapspecm_sstackt : simpl never.
  #[local] Arguments SYMB.SStackT.sstackm_sstackt : simpl never.

  Section WithBI.

    Context {L : bi} {biA : BiAffine L} {PI : PredicateDef L}.

    Abbreviation CM := (SHAL.CPureSpec.CPureSpec (L := L)).

    (* Relates a symbolic proposition, which still expects a symbolic heap, to
       an assertion in [L]: whenever the symbolic proposition is safe for a
       heap, the interpretation of that heap entails the assertion. *)
    Definition RHeapProp : Rel (SHeap -> 𝕊)%modal L :=
      MkRel (fun P w sP => ℛ⟦RHeap -> ℙ⟧ (fun h => interpret_scheap h ⊢ P) sP).

    Definition RM [SA CA] (RA : Rel SA CA) : Rel (SHeapSpec SA) (CM CA) :=
      □ᵣ(RA -> RHeapProp) -> RHeapProp.

    (* The executor runs in the stack transformer over the heap monad. The
       shallow executor has no call stack, so we relate for every stack. *)
    Abbreviation SM := (SYMB.SStackT.SStackT SHeapSpec).

    Definition RS [SA CA] (RA : Rel SA CA) : Rel (SM SA) (CM CA) :=
      MkRel (fun cm w sm => ∀ stk : List SYMB.Frame w, ℛ⟦RM RA⟧ cm (sm stk))%I.

    (* Every refinement of an operation of the old shallow heap monad lifts to
       the new relation, given that the old operation implies the new one. *)
    Lemma refine_bridge `{RA : Rel SA CA} {w} (cm : CHeapSpec CA) (cmL : CM CA)
      (sm : SHeapSpec SA w) :
      (forall Φ h, cm (fun a h' => interpret_scheap h' ⊢ Φ a) h ->
                   interpret_scheap h ⊢ cmL Φ) ->
      ℛ⟦RHeapSpec RA⟧ cm sm ⊢ ℛ⟦RM RA⟧ cmL sm.
    Proof.
      iIntros (Hb) "Hm %Φ %sΦ HΦ %h %sh Hh Hs".
      iPoseProof ("Hm" $! (fun a h' => interpret_scheap h' ⊢ Φ a) sΦ with "HΦ Hh Hs")
        as "%Hc".
      iPureIntro. now apply Hb.
    Qed.

    Ltac unfold_instances :=
      unfold SHAL.CPureSpec.purespecm, SHAL.CPureSpec.heapspecm,
        SYMB.spurespecm_sheapspec, SYMB.sheapspecm_sheapspec;
      cbn [SHAL.CPureSpecM.pure SHAL.CPureSpecM.bind SHAL.CPureSpecM.error
           SHAL.CPureSpecM.block SHAL.CPureSpecM.angelic SHAL.CPureSpecM.demonic
           SHAL.CPureSpecM.angelic_binary SHAL.CPureSpecM.demonic_binary
           SHAL.CPureSpecM.assert_formula SHAL.CPureSpecM.assume_formula
           SHAL.CHeapSpecM.produce_chunk SHAL.CHeapSpecM.consume_chunk
           SYMB.SPureSpecM.pure SYMB.SPureSpecM.bind SYMB.SPureSpecM.error
           SYMB.SPureSpecM.block SYMB.SPureSpecM.angelic SYMB.SPureSpecM.demonic
           SYMB.SPureSpecM.angelic_binary SYMB.SPureSpecM.demonic_binary
           SYMB.SPureSpecM.assert_formula SYMB.SPureSpecM.assume_formula
           SYMB.SPureSpecM.angelic_pattern_match SYMB.SPureSpecM.demonic_pattern_match
           SYMB.SPureSpecM.debug
           SYMB.SHeapSpecM.produce_chunk SYMB.SHeapSpecM.consume_chunk
           SYMB.SHeapSpecM.consume_chunk_angelic SYMB.SHeapSpecM.read_register
           SYMB.SHeapSpecM.write_register].

    Section Basics.

      Lemma refine_pure `{RA : Rel SA CA} {w} :
        ⊢ ℛ⟦RA -> RM RA⟧
          (SHAL.CPureSpecM.pure (M := CM))
          (SYMB.SPureSpecM.pure (M := SHeapSpec) (w := w)).
      Proof.
        unfold_instances. iIntros (v sv) "rv %Φ %sΦ rΦ".
        iApply (refine_T with "rΦ rv").
      Qed.

      Lemma refine_bind `{RA : Rel SA CA, RB : Rel SB CB} {w} :
        ⊢ ℛ⟦RM RA -> □ᵣ(RA -> RM RB) -> RM RB⟧
          (SHAL.CPureSpecM.bind (M := CM))
          (SYMB.SPureSpecM.bind (M := SHeapSpec) (w := w)).
      Proof.
        unfold_instances.
        iIntros (cm sm) "rm %cf %sf rf %Φ %sΦ rΦ".
        unfold SHeapSpec.bind, SHAL.CPureSpec.bind. iApply "rm".
        iIntros (w1 θ1) "!> %ca %sa ra".
        iApply ("rf" with "ra").
        now iApply (refine_four with "rΦ").
      Qed.

      Lemma refine_error `{RA : Rel SA CA} (cm : CM CA) {w : World} (msg : SYMB.SMsg w) :
        ⊢ ℛ⟦RM RA⟧ cm (SYMB.SPureSpecM.error (M := SHeapSpec) msg).
      Proof.
        unfold_instances. iIntros (Φ sΦ) "_ %h %sh _ HS".
        now cbn.
      Qed.

      Lemma refine_block `{RA : Rel SA CA} {w} :
        ⊢ ℛ⟦RM RA⟧
          (SHAL.CPureSpecM.block (M := CM))
          (SYMB.SPureSpecM.block (M := SHeapSpec) (w := w)).
      Proof.
        unfold_instances. iIntros (Φ sΦ) "_ %h %sh _ _".
        iPureIntro. apply bi.True_intro.
      Qed.

      Lemma refine_angelic_binary `{RA : Rel SA CA} {w} :
        ⊢ ℛ⟦RM RA -> RM RA -> RM RA⟧
          (SHAL.CPureSpecM.angelic_binary (M := CM))
          (SYMB.SPureSpecM.angelic_binary (M := SHeapSpec) (w := w)).
      Proof.
        unfold_instances.
        iIntros (cm1 sm1) "rm1 %cm2 %sm2 rm2 %Φ %sΦ #rΦ %h %sh #rh [HS|HS]";
          cbn - [RSat].
        - iPoseProof ("rm1" with "rΦ rh HS") as "%H".
          iPureIntro. rewrite H. apply bi.or_intro_l.
        - iPoseProof ("rm2" with "rΦ rh HS") as "%H".
          iPureIntro. rewrite H. apply bi.or_intro_r.
      Qed.

      Lemma refine_demonic_binary `{RA : Rel SA CA} {w} :
        ⊢ ℛ⟦RM RA -> RM RA -> RM RA⟧
          (SHAL.CPureSpecM.demonic_binary (M := CM))
          (SYMB.SPureSpecM.demonic_binary (M := SHeapSpec) (w := w)).
      Proof.
        unfold_instances.
        iIntros (cm1 sm1) "rm1 %cm2 %sm2 rm2 %Φ %sΦ #rΦ %h %sh #rh [HS1 HS2]".
        iPoseProof ("rm1" with "rΦ rh HS1") as "%H1".
        iPoseProof ("rm2" with "rΦ rh HS2") as "%H2".
        iPureIntro. now apply bi.and_intro.
      Qed.

      Lemma refine_debug `{RA : Rel SA CA} {w : World} (msg : SYMB.SMsg w) :
        ⊢ ℛ⟦RM RA -> RM RA⟧ (fun m => m)
          (SYMB.SPureSpecM.debug (M := SHeapSpec) msg).
      Proof.
        unfold_instances.
        iIntros (cm sm) "rm %Φ %sΦ rΦ %h %sh rh HS".
        iDestruct (elim_debugPred with "HS") as "HS".
        iApply ("rm" with "rΦ rh HS").
      Qed.

    End Basics.

    Section Primitives.

      Lemma refine_angelic x σ {w} :
        ⊢ ℛ⟦RM (RVal σ)⟧
          (SHAL.CPureSpecM.angelic (M := CM) σ)
          (SYMB.SPureSpecM.angelic (M := SHeapSpec) x (w := w) σ).
      Proof.
        unfold_instances. iApply refine_bridge; [|iApply HeapSpec.refine_angelic].
        intros Φ h [v Hv]. cbn. rewrite Hv. now apply bi.exist_intro' with v.
      Qed.

      Lemma refine_demonic x σ {w} :
        ⊢ ℛ⟦RM (RVal σ)⟧
          (SHAL.CPureSpecM.demonic (M := CM) σ)
          (SYMB.SPureSpecM.demonic (M := SHeapSpec) x (w := w) σ).
      Proof.
        unfold_instances. iApply refine_bridge; [|iApply HeapSpec.refine_demonic].
        intros Φ h Hv. cbn. apply bi.forall_intro. intros v. apply Hv.
      Qed.

      Lemma refine_assert_formula {w : World} (msg : SYMB.SMsg w) :
        ⊢ ℛ⟦RFormula -> RM RUnit⟧
          (SHAL.CPureSpecM.assert_formula (M := CM))
          (SYMB.SPureSpecM.assert_formula (M := SHeapSpec) msg).
      Proof.
        unfold_instances. iIntros (F sF) "rF".
        iApply refine_bridge; [|iApply (HeapSpec.refine_assert_formula with "rF")].
        intros Φ h [HF HΦ]. cbn. rewrite HΦ.
        apply bi.and_intro; [now apply bi.pure_intro|easy].
      Qed.

      Lemma refine_assume_formula {w} :
        ⊢ ℛ⟦RFormula -> RM RUnit⟧
          (SHAL.CPureSpecM.assume_formula (M := CM))
          (SYMB.SPureSpecM.assume_formula (M := SHeapSpec) (w := w)).
      Proof.
        unfold_instances. iIntros (F sF) "rF".
        iApply refine_bridge; [|iApply (HeapSpec.refine_assume_formula with "rF")].
        intros Φ h HΦ. cbn. apply bi.impl_intro_l, bi.pure_elim_l. auto.
      Qed.

      Lemma refine_produce_chunk {w} :
        ⊢ ℛ⟦RChunk -> RM RUnit⟧
          (SHAL.CHeapSpecM.produce_chunk (M := CM))
          (SYMB.SHeapSpecM.produce_chunk (M := SHeapSpec) (w := w)).
      Proof.
        unfold_instances. iIntros (c sc) "rc".
        iApply refine_bridge; [|iApply (HeapSpec.refine_produce_chunk with "rc")].
        intros Φ h HΦ. unfold CHeapSpec.produce_chunk in HΦ.
        apply (CPureSpec.wp_produce_chunk (L := L)) in HΦ. cbn. rewrite HΦ.
        apply bi.wand_mono'; [easy|].
        apply bi.exist_elim. intros h'. now apply bi.pure_elim_r.
      Qed.

      Lemma refine_consume_chunk {w} :
        ⊢ ℛ⟦RChunk -> RM RUnit⟧
          (SHAL.CHeapSpecM.consume_chunk (M := CM))
          (SYMB.SHeapSpecM.consume_chunk (M := SHeapSpec) (w := w)).
      Proof.
        unfold_instances. iIntros (c sc) "rc".
        iApply refine_bridge; [|iApply (HeapSpec.refine_consume_chunk with "rc")].
        intros Φ h HΦ. unfold CHeapSpec.consume_chunk in HΦ.
        apply (CPureSpec.wp_consume_chunk (L := L)) in HΦ. cbn. rewrite HΦ.
        apply bi.sep_mono'; [easy|].
        apply bi.exist_elim. intros h'. now apply bi.pure_elim_r.
      Qed.

      Lemma refine_consume_chunk_angelic {w} :
        ⊢ ℛ⟦RChunk -> RM RUnit⟧
          (SHAL.CHeapSpecM.consume_chunk (M := CM))
          (SYMB.SHeapSpecM.consume_chunk_angelic (M := SHeapSpec) (w := w)).
      Proof.
        unfold_instances. iIntros (c sc) "rc".
        iApply refine_bridge; [|iApply (HeapSpec.refine_consume_chunk_angelic with "rc")].
        intros Φ h HΦ. unfold CHeapSpec.consume_chunk in HΦ.
        apply (CPureSpec.wp_consume_chunk (L := L)) in HΦ. cbn. rewrite HΦ.
        apply bi.sep_mono'; [easy|].
        apply bi.exist_elim. intros h'. now apply bi.pure_elim_r.
      Qed.

      Lemma refine_read_register {τ} (reg : 𝑹𝑬𝑮 τ) {w} :
        ⊢ ℛ⟦RM (RVal τ)⟧
          (SHAL.CHeapSpecM.read_register (M := CM) reg)
          (SYMB.SHeapSpecM.read_register (M := SHeapSpec) reg (w := w)).
      Proof.
        unfold SHAL.CHeapSpecM.read_register. unfold_instances.
        iApply refine_bridge; [|iApply HeapSpec.refine_read_register].
        intros Φ h HΦ. unfold CHeapSpec.read_register in HΦ.
        apply (CPureSpec.wp_read_register (L := L)) in HΦ.
        rewrite HΦ. cbn. apply bi.exist_mono'. intros v.
        apply bi.sep_mono'; [easy|]. apply bi.wand_mono'; [easy|].
        apply bi.exist_elim. intros h'. now apply bi.pure_elim_r.
      Qed.

      Lemma refine_write_register {τ} (reg : 𝑹𝑬𝑮 τ) {w} :
        ⊢ ℛ⟦RVal τ -> RM (RVal τ)⟧
          (SHAL.CHeapSpecM.write_register (M := CM) reg)
          (SYMB.SHeapSpecM.write_register (M := SHeapSpec) reg (w := w)).
      Proof.
        unfold SHAL.CHeapSpecM.write_register. unfold_instances.
        iIntros (v sv) "rv".
        iApply refine_bridge; [|iApply (HeapSpec.refine_write_register with "rv")].
        intros Φ h HΦ. unfold CHeapSpec.write_register in HΦ.
        apply (CPureSpec.wp_write_register (L := L)) in HΦ.
        rewrite HΦ. cbn. apply bi.exist_mono'. intros vold.
        apply bi.sep_mono'; [easy|]. apply bi.wand_mono'; [easy|].
        apply bi.exist_elim. intros h'. now apply bi.pure_elim_r.
      Qed.

      Lemma refine_demonic_pattern_match {N : Set} (n : N -> LVar) {σ}
        (pat : Pattern (N:=N) σ) {w} :
        ⊢ ℛ⟦RVal σ -> RM (RMatchResult pat)⟧
          (fun v => SHAL.CPureSpecM.pure (M := CM) (pattern_match_val pat v))
          (SYMB.SPureSpecM.demonic_pattern_match (M := SHeapSpec) n pat (w := w)).
      Proof.
        unfold_instances. iIntros (v sv) "rv".
        iApply refine_bridge;
          [|iApply HeapSpec.refine_lift_purespec;
            iApply (PureSpec.refine_demonic_pattern_match with "rv")].
        intros Φ h HΦ. unfold CHeapSpec.lift_purespec in HΦ.
        now rewrite CPureSpec.wp_demonic_pattern_match in HΦ.
      Qed.

      Lemma refine_angelic_pattern_match {N : Set} (n : N -> LVar) {σ}
        (pat : Pattern (N:=N) σ) {w : World} (msg : SYMB.SMsg w) :
        ⊢ ℛ⟦RVal σ -> RM (RMatchResult pat)⟧
          (fun v => SHAL.CPureSpecM.pure (M := CM) (pattern_match_val pat v))
          (SYMB.SPureSpecM.angelic_pattern_match (M := SHeapSpec) n pat msg).
      Proof.
        unfold_instances. iIntros (v sv) "rv %Φ %sΦ rΦ %h %sh rh HS".
        (* The message depends on the symbolic heap, so fix it first. *)
        iPoseProof (HeapSpec.refine_lift_purespec $! _ _ with "[rv]") as "Hm";
          [iApply (PureSpec.refine_angelic_pattern_match n pat
                     $! (SYMB.debug_info (wco w) sh msg) with "rv")|].
        iPoseProof ("Hm" $! (fun a h' => interpret_scheap h' ⊢ Φ a) sΦ with "rΦ rh HS")
          as "%Hc".
        iPureIntro. unfold CHeapSpec.lift_purespec in Hc.
        now rewrite CPureSpec.wp_angelic_pattern_match in Hc.
      Qed.

    End Primitives.

    Section CompatInstances.

      #[export] Instance refine_compat_pure `{RA : Rel SA CA} {w} :
        RefineCompat (RA -> RM RA) (SHAL.CPureSpecM.pure (M := CM)) w
          (SYMB.SPureSpecM.pure (M := SHeapSpec) (w := w)) _ :=
        MkRefineCompat refine_pure.

      #[export] Instance refine_compat_bind `{RA : Rel SA CA, RB : Rel SB CB} {w} :
        RefineCompat (RM RA -> □ᵣ(RA -> RM RB) -> RM RB)
          (SHAL.CPureSpecM.bind (M := CM)) w
          (SYMB.SPureSpecM.bind (M := SHeapSpec) (w := w)) _ :=
        MkRefineCompat refine_bind.

      #[export] Instance refine_compat_error `{RA : Rel SA CA} {cm : CM CA} {w : World}
        {msg : SYMB.SMsg w} :
        RefineCompat (RM RA) cm w (SYMB.SPureSpecM.error (M := SHeapSpec) msg) emp :=
        MkRefineCompat (refine_error cm msg).

      #[export] Instance refine_compat_block `{RA : Rel SA CA} {w} :
        RefineCompat (RM RA) (SHAL.CPureSpecM.block (M := CM)) w
          (SYMB.SPureSpecM.block (M := SHeapSpec) (w := w)) emp :=
        MkRefineCompat refine_block.

      #[export] Instance refine_compat_angelic_binary `{RA : Rel SA CA} {w} :
        RefineCompat (RM RA -> RM RA -> RM RA)
          (SHAL.CPureSpecM.angelic_binary (M := CM)) w
          (SYMB.SPureSpecM.angelic_binary (M := SHeapSpec) (w := w)) _ :=
        MkRefineCompat refine_angelic_binary.

      #[export] Instance refine_compat_demonic_binary `{RA : Rel SA CA} {w} :
        RefineCompat (RM RA -> RM RA -> RM RA)
          (SHAL.CPureSpecM.demonic_binary (M := CM)) w
          (SYMB.SPureSpecM.demonic_binary (M := SHeapSpec) (w := w)) _ :=
        MkRefineCompat refine_demonic_binary.

      #[export] Program Instance refine_compat_debug `{RA : Rel SA CA} {cm : CM CA}
        {w : World} {msg : SYMB.SMsg w} {sm} :
        RefineCompat (RM RA) cm w (SYMB.SPureSpecM.debug (M := SHeapSpec) msg sm)
          (ℛ⟦RM RA⟧ cm sm) :=
        MkRefineCompat _.
      Next Obligation.
        iIntros (SA CA RA cm w msg sm) "rm".
        iApply (refine_debug msg with "rm").
      Qed.

      #[export] Instance refine_compat_angelic x σ {w} :
        RefineCompat (RM (RVal σ)) (SHAL.CPureSpecM.angelic (M := CM) σ) w
          (SYMB.SPureSpecM.angelic (M := SHeapSpec) x (w := w) σ) emp :=
        MkRefineCompat (refine_angelic x σ).

      #[export] Instance refine_compat_demonic x σ {w} :
        RefineCompat (RM (RVal σ)) (SHAL.CPureSpecM.demonic (M := CM) σ) w
          (SYMB.SPureSpecM.demonic (M := SHeapSpec) x (w := w) σ) emp :=
        MkRefineCompat (refine_demonic x σ).

      #[export] Instance refine_compat_assert_formula {w : World} {msg : SYMB.SMsg w} :
        RefineCompat (RFormula -> RM RUnit) (SHAL.CPureSpecM.assert_formula (M := CM)) w
          (SYMB.SPureSpecM.assert_formula (M := SHeapSpec) msg) _ :=
        MkRefineCompat (refine_assert_formula msg).

      #[export] Instance refine_compat_assume_formula {w} :
        RefineCompat (RFormula -> RM RUnit) (SHAL.CPureSpecM.assume_formula (M := CM)) w
          (SYMB.SPureSpecM.assume_formula (M := SHeapSpec) (w := w)) _ :=
        MkRefineCompat refine_assume_formula.

      #[export] Instance refine_compat_produce_chunk {w} :
        RefineCompat (RChunk -> RM RUnit) (SHAL.CHeapSpecM.produce_chunk (M := CM)) w
          (SYMB.SHeapSpecM.produce_chunk (M := SHeapSpec) (w := w)) _ :=
        MkRefineCompat refine_produce_chunk.

      #[export] Instance refine_compat_consume_chunk {w} :
        RefineCompat (RChunk -> RM RUnit) (SHAL.CHeapSpecM.consume_chunk (M := CM)) w
          (SYMB.SHeapSpecM.consume_chunk (M := SHeapSpec) (w := w)) _ :=
        MkRefineCompat refine_consume_chunk.

      #[export] Instance refine_compat_consume_chunk_angelic {w} :
        RefineCompat (RChunk -> RM RUnit) (SHAL.CHeapSpecM.consume_chunk (M := CM)) w
          (SYMB.SHeapSpecM.consume_chunk_angelic (M := SHeapSpec) (w := w)) _ :=
        MkRefineCompat refine_consume_chunk_angelic.

      #[export] Instance refine_compat_read_register {τ} (reg : 𝑹𝑬𝑮 τ) {w} :
        RefineCompat (RM (RVal τ)) (SHAL.CHeapSpecM.read_register (M := CM) reg) w
          (SYMB.SHeapSpecM.read_register (M := SHeapSpec) reg (w := w)) _ :=
        MkRefineCompat (refine_read_register reg).

      #[export] Instance refine_compat_write_register {τ} (reg : 𝑹𝑬𝑮 τ) {w} :
        RefineCompat (RVal τ -> RM (RVal τ)) (SHAL.CHeapSpecM.write_register (M := CM) reg) w
          (SYMB.SHeapSpecM.write_register (M := SHeapSpec) reg (w := w)) _ :=
        MkRefineCompat (refine_write_register reg).

      (* The shallow executor dispatches on the value directly, whereas the
         symbolic executor branches with a monadic operation. *)
      Lemma pattern_match_as_bind {N : Set} {A σ} (pat : Pattern (N:=N) σ) (v : Val σ)
        (k : forall pc, NamedEnv Val (PatternCaseCtx pc) -> CM A) :
        SHAL.CPureSpecM.pattern_match (M := CM) v pat k =
          SHAL.CPureSpecM.bind (M := CM)
            (SHAL.CPureSpecM.pure (M := CM) (pattern_match_val pat v))
            (fun '(existT pc δpc) => k pc δpc).
      Proof. reflexivity. Qed.

      Lemma refine_pattern_match_demonic `{RA : Rel SA CA} {N : Set} (n : N -> LVar)
        {σ} (pat : Pattern (N:=N) σ) {w : World} {v : Val σ} {sv : STerm σ w} {k} {sk} :
        ℛ⟦RVal σ⟧ v sv ∗
        ℛ⟦□ᵣ(RMatchResult pat -> RM RA)⟧ (fun '(existT pc δpc) => k pc δpc) sk ⊢
        ℛ⟦RM RA⟧ (SHAL.CPureSpecM.pattern_match (M := CM) v pat k)
          (SYMB.SPureSpecM.bind (M := SHeapSpec)
             (SYMB.SPureSpecM.demonic_pattern_match (M := SHeapSpec) n pat sv) sk).
      Proof.
        iIntros "[rv rk]". rewrite pattern_match_as_bind.
        iApply (refine_bind (RA := RMatchResult pat) with "[rv] rk").
        now iApply (refine_demonic_pattern_match with "rv").
      Qed.

      #[export] Instance refine_compat_demonic_pattern_match
        `{RA : Rel SA CA} {N : Set} (n : N -> LVar) {σ} (pat : Pattern (N:=N) σ)
        {w : World} {v : Val σ} {sv : STerm σ w} {k} {sk} :
        RefineCompat (RM RA) (SHAL.CPureSpecM.pattern_match (M := CM) v pat k) w
          (SYMB.SPureSpecM.bind (M := SHeapSpec)
             (SYMB.SPureSpecM.demonic_pattern_match (M := SHeapSpec) n pat sv) sk)
          _ :=
        MkRefineCompat (refine_pattern_match_demonic n (pat := pat)).

      Lemma refine_pattern_match_angelic `{RA : Rel SA CA} {N : Set} (n : N -> LVar)
        {σ} (pat : Pattern (N:=N) σ) {w : World} {msg : SYMB.SMsg w} {v : Val σ}
        {sv : STerm σ w} {k} {sk} :
        ℛ⟦RVal σ⟧ v sv ∗
        ℛ⟦□ᵣ(RMatchResult pat -> RM RA)⟧ (fun '(existT pc δpc) => k pc δpc) sk ⊢
        ℛ⟦RM RA⟧ (SHAL.CPureSpecM.pattern_match (M := CM) v pat k)
          (SYMB.SPureSpecM.bind (M := SHeapSpec)
             (SYMB.SPureSpecM.angelic_pattern_match (M := SHeapSpec) n pat msg sv) sk).
      Proof.
        iIntros "[rv rk]". rewrite pattern_match_as_bind.
        iApply (refine_bind (RA := RMatchResult pat) with "[rv] rk").
        now iApply (refine_angelic_pattern_match with "rv").
      Qed.

      #[export] Instance refine_compat_angelic_pattern_match
        `{RA : Rel SA CA} {N : Set} (n : N -> LVar) {σ} (pat : Pattern (N:=N) σ)
        {w : World} {msg : SYMB.SMsg w} {v : Val σ} {sv : STerm σ w} {k} {sk} :
        RefineCompat (RM RA) (SHAL.CPureSpecM.pattern_match (M := CM) v pat k) w
          (SYMB.SPureSpecM.bind (M := SHeapSpec)
             (SYMB.SPureSpecM.angelic_pattern_match (M := SHeapSpec) n pat msg sv) sk)
          _ :=
        MkRefineCompat (refine_pattern_match_angelic n (pat := pat)).

    End CompatInstances.

    Section Stack.

      Ltac unfold_stack :=
        unfold SYMB.SStackT.spurespecm_sstackt, SYMB.SStackT.sheapspecm_sstackt,
          SYMB.SStackT.sstackm_sstackt;
        cbn [SYMB.SPureSpecM.pure SYMB.SPureSpecM.bind SYMB.SPureSpecM.error
             SYMB.SPureSpecM.block SYMB.SPureSpecM.angelic SYMB.SPureSpecM.demonic
             SYMB.SPureSpecM.angelic_binary SYMB.SPureSpecM.demonic_binary
             SYMB.SPureSpecM.assert_formula SYMB.SPureSpecM.assume_formula
             SYMB.SPureSpecM.angelic_pattern_match SYMB.SPureSpecM.demonic_pattern_match
             SYMB.SPureSpecM.debug
             SYMB.SHeapSpecM.produce_chunk SYMB.SHeapSpecM.consume_chunk
             SYMB.SHeapSpecM.consume_chunk_angelic SYMB.SHeapSpecM.read_register
             SYMB.SHeapSpecM.write_register SYMB.SStackM.with_frame].

      Lemma refine_backtrace `{RA : Rel SA CA} {w : World} (stk : List SYMB.Frame w) :
        ⊢ ℛ⟦RM RA -> RM RA⟧ (fun m => m) (SYMB.SStackT.backtrace (M := SHeapSpec) stk).
      Proof.
        iIntros (cm sm) "rm". destruct stk; cbn - [RSat]; [done|].
        iApply (refine_debug with "rm").
      Qed.

      Lemma refine_stk_pure `{RA : Rel SA CA} {w} :
        ⊢ ℛ⟦RA -> RS RA⟧
          (SHAL.CPureSpecM.pure (M := CM))
          (SYMB.SPureSpecM.pure (M := SM) (w := w)).
      Proof. unfold_stack. iIntros (a sa) "ra %stk". iApply (refine_pure with "ra"). Qed.

      Lemma refine_stk_bind `{RA : Rel SA CA, RB : Rel SB CB} {w} :
        ⊢ ℛ⟦RS RA -> □ᵣ(RA -> RS RB) -> RS RB⟧
          (SHAL.CPureSpecM.bind (M := CM))
          (SYMB.SPureSpecM.bind (M := SM) (w := w)).
      Proof.
        unfold_stack. iIntros (cm sm) "rm %cf %sf rf %stk".
        iApply (refine_bind with "[rm]"); [iApply "rm"|].
        iIntros (w1 θ1) "!> %a %sa ra".
        iApply ("rf" with "ra").
      Qed.

      Lemma refine_stk_error `{RA : Rel SA CA} (cm : CM CA) {w : World} (msg : SYMB.SMsg w) :
        ⊢ ℛ⟦RS RA⟧ cm (SYMB.SPureSpecM.error (M := SM) msg).
      Proof. unfold_stack. iIntros (stk). iApply refine_error. Qed.

      Lemma refine_stk_block `{RA : Rel SA CA} {w} :
        ⊢ ℛ⟦RS RA⟧
          (SHAL.CPureSpecM.block (M := CM))
          (SYMB.SPureSpecM.block (M := SM) (w := w)).
      Proof. unfold_stack. iIntros (stk). iApply refine_block. Qed.

      Lemma refine_stk_angelic_binary `{RA : Rel SA CA} {w} :
        ⊢ ℛ⟦RS RA -> RS RA -> RS RA⟧
          (SHAL.CPureSpecM.angelic_binary (M := CM))
          (SYMB.SPureSpecM.angelic_binary (M := SM) (w := w)).
      Proof.
        unfold_stack. iIntros (cm1 sm1) "rm1 %cm2 %sm2 rm2 %stk".
        iApply (refine_angelic_binary with "[rm1] [rm2]"); [iApply "rm1"|iApply "rm2"].
      Qed.

      Lemma refine_stk_demonic_binary `{RA : Rel SA CA} {w} :
        ⊢ ℛ⟦RS RA -> RS RA -> RS RA⟧
          (SHAL.CPureSpecM.demonic_binary (M := CM))
          (SYMB.SPureSpecM.demonic_binary (M := SM) (w := w)).
      Proof.
        unfold_stack. iIntros (cm1 sm1) "rm1 %cm2 %sm2 rm2 %stk".
        iApply (refine_demonic_binary with "[rm1] [rm2]"); [iApply "rm1"|iApply "rm2"].
      Qed.

      Lemma refine_stk_debug `{RA : Rel SA CA} {w : World} (msg : SYMB.SMsg w) :
        ⊢ ℛ⟦RS RA -> RS RA⟧ (fun m => m) (SYMB.SPureSpecM.debug (M := SM) msg).
      Proof.
        unfold_stack. iIntros (cm sm) "rm %stk".
        iApply refine_debug. iApply "rm".
      Qed.

      Lemma refine_stk_with_frame `{RA : Rel SA CA} {w : World} (fr : SYMB.Frame w) :
        ⊢ ℛ⟦RS RA -> RS RA⟧ (fun m => m) (SYMB.SStackM.with_frame (M := SM) fr).
      Proof. unfold_stack. iIntros (cm sm) "rm %stk". iApply "rm". Qed.

      Lemma refine_stk_angelic x σ {w} :
        ⊢ ℛ⟦RS (RVal σ)⟧
          (SHAL.CPureSpecM.angelic (M := CM) σ)
          (SYMB.SPureSpecM.angelic (M := SM) x (w := w) σ).
      Proof. unfold_stack. iIntros (stk). iApply refine_angelic. Qed.

      Lemma refine_stk_demonic x σ {w} :
        ⊢ ℛ⟦RS (RVal σ)⟧
          (SHAL.CPureSpecM.demonic (M := CM) σ)
          (SYMB.SPureSpecM.demonic (M := SM) x (w := w) σ).
      Proof. unfold_stack. iIntros (stk). iApply refine_demonic. Qed.

      Lemma refine_stk_assert_formula {w : World} (msg : SYMB.SMsg w) :
        ⊢ ℛ⟦RFormula -> RS RUnit⟧
          (SHAL.CPureSpecM.assert_formula (M := CM))
          (SYMB.SPureSpecM.assert_formula (M := SM) msg).
      Proof.
        unfold_stack. iIntros (F sF) "rF %stk".
        iApply (refine_assert_formula with "rF").
      Qed.

      Lemma refine_stk_assume_formula {w} :
        ⊢ ℛ⟦RFormula -> RS RUnit⟧
          (SHAL.CPureSpecM.assume_formula (M := CM))
          (SYMB.SPureSpecM.assume_formula (M := SM) (w := w)).
      Proof.
        unfold_stack. iIntros (F sF) "rF %stk".
        iApply (refine_assume_formula with "rF").
      Qed.

      Lemma refine_stk_produce_chunk {w} :
        ⊢ ℛ⟦RChunk -> RS RUnit⟧
          (SHAL.CHeapSpecM.produce_chunk (M := CM))
          (SYMB.SHeapSpecM.produce_chunk (M := SM) (w := w)).
      Proof.
        unfold_stack. iIntros (c sc) "rc %stk".
        iApply (refine_produce_chunk with "rc").
      Qed.

      Lemma refine_stk_consume_chunk {w} :
        ⊢ ℛ⟦RChunk -> RS RUnit⟧
          (SHAL.CHeapSpecM.consume_chunk (M := CM))
          (SYMB.SHeapSpecM.consume_chunk (M := SM) (w := w)).
      Proof.
        unfold_stack. iIntros (c sc) "rc %stk".
        iApply refine_backtrace. iApply (refine_consume_chunk with "rc").
      Qed.

      Lemma refine_stk_consume_chunk_angelic {w} :
        ⊢ ℛ⟦RChunk -> RS RUnit⟧
          (SHAL.CHeapSpecM.consume_chunk (M := CM))
          (SYMB.SHeapSpecM.consume_chunk_angelic (M := SM) (w := w)).
      Proof.
        unfold_stack. iIntros (c sc) "rc %stk".
        iApply refine_backtrace. iApply (refine_consume_chunk_angelic with "rc").
      Qed.

      Lemma refine_stk_read_register {τ} (reg : 𝑹𝑬𝑮 τ) {w} :
        ⊢ ℛ⟦RS (RVal τ)⟧
          (SHAL.CHeapSpecM.read_register (M := CM) reg)
          (SYMB.SHeapSpecM.read_register (M := SM) reg (w := w)).
      Proof.
        unfold_stack. iIntros (stk).
        iApply refine_backtrace. iApply refine_read_register.
      Qed.

      Lemma refine_stk_write_register {τ} (reg : 𝑹𝑬𝑮 τ) {w} :
        ⊢ ℛ⟦RVal τ -> RS (RVal τ)⟧
          (SHAL.CHeapSpecM.write_register (M := CM) reg)
          (SYMB.SHeapSpecM.write_register (M := SM) reg (w := w)).
      Proof.
        unfold_stack. iIntros (v sv) "rv %stk".
        iApply refine_backtrace. iApply (refine_write_register with "rv").
      Qed.

      Lemma refine_stk_demonic_pattern_match {N : Set} (n : N -> LVar) {σ}
        (pat : Pattern (N:=N) σ) {w} :
        ⊢ ℛ⟦RVal σ -> RS (RMatchResult pat)⟧
          (fun v => SHAL.CPureSpecM.pure (M := CM) (pattern_match_val pat v))
          (SYMB.SPureSpecM.demonic_pattern_match (M := SM) n pat (w := w)).
      Proof.
        unfold_stack. iIntros (v sv) "rv %stk".
        iApply (refine_demonic_pattern_match with "rv").
      Qed.

      Lemma refine_stk_angelic_pattern_match {N : Set} (n : N -> LVar) {σ}
        (pat : Pattern (N:=N) σ) {w : World} (msg : SYMB.SMsg w) :
        ⊢ ℛ⟦RVal σ -> RS (RMatchResult pat)⟧
          (fun v => SHAL.CPureSpecM.pure (M := CM) (pattern_match_val pat v))
          (SYMB.SPureSpecM.angelic_pattern_match (M := SM) n pat msg).
      Proof.
        unfold_stack. iIntros (v sv) "rv %stk".
        iApply (refine_angelic_pattern_match with "rv").
      Qed.

      Lemma refine_stk_pattern_match_demonic `{RA : Rel SA CA} {N : Set} (n : N -> LVar)
        {σ} (pat : Pattern (N:=N) σ) {w : World} {v : Val σ} {sv : STerm σ w} {k} {sk} :
        ℛ⟦RVal σ⟧ v sv ∗
        ℛ⟦□ᵣ(RMatchResult pat -> RS RA)⟧ (fun '(existT pc δpc) => k pc δpc) sk ⊢
        ℛ⟦RS RA⟧ (SHAL.CPureSpecM.pattern_match (M := CM) v pat k)
          (SYMB.SPureSpecM.bind (M := SM)
             (SYMB.SPureSpecM.demonic_pattern_match (M := SM) n pat sv) sk).
      Proof.
        iIntros "[rv rk]". rewrite pattern_match_as_bind.
        iApply (refine_stk_bind (RA := RMatchResult pat) with "[rv] rk").
        now iApply (refine_stk_demonic_pattern_match with "rv").
      Qed.

      Lemma refine_stk_pattern_match_angelic `{RA : Rel SA CA} {N : Set} (n : N -> LVar)
        {σ} (pat : Pattern (N:=N) σ) {w : World} {msg : SYMB.SMsg w} {v : Val σ}
        {sv : STerm σ w} {k} {sk} :
        ℛ⟦RVal σ⟧ v sv ∗
        ℛ⟦□ᵣ(RMatchResult pat -> RS RA)⟧ (fun '(existT pc δpc) => k pc δpc) sk ⊢
        ℛ⟦RS RA⟧ (SHAL.CPureSpecM.pattern_match (M := CM) v pat k)
          (SYMB.SPureSpecM.bind (M := SM)
             (SYMB.SPureSpecM.angelic_pattern_match (M := SM) n pat msg sv) sk).
      Proof.
        iIntros "[rv rk]". rewrite pattern_match_as_bind.
        iApply (refine_stk_bind (RA := RMatchResult pat) with "[rv] rk").
        now iApply (refine_stk_angelic_pattern_match with "rv").
      Qed.

      #[export] Instance refine_compat_stk_pure `{RA : Rel SA CA} {w} :
        RefineCompat (RA -> RS RA) (SHAL.CPureSpecM.pure (M := CM)) w
          (SYMB.SPureSpecM.pure (M := SM) (w := w)) _ :=
        MkRefineCompat refine_stk_pure.

      #[export] Instance refine_compat_stk_bind `{RA : Rel SA CA, RB : Rel SB CB} {w} :
        RefineCompat (RS RA -> □ᵣ(RA -> RS RB) -> RS RB)
          (SHAL.CPureSpecM.bind (M := CM)) w
          (SYMB.SPureSpecM.bind (M := SM) (w := w)) _ :=
        MkRefineCompat refine_stk_bind.

      #[export] Instance refine_compat_stk_error `{RA : Rel SA CA} {cm : CM CA} {w : World}
        {msg : SYMB.SMsg w} :
        RefineCompat (RS RA) cm w (SYMB.SPureSpecM.error (M := SM) msg) emp :=
        MkRefineCompat (refine_stk_error cm msg).

      #[export] Instance refine_compat_stk_block `{RA : Rel SA CA} {w} :
        RefineCompat (RS RA) (SHAL.CPureSpecM.block (M := CM)) w
          (SYMB.SPureSpecM.block (M := SM) (w := w)) emp :=
        MkRefineCompat refine_stk_block.

      #[export] Instance refine_compat_stk_angelic_binary `{RA : Rel SA CA} {w} :
        RefineCompat (RS RA -> RS RA -> RS RA)
          (SHAL.CPureSpecM.angelic_binary (M := CM)) w
          (SYMB.SPureSpecM.angelic_binary (M := SM) (w := w)) _ :=
        MkRefineCompat refine_stk_angelic_binary.

      #[export] Instance refine_compat_stk_demonic_binary `{RA : Rel SA CA} {w} :
        RefineCompat (RS RA -> RS RA -> RS RA)
          (SHAL.CPureSpecM.demonic_binary (M := CM)) w
          (SYMB.SPureSpecM.demonic_binary (M := SM) (w := w)) _ :=
        MkRefineCompat refine_stk_demonic_binary.

      #[export] Program Instance refine_compat_stk_debug `{RA : Rel SA CA} {cm : CM CA}
        {w : World} {msg : SYMB.SMsg w} {sm} :
        RefineCompat (RS RA) cm w (SYMB.SPureSpecM.debug (M := SM) msg sm)
          (ℛ⟦RS RA⟧ cm sm) :=
        MkRefineCompat _.
      Next Obligation.
        iIntros (SA CA RA cm w msg sm) "rm".
        iApply (refine_stk_debug msg with "rm").
      Qed.

      #[export] Program Instance refine_compat_stk_with_frame `{RA : Rel SA CA}
        {cm : CM CA} {w : World} {fr : SYMB.Frame w} {sm} :
        RefineCompat (RS RA) cm w (SYMB.SStackM.with_frame (M := SM) fr sm)
          (ℛ⟦RS RA⟧ cm sm) :=
        MkRefineCompat _.
      Next Obligation.
        iIntros (SA CA RA cm w fr sm) "rm".
        iApply (refine_stk_with_frame fr with "rm").
      Qed.

      #[export] Instance refine_compat_stk_angelic x σ {w} :
        RefineCompat (RS (RVal σ)) (SHAL.CPureSpecM.angelic (M := CM) σ) w
          (SYMB.SPureSpecM.angelic (M := SM) x (w := w) σ) emp :=
        MkRefineCompat (refine_stk_angelic x σ).

      #[export] Instance refine_compat_stk_demonic x σ {w} :
        RefineCompat (RS (RVal σ)) (SHAL.CPureSpecM.demonic (M := CM) σ) w
          (SYMB.SPureSpecM.demonic (M := SM) x (w := w) σ) emp :=
        MkRefineCompat (refine_stk_demonic x σ).

      #[export] Instance refine_compat_stk_assert_formula {w : World} {msg : SYMB.SMsg w} :
        RefineCompat (RFormula -> RS RUnit) (SHAL.CPureSpecM.assert_formula (M := CM)) w
          (SYMB.SPureSpecM.assert_formula (M := SM) msg) _ :=
        MkRefineCompat (refine_stk_assert_formula msg).

      #[export] Instance refine_compat_stk_assume_formula {w} :
        RefineCompat (RFormula -> RS RUnit) (SHAL.CPureSpecM.assume_formula (M := CM)) w
          (SYMB.SPureSpecM.assume_formula (M := SM) (w := w)) _ :=
        MkRefineCompat refine_stk_assume_formula.

      #[export] Instance refine_compat_stk_produce_chunk {w} :
        RefineCompat (RChunk -> RS RUnit) (SHAL.CHeapSpecM.produce_chunk (M := CM)) w
          (SYMB.SHeapSpecM.produce_chunk (M := SM) (w := w)) _ :=
        MkRefineCompat refine_stk_produce_chunk.

      #[export] Instance refine_compat_stk_consume_chunk {w} :
        RefineCompat (RChunk -> RS RUnit) (SHAL.CHeapSpecM.consume_chunk (M := CM)) w
          (SYMB.SHeapSpecM.consume_chunk (M := SM) (w := w)) _ :=
        MkRefineCompat refine_stk_consume_chunk.

      #[export] Instance refine_compat_stk_consume_chunk_angelic {w} :
        RefineCompat (RChunk -> RS RUnit) (SHAL.CHeapSpecM.consume_chunk (M := CM)) w
          (SYMB.SHeapSpecM.consume_chunk_angelic (M := SM) (w := w)) _ :=
        MkRefineCompat refine_stk_consume_chunk_angelic.

      #[export] Instance refine_compat_stk_read_register {τ} (reg : 𝑹𝑬𝑮 τ) {w} :
        RefineCompat (RS (RVal τ)) (SHAL.CHeapSpecM.read_register (M := CM) reg) w
          (SYMB.SHeapSpecM.read_register (M := SM) reg (w := w)) _ :=
        MkRefineCompat (refine_stk_read_register reg).

      #[export] Instance refine_compat_stk_write_register {τ} (reg : 𝑹𝑬𝑮 τ) {w} :
        RefineCompat (RVal τ -> RS (RVal τ)) (SHAL.CHeapSpecM.write_register (M := CM) reg) w
          (SYMB.SHeapSpecM.write_register (M := SM) reg (w := w)) _ :=
        MkRefineCompat (refine_stk_write_register reg).

      #[export] Instance refine_compat_stk_demonic_pattern_match
        `{RA : Rel SA CA} {N : Set} (n : N -> LVar) {σ} (pat : Pattern (N:=N) σ)
        {w : World} {v : Val σ} {sv : STerm σ w} {k} {sk} :
        RefineCompat (RS RA) (SHAL.CPureSpecM.pattern_match (M := CM) v pat k) w
          (SYMB.SPureSpecM.bind (M := SM)
             (SYMB.SPureSpecM.demonic_pattern_match (M := SM) n pat sv) sk)
          _ :=
        MkRefineCompat (refine_stk_pattern_match_demonic n (pat := pat)).

      #[export] Instance refine_compat_stk_angelic_pattern_match
        `{RA : Rel SA CA} {N : Set} (n : N -> LVar) {σ} (pat : Pattern (N:=N) σ)
        {w : World} {msg : SYMB.SMsg w} {v : Val σ} {sv : STerm σ w} {k} {sk} :
        RefineCompat (RS RA) (SHAL.CPureSpecM.pattern_match (M := CM) v pat k) w
          (SYMB.SPureSpecM.bind (M := SM)
             (SYMB.SPureSpecM.angelic_pattern_match (M := SM) n pat msg sv) sk)
          _ :=
        MkRefineCompat (refine_stk_pattern_match_angelic n (pat := pat)).

    End Stack.

    Section Derived.

      Lemma refine_angelic_ctx {N : Set} {n : N -> LVar} {w} :
        ⊢ ℛ⟦∀ᵣ Δ, RS (RNEnv N Δ)⟧
          (SHAL.CPureSpecM.angelic_ctx (M := CM))
          (SYMB.SPureSpecM.angelic_ctx (M := SM) n (w := w)).
      Proof.
        iIntros (Δ).
        iInduction Δ as [|Δ IHΔ b] "Hind";
          unfold SYMB.SPureSpecM.angelic_ctx, SHAL.CPureSpecM.angelic_ctx;
          rsolve.
      Qed.

      #[export] Instance refine_compat_angelic_ctx {N : Set} {n : N -> LVar} {w} {Δ} :
        RefineCompat (RS (RNEnv N Δ)) (SHAL.CPureSpecM.angelic_ctx (M := CM) Δ) w
          (SYMB.SPureSpecM.angelic_ctx (M := SM) n (w := w) Δ) emp.
      Proof. constructor. iIntros. iApply refine_angelic_ctx. Qed.

      Lemma refine_demonic_ctx {N : Set} {n : N -> LVar} {w} :
        ⊢ ℛ⟦∀ᵣ Δ, RS (RNEnv N Δ)⟧
          (SHAL.CPureSpecM.demonic_ctx (M := CM))
          (SYMB.SPureSpecM.demonic_ctx (M := SM) n (w := w)).
      Proof.
        iIntros (Δ).
        iInduction Δ as [|Δ IHΔ b] "Hind";
          unfold SYMB.SPureSpecM.demonic_ctx, SHAL.CPureSpecM.demonic_ctx;
          rsolve.
      Qed.

      #[export] Instance refine_compat_demonic_ctx {N : Set} {n : N -> LVar} {w} {Δ} :
        RefineCompat (RS (RNEnv N Δ)) (SHAL.CPureSpecM.demonic_ctx (M := CM) Δ) w
          (SYMB.SPureSpecM.demonic_ctx (M := SM) n (w := w) Δ) emp.
      Proof. constructor. iIntros. iApply refine_demonic_ctx. Qed.

      Lemma refine_assert_eq_nenv {N : Set} {Δ : NCtx N Ty} {w : World} (msg : SYMB.SMsg w) :
        ⊢ ℛ⟦RNEnv _ Δ -> RNEnv _ Δ -> RS RUnit⟧
          (SHAL.CPureSpecM.assert_eq_nenv (M := CM) (Δ := Δ))
          (SYMB.SPureSpecM.assert_eq_nenv (M := SM) msg).
      Proof.
        iIntros (E1 Es1) "HE1 %E2 %Es2 HE2".
        iInduction Es1 as [|Es1] "IHEs1";
          env.destroy Es2; env.destroy E1; env.destroy E2; cbn -[RSat].
        - now iApply (refine_stk_pure (RA := RUnit)).
        - iDestruct (repₚ_invert_snoc with "HE1") as "(HE1 & Hv0db)".
          iDestruct (repₚ_invert_snoc with "HE2") as "(HE2 & Hv1v)".
          iSpecialize ("IHEs1" with "HE1 HE2").
          iApply (refine_stk_bind (RA := RUnit) (RB := RUnit) with "IHEs1"); rsolve.
          iApply refine_formula_persist.
          iModIntro; rsolve.
      Qed.

      #[export] Instance refine_compat_assert_eq_nenv {N : Set} {w : World}
        {Δ : NCtx N Ty} {msg : SYMB.SMsg w} :
        RefineCompat (RNEnv _ Δ -> RNEnv _ Δ -> RS RUnit)
          (SHAL.CPureSpecM.assert_eq_nenv (M := CM) (Δ := Δ)) w
          (SYMB.SPureSpecM.assert_eq_nenv (M := SM) msg) emp.
      Proof. constructor. iIntros. iApply (refine_assert_eq_nenv msg). Qed.

      Lemma refine_produce {Σ} (asn : Assertion Σ) :
        ∀ w, ⊢ ℛ⟦RInst (Sub Σ) (Valuation Σ) -> RS RUnit⟧
               (SHAL.CHeapSpecM.produce (M := CM) asn)
               (SYMB.SHeapSpecM.produce (M := SM) asn (w := w)).
      Proof.
        induction asn; cbn - [RSat]; iIntros (w δ sδ) "#rδ"; rsolve.
        - destruct a as [pc sub].
          destruct ta as [spc ssub].
          iRename select (ℛ⟦RMatchResult pat⟧ (existT pc sub) (existT spc ssub)) into "Hmr".
          iDestruct "Hmr" as "(%e & Hmr)"; subst; cbn -[RSat].
          iApply H; rsolve.
        - now iApply IHasn1.
        - iApply IHasn2; rsolve.
        - now iApply IHasn1.
        - now iApply IHasn2.
        - iApply IHasn; rsolve.
      Qed.

      #[export] Instance refine_compat_produce {Σ} (asn : Assertion Σ) {w} :
        RefineCompat (RNEnv LVar Σ -> RS RUnit) (SHAL.CHeapSpecM.produce (M := CM) asn) w
          (SYMB.SHeapSpecM.produce (M := SM) asn (w := w)) _ :=
        MkRefineCompat (refine_produce asn w).

      Lemma refine_consume {Σ} (asn : Assertion Σ) :
        ∀ w, ⊢ ℛ⟦RInst (Sub Σ) (Valuation Σ) -> RS RUnit⟧
               (SHAL.CHeapSpecM.consume (M := CM) asn)
               (SYMB.SHeapSpecM.consume (M := SM) asn (w := w)).
      Proof.
        induction asn; cbn - [RSat]; iIntros (w δ sδ) "#rδ"; rsolve.
        - destruct a as [pc sub].
          destruct ta as [spc ssub].
          iRename select (ℛ⟦RMatchResult pat⟧ (existT pc sub) (existT spc ssub)) into "Hmr".
          iDestruct "Hmr" as "(%e & Hmr)"; subst; cbn -[RSat].
          iApply H; rsolve.
        - now iApply IHasn1.
        - iApply IHasn2; rsolve.
        - now iApply IHasn1.
        - now iApply IHasn2.
        - iApply IHasn; rsolve.
      Qed.

      #[export] Instance refine_compat_consume {Σ} (asn : Assertion Σ) {w} :
        RefineCompat (RNEnv LVar Σ -> RS RUnit) (SHAL.CHeapSpecM.consume (M := CM) asn) w
          (SYMB.SHeapSpecM.consume (M := SM) asn (w := w)) _ :=
        MkRefineCompat (refine_consume asn w).

      Lemma refine_call_contract {Δ τ} (c : SepContract Δ τ) {w} :
        ⊢ ℛ⟦RInst (SStore Δ) (CStore Δ) -> RS (RVal τ)⟧
          (SHAL.CHeapSpecM.call_contract (M := CM) c)
          (SYMB.SHeapSpecM.call_contract (M := SM) c (w := w)).
      Proof.
        iIntros (cδ sδ) "#rδ".
        destruct c as [lvars pats req res ens]; cbn - [RSat].
        rsolve.
      Qed.

      #[export] Instance refine_compat_call_contract {Δ τ} (c : SepContract Δ τ) {w} :
        RefineCompat (RInst (SStore Δ) (CStore Δ) -> RS (RVal τ))
          (SHAL.CHeapSpecM.call_contract (M := CM) c) w
          (SYMB.SHeapSpecM.call_contract (M := SM) c (w := w)) _ :=
        MkRefineCompat (refine_call_contract _).

      Lemma refine_call_lemma {Δ} (lem : Lemma Δ) w :
        ⊢ ℛ⟦RInst (SStore Δ) (CStore Δ) -> RS RUnit⟧
          (SHAL.CHeapSpecM.call_lemma (M := CM) lem)
          (SYMB.SHeapSpecM.call_lemma (M := SM) lem (w := w)).
      Proof.
        iIntros (cδ sδ) "#rδ".
        destruct lem as [lvars pats req ens]; cbn - [RSat].
        rsolve.
      Qed.

      #[export] Instance refine_compat_call_lemma {Δ} (lem : Lemma Δ) w :
        RefineCompat (RInst (SStore Δ) (CStore Δ) -> RS RUnit)
          (SHAL.CHeapSpecM.call_lemma (M := CM) lem) w
          (SYMB.SHeapSpecM.call_lemma (M := SM) lem (w := w)) _ :=
        MkRefineCompat (refine_call_lemma _ _).

    End Derived.

    Section Store.

      Definition RStore (Γ : PCtx) : Rel (SStore Γ) (CStore Γ) :=
        RInst (SStore Γ) (CStore Γ).

      Definition RStoreT Γ1 Γ2 `(RA : Rel SA CA) :
        Rel (SYMB.SStoreT.SStoreT SM Γ1 Γ2 SA) (SHAL.CStoreT.CStoreT CM Γ1 Γ2 CA) :=
        RStore Γ1 -> RS (RProd RA (RStore Γ2)).

      Lemma refine_pair `{RA : Rel SA CA, RB : Rel SB CB} {w} {a : CA} {b : CB}
        {sa : SA w} {sb : SB w} :
        ℛ⟦RA⟧ a sa ∗ ℛ⟦RB⟧ b sb ⊢ ℛ⟦RProd RA RB⟧ (a, b) (sa, sb).
      Proof. now cbn. Qed.

      Lemma refine_peval {w : World} {σ} (t : STerm σ w) v :
        ℛ⟦RVal σ⟧ v t ⊢ ℛ⟦RVal σ⟧ v (peval t).
      Proof. unfold RVal, RInst. crushPredEntails3. now rewrite peval_sound. Qed.

      Lemma refine_seval_exp {Γ σ} (e : Exp Γ σ) {w : World} {δ} {sδ : SStore Γ w} :
        ℛ⟦RStore Γ⟧ δ sδ ⊢ ℛ⟦RVal σ⟧ (B.eval e δ) (seval_exp sδ e).
      Proof.
        unfold RStore, RVal, RInst. crushPredEntails3.
        rewrite <-eval_exp_inst.
        now subst.
      Qed.

      Lemma refine_seval_exps {Γ Δ : PCtx} {es : NamedEnv (Exp Γ) Δ} {w : World}
        {δ : CStore Γ} {sδ : SStore Γ w} :
        ℛ⟦RStore Γ⟧ δ sδ ⊢ ℛ⟦RStore Δ⟧ (evals es δ) (seval_exps sδ es).
      Proof.
        unfold RStore, RInst; cbn.
        crushPredEntails3.
        unfold seval_exps, inst, inst_store, inst_env, evals.
        rewrite env.map_map.
        apply env.map_ext.
        intros.
        rewrite peval_sound.
        now apply refine_seval_exp.
      Qed.

      Lemma refine_env_update {Γ x σ} (xIn : (x∷σ ∈ Γ)%katamaran) (w : World)
        (t : Term w σ) (v : Val σ) (δs : SStore Γ w) (δc : CStore Γ) :
        ℛ⟦RVal σ⟧ v t ∗ ℛ⟦RStore Γ⟧ δc δs ⊢ ℛ⟦RStore Γ⟧ (δc ⟪ x ↦ v ⟫) (δs ⟪ x ↦ t ⟫).
      Proof.
        unfold RVal, RStore, RInst.
        crushPredEntails3; subst.
        unfold inst, inst_store, inst_env.
        now rewrite env.map_update.
      Qed.

      Lemma refine_store_lift `{RA : Rel SA CA} {Γ w} :
        ⊢ ℛ⟦RS RA -> RStoreT Γ Γ RA⟧
          (SHAL.CStoreT.lift (M := CM))
          (SYMB.SStoreT.liftM (M := SM) (w := w)).
      Proof.
        iIntros (m sm) "rm %δ %sδ #rδ".
        unfold SHAL.CStoreT.lift, SYMB.SStoreT.liftM.
        iApply (refine_stk_bind with "rm").
        iIntros (w1 ω1) "!> %a %sa ra".
        iApply refine_stk_pure. iApply refine_pair. iSplitL "ra"; [done|rsolve].
      Qed.

      Lemma refine_store_eval `{RA : Rel SA CA} {Γ1 Γ2 w} :
        ⊢ ℛ⟦RStoreT Γ1 Γ2 RA -> RStore Γ1 -> RS RA⟧
          (SHAL.CStoreT.evalCStoreT (M := CM))
          (SYMB.SStoreT.evalSStoreT (M := SM) (w := w)).
      Proof.
        iIntros (m sm) "rm %δ %sδ rδ".
        unfold SHAL.CStoreT.evalCStoreT, SYMB.SStoreT.evalSStoreT.
        iApply (refine_stk_bind with "[rm rδ]"); [now iApply "rm"|].
        iIntros (w1 ω1) "!> %p %sp rp".
        destruct p as [a δ1], sp as [sa sδ1].
        iDestruct "rp" as "[ra _]". rsolve.
      Qed.

      Lemma refine_store_pure `{RA : Rel SA CA} {Γ w} :
        ⊢ ℛ⟦RA -> RStoreT Γ Γ RA⟧
          (SHAL.CStoreT.pure (M := CM))
          (SYMB.SStoreT.pure (M := SM) (w := w)).
      Proof.
        iIntros (a sa) "ra %δ %sδ rδ".
        unfold SHAL.CStoreT.pure, SHAL.CStoreT.state, SYMB.SStoreT.pure.
        iApply refine_stk_pure. iApply refine_pair. iFrame.
      Qed.

      Lemma refine_store_bind `{RA : Rel SA CA, RB : Rel SB CB} {Γ1 Γ2 Γ3 w} :
        ⊢ ℛ⟦RStoreT Γ1 Γ2 RA -> □ᵣ(RA -> RStoreT Γ2 Γ3 RB) -> RStoreT Γ1 Γ3 RB⟧
          (SHAL.CStoreT.bind (M := CM))
          (SYMB.SStoreT.bind (M := SM) (w := w)).
      Proof.
        iIntros (m sm) "rm %f %sf rf %δ %sδ rδ".
        unfold SHAL.CStoreT.bind, SYMB.SStoreT.bind.
        iApply (refine_stk_bind with "[rm rδ]"); [now iApply "rm"|].
        iIntros (w1 ω1) "!> %p %sp rp".
        destruct p as [a δ1], sp as [sa sδ1].
        iDestruct "rp" as "[ra rδ1]".
        iApply ("rf" with "ra rδ1").
      Qed.

      Lemma refine_store_error `{RA : Rel SA CA} {Γ1 Γ2} {w : World}
        (cm : SHAL.CStoreT.CStoreT CM Γ1 Γ2 CA) (msg : SStore Γ1 w -> SYMB.SMsg w) :
        ⊢ ℛ⟦RStoreT Γ1 Γ2 RA⟧ cm (SYMB.SStoreT.error (M := SM) msg).
      Proof.
        iIntros (δ sδ) "rδ". unfold SYMB.SStoreT.error.
        iApply refine_stk_error.
      Qed.

      Lemma refine_store_debug `{RA : Rel SA CA} {Γ1 Γ2} {w : World}
        (cm : SHAL.CStoreT.CStoreT CM Γ1 Γ2 CA) (msg : SStore Γ1 w -> SYMB.SMsg w) sm :
        ℛ⟦RStoreT Γ1 Γ2 RA⟧ cm sm ⊢
        ℛ⟦RStoreT Γ1 Γ2 RA⟧ cm (SYMB.SStoreT.debug (M := SM) msg sm).
      Proof.
        iIntros "rm %δ %sδ rδ". unfold SYMB.SStoreT.debug.
        iApply (refine_stk_debug with "[rm rδ]"). now iApply "rm".
      Qed.

      Lemma refine_store_pushpop `{RA : Rel SA CA} {Γ1 Γ2 x σ w} :
        ⊢ ℛ⟦RVal σ -> RStoreT (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) RA -> RStoreT Γ1 Γ2 RA⟧
          (SHAL.CStoreT.pushpop (M := CM))
          (SYMB.SStoreT.pushpop (M := SM) (w := w)).
      Proof.
        iIntros (v sv) "rv %m %sm rm %δ %sδ rδ".
        unfold SHAL.CStoreT.pushpop, SYMB.SStoreT.pushpop.
        iApply (refine_stk_bind with "[rm rδ rv]"); [iApply "rm"; rsolve|].
        iIntros (w1 ω1) "!> %p %sp rp".
        destruct p as [a δ1], sp as [sa sδ1].
        iDestruct "rp" as "[ra rδ1]".
        iApply refine_stk_pure. iApply refine_pair. iSplitL "ra"; [done|].
        iApply (repₚ_cong (T1 := SStore (Γ2 ▻ x∷σ)) (T2 := SStore Γ2) env.tail env.tail);
          last done.
        intros. now env.destroy vs1.
      Qed.

      Lemma refine_store_pushspops `{RA : Rel SA CA} {Γ1 Γ2 Δ w} :
        ⊢ ℛ⟦RStore Δ -> RStoreT (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) RA -> RStoreT Γ1 Γ2 RA⟧
          (SHAL.CStoreT.pushspops (M := CM))
          (SYMB.SStoreT.pushspops (M := SM) (w := w)).
      Proof.
        iIntros (δΔ sδΔ) "rδΔ %m %sm rm %δ %sδ rδ".
        unfold SHAL.CStoreT.pushspops, SYMB.SStoreT.pushspops.
        iApply (refine_stk_bind with "[rm rδ rδΔ]"); [iApply "rm"; rsolve|].
        iIntros (w1 ω1) "!> %p %sp rp".
        destruct p as [a δ1], sp as [sa sδ1].
        iDestruct "rp" as "[ra rδ1]".
        iApply refine_stk_pure. iApply refine_pair. iSplitL "ra"; [done|].
        iApply (repₚ_cong (T1 := SStore (Γ2 ▻▻ Δ)) (T2 := SStore Γ2)
                  (env.drop Δ) (env.drop Δ)); last done.
        intros. env.destroy vs1.
        now rewrite inst_env_cat !env.drop_cat.
      Qed.

      Lemma refine_store_get_local {Γ w} :
        ⊢ ℛ⟦RStoreT Γ Γ (RStore Γ)⟧
          (SHAL.CStoreT.get_local (M := CM))
          (SYMB.SStoreT.get_local (M := SM) (w := w)).
      Proof.
        iIntros (δ sδ) "#rδ".
        unfold SHAL.CStoreT.get_local, SHAL.CStoreT.state, SYMB.SStoreT.get_local.
        iApply refine_stk_pure. iApply refine_pair. now iSplit.
      Qed.

      Lemma refine_store_put_local {Γ1 Γ2 w} :
        ⊢ ℛ⟦RStore Γ2 -> RStoreT Γ1 Γ2 RUnit⟧
          (SHAL.CStoreT.put_local (M := CM))
          (SYMB.SStoreT.put_local (M := SM) (w := w)).
      Proof.
        iIntros (δ2 sδ2) "rδ2 %δ %sδ rδ".
        unfold SHAL.CStoreT.put_local, SHAL.CStoreT.state, SYMB.SStoreT.put_local.
        iApply refine_stk_pure. iApply refine_pair. iSplitR "rδ2"; [rsolve|done].
      Qed.

      Lemma refine_store_eval_exp {Γ σ} (e : Exp Γ σ) {w} :
        ⊢ ℛ⟦RStoreT Γ Γ (RVal σ)⟧
          (SHAL.CStoreT.eval_exp (M := CM) e)
          (SYMB.SStoreT.eval_exp (M := SM) e (w := w)).
      Proof.
        iIntros (δ sδ) "#rδ".
        unfold SHAL.CStoreT.eval_exp, SHAL.CStoreT.state, SYMB.SStoreT.eval_exp.
        iApply refine_stk_pure. iApply refine_pair. iSplit; last done.
        iApply refine_peval. now iApply refine_seval_exp.
      Qed.

      Lemma refine_store_eval_exps {Γ Δ} (es : NamedEnv (Exp Γ) Δ) {w} :
        ⊢ ℛ⟦RStoreT Γ Γ (RStore Δ)⟧
          (SHAL.CStoreT.eval_exps (M := CM) es)
          (SYMB.SStoreT.eval_exps (M := SM) es (w := w)).
      Proof.
        iIntros (δ sδ) "#rδ".
        unfold SHAL.CStoreT.eval_exps, SHAL.CStoreT.state, SYMB.SStoreT.eval_exps.
        iApply refine_stk_pure. iApply refine_pair. iSplit; last done.
        now iApply refine_seval_exps.
      Qed.

      Lemma refine_store_assign {Γ x σ} {xIn : (x∷σ ∈ Γ)%katamaran} {w} :
        ⊢ ℛ⟦RVal σ -> RStoreT Γ Γ RUnit⟧
          (SHAL.CStoreT.assign (M := CM) x)
          (SYMB.SStoreT.assign (M := SM) (x := x) (w := w)).
      Proof.
        iIntros (v sv) "rv %δ %sδ rδ".
        unfold SHAL.CStoreT.assign, SHAL.CStoreT.state, SYMB.SStoreT.assign.
        iApply refine_stk_pure. iApply refine_pair. iSplit; first done.
        iApply (refine_env_update with "[$rv $rδ]").
      Qed.

      Lemma store_pattern_match_as_bind {N : Set} {A σ Γ1 Γ2} (pat : Pattern (N:=N) σ)
        (v : Val σ) (k : forall pc, NamedEnv Val (PatternCaseCtx pc) -> SHAL.CStoreT.CStoreT CM Γ1 Γ2 A) :
        SHAL.CStoreT.pattern_match (M := CM) v pat k =
          SHAL.CStoreT.bind (M := CM)
            (SHAL.CStoreT.lift (M := CM) (SHAL.CPureSpecM.pure (M := CM) (pattern_match_val pat v)))
            (fun '(existT pc δpc) => k pc δpc).
      Proof. reflexivity. Qed.

      Lemma refine_store_pattern_match `{RA : Rel SA CA} {N : Set} (n : N -> LVar)
        {Γ1 σ} (pat : Pattern (N:=N) σ) {w : World} {v : Val σ} {sv : STerm σ w} {k} {sk} :
        ℛ⟦RVal σ⟧ v sv ∗
        ℛ⟦□ᵣ(RMatchResult pat -> RStoreT Γ1 Γ1 RA)⟧ (fun '(existT pc δpc) => k pc δpc) sk ⊢
        ℛ⟦RStoreT Γ1 Γ1 RA⟧ (SHAL.CStoreT.pattern_match (M := CM) v pat k)
          (SYMB.SStoreT.bind (M := SM)
             (SYMB.SStoreT.demonic_pattern_match (M := SM) n pat sv) sk).
      Proof.
        iIntros "[rv rk]". rewrite store_pattern_match_as_bind.
        iApply (refine_store_bind (RA := RMatchResult pat) with "[rv] rk").
        unfold SYMB.SStoreT.demonic_pattern_match.
        iApply refine_store_lift.
        now iApply (refine_stk_demonic_pattern_match with "rv").
      Qed.

      #[export] Instance refine_compat_store_lift `{RA : Rel SA CA} {Γ w} :
        RefineCompat (RS RA -> RStoreT Γ Γ RA) (SHAL.CStoreT.lift (M := CM)) w
          (SYMB.SStoreT.liftM (M := SM) (w := w)) _ :=
        MkRefineCompat refine_store_lift.
      #[export] Instance refine_compat_store_eval `{RA : Rel SA CA} {Γ1 Γ2 w} :
        RefineCompat (RStoreT Γ1 Γ2 RA -> RStore Γ1 -> RS RA)
          (SHAL.CStoreT.evalCStoreT (M := CM)) w
          (SYMB.SStoreT.evalSStoreT (M := SM) (w := w)) _ :=
        MkRefineCompat refine_store_eval.
      #[export] Instance refine_compat_store_pure `{RA : Rel SA CA} {Γ w} :
        RefineCompat (RA -> RStoreT Γ Γ RA) (SHAL.CStoreT.pure (M := CM)) w
          (SYMB.SStoreT.pure (M := SM) (w := w)) _ :=
        MkRefineCompat refine_store_pure.
      #[export] Instance refine_compat_store_bind `{RA : Rel SA CA, RB : Rel SB CB}
        {Γ1 Γ2 Γ3 w} :
        RefineCompat (RStoreT Γ1 Γ2 RA -> □ᵣ(RA -> RStoreT Γ2 Γ3 RB) -> RStoreT Γ1 Γ3 RB)
          (SHAL.CStoreT.bind (M := CM)) w
          (SYMB.SStoreT.bind (M := SM) (w := w)) _ :=
        MkRefineCompat refine_store_bind.
      #[export] Instance refine_compat_store_error `{RA : Rel SA CA} {Γ1 Γ2} {w : World}
        {cm : SHAL.CStoreT.CStoreT CM Γ1 Γ2 CA} {msg : SStore Γ1 w -> SYMB.SMsg w} :
        RefineCompat (RStoreT Γ1 Γ2 RA) cm w (SYMB.SStoreT.error (M := SM) msg) emp :=
        MkRefineCompat (refine_store_error cm msg).
      #[export] Instance refine_compat_store_debug `{RA : Rel SA CA} {Γ1 Γ2} {w : World}
        {cm : SHAL.CStoreT.CStoreT CM Γ1 Γ2 CA} {msg : SStore Γ1 w -> SYMB.SMsg w} {sm} :
        RefineCompat (RStoreT Γ1 Γ2 RA) cm w (SYMB.SStoreT.debug (M := SM) msg sm) _ :=
        MkRefineCompat (refine_store_debug cm msg sm).
      #[export] Instance refine_compat_store_pushpop `{RA : Rel SA CA} {Γ1 Γ2 x σ w} :
        RefineCompat (RVal σ -> RStoreT (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) RA -> RStoreT Γ1 Γ2 RA)
          (SHAL.CStoreT.pushpop (M := CM)) w
          (SYMB.SStoreT.pushpop (M := SM) (w := w)) _ :=
        MkRefineCompat refine_store_pushpop.
      #[export] Instance refine_compat_store_pushspops `{RA : Rel SA CA} {Γ1 Γ2 Δ w} :
        RefineCompat (RStore Δ -> RStoreT (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) RA -> RStoreT Γ1 Γ2 RA)
          (SHAL.CStoreT.pushspops (M := CM)) w
          (SYMB.SStoreT.pushspops (M := SM) (w := w)) _ :=
        MkRefineCompat refine_store_pushspops.
      #[export] Instance refine_compat_store_get_local {Γ w} :
        RefineCompat (RStoreT Γ Γ (RStore Γ)) (SHAL.CStoreT.get_local (M := CM)) w
          (SYMB.SStoreT.get_local (M := SM) (w := w)) _ :=
        MkRefineCompat refine_store_get_local.
      #[export] Instance refine_compat_store_put_local {Γ1 Γ2 w} :
        RefineCompat (RStore Γ2 -> RStoreT Γ1 Γ2 RUnit) (SHAL.CStoreT.put_local (M := CM)) w
          (SYMB.SStoreT.put_local (M := SM) (w := w)) _ :=
        MkRefineCompat refine_store_put_local.
      #[export] Instance refine_compat_store_eval_exp {Γ σ} (e : Exp Γ σ) {w} :
        RefineCompat (RStoreT Γ Γ (RVal σ)) (SHAL.CStoreT.eval_exp (M := CM) e) w
          (SYMB.SStoreT.eval_exp (M := SM) e (w := w)) _ :=
        MkRefineCompat (refine_store_eval_exp e).
      #[export] Instance refine_compat_store_eval_exps {Γ Δ} (es : NamedEnv (Exp Γ) Δ) {w} :
        RefineCompat (RStoreT Γ Γ (RStore Δ)) (SHAL.CStoreT.eval_exps (M := CM) es) w
          (SYMB.SStoreT.eval_exps (M := SM) es (w := w)) _ :=
        MkRefineCompat (refine_store_eval_exps es).
      #[export] Instance refine_compat_store_assign {Γ x σ} {xIn : (x∷σ ∈ Γ)%katamaran} {w} :
        RefineCompat (RVal σ -> RStoreT Γ Γ RUnit) (SHAL.CStoreT.assign (M := CM) x) w
          (SYMB.SStoreT.assign (M := SM) (x := x) (w := w)) _ :=
        MkRefineCompat refine_store_assign.
      #[export] Instance refine_compat_store_pattern_match `{RA : Rel SA CA} {N : Set}
        (n : N -> LVar) {Γ1 σ} (pat : Pattern (N:=N) σ) {w : World} {v : Val σ}
        {sv : STerm σ w} {k} {sk} :
        RefineCompat (RStoreT Γ1 Γ1 RA) (SHAL.CStoreT.pattern_match (M := CM) v pat k) w
          (SYMB.SStoreT.bind (M := SM)
             (SYMB.SStoreT.demonic_pattern_match (M := SM) n pat sv) sk) _ :=
        MkRefineCompat (refine_store_pattern_match n (pat := pat)).

    End Store.

    Section Exec.

      Definition RefineExecCall (cec : SHAL.CStoreT.ExecCall CM) (sec : SYMB.SStoreT.ExecCall SM) : Prop :=
        ∀ Δ τ (f : 𝑭 Δ τ) w,
          ⊢ ℛ⟦RStore Δ -> RS (RVal τ)⟧ (cec Δ τ f) (sec Δ τ f w).
      Definition RefineExecCallForeign (cec : SHAL.CStoreT.ExecCallForeign CM)
        (sec : SYMB.SStoreT.ExecCallForeign SM) : Prop :=
        ∀ Δ τ (f : 𝑭𝑿 Δ τ) w,
          ⊢ ℛ⟦RStore Δ -> RS (RVal τ)⟧ (cec Δ τ f) (sec Δ τ f w).
      Definition RefineExecLemma (cel : SHAL.CStoreT.ExecLemma CM) (sel : SYMB.SStoreT.ExecLemma SM) : Prop :=
        ∀ Δ (l : 𝑳 Δ) w,
          ⊢ ℛ⟦RStore Δ -> RS RUnit⟧ (cel Δ l) (sel Δ l w).
      Definition RefineExecFail (cef : SHAL.CStoreT.ExecFail CM) (sef : SYMB.SStoreT.ExecFail SM) : Prop :=
        ∀ Γ τ (s : Val ty.string) w,
          ⊢ ℛ⟦RStoreT Γ Γ (RVal τ)⟧ (cef Γ τ s) (sef Γ τ s w).
      Definition RefineExec (ce : SHAL.CStoreT.Exec CM) (se : SYMB.SStoreT.Exec SM) : Prop :=
        ∀ Γ τ (s : Stm Γ τ) w,
          ⊢ ℛ⟦RStoreT Γ Γ (RVal τ)⟧ (ce Γ τ s) (se Γ τ s w).

      Context {SPEC : Specification}.

      Section ExecAux.

        Context `(rexec_call_foreign : RefineExecCallForeign c_exec_call_foreign s_exec_call_foreign).
        Context `(rexec_lemma : RefineExecLemma c_exec_lemma s_exec_lemma).
        Context `(rexec_call : RefineExecCall c_exec_call s_exec_call).
        Context `(rexec_fail : RefineExecFail c_exec_fail s_exec_fail).

        Lemma refine_exec_aux :
          RefineExec
            (SHAL.CStoreT.exec_aux c_exec_call_foreign c_exec_lemma c_exec_call c_exec_fail)
            (SYMB.SStoreT.exec_aux s_exec_call_foreign s_exec_lemma s_exec_call s_exec_fail).
        Proof.
          intros ? ? s. induction s; cbn; intros w; rsolve.
          - now iApply rexec_call.
          - now iApply rexec_call_foreign.
          - now iApply rexec_lemma.
          - iApply IHs1.
          - destruct fail_rule_pre; rsolve.
          - now iApply rexec_fail.
          - destruct a0, ta0.
            iRename select (ℛ⟦RMatchResult pat⟧ (existT x n) (existT x0 n0)) into "Hmr".
            iDestruct "Hmr" as "[%e Hvs]".
            subst x0.
            rsolve.
            now iApply H.
        Qed.

      End ExecAux.

      Lemma refine_exec_contract `(rexec : RefineExec c_exec s_exec)
        {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) w :
        ⊢ ℛ⟦RS RUnit⟧
            (SHAL.exec_contract (M := CM) c_exec c s)
            (SYMB.exec_contract (M := SM) s_exec c s w).
      Proof.
        destruct c as [lvars pats req result ens]; cbn - [RS]. rsolve.
        iApply rexec.
      Qed.

      Lemma refine_exec_call_error_no_fuel :
        RefineExecCall (SHAL.exec_call_error_no_fuel (M := CM))
          (SYMB.sexec_call_error_no_fuel (M := SM)).
      Proof.
        iIntros (? ? ? ? cδ sδ) "#rδ".
        unfold SHAL.exec_call_error_no_fuel, SYMB.sexec_call_error_no_fuel.
        iApply refine_stk_error.
      Qed.

      Lemma refine_exec_call_foreign :
        RefineExecCallForeign (SHAL.cexec_call_foreign (M := CM))
          (SYMB.sexec_call_foreign (M := SM)).
      Proof.
        iIntros (? ? ? ? cδ sδ) "#rδ".
        unfold SHAL.cexec_call_foreign, SYMB.sexec_call_foreign.
        iApply refine_stk_with_frame. now iApply refine_call_contract.
      Qed.

      Lemma refine_exec_lemma :
        RefineExecLemma (SHAL.cexec_lemma (M := CM)) (SYMB.sexec_lemma (M := SM)).
      Proof.
        iIntros (? ? ? cδ sδ) "#rδ".
        unfold SHAL.cexec_lemma, SYMB.sexec_lemma.
        iApply refine_stk_with_frame. now iApply refine_call_lemma.
      Qed.

      Lemma refine_exec_fail :
        RefineExecFail (SHAL.cexec_fail (M := CM)) (SYMB.sexec_fail (M := SM)).
      Proof.
        iIntros (? ? ? ?).
        unfold SHAL.cexec_fail, SYMB.sexec_fail; destruct fail_rule_pre; rsolve.
      Qed.

      Lemma refine_exec_call (fuel : nat) :
        RefineExecCall (SHAL.cexec_call (M := CM) fuel)
          (SYMB.sexec_call (M := SM) fuel).
      Proof.
        induction fuel; cbn; iIntros (? ? f ? cδ sδ) "#rδ";
          destruct (CEnv f); rsolve.
        iApply refine_exec_aux;
          auto using refine_exec_call_foreign, refine_exec_lemma, refine_exec_fail.
      Qed.

      Lemma refine_exec (fuel : nat) :
        RefineExec (SHAL.cexec (M := CM) fuel) (SYMB.sexec (M := SM) fuel).
      Proof.
        unfold SHAL.cexec, SYMB.sexec. apply refine_exec_aux.
        all: auto using refine_exec_call_foreign, refine_exec_lemma,
                        refine_exec_call, refine_exec_fail.
      Qed.

      Lemma refine_run {w} :
        ⊢ ℛ⟦RM RUnit -> ℙ⟧ (fun m => ⊢ SHAL.CPureSpec.run m) (SHeapSpec.run (w := w)).
      Proof.
        iIntros (m sm) "rm HS".
        unfold SHeapSpec.run, SHAL.CPureSpec.run.
        iPoseProof ("rm" $! (fun _ => SHAL.CPureSpec.FINISH)
                      (fun _ _ _ _ => SymProp.block) with "[]") as "rm".
        { iIntros (w1 ω1) "!> %u %su _ %h %sh _ _". iPureIntro.
          apply bi.True_intro. }
        iPoseProof ("rm" $! nil nil with "[] HS") as "%H"; [rsolve|].
        iPureIntro. exact H.
      Qed.

      Lemma refine_vcgen (fuel : nat) {Γ τ} (c : SepContract Γ τ) (body : Stm Γ τ) w :
        ⊢ ℛ⟦ℙ⟧ (⊢ SHAL.vcgen (L := L) fuel c body) (SYMB.vcgen fuel c body w).
      Proof.
        iApply refine_run.
        iPoseProof (refine_exec_contract (refine_exec fuel) c body w) as "H".
        iApply "H".
      Qed.

    End Exec.

  End WithBI.

  Lemma replay_sound (s : 𝕊 wnil) :
    safe (SPureSpec.replay s) [env] -> safe s [env].
  Proof.
    intros H.
    apply CPureSpec.replay_sound.
    pose proof (PureSpec.refine_replay s).
    unfold RProp in H0; cbn in H0.
    rewrite psafe_safe in H0.
    now apply (fromEntails H0 [env]).
  Qed.

  Section Soundness.

    Context {L : bi} {biA : BiAffine L} {PI : PredicateDef L} {SPEC : Specification}.
    Import Postprocessing.

    Lemma symbolic_vcgen_fuel_soundness {Γ τ} (fuel : nat)
      (c : SepContract Γ τ) (body : Stm Γ τ) :
      SYMB.Symbolic.ValidContractWithFuel fuel c body ->
      ⊢ SHAL.vcgen (L := L) fuel c body.
    Proof.
      unfold SYMB.Symbolic.ValidContractWithFuel.
      intros [Hwp%postprocess_sound].
      apply replay_sound in Hwp.
      apply postprocess_sound in Hwp.
      apply (psafe_safe (w := wnil)) in Hwp; [|easy].
      revert Hwp.
      apply refine_vcgen; try done.
    Qed.

    Lemma symbolic_vcgen_soundness {Γ τ} (c : SepContract Γ τ) (body : Stm Γ τ) :
      SYMB.Symbolic.ValidContract c body ->
      SHAL.Shallow.ValidContract (L := L) c body.
    Proof. apply symbolic_vcgen_fuel_soundness. Qed.

  End Soundness.

End NewSymbolicSoundness.
