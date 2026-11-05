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
     Classes.Morphisms_Prop
     ZArith.ZArith
     Lists.List
     micromega.Lia
     Strings.String.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Iris.Instance
     Iris.Base
     Notations
     Semantics
     Bitvector
     Refinement.Monads
     Sep.Hoare
     Symbolic.Propositions
     Symbolic.Solver
     Symbolic.Worlds
     MicroSail.ShallowExecutor
     MicroSail.ShallowSoundness
     MicroSail.SymbolicExecutor
     MicroSail.RefineExecutor
     MicroSail.Soundness
     RiscvPmp.Model
     RiscvPmp.BlockVer.Spec
     RiscvPmp.IrisModel
     RiscvPmp.IrisInstance
     RiscvPmp.Machine
     RiscvPmp.Logic
     RiscvPmp.trace
     RiscvPmp.Sig.
From iris.base_logic Require lib.gen_heap lib.iprop invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac.
From iris.program_logic Require weakestpre adequacy.
From iris.proofmode Require string_ident proofmode.
From stdpp Require namespaces.

Import RiscvPmpProgram.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.
Import ListNotations.
Open Scope string_scope.
Open Scope ctx_scope.
Open Scope Z_scope.

Module ns := stdpp.namespaces.

(*   Definition pmp_entry_cfg := ty_prod ty_pmpcfg_ent ty_xlenbits. *)

Module Type RiscvPmpBlockVerifTotalVerifier
  (LOR : LeftOrRight)
  (Import RVPCOM : RiscvPmpIrisBaseCommon)
  (Import RVPBASE : RiscvPmpIrisBase LOR RVPCOM)
  (Import RVPPRED : RiscvPmpIrisInstancePredicates LOR RVPCOM RVPBASE)
  (Import RVPINST : RiscvPmpIrisInstance LOR RVPCOM RVPBASE RVPPRED)
  (Import RVPCONTR : RiscvPmpIrisInstanceWithContracts LOR RVPCOM RVPBASE RVPPRED RVPINST).
  Section BlockVerificationDerived.

    Import RiscvPmpExecutor.

    Import RiscvPmpShallowExec.

    Import RiscvPmpBlockVerifSpec.

    Definition safeE {Σ} : 𝕊 Σ -> Prop :=
      fun P => VerificationConditionWithErasure (Erasure.erase_symprop P).

    Definition safeE_safe (p : 𝕊 wnil) (ι : Valuation wnil) : safeE p -> SymProp.safe p [].
    Proof.
      unfold safeE.
      destruct 1 as [H].
      now apply Erasure.erase_safe'.
    Qed.

    Section Symbolic.

      Import ModalNotations.
      Import SStoreSpec (evalStoreSpec).
      Import SHeapSpec SHeapSpec.notations.
      Import asn.notations.

      Definition exec_instruction_prologue (i : AST) :
        Assertion ([ctx] ▻ ("a":: ty_xlenbits)) :=
        pc     ↦ term_var "a" ∗
        asn.chunk (chunk_user ptstoinstr [term_var "a"; term_val ty_ast i]) ∗
        asn.exist "an" ty_xlenbits (nextpc ↦ term_var "an").

      Definition exec_instruction_epilogue (i : AST) :
        Assertion ([ctx] ▻ ("a":: ty_xlenbits) ▻ ("an":: ty_xlenbits)) :=
        pc     ↦ term_var "an" ∗
        asn.chunk (chunk_user ptstoinstr [term_var "a"; term_val ty_ast i]) ∗
        nextpc ↦ term_var "an".

      Definition sexec_instruction (i : AST) :
        ⊢ STerm ty_xlenbits -> SHeapSpec (STerm ty_xlenbits) :=
        let inline_fuel := 10%nat in
        fun _ a =>
          ⟨ θ1 ⟩ _  <- produce
                         (exec_instruction_prologue i)
                         [env].["a"∷_ ↦ a] ;;
          ⟨ θ2 ⟩ _  <- evalStoreSpec (sexec default_config inline_fuel (FunDef step) _) [env] ;;
          ⟨ θ3 ⟩ na <- angelic None _ ;;
          let a3 := persist__term a (θ1 ∘ θ2 ∘ θ3) in
          ⟨ θ4 ⟩ _  <- consume
                         (exec_instruction_epilogue i)
                         [env].["a"∷_ ↦ a3].["an"∷_ ↦ na] ;;
          pure (persist__term na θ4).

      Fixpoint sexec_block_addr (b : list AST) :
        ⊢ STerm ty_xlenbits -> STerm ty_xlenbits -> SHeapSpec (STerm ty_xlenbits) :=
        fun _ ainstr apc =>
          match b with
          | nil       => pure apc
          | cons i b' =>
              ⟨ θ1 ⟩ _    <- assert_formula (fun _ => amsg.empty)
                               (formula_relop bop.eq ainstr apc) ;;
              ⟨ θ2 ⟩ apc' <- sexec_instruction i (persist__term apc θ1) ;;
              sexec_block_addr b'
                (term_binop bop.bvadd
                   (persist__term ainstr (θ1 ∘ θ2))
                   (term_val ty_word bv_instrsize))
                apc'
          end.

      Definition sexec_triple_addr {Σ : LCtx}
        (req : Assertion (Σ ▻ ("a"::ty_xlenbits))) (b : list AST)
        (ens : Assertion (Σ ▻ ("a"::ty_xlenbits) ▻ ("an"::ty_xlenbits))) :
        ⊢ SHeapSpec Unit :=
        fun w =>
          ⟨ θ0 ⟩ δ <- demonic_ctx id Σ ;;
          ⟨ θ1 ⟩ a <- demonic (Some "a") _ ;;
          let δ1 := env.snoc (persist ( A:= Sub Σ) δ θ1) _ a in
          ⟨ θ2 ⟩ _ <- produce req δ1 ;;
          let a2 := persist__term a θ2 in
          ⟨ θ3 ⟩ na <- sexec_block_addr b a2 a2 ;;
          let δ3 := persist δ1 (θ2 ∘ θ3) in
          consume ens δ3.["an"∷ty_xlenbits ↦ na].

      (* This is a VC for triples, for doubles we probably need to talk
         about the continuation of a block. *)
      Definition sblock_verification_condition {Σ : LCtx}
        (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AST)
        (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) : ⊢ 𝕊 :=
        fun w =>
          (* SHeapSpec does not perform a leakcheck. We could include one here. *)
          SHeapSpec.run (sexec_triple_addr req b ens (w := w)).

    End Symbolic.

    Section Shallow.

      Import CStoreSpec (evalStoreSpec).
      Import CHeapSpec CHeapSpec.notations.

      Definition cexec_instruction (i : AST) :
        Val ty_xlenbits -> CHeapSpec (Val ty_xlenbits) :=
        let inline_fuel := 10%nat in
        fun a =>
          _ <- produce
                 (exec_instruction_prologue i)
                 [env].["a"∷_ ↦ a] ;;
          _ <- evalStoreSpec (cexec inline_fuel (FunDef step)) [env] ;;
          na <- angelic _ ;;
          _ <- consume
                 (exec_instruction_epilogue i)
                 [env].["a"∷ty_xlenbits ↦ a].["an"∷_ ↦ na] ;;
          pure na.

      Fixpoint cexec_block_addr (b : list AST) :
        Val ty_xlenbits -> Val ty_xlenbits -> CHeapSpec (Val ty_xlenbits) :=
        fun ainstr apc =>
          match b with
          | nil       => pure apc
          | cons i b' =>
              _ <- assert_formula (ainstr = apc) ;;
              apc' <- cexec_instruction i apc ;;
              cexec_block_addr b' (bv.add ainstr bv_instrsize) apc'
          end.

      Definition cexec_triple_addr {Σ : LCtx}
        (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AST)
        (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) :
        CHeapSpec unit :=
        lenv <- demonic_ctx Σ ;;
        a    <- demonic _ ;;
        _    <- produce req lenv.["a"∷ty_xlenbits ↦ a]  ;;
        na   <- cexec_block_addr b a a ;;
        consume ens lenv.["a"∷ty_xlenbits ↦ a].["an"∷ty_xlenbits ↦ na].

      Definition cblock_verification_condition {Σ : LCtx}
        (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AST)
        (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) : Prop :=
        (* CHeapSpec.run does not perform a leakcheck. We could include one here. *)
        CHeapSpec.run (cexec_triple_addr req b ens).

      Import (hints) CStoreSpec.

      #[export] Instance mono_cexec_instruction {i a} :
        Monotonic (MHeapSpec eq) (cexec_instruction i a).
      Proof. typeclasses eauto. Qed.

      #[export] Instance mono_cexec_block_addr {instrs ainstr apc} :
        Monotonic (MHeapSpec eq) (cexec_block_addr instrs ainstr apc).
      Proof. revert ainstr apc. induction instrs; cbn; typeclasses eauto. Qed.

    End Shallow.

    Section Relational.

      Import iris.proofmode.proofmode logicalrelation logicalrelation.notations.
      Import RiscvPmpSymbolicSoundness RiscvPmpSymbolicSoundness.StoreSpec.
      Import RiscvPmpSignature.HeapSpec.
      Import HeapSpec.

      Import RiscvPmpProgramLogic.

      Import RiscvPmpProgramLogic.ProgLog.

      Import RiscvPmpShallowSoundness.

      #[export] Instance rexec_instruction (i : AST) {w} :
        Related (RVal ty_xlenbits -> RHeapSpec (RVal ty_xlenbits))
            (cexec_instruction i) w
            (sexec_instruction (w := w) i).
      Proof.
        unfold cexec_instruction, sexec_instruction. solve_related.
      Qed.

      #[export] Instance rexec_block_addr (b : list AST) {w} :
        Related (RVal ty_xlenbits -> RVal ty_xlenbits -> RHeapSpec (RVal ty_xlenbits))
            (cexec_block_addr b) w
            (sexec_block_addr b (w := w)).
      Proof.
        revert w; induction b; intros w; cbn; solve_related.
      Qed.

      #[export] Instance rexec_triple_addr {Σ : LCtx}
        (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AST)
        (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) {w} :
        Related (RHeapSpec RUnit)
            (cexec_triple_addr req b ens) w
            (sexec_triple_addr req b ens (w := w)).
      Proof.
        unfold cexec_triple_addr, sexec_triple_addr. solve_related.
      Qed.

      Lemma rblock_verification_condition {Σ : LCtx}
        (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AST)
        (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) {w} :
        ⊢ RSat LogicalSoundness.RProp (w := w)
            (cblock_verification_condition req b ens)
            (sblock_verification_condition req b ens w).
      Proof.
        unfold cblock_verification_condition, sblock_verification_condition. solve_related.
      Qed.

    End Relational.

    Section Soundness.

      Import iris.base_logic.lib.iprop iris.proofmode.proofmode.
      Import RiscvPmpProgramLogic.
      Import RiscvPmpProgramLogic.ProgLog.
      Import RiscvPmpShallowSoundness.
      Import CHeapSpec.

      (* we hardcode reasoning about the right execution for now *)

      #[local] Notation "a '↦' t" := (reg_pointsTo a t) (at level 70).
      #[local] Notation "a '↦ₘ' t" := (interp_ptsto a t) (at level 70).

      Context {Σ} {GS : sailGS Σ}.

      Definition exec_instructions_prologue (a : Val ty_xlenbits) (l : list AST) : iProp Σ :=
        pc ↦ a ∗
        ptsto_instrs a l ∗
        ∃ v, nextpc ↦ v.

      Definition exec_instructions_epilogue (a an : Val ty_xlenbits) (l : list AST) : iProp Σ :=
        pc ↦ an ∗
        ptsto_instrs a l ∗
        ∃ v, nextpc ↦ v.

      Fixpoint step_n (instrs : list AST) (ainstr apc : Val ty_xlenbits) (POST : Val ty_xlenbits -> iProp Σ) : iProp Σ :=
        match instrs with
        | []   => POST apc
        | i :: instrs => ⌜ainstr = apc⌝
                  ∗ (asn.interpret (exec_instruction_prologue i) [env].["a"∷ty_xlenbits ↦ ainstr]  -∗
                     semTWP [env] fun_step
                       (λ v δ, match v with
                               | inl v => ∃ na, asn.interpret (exec_instruction_epilogue i) [env].["a"∷ty_xlenbits ↦ ainstr].["an"∷ty_xlenbits ↦ na] ∗ step_n instrs (bv.add ainstr bv_instrsize) na POST
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
          iApply (semTWP_mono with "H").
          iIntros ([] ?); auto.
          iIntros "H". iDestruct "H" as "(%na & $ & H)".
          iApply ("IHinstrs" with "H HPOSTS").
      Qed.

      Definition stepTriple (l : list AST) (a apc : Val ty_xlenbits)
        (PRE : Val ty_xlenbits -> iProp Σ) (POST : Val ty_xlenbits -> Val ty_xlenbits -> iProp Σ) : iProp Σ :=
        PRE a -∗
          step_n l a apc (POST a).

      Definition semTripleOneInstrStep (PRE : Val ty_xlenbits -> iProp Σ) (instr : AST) (POST : Val ty_xlenbits -> Val ty_xlenbits -> iProp Σ) (a : Val ty_xlenbits) : iProp Σ :=
        stepTriple [instr] a a PRE POST.

      Definition semTripleBlock (PRE : Val ty_xlenbits -> iProp Σ) (a : Val ty_xlenbits) (instrs : list AST) (POST : Val ty_xlenbits -> Val ty_xlenbits -> iProp Σ) : iProp Σ :=
        stepTriple instrs a a PRE POST.

      Lemma sound_exec_instruction {instr} a Φ (h : SCHeap) :
        cexec_instruction instr a Φ h ->
        ⊢ semTripleOneInstrStep (λ a, interpret_scheap h) instr
          (λ a an, ∃ h' : SCHeap, interpret_scheap h' ∧ ⌜Φ an h'⌝) a.
      Proof.
        cbv [cexec_instruction exec_instruction_prologue bind produce demonic
               produce_chunk lift_purespec CPureSpec.produce_chunk CPureSpec.pure
               CPureSpec.demonic CStoreSpec.evalStoreSpec].
        cbn - [consume].
        iIntros (Hverif) "Hheap". iSplitR; first auto.
        iIntros "(Hpc & Hinstr & [%npc Hnpc])". cbn.
        specialize (Hverif npc). apply sound_cexec in Hverif.
        iApply (semTWP_mono with "[-]").
        iApply (sound_tstm (callgraph.mkNode step) TforeignSemBlockVerif lemSemBlockVerif Hverif with "[] [$]").
        - apply callgraph.InvokedByStmList_WellFormed_aux; auto.
        - iIntros (n R) "!>". iApply TcontractsSound. iPureIntro.
          apply (Transitive_Closure.Acc_inv_trans _ _ _ _ R).
          apply accessible_step.
        - iIntros ([v|m] _); last done; iIntros "(%h1 & Hh1 & %Htrip)". clear Hverif.
          destruct Htrip as [an Htrip].
          iPoseProof (consume_sound _ _ Htrip with "Hh1")
            as "[(Hpc & Hinstr & Han) (%h2 & Hh2 & %HΦ)]".
          iExists an. iFrame "Hpc Hinstr Han".
          iExists h2. by iFrame.
      Qed.

      Lemma sound_exec_block_addr {instrs ainstr apc} Φ (h : SCHeap) :
        cexec_block_addr instrs ainstr apc Φ h ->
        ⊢ (stepTriple instrs ainstr apc (λ a, interpret_scheap h)
             (λ a an, ∃ h', interpret_scheap h' ∧ ⌜Φ an h'⌝))%I.
      Proof.
        revert ainstr apc Φ h.
        iInduction instrs as [|instr instrs]; cbn; iIntros (ainstr apc Φ h);
          cbv [bind assert_formula lift_purespec CPureSpec.assert_formula
                 CPureSpec.assert_pathcondition pure CPureSpec.pure].
        - iIntros (HΦ) "Hh". iFrame "Hh". done.
        - iIntros ([-> Hverif%sound_exec_instruction]).
          unfold semTripleOneInstrStep, semTTriple in Hverif.
          iIntros "Hh". iSplitR; first auto.
          iIntros "(Hpc & Hinstr & Hnpc)".
          iPoseProof (Hverif with "[$]") as "(_ & H)".
          cbn. iSpecialize ("H" with "[$]").
          iApply (semTWP_mono with "H").
          iIntros ([] ?); auto.
          iIntros "(%an & Hepi & %h' & Hh' & %Hexec)".
          iFrame "Hepi".
          destruct instrs. cbn.
          + iExists h'. now iFrame "Hh'".
          + remember Hexec as Hexec'.
            cbn in Hexec'.
            cbv [bind assert_formula lift_purespec CPureSpec.assert_formula
                   CPureSpec.assert_pathcondition pure CPureSpec.pure] in Hexec'.
            destruct Hexec' as [<- Hexec']. clear HeqHexec' Hexec'.
            iSpecialize ("IHinstrs" $! _ _ _ _ Hexec with "[$]").
            iApply (step_n_mono with "IHinstrs"). auto.
      Qed.

      Lemma sound_cexec_triple_addr {Γ : LCtx} {pre post instrs} {ι : Valuation Γ} {a : Val ty_xlenbits} :
        cexec_triple_addr pre instrs post (fun _ _ => True) []%list ->
        ⊢ semTripleBlock (λ a : Val ty_xlenbits, asn.interpret pre (ι.[("a"::ty_xlenbits) ↦ a])) a instrs
            (λ a na : Val ty_xlenbits, asn.interpret post (ι.[("a"::ty_xlenbits) ↦ a].[("an"::ty_xlenbits) ↦ na])).
      Proof.
        cbv [cexec_triple_addr bind demonic_ctx demonic CPureSpec.demonic lift_purespec].
        iIntros (Htrip). unfold semTripleBlock, stepTriple.
        rewrite CPureSpec.wp_demonic_ctx in Htrip.
        specialize (Htrip ι a). apply produce_sound in Htrip.
        destruct instrs as [|instr instrs].
        - iIntros "Hpre".
          iPoseProof (Htrip with "[$] Hpre") as "(%h2 & [Hh2 %Hexec])". clear Htrip.
          apply sound_exec_block_addr in Hexec.
          iPoseProof (Hexec with "[$]") as "H". clear Hexec.
          iDestruct "H" as "(%h' & Hh' & %Hconsume)".
          apply consume_sound in Hconsume.
          iDestruct (Hconsume with "Hh'") as "($ & _)".
        - iIntros "Hpre".
          iPoseProof (Htrip with "[$] Hpre") as "(%h2 & [Hh2 %Hexec])". clear Htrip.
          apply sound_exec_block_addr in Hexec.
          iPoseProof (Hexec with "[$]") as "H". clear Hexec.
          iApply (step_n_mono with "H").
          iIntros (an) "(%h' & Hh' & %Hconsume)".
          apply consume_sound in Hconsume.
          iDestruct (Hconsume with "Hh'") as "($ & _)".
      Qed.

      Lemma sound_cblock_verification_condition {Γ pre post a instrs} :
        cblock_verification_condition pre instrs post ->
        forall ι : Valuation Γ,
        ⊢ semTripleBlock (fun a => asn.interpret pre (ι.[("a"::ty_xlenbits) ↦ a]))
            a instrs
            (fun a na => asn.interpret post (ι.[("a"::ty_xlenbits) ↦ a].[("an"::ty_xlenbits) ↦ na])).
      Proof.
        intros Hverif ι.
        now apply sound_cexec_triple_addr.
      Qed.

      Lemma sound_sblock_verification_condition {Γ pre post a instrs} :
        safeE (postprocess2 (sblock_verification_condition pre instrs post wnil)) ->
        forall ι : Valuation Γ,
        ⊢ semTripleBlock (fun a => asn.interpret pre (ι.[("a"::ty_xlenbits) ↦ a]))
            a instrs
            (fun a na => asn.interpret post (ι.[("a"::ty_xlenbits) ↦ a].[("an"::ty_xlenbits) ↦ na])).
      Proof.
        intros Hverif ι.
        apply sound_cexec_triple_addr.
        apply (safeE_safe env.nil), postprocess2_sound in Hverif.
        apply LogicalSoundness.psafe_safe in Hverif; [|done].
        revert Hverif.
        apply rexec_triple_addr.
        - easy.
        - easy.
        - easy.
        - constructor.
      Qed.

      Lemma WP_loop_semTTriple : ∀ PRE POST,
        PRE -∗
        semTTriple [env] PRE fun_step POST -∗
        (∀ v1 δ1, POST v1 δ1 -∗ WP_loop) -∗
        WP_loop.
      Proof.
        iIntros (PRE POST) "HPRE Htrip Hk".
        unfold semTTriple.
        iSpecialize ("Htrip" with "HPRE").
        unfold WP_loop at 2.
        iApply semWP_fun_loop. iSplit; last done. iIntros (Γon δon).
        iApply semWP_seq.
        iApply semWP_call_inline.
        iPoseProof (semTWP_semWP with "Htrip") as "Htrip".
        iApply (semWP_mono with "Htrip").
        iIntros ([] ?) "H"; auto.
        iSpecialize ("Hk" with "H").
        now iApply semWP_call_inline.
      Qed.

      Lemma WP_loop_semTripleBlock : ∀ PRE a instrs POST,
        (exec_instructions_prologue a instrs) -∗
        (PRE a) -∗
        semTripleBlock PRE a instrs POST -∗
        (∀ an, POST a an ∗ exec_instructions_epilogue a an instrs -∗ WP_loop) -∗
        WP_loop.
      Proof.
        iIntros (PRE a instrs).
        iRevert (PRE a).
        iInduction instrs as [|instr instrs] "IH";
          iIntros (PRE a POST) "Hpro HPRE Htrip Hk".
        - cbn. iSpecialize ("Htrip" with "HPRE").
          iApply ("Hk" with "[$Htrip $Hpro]").
        - cbn. iDestruct ("Htrip" with "HPRE") as "(_ & Htrip)".
          iDestruct "Hpro" as "(Hpc & Hinstrs & Hnpc)"; cbn.
          iDestruct "Hinstrs" as "(Hinstr & Hinstrs)".
          iSpecialize ("Htrip" with "[$]").
          unfold WP_loop at 4.
          iApply semWP_fun_loop. iSplit; last done. iIntros (Γon δon).
          iApply semWP_seq.
          iApply semWP_call_inline. simpl.
          rewrite semTWP_semWP.
          iApply (semWP_mono with "Htrip").
          iIntros ([] ?) "H"; auto.
          iDestruct "H" as "(%na & (Hpc & Hinstr & Hnpc) & Htrip)".
          iApply semWP_call_inline.
          destruct instrs.
          + cbn. now iApply ("Hk" with "[$Htrip $Hpc $Hinstr $Hnpc]").
          + cbn. iDestruct "Htrip" as "(<- & Htrip)".
            iApply ("IH" $! (λ _, True)%I _ (λ a' an, ⌜a' = bv.add a bv_instrsize⌝ ∗ POST a an)%I with "[$Hpc $Hinstrs $Hnpc] [] [Htrip]");
              auto.
            { iIntros "_". iSplitR; first auto. iIntros "H".
              iSpecialize ("Htrip" with "H"). iApply (semTWP_mono with "Htrip").
              iIntros ([] ?); auto.
              iIntros "(%na & Hepi & H)". iExists na. iFrame "Hepi".
              iApply (step_n_mono with "H").
              iIntros (an) "$"; auto. }
            iIntros (an) "([-> HPOST] & Hpc & Hinstrs & Hnpc)".
            iApply ("Hk" with "[$HPOST $Hpc $Hnpc $Hinstr $Hinstrs]").
      Qed.
    End Soundness.

  End BlockVerificationDerived.

  Section AnnotatedBlockVerification.

    Section Debug.

      Import option.notations.

      Record DebugBlockver (Σ : LCtx) : Type :=
        MkDebugBlockver
          { debug_blockver_pathcondition          : PathCondition Σ;
            debug_blockver_heap                   : SHeap Σ;
            debug_blockver_string                 : string;
          }.
      Record EDebugBlockver : Type :=
        MkEDebugBlockver
          { edebug_blockver_pathcondition          : list EFormula;
            edebug_blockver_heap                   : list EChunk;
            edebug_blockver_string                 : string;
          }.
      #[export] Instance EraseDebugBlockVer : Erase DebugBlockver EDebugBlockver :=
        fun _ '(MkDebugBlockver pathc h s) => MkEDebugBlockver (erase pathc) (erase h) s.
      #[export] Instance SubstDebugBlockver : Subst DebugBlockver :=
        fun Σ0 d Σ1 ζ01 =>
          match d with
          | MkDebugBlockver pc1 h s => MkDebugBlockver (subst pc1 ζ01) (subst h ζ01) s
          end.

      #[export] Instance SubstSUDebugBlockver `{SubstUniv Sb} : SubstSU Sb DebugBlockver :=
        fun Σ0 Σ1 d ζ01 =>
          match d with
          | MkDebugBlockver pc1 h s => MkDebugBlockver (substSU pc1 ζ01) (substSU h ζ01) s
          end.

      #[export] Instance SubstSULawsDebugBlockver `{SubstUnivLaws Sb} :
        SubstSULaws Sb DebugBlockver.
      Proof.
        intros ? ? ? ? ? [pc h]; cbn; f_equal; now apply substSU_trans.
      Qed.

      #[export] Instance SubstLawsDebugBlockver : SubstLaws DebugBlockver.
      Proof.
        constructor.
        - intros ? []; cbn; now rewrite ?subst_sub_id.
        - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
      Qed.

      #[export] Instance OccursCheckDebugBlockver : OccursCheck DebugBlockver :=
        fun Σ x xIn d =>
          match d with
          | MkDebugBlockver pc1 h s =>
              pc' <- occurs_check xIn pc1 ;;
              h'  <- occurs_check xIn h ;;
              Some (MkDebugBlockver pc' h' s)
          end.

      (* #[export] Instance GenOccursCheckDebugBlockver : GenOccursCheck DebugBlockver := *)
      (*   fun Σ d => *)
      (*     match d with *)
      (*     | MkDebugBlockver pc1 h => *)
      (*         liftBinOp (fun _ pc' h' => MkDebugBlockver pc' h') *)
      (*           (gen_occurs_check pc1) (gen_occurs_check h) *)
      (*     end. *)

    End Debug.

    Import RiscvPmpBlockVerifSpec.

    Section Symbolic.

      Import ModalNotations.
      Import SHeapSpec.
      Import SHeapSpec.notations.
      Import asn.notations.

      Fixpoint sexec_annotated_block_addr (b : list AnnotInstr) :
        ⊢ STerm ty_xlenbits -> STerm ty_xlenbits -> SHeapSpec (STerm ty_xlenbits) :=
        fun w0 ainstr apc =>
          match b with
          | nil       => pure apc
          | cons instr b' =>
              match instr with
              | AnnotAST i =>
                  ⟨ θ1 ⟩ _    <- assert_formula
                                   (fun _ => amsg.empty)
                                   (formula_relop bop.eq ainstr apc) ;;
                  ⟨ θ2 ⟩ apc' <- sexec_instruction i (persist__term apc θ1) ;;
                  sexec_annotated_block_addr b'
                    (term_binop bop.bvadd
                       (persist__term ainstr (θ1 ∘ θ2))
                       (term_val ty_word bv_instrsize))
                    apc'
              | AnnotDebugBreak =>
                  error
                    (fun (h0 : SHeap w0) =>
                       amsg.mk
                         {| debug_blockver_pathcondition := wco w0;
                            debug_blockver_heap := h0;
                            debug_blockver_string := "Blockver encountered an AnnotDebugBreak. Failing the verification."
                         |})
              | AnnotLemmaInvocation l es =>
                  let args := seval_exps [env] es in
                  ⟨ θ1 ⟩ _ <- call_lemma (lemma_environment l) args ;;
                  sexec_annotated_block_addr b'
                    (persist__term ainstr θ1)
                    (persist__term apc θ1)
              end
          end.

      Definition sexec_annotated_block_triple_addr {Σ : LCtx}
        (req : Assertion (Σ ▻ ("a"::ty_xlenbits))) (b : list AnnotInstr)
        (ens : Assertion (Σ ▻ ("a"::ty_xlenbits) ▻ ("an"::ty_xlenbits))) :
        ⊢ SHeapSpec Unit :=
        fun _ =>
          ⟨ θ1 ⟩ lenv1 <- demonic_ctx id Σ ;;
          ⟨ θ2 ⟩ a2 <- demonic (Some "a") _ ;;
          let lenv2 := env.snoc (persist (A := Sub Σ) lenv1 θ2) _ a2 in
          ⟨ θ3 ⟩ _ <- produce req lenv2 ;;
          let a3 := persist__term a2 θ3 in
          ⟨ θ4 ⟩ na <- sexec_annotated_block_addr b a3 a3 ;;
          let lenv4 := persist lenv2 (θ3 ∘ θ4) in
          consume ens lenv4.["an"∷ty_xlenbits ↦ na].

      (* This is a VC for triples, for doubles we probably need to talk
       about the continuation of a block. *)
      Definition sannotated_block_verification_condition {Σ : LCtx}
        (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AnnotInstr)
        (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) : ⊢ 𝕊 :=
        (* SHeapSpec does not perform a leakcheck. We could include one here. *)
        fun w => SHeapSpec.run (sexec_annotated_block_triple_addr req b ens (w := w)).

    End Symbolic.

    Section Shallow.

      Import CHeapSpec CHeapSpec.notations.

      Fixpoint cexec_annotated_block_addr (b : list AnnotInstr) :
        Val ty_xlenbits -> Val ty_xlenbits -> CHeapSpec (Val ty_xlenbits) :=
        fun ainstr apc =>
          match b with
          | nil       => pure apc
          | cons instr b' =>
              match instr with
              | AnnotAST i =>
                  _ <- assert_formula (ainstr = apc) ;;
                  apc' <- cexec_instruction i apc ;;
                  cexec_annotated_block_addr b' (bv.add ainstr bv_instrsize) apc'
              | AnnotDebugBreak => debug error
              | AnnotLemmaInvocation l es =>
                  let args := evals es [env] in
                  _ <- call_lemma (lemma_environment l) args ;;
                  cexec_annotated_block_addr b' ainstr apc
              end
          end.

      Definition cexec_annotated_block_triple_addr {Σ}
        (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AnnotInstr)
        (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) :
        CHeapSpec unit :=
        lenv <- demonic_ctx Σ ;;
        a  <- demonic _ ;;
        _  <- produce req lenv.["a"∷ty_xlenbits ↦ a]  ;;
        na <- cexec_annotated_block_addr b a a ;;
        consume ens lenv.["a"∷ty_xlenbits ↦ a].["an"∷ty_xlenbits ↦ na].

      Definition cannotated_block_verification_condition {Σ : LCtx}
        (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AnnotInstr)
        (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) : Prop :=
        (* SHeapSpec does not perform a leakcheck. We could include one here. *)
        CHeapSpec.run (cexec_annotated_block_triple_addr req b ens).

      #[export] Instance mono_cexec_annotated_block_addr {instrs ainstr apc} :
        Monotonic (MHeapSpec eq) (cexec_annotated_block_addr instrs ainstr apc).
      Proof.
        revert ainstr apc.
        induction instrs; cbn; try typeclasses eauto.
        destruct a; typeclasses eauto.
      Qed.

    End Shallow.

    Section Relational.

      Import RiscvPmpSymbolicSoundness.

      Import RiscvPmpShallowSoundness.
      Import StoreSpec.
      Import logicalrelation logicalrelation.notations.
      Import proofmode.
      Import iris.proofmode.proofmode.
      Import RiscvPmpSignature.HeapSpec.

      #[export] Instance rexec_annotated_block_addr (b : list AnnotInstr) {w} :
        Related (RVal ty_xlenbits -> RVal ty_xlenbits -> RHeapSpec (RVal ty_xlenbits))
            (cexec_annotated_block_addr b) w
            (sexec_annotated_block_addr b (w := w)).
      Proof.
        revert w; induction b as [|instr b]; intros w; cbn; solve_related.
      Qed.

      Lemma rexec_annotated_block_triple_addr {Σ}
        (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AnnotInstr)
        (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) {w} :
        Related (RHeapSpec RUnit)
            (cexec_annotated_block_triple_addr req b ens) w
            (sexec_annotated_block_triple_addr req b ens (w := w)).
      Proof.
        unfold cexec_annotated_block_triple_addr, sexec_annotated_block_triple_addr. solve_related.
      Qed.

      Lemma rannotated_block_verification_condition {Σ}
        (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AnnotInstr)
        (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) {w} :
        ⊢ ℛ⟦LogicalSoundness.RProp⟧
            (cannotated_block_verification_condition req b ens)
            (sannotated_block_verification_condition req b ens w).
      Proof.
        iApply HeapSpec.refine_run.
        iApply rexec_annotated_block_triple_addr.
      Qed.

    End Relational.

    Section Soundness.

      Import iris.base_logic.lib.iprop iris.proofmode.proofmode.
      Import RiscvPmpProgramLogic.
      Import RiscvPmpProgramLogic.ProgLog.
      Import RiscvPmpShallowSoundness.
      Import CHeapSpec.

      Context {Σ} {GS : sailGS Σ} {rG : trivGS Σ}.

      Lemma sound_exec_annotated_block_addr {instrs ainstr apc} (h : SCHeap) (POST : Val ty_xlenbits -> iProp Σ) :
        LemmaSem ->
        cexec_annotated_block_addr instrs ainstr apc (fun res h' => interpret_scheap h' ⊢ POST res) h ->
        (⊢ (stepTriple (filter_AST instrs) ainstr apc (λ a, interpret_scheap h) (λ a an, POST an)))%I.
      Proof.
        intros lemSem.
        revert ainstr apc h POST.
        induction instrs as [|instr instrs]; cbn; intros ainstr apc h POST;
          cbv [bind assert_formula lift_purespec CPureSpec.assert_formula
                 CPureSpec.assert_pathcondition pure CPureSpec.pure]; auto.
        - iIntros (H) "Hh". iApply (H with "Hh").
        - destruct instr as [instr | | Δ lem es].
          + intros [-> Hverif%sound_exec_instruction].
            cbn. iIntros "Hh".
            iPoseProof (Hverif with "Hh") as "H".
            iApply (step_n_mono with "H").
            iIntros (an) "(%h' & Hh' & %Hexec)".
            iPoseProof (IHinstrs _ _ _ _ Hexec) as "IH".
            destruct (filter_AST instrs).
            * cbn. now iApply "IH".
            * now iSpecialize ("IH" with "Hh'").
          + iIntros ([]).
          + intros Hexec.
            apply call_lemma_sound in Hexec.
            pose proof (lemSem _ lem) as H. cbn in H.
            destruct (lemma_environment lem) as [lvars lpats req ens].
            destruct Hexec as [lvars' lpats' req' ens' Hexec].
            cbn. destruct (filter_AST instrs) eqn:Einstrs.
            * cbn. iIntros "Hh". iPoseProof (Hexec with "Hh") as "H".
              iDestruct "H" as "(%ι & %Hes & Hreq & H)".
              cbn in H.
              iPoseProof (H ι with "Hreq") as "Hens".
              iDestruct ("H" with "Hens") as "(%h' & Hh' & %Hexec')".
              iPoseProof (IHinstrs _ _ _ _ Hexec') as "H".
              iApply ("H" with "Hh'").
            * cbn. iIntros "Hh".
              iPoseProof (Hexec with "Hh") as "H".
              iDestruct "H" as "(%ι & %Hes & Hreq & H)".
              cbn in H.
              iPoseProof (H ι with "Hreq") as "Hens".
              iDestruct ("H" with "Hens") as "(%h' & Hh' & %Hexec')".
              iPoseProof (IHinstrs _ _ _ _ Hexec') as "H".
              iSpecialize ("H" with "Hh'").
              now simpl.
      Qed.

      Lemma sound_cexec_annotated_block_triple_addr {Γ pre post a instrs} :
        LemmaSem ->
        (cexec_annotated_block_triple_addr (Σ := Γ) pre instrs post (λ _ _ , True) []%list) ->
        forall ι : Valuation Γ,
          ⊢ semTripleBlock (λ a : Val ty_xlenbits, asn.interpret pre (ι.[("a"::ty_xlenbits) ↦ a])) a (filter_AST instrs)
            (λ a na : Val ty_xlenbits, asn.interpret post (ι.[("a"::ty_xlenbits) ↦ a].[("an"::ty_xlenbits) ↦ na])).
      Proof.
        intros lemSem Hexec ι.
        hnf in Hexec.
        rewrite CPureSpec.wp_demonic_ctx in Hexec.
        specialize (Hexec ι a).
        unfold bind in Hexec.
        destruct (filter_AST instrs) as [|ainstr ainstrs] eqn:Einstrs.
        - cbn. iIntros "Hpre".
          iPoseProof (produce_sound _ _ Hexec with "[//] [$Hpre]") as "(%h2 & Hh2 & %Hexec')".
          iRevert "Hh2".
          iAssert (stepTriple (filter_AST instrs) a a (λ _, interpret_scheap h2) (λ _ an, asn.interpret post ι.["a"∷ty_xlenbits ↦ a].["an"∷ty_xlenbits ↦ an]) -∗
                   (interpret_scheap h2 -∗ asn.interpret post ι.["a"∷ty_xlenbits ↦ a].["an"∷ty_xlenbits ↦ a]))%I as "Himpl".
          { rewrite Einstrs. cbn. iIntros "$". }
          iApply "Himpl". iClear "Himpl".
          iApply (sound_exec_annotated_block_addr (apc := a) h2); auto.
          eapply mono_cexec_annotated_block_addr.
          intros ? ? <- h3 Hcons.
          iIntros "Hh3".
          iPoseProof (consume_sound _ _ Hcons with "Hh3") as "[Hcons _]".
          iFrame.
          apply Hexec'.
        - cbn. iIntros "Hpre". iSplitR; first auto.
          iPoseProof (produce_sound _ _ Hexec with "[//] [$Hpre]") as "(%h2 & Hh2 & %Hexec')".
          clear Hexec.
          iRevert "Hh2".
          iAssert (stepTriple (filter_AST instrs) a a (λ _, interpret_scheap h2) (λ _ an, asn.interpret post ι.["a"∷ty_xlenbits ↦ a].["an"∷ty_xlenbits ↦ an]) -∗
                   interpret_scheap h2 -∗
                   asn.interpret (exec_instruction_prologue ainstr) [env].["a"∷ty_xlenbits ↦ a] -∗
                   semTWP [env] fun_step
                       (λ (v : IVal ty.unit) (_ : NamedEnv Val [ctx]),
                         match v with
                         | inl _ =>
                           ∃ na : bv 32,
                             asn.interpret (exec_instruction_epilogue ainstr) [env].["a"∷ty_xlenbits ↦ a].["an"∷ty_xlenbits ↦ na] ∗
                             step_n ainstrs (bv.add a bv_instrsize) na
                               (λ an : bv 32, asn.interpret post ι.["a"∷ty_xlenbits ↦ a].["an"∷ty_xlenbits ↦ an])
                         | inr _ => False
                         end))%I as "Himpl".
          { rewrite Einstrs. cbn. iIntros "H Hh2 Hpro".
            iDestruct ("H" with "Hh2") as "(_ & H)".
            now iSpecialize ("H" with "Hpro"). }
          iApply "Himpl". iClear "Himpl".
          iApply (sound_exec_annotated_block_addr (apc := a) h2); auto.
          eapply mono_cexec_annotated_block_addr.
          intros ? ? <- h3 Hcons.
          iIntros "Hh3".
          iPoseProof (consume_sound _ _ Hcons with "Hh3") as "[Hcons _]".
          iFrame.
          apply Hexec'.
      Qed.

      Lemma sound_sannotated_block_verification_condition {Γ pre post a instrs} :
        LemmaSem ->
        safeE (postprocess2 (sannotated_block_verification_condition (Σ := Γ)
                               pre instrs post wnil)) ->
        forall ι : Valuation Γ,
          ⊢ semTripleBlock (fun a => asn.interpret pre (ι.[("a"::ty_xlenbits) ↦ a]))
              a (filter_AST instrs) (fun a na => asn.interpret post (ι.[("a"::ty_xlenbits) ↦ a].[("an"::ty_xlenbits) ↦ na])).
      Proof.
        unfold sannotated_block_verification_condition, SHeapSpec.run.
        intros lemSem Hverif ι.
        apply sound_cexec_annotated_block_triple_addr; auto.
        apply (safeE_safe env.nil), postprocess2_sound in Hverif.
        apply LogicalSoundness.psafe_safe in Hverif; [|done].
        revert Hverif.
        apply rexec_annotated_block_triple_addr.
        - easy.
        - easy.
        - easy.
        - constructor.
      Qed.
    End Soundness.

  End AnnotatedBlockVerification.

End RiscvPmpBlockVerifTotalVerifier.
