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

From Stdlib Require Import
     Bool.Bool
     Program.Tactics
     ZArith.ZArith
     Strings.String
     Classes.Morphisms
     Classes.RelationClasses
     Classes.Morphisms_Prop
     Classes.Morphisms_Relations.
Require Import Basics.

From Stdlib Require Lists.List.

From Equations Require Import
     Equations.

From Katamaran Require Import
     Signature
     Program
     Tactics
     Hoare
     MicroSail.ShallowExecutor
     MicroSail.SymbolicExecutor.


Set Implicit Arguments.

Import ctx.notations.
Import env.notations.

Module RefineExecOn
  (Import B    : Base)
  (Import SIG  : Signature B)
  (Import PROG : Program B)
  (Import PLOG : ProgramLogic B SIG PROG)

  (Import SHAL : ShallowExecOn B SIG PROG PLOG)
  (Import SYMB : SymbolicExecOn B SIG PROG PLOG).

  Import ModalNotations.
  Import SymProp.
  Import logicalrelation logicalrelation.notations.
  Import LogicalSoundness.
  Import proofmode.
  Import iris.proofmode.environments.
  Import iris.proofmode.proofmode.

  Definition RStore (Γ : PCtx) : Rel (SStore Γ) (CStore Γ) :=
    RInst (SStore Γ) (CStore Γ).

  Module StoreT.
    Import PureSpec.
    Import HeapSpec.

    (* Instance search does not unfold the concrete operations, so their
       instances are indexed, and tried, by their head. *)
    #[export] Typeclasses Opaque CStoreT.assign CStoreT.bind
      CStoreT.block CStoreT.eval_exp CStoreT.eval_exps
      CStoreT.evalStoreT CStoreT.get_local CStoreT.lift_heapspec
      CStoreT.lift_purespec CStoreT.pure CStoreT.pushpop
      CStoreT.pushspops CStoreT.put_local.

    Definition RStoreT Γ1 Γ2 `(R : Rel AT A) :
      Rel (SStoreT Γ1 Γ2 AT) (CStoreT Γ1 Γ2 A) :=
      □ᵣ (R -> RStore Γ2 -> RHeap -> ℙ) -> RStore Γ1 -> RHeap -> ℙ.

    (* Abbreviations, so that hypotheses are local [Related] instances. *)
    Abbreviation RefineExecCall cexec_call sexec_call :=
      (forall Δ τ (f : 𝑭 Δ τ) w,
        Related (RStore Δ -> RHeapSpec (RVal τ))
          ((cexec_call : SHAL.ExecCall) Δ τ f) w ((sexec_call : SYMB.ExecCall) Δ τ f w)).
    Abbreviation RefineExecCallForeign cexec_call_foreign sexec_call_foreign :=
      (forall Δ τ (f : 𝑭𝑿 Δ τ) w,
        Related (RStore Δ -> RHeapSpec (RVal τ))
          ((cexec_call_foreign : SHAL.ExecCallForeign) Δ τ f) w
          ((sexec_call_foreign : SYMB.ExecCallForeign) Δ τ f w)).
    Abbreviation RefineExecLemma cexec_lemma sexec_lemma :=
      (forall Δ (l : 𝑳 Δ) w,
        Related (RStore Δ -> RHeapSpec RUnit)
          ((cexec_lemma : SHAL.ExecLemma) Δ l) w ((sexec_lemma : SYMB.ExecLemma) Δ l w)).
    Abbreviation RefineExecFail cexec_fail sexec_fail :=
      (forall Γ τ (s : Val ty.string) w,
        Related (RStoreT Γ Γ (RVal τ))
          ((cexec_fail : SHAL.ExecFail) Γ τ s) w ((sexec_fail : SYMB.ExecFail) Γ τ s w)).
    Abbreviation RefineExec cexec sexec :=
      (forall Γ τ (s : Stm Γ τ) w,
        Related (RStoreT Γ Γ (RVal τ))
          ((cexec : SHAL.Exec) Γ τ s) w ((sexec : SYMB.Exec) Γ τ s w)).

    #[export] Instance refine_evalStoreT {Γ1 Γ2} `{RA : Rel SA CA} {w : World} :
      Related (RStoreT Γ1 Γ2 RA -> RStore Γ1 -> RHeapSpec RA)
        CStoreT.evalStoreT w (SStoreT.evalStoreT (w := w)).
    Proof.
      unfold SStoreT.evalStoreT, CStoreT.evalStoreT.
      iIntros (ss tss) "Hss %s %ts Hs %k %ks Hk %h %hs Hh Hsym".
      iApply ("Hss" with "[Hk] Hs Hh Hsym").
      iIntros (w' ω).
      iSpecialize ("Hk" $! _ ω).
      iModIntro.
      iIntros (a ta) "Ha %s2 %ts2 Hs2 %h2 %th2 Hh2".
      now iApply ("Hk" with "Ha Hh2").
    Qed.

    #[export] Instance refine_lift_heapspec {Γ} `(R : Rel AT A) {w : World}:
      Related (RHeapSpec R -> RStoreT Γ Γ R)
          CStoreT.lift_heapspec w (SStoreT.lift_heapspec (w := w)).
    Proof. unfold CStoreT.lift_heapspec, SStoreT.lift_heapspec, RStoreT; solve_related. Qed.

    #[export] Instance refine_pure `{R : Rel AT A} {Γ} {w : World} :
      Related (R -> RStoreT Γ Γ R) CStoreT.pure w (SStoreT.pure (w := w)).
    Proof. unfold CStoreT.pure, SStoreT.pure, RStoreT; solve_related. Qed.

    Lemma refine_bind `{RA : Rel AT A, RB : Rel BT B} {Γ1 Γ2 Γ3} {w : World} :
      ⊢ ℛ⟦RStoreT Γ1 Γ2 RA -> □ᵣ(RA -> RStoreT Γ2 Γ3 RB) -> RStoreT Γ1 Γ3 RB⟧
        CStoreT.bind (SStoreT.bind (w := w)).
    Proof. unfold CStoreT.bind, SStoreT.bind, RStoreT; solve_related. Qed.

    #[export] Instance refine_compat_bind {Γ1 Γ2 Γ3 : PCtx} `{RA : Rel AT A} `{RB : Rel BT B} {w} : Related (RStoreT Γ1 Γ2 RA -> (□ᵣ (RA -> RStoreT Γ2 Γ3 RB)) -> RStoreT Γ1 Γ3 RB) CStoreT.bind w (SStoreT.bind (w := w)) | (Related _ _ _ SStoreT.bind) :=
      refine_bind.

    #[export] Instance refine_block {Γ1 Γ2} `{R : Rel AT A} {w : World} :
      Related (RStoreT Γ1 Γ2 R) CStoreT.block w (SStoreT.block (w := w)).
    Proof.
      iIntros (k ks) "Hk %s %ss Hs %h %hs Hh _".
      now iPureIntro.
    Qed.

    #[export] Instance refine_error `{Subst M, OccursCheck M, R : Rel AT A} {Γ1 Γ2} {w : World}
      (cm : CStoreT Γ1 Γ2 A) :
      Related (RMsg _ (RStoreT Γ1 Γ2 R)) cm w (SStoreT.error (w := w)).
    Proof.
      iIntros (msg k ks) "Hk %s %ss Hs %h %hs Hh []".
    Qed.

    Lemma refine_debug `{R : Rel AT A}
      {Γ1 Γ2} {w0 : World} {f ms mc} :
      ℛ⟦RStoreT Γ1 Γ2 R⟧ mc ms ⊢
                   ℛ⟦RStoreT Γ1 Γ2 R⟧ mc (@SStoreT.debug AT Γ1 Γ2 w0 f ms).
    Proof.
      iIntros "Hm %K %Ks HK %s %ss Hs %h %hs Hh HSP".
      iApply ("Hm" with "HK Hs Hh [HSP]").
      now iApply elim_debugPred.
    Qed.

    #[export] Instance refine_compat_debug `{R : Rel AT A} {Γ1 Γ2} {w0 : World} {f} {mc ms} :
      RelatedFrom (RStoreT Γ1 Γ2 R) mc w0 (@SStoreT.debug AT Γ1 Γ2 w0 f ms) _ :=
      refine_debug.

    #[export] Instance refine_demonic_pattern_match {N : Set} (n : N -> LVar) {Γ σ} (pat : Pattern (N:=N) σ) {w} :
      Related (RVal σ -> RStoreT Γ Γ (RMatchResult pat))
        (CStoreT.demonic_pattern_match pat) w (SStoreT.demonic_pattern_match (w := w) n pat).
    Proof.
      iIntros (v sv) "rv %Φ %sΦ rΦ %δ %sδ rδ %h %sh rh".
      unfold SStoreT.demonic_pattern_match, CStoreT.demonic_pattern_match,
               CStoreT.lift_purespec.
      iApply (PureSpec.refine_demonic_pattern_match with "rv").
      iIntros (w1 θ1) "!> %mr %smr rmr".
      iApply ("rΦ" with "rmr [rδ] [rh]"); solve_related.
    Qed.

    #[export] Instance refine_compat_store_tail {Γ b} {w : World} :
      Related (RStore (Γ ▻ b) -> RStore Γ) env.tail w env.tail.
    Proof.
      iIntros (δ sδ) "H".
      iApply (repₚ_cong (T1 := SStore (Γ ▻ b)) (T2 := SStore Γ) env.tail env.tail with "H").
      intros. now env.destroy vs1.
    Qed.

    #[export] Instance refine_compat_store_drop {Γ Δ} {w : World} :
      Related (RStore (Γ ▻▻ Δ) -> RStore Γ) (env.drop Δ) w (env.drop Δ).
    Proof.
      iIntros (δ sδ) "H".
      iApply (repₚ_cong (T1 := SStore (Γ ▻▻ Δ)) (T2 := SStore Γ) (env.drop Δ) (env.drop Δ) with "H").
      intros. env.destroy vs1.
      now rewrite inst_env_cat !env.drop_cat.
    Qed.

    #[export] Instance refine_pushpop `{R : Rel AT A} {Γ1 Γ2 x σ} {w} :
      Related (RVal σ -> RStoreT (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) R -> RStoreT Γ1 Γ2 R)
        CStoreT.pushpop w (SStoreT.pushpop (w := w)).
    Proof.
      unfold SStoreT.pushpop, CStoreT.pushpop, RStoreT. solve_related.
    Qed.

    #[export] Instance refine_pushspops `{R : Rel AT A} {Γ1 Γ2 Δ} {w} :
      Related (RStore Δ -> RStoreT (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) R -> RStoreT Γ1 Γ2 R)
        CStoreT.pushspops w (SStoreT.pushspops (w := w)).
    Proof.
      unfold SStoreT.pushspops, CStoreT.pushspops, RStoreT. solve_related.
    Qed.

    #[export] Instance refine_get_local {Γ} {w} :
      Related (RStoreT Γ Γ (RStore Γ)) CStoreT.get_local w (SStoreT.get_local (w := w)).
    Proof. unfold CStoreT.get_local, SStoreT.get_local, RStoreT; solve_related. Qed.

    #[export] Instance refine_put_local {Γ1 Γ2} {w} :
      Related (RStore Γ2 -> RStoreT Γ1 Γ2 RUnit)
        CStoreT.put_local w (SStoreT.put_local (w := w)).
    Proof. unfold CStoreT.put_local, SStoreT.put_local, RStoreT; solve_related. Qed.

    Lemma refine_peval {w : World} {σ} (t : STerm σ w) v :
      ℛ⟦RVal σ⟧ v t ⊢ ℛ⟦RVal σ⟧ v (peval t).
    Proof. unfold RVal, RInst. crushPredEntails3. now rewrite peval_sound. Qed.

    Lemma refine_seval_exp {Γ σ} (e : Exp Γ σ) {w : World} {δ} {sδ : SStore Γ w} :
      ℛ⟦ RStore Γ ⟧ δ sδ ⊢ ℛ⟦RVal σ⟧ (Expressions.eval e δ) (seval_exp sδ e).
    Proof.
      unfold RStore, RVal, RInst. crushPredEntails3.
      rewrite <-eval_exp_inst.
      now subst.
    Qed.

    Lemma refine_seval_exps {Γ Δ : PCtx} {es : NamedEnv (Exp Γ) Δ} {w : World} {δ : CStore Γ} {sδ : SStore Γ w} :
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

    #[export] Instance refine_compat_peval {w : World} {σ} (t : STerm σ w) v : RelatedFrom (RVal σ) v w (peval t) _ :=
      refine_peval t v.

    #[export] Instance refine_compat_seval_exp {Γ σ} (e : Exp Γ σ) {w : World} {δ} {sδ : SStore Γ w} :
      RelatedFrom (RVal σ) (Expressions.eval e δ) w (seval_exp sδ e) _ :=
      refine_seval_exp e.

    #[export] Instance refine_compat_seval_exps {Γ Δ : PCtx} {es : NamedEnv (Exp Γ) Δ} {w : World} {δ : CStore Γ} {sδ : SStore Γ w} : RelatedFrom (RStore Δ) (evals es δ) w (seval_exps sδ es) _ :=
      refine_seval_exps.

    #[export] Instance refine_eval_exp {Γ σ} (e : Exp Γ σ) {w} :
      Related (RStoreT Γ Γ (RVal σ))
        (CStoreT.eval_exp e) w (SStoreT.eval_exp (w := w) e).
    Proof.
      iIntros (K sK) "HK %δ0 %sδ0 #Hδ0 %h0 %sh0 Hh0".
      unfold SStoreT.eval_exp, CStoreT.eval_exp.
      iApply (refine_T with "HK [Hδ0] Hδ0 Hh0").
      iApply refine_peval.
      now iApply refine_seval_exp.
    Qed.

    #[export] Instance refine_eval_exps {Γ Δ} (es : NamedEnv (Exp Γ) Δ) {w} :
      Related (RStoreT Γ Γ (RStore Δ))
        (CStoreT.eval_exps es) w (SStoreT.eval_exps (w := w) es).
    Proof.
      iIntros (K sK) "HK %δ0 %sδ0 #Hδ0 %h0 %sh0 Hh0".
      unfold SStoreT.eval_exps, CStoreT.eval_exps.
      iApply (refine_T with "HK [Hδ0] Hδ0 Hh0").
      now iApply refine_seval_exps.
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

    #[export] Instance refine_compat_env_update {Γ x σ} (xIn : (x∷σ ∈ Γ)%katamaran) (w : World)
      (t : Term w σ) (v : Val σ) (δs : SStore Γ w) (δc : CStore Γ) :
      RelatedFrom (RStore Γ) (δc ⟪ x ↦ v ⟫) w (δs ⟪ x ↦ t ⟫) _ :=
      refine_env_update xIn w t v δs δc.

    #[export] Instance refine_assign {Γ x σ} {xIn : (x∷σ ∈ Γ)%katamaran} {w} :
      Related (RVal σ -> RStoreT Γ Γ RUnit)
        (CStoreT.assign x) w (SStoreT.assign (w := w) x).
    Proof.
      iIntros (v sv) "Hv %K %sK HK %δ %sδ Hδ %h %sh Hh".
      unfold SStoreT.assign, CStoreT.assign.
      iApply (refine_T with "HK [//] [Hv Hδ] Hh").
      now iApply (refine_env_update with "[$Hv $Hδ]").
    Qed.

    Section ExecAux.

      Context `(rexec_call_foreign : RefineExecCallForeign c_exec_call_foreign s_exec_call_foreign).
      Context `(rexec_lemma : RefineExecLemma c_exec_lemma s_exec_lemma).
      Context `(rexec_call : RefineExecCall c_exec_call s_exec_call).
      Context `(rexec_fail : RefineExecFail c_exec_fail s_exec_fail).

      #[export] Instance refine_exec_aux {SPEC : Specification} :
        RefineExec (@CStoreT.exec_aux _ c_exec_call_foreign c_exec_lemma c_exec_call c_exec_fail) (@SStoreT.exec_aux _ s_exec_call_foreign s_exec_lemma s_exec_call s_exec_fail).
      Proof.
        intros ? ? s. induction s; cbn; intros w; solve_related.
      Qed.

    End ExecAux.

    Section WithSpec.

    #[export] Instance refine_exec_contract `(rexec : RefineExec c_exec s_exec)
      {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) w :
      Related (RHeapSpec RUnit)
          (SHAL.exec_contract c_exec c s) w
          (SYMB.exec_contract s_exec c s (w := w)).
    Proof.
      unfold Related.
      destruct c as [lvars pats req result ens]; cbn. solve_related.
    Qed.

    #[export] Instance refine_exec_call_error_no_fuel :
      RefineExecCall SHAL.exec_call_error_no_fuel SYMB.exec_call_error_no_fuel.
    Proof.
      iIntros (? ? ? ? cδ sδ) "#rδ".
      unfold SHAL.exec_call_error_no_fuel, SYMB.exec_call_error_no_fuel.
      iApply HeapSpec.refine_error.
    Qed.

    Context {SPEC : Specification}.

    #[export] Instance refine_exec_call_foreign :
      RefineExecCallForeign cexec_call_foreign sexec_call_foreign.
    Proof.
      iIntros (? ? ? ? cδ sδ) "#rδ".
      unfold cexec_call_foreign, sexec_call_foreign.
      now iApply refine_call_contract.
    Qed.

    Variable cfg : Config.

    #[export] Instance refine_debug_lemma [Δ] (l : 𝑳 Δ) w :
      Related (RStore Δ -> RHeapSpec RUnit)
        (SHAL.debug_lemma l) w (SYMB.debug_lemma cfg l (w := w)).
    Proof.
      unfold SHAL.debug_lemma, SYMB.debug_lemma.
      destruct config_debug_lemma; solve_related.
    Qed.

    #[export] Instance refine_exec_lemma :
      RefineExecLemma cexec_lemma (sexec_lemma cfg).
    Proof.
      unfold cexec_lemma, sexec_lemma; intros. solve_related.
    Qed.

    #[export] Instance refine_debug_call [Δ τ] (f : 𝑭 Δ τ) w :
      Related (RStore Δ -> RHeapSpec RUnit)
        (SHAL.debug_call f) w (SYMB.debug_call cfg f (w := w)).
    Proof.
      unfold SHAL.debug_call, SYMB.debug_call.
      destruct config_debug_function; solve_related.
    Qed.

    #[export] Instance refine_exec_fail :
      RefineExecFail cexec_fail sexec_fail.
    Proof.
      unfold cexec_fail, sexec_fail; intros.
      destruct fail_rule_pre; solve_related.
    Qed.

    #[export] Instance refine_exec_call (fuel : nat) :
      RefineExecCall (cexec_call fuel) (sexec_call cfg fuel).
    Proof.
      induction fuel; intros; cbn; solve_related.
    Qed.

    #[export] Instance refine_exec (fuel : nat) :
      RefineExec (cexec fuel) (sexec cfg fuel).
    Proof.
      unfold cexec, sexec; intros; solve_related.
    Qed.

    End WithSpec.

  End StoreT.
  Export (hints) StoreT.

  Section WithSpec.

    Import HeapSpec.

    Context {SPEC : Specification}.

    #[export] Instance refine_vcgen (cfg : Config) (fuel : nat) {Γ τ} (c : SepContract Γ τ) (body : Stm Γ τ) w :
      Related (RProp) (SHAL.vcgen fuel c body) w (SYMB.vcgen cfg fuel c body w).
    Proof.
      iApply HeapSpec.refine_run.
      iApply StoreT.refine_exec_contract.
    Qed.

  End WithSpec.

  Lemma replay_sound (s : 𝕊 wnil) :
    safe (SPureSpec.replay s) [env] -> safe s [env].
  Proof.
    intros H.
    apply CPureSpec.replay_sound.
    exact (RProp_safe (PureSpec.refine_replay s) H).
  Qed.

  Lemma symbolic_vcgen_fuel_soundness {SPEC : Specification} {Γ τ} (fuel : nat)
    (c : SepContract Γ τ) (body : Stm Γ τ) :
    Symbolic.ValidContractWithFuel fuel c body ->
    Shallow.ValidContractWithFuel fuel c body.
  Proof.
    unfold Symbolic.ValidContractWithFuel, Shallow.ValidContractWithFuel.
    intros [Hwp%postprocess_sound].
    apply replay_sound in Hwp.
    apply postprocess_sound in Hwp.
    exact (RProp_safe (refine_vcgen _ _ _ _ _) Hwp).
  Qed.

  Lemma symbolic_vcgen_soundness {SPEC : Specification} {Γ τ}
    (c : SepContract Γ τ) (body : Stm Γ τ) :
    Symbolic.ValidContract c body ->
    Shallow.ValidContract c body.
  Proof.
    unfold Symbolic.ValidContract, Shallow.ValidContract.
    apply symbolic_vcgen_fuel_soundness.
  Qed.

  (* Print Assumptions symbolic_vcgen_soundness. *)

End RefineExecOn.
