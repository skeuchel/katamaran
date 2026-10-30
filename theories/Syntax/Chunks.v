(******************************************************************************)
(* Copyright (c) 2020 Dominique Devriese, Georgy Lukyanov,                    *)
(*   Sander Huyghebaert, Steven Keuchel                                       *)
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
     Classes.Morphisms
     Classes.RelationClasses
     Lists.List
     (* Program.Basics *)
     (* Program.Tactics *)
     ZArith.

From Katamaran Require Import
     Prelude
     Tactics
     Syntax.Formulas
     Syntax.Predicates
     Syntax.Registers
     Symbolic.PartialEvaluation
     Base.

From Equations Require Import
     Equations.

Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.

Fixpoint heap_extractions `{IsDuplicable C} (h : list C) : list (C * list C) :=
  match h with
  | nil      => nil
  | cons c h => let h' := if is_duplicable c then cons c h else h in
                let ec := pair c h' in
                cons ec (map (base.prod_map id (cons c)) (heap_extractions h))
  end.

Lemma heap_extractions_map `{IsDuplicable A} `{IsDuplicable B} (f : A -> B) (h : list A)
      (is_dup_map : (forall c, is_duplicable (f c) = is_duplicable c)) :
  heap_extractions (List.map f h) = List.map (base.prod_map f (List.map f)) (heap_extractions h).
Proof.
  induction h; cbn.
  - reflexivity.
  - f_equal.
    + unfold base.prod_map; cbn. f_equal.
      rewrite is_dup_map.
      now destruct is_duplicable.
    + rewrite IHh.
      rewrite ?List.map_map.
      apply List.map_ext.
      intros [x xs]; reflexivity.
Qed.

Module Type ChunksOn
  (Import GLOBAL : GlobalState)
  (Import P      : PredicateKit GLOBAL)
  (Import PE     : PartialEvaluationOn GLOBAL.BASE)
  (Import F      : FormulasOn GLOBAL P).

  Inductive GChunk (V : Ty -> Set) : Type :=
  | chunk_user   (p : 𝑯) (ts : Env V (𝑯_Ty p))
  | chunk_ptsreg {σ : Ty} (r : 𝑹𝑬𝑮 σ) (v : V σ)
  | chunk_conj   (c1 c2 : GChunk V)
  | chunk_wand   (c1 c2 : GChunk V).
  Global Arguments chunk_user [_] _ _.
  Global Arguments chunk_ptsreg [_] [_] _ _.

  (* Semi-concrete chunks *)
  Definition SCChunk := GChunk Val.

  (* Symbolic chunks *)
  Definition Chunk (Σ : LCtx) := GChunk (Term Σ).

  Section TransparentObligations.
    Local Set Transparent Obligations.
    Derive NoConfusion for GChunk.
  End TransparentObligations.

  #[export] Instance chunk_isdup {V} : IsDuplicable (GChunk V) := {
    is_duplicable := fun c => match c with
                           | chunk_user p _ => is_duplicable p
                           | chunk_ptsreg _ _ => false
                           | chunk_conj _ _ => false
                           | chunk_wand _ _ => false
                           end
    }.

  Open Scope lazy_bool_scope.

  Fixpoint chunk_eqb {V : Ty -> Set} (eqv : forall σ, V σ -> V σ -> bool) (c1 c2 : GChunk V) : bool :=
    match c1 , c2 with
    | chunk_user p1 ts1, chunk_user p2 ts2 =>
      match eq_dec p1 p2 with
      | left e => env.eqb_hom
                    eqv
                    (eq_rect _ (fun p => Env _ (𝑯_Ty p)) ts1 _ e)
                    ts2
      | right _ => false
      end
    | chunk_ptsreg r1 t1 , chunk_ptsreg r2 t2 =>
      match eq_dec_het r1 r2 with
      | left e  => eqv _
                     (eq_rect _ V t1 _ (f_equal projT1 e))
                     t2
      | right _ => false
      end
    | chunk_conj c11 c12 , chunk_conj c21 c22 =>
      chunk_eqb eqv c11 c21 &&& chunk_eqb eqv c12 c22
    | chunk_wand c11 c12 , chunk_wand c21 c22 =>
      chunk_eqb eqv c11 c21 &&& chunk_eqb eqv c12 c22
    | _ , _ => false
    end.

  Local Set Equations With UIP.

  Lemma chunk_eqb_spec {V : Ty -> Set} eqv (eqv_spec : forall {σ} {v1 v2 : V σ}, reflect (v1 = v2) (eqv _ v1 v2)):
    forall (c1 c2 : GChunk V),
      reflect (c1 = c2) (chunk_eqb eqv c1 c2).
  Proof.
    induction c1; intros [];
      solve_eqb_spec with
      try match goal with
          | |- reflect _ (env.eqb_hom eqv ?x ?y) =>
              destruct (env.eqb_hom_spec eqv eqv_spec x y)
          | |- reflect _ (eqv _ ?x ?y) =>
              destruct (eqv_spec _ x y)
          end.
  Qed.

  #[export] Instance SubstChunk : Subst Chunk :=
    fix sub_chunk {Σ1} (c : Chunk Σ1) {Σ2} (ζ : Sub Σ1 Σ2) {struct c} : Chunk Σ2 :=
      match c with
      | chunk_user p ts => chunk_user p (subst ts ζ)
      | chunk_ptsreg r t => chunk_ptsreg r (subst t ζ)
      | chunk_conj c1 c2 =>
        chunk_conj (sub_chunk c1 ζ) (sub_chunk c2 ζ)
      | chunk_wand c1 c2 =>
        chunk_wand (sub_chunk c1 ζ) (sub_chunk c2 ζ)
      end.

  #[export] Instance SubstSUChunk `{SubstUniv Sb} : SubstSU Sb Chunk :=
    fix subSU_chunk {Σ1 Σ2} (c : Chunk Σ1) (ζ : Sb Σ1 Σ2) {struct c} : Chunk Σ2 :=
      match c with
      | chunk_user p ts => chunk_user p (substSU ts ζ)
      | chunk_ptsreg r t => chunk_ptsreg r (substSU (T := fun Σ => Term Σ _) t ζ)
      | chunk_conj c1 c2 =>
        chunk_conj (subSU_chunk c1 ζ) (subSU_chunk c2 ζ)
      | chunk_wand c1 c2 =>
        chunk_wand (subSU_chunk c1 ζ) (subSU_chunk c2 ζ)
      end.

  #[export] Instance substlaws_chunk : SubstLaws Chunk.
  Proof.
    constructor.
    { intros ? c. induction c; cbn; f_equal; auto; apply subst_sub_id. }
    { intros ? ? ? ? ? c. induction c; cbn; f_equal; auto; apply subst_sub_comp. }
  Qed.

  #[export] Instance substsulaws_chunk `{SubstUnivLaws Sb} :
    SubstSULaws Sb Chunk.
  Proof.
    intros Σ1 Σ2 Σ3 ζ1 ζ2 t.
    induction t; cbn; f_equal; auto; now rewrite substSU_trans.
  Qed.

  Fixpoint map_GChunk {T1 T2 : Ty -> Set} (f : forall σ, T1 σ -> T2 σ) (c : GChunk T1) : GChunk T2 :=
    match c with
    | chunk_user p ts => chunk_user p (env.map f ts)
    | chunk_ptsreg r t => chunk_ptsreg r (f _ t)
    | chunk_conj c1 c2 => chunk_conj (map_GChunk f c1) (map_GChunk f c2)
    | chunk_wand c1 c2 => chunk_wand (map_GChunk f c1) (map_GChunk f c2)
    end.
  Arguments map_GChunk {T1 T2} f !c : simpl nomatch.

  #[export] Instance inst_chunk : Inst Chunk SCChunk :=
    fun Σ c ι => map_GChunk (T1 := Term Σ) (fun _ v => inst v ι) c.

  #[export] Instance inst_subst_chunk : InstSubst Chunk SCChunk.
  Proof.
    intros ? ? ζ ι c; induction c; cbn; f_equal; auto.
    refine (inst_subst _ _ ts).
    apply inst_subst.
  Qed.

  Import option.notations.
  #[export] Instance OccursCheckChunk :
    OccursCheck Chunk :=
    fun Σ b bIn =>
      fix occurs_check_chunk (c : Chunk Σ) : option (Chunk (Σ - b)) :=
      match c with
      | chunk_user p ts => option.map (chunk_user p) (occurs_check bIn ts)
      | chunk_ptsreg r t => option.map (chunk_ptsreg r) (occurs_check bIn t)
      | chunk_conj c1 c2 =>
          c1' <- occurs_check_chunk c1 ;;
          c2' <- occurs_check_chunk c2 ;;
          Some (chunk_conj c1' c2')
      | chunk_wand c1 c2 =>
          c1' <- occurs_check_chunk c1 ;;
          c2' <- occurs_check_chunk c2 ;;
          Some (chunk_wand c1' c2')
      end.

  #[export] Instance GenOccursCheckChunk : GenOccursCheck (Sb := WeakensTo) Chunk :=
    fun Σ =>
      fix gen_occurs_check_chunk (c : Chunk Σ) : Weakened WeakensTo Chunk Σ :=
      match c with
      | chunk_user p ts => liftUnOp (fun _ => chunk_user p) (fun _ _ _ _ => eq_refl) (gen_occurs_check ts)
      | chunk_ptsreg r t => liftUnOp (fun _ => chunk_ptsreg r) (fun _ _ _ _ => eq_refl) (gen_occurs_check t)
      | chunk_conj c1 c2 => liftBinOp (fun _ c1' c2' => chunk_conj c1' c2') (fun _ _ _ _ _ => eq_refl) (gen_occurs_check_chunk c1) (gen_occurs_check_chunk c2)
      | chunk_wand c1 c2 => liftBinOp (fun _ c1' c2' => chunk_wand c1' c2') (fun _ _ _ _ _ => eq_refl) (gen_occurs_check_chunk c1) (gen_occurs_check_chunk c2)
      end.

  Definition SCHeap : Type := list SCChunk.
  Definition SHeap : LCtx -> Type := fun Σ => list (Chunk Σ).

  #[export] Instance inst_heap : Inst SHeap SCHeap :=
    inst_list.
  #[export] Instance inst_subst_heap : InstSubst SHeap SCHeap.
  Proof. apply inst_subst_list. Qed.

  Definition peval_chunk {Σ} (c : Chunk Σ) : Chunk Σ := map_GChunk peval c.

  Lemma peval_chunk_sound {Σ} (c : Chunk Σ) :
    forall (ι : Valuation Σ),
      inst (peval_chunk c) ι = inst c ι.
  Proof.
    intros ι.
    induction c; cbn; f_equal; eauto using peval_sound.
    apply pevals_sound. apply peval_sound.
  Qed.

  Lemma inst_is_duplicable {Σ} (c : Chunk Σ) (ι : Valuation Σ) :
    is_duplicable (inst c ι) = is_duplicable c.
  Proof.
    destruct c; now cbn.
  Qed.

  Section Consume.
    Import EqNotations.

    Fixpoint try_consume_chunk_exact {Σ} (h : SHeap Σ) (c : Chunk Σ) : option (SHeap Σ) :=
      match h with
      | nil       => None
      | cons c' h =>
          if chunk_eqb Term_eqb c c'
          then Some (if is_duplicable c then (cons c h) else h)
          else option_map (cons c') (try_consume_chunk_exact h c)
      end.

    Lemma try_consume_chunk_exact_spec {Σ} (h : SHeap Σ) (c : Chunk Σ) :
      option.wlp
        (fun h' => List.In (c , h') (heap_extractions h))
        (try_consume_chunk_exact h c).
    Proof.
      induction h as [|c' h].
      - now constructor.
      - cbn -[is_duplicable].
        destruct (chunk_eqb_spec _ (@Term_eqb_spec _) c c').
        + constructor. left. subst.
          now destruct is_duplicable.
        + apply option.wlp_map. revert IHh.
          apply option.wlp_monotonic; auto.
          intros h' HIn. right.
          rewrite List.in_map_iff.
          exists (c,h'). auto.
    Qed.

    Section PreciseUser.

      Context {Σ} (p : 𝑯) {ΔI ΔO : Ctx Ty} (prec : 𝑯_Ty p = ΔI ▻▻ ΔO)
        (tsI : Env (Term Σ) ΔI) (tsO : Env (Term Σ) ΔO).

      Equations(noeqns) match_chunk_user_precise (c : Chunk Σ) : option (PathCondition Σ) :=
        match_chunk_user_precise (chunk_user p' ts')
          with eq_dec p p' => {
            match_chunk_user_precise (chunk_user ?(p) ts') (left eq_refl) :=
              match env.catView (rew prec in ts') with
              | env.isCat tsI' tsO' =>
                  if env.eqb_hom Term_eqb tsI tsI'
                  then Some (formula_eqs_ctx tsO tsO')
                  else None
              end;
            match_chunk_user_precise (chunk_user p' ts') (right _) := None
          };
        match_chunk_user_precise _ := None.

      Fixpoint try_consume_chunk_user_precise (h : SHeap Σ) : option (SHeap Σ * PathCondition Σ) :=
        match h with
        | nil => None
        | cons c h' =>
            match match_chunk_user_precise c with
            | Some eqs => Some (if is_duplicable p then cons c h' else h', eqs)
            | None => option_map (base.prod_map (cons c) id) (try_consume_chunk_user_precise h')
            end
        end.

      Lemma try_consume_chunk_user_precise_spec (h : SHeap Σ) :
        option.wlp
          (fun '(h', eqs) =>
             forall ι : Valuation Σ,
             instprop eqs ι ->
             List.In
               (inst (chunk_user p (eq_rect_r (fun c : Ctx Ty => Env (Term Σ) c) (tsI ►► tsO) prec)) ι, inst h' ι)
               (heap_extractions (inst h ι)))
          (try_consume_chunk_user_precise h).
      Proof.
        induction h as [|c h]; [now constructor|]. cbn [try_consume_chunk_user_precise].
        destruct match_chunk_user_precise as [eqs|] eqn:?.
        - clear IHh. constructor. intros ι Heqs. left.
          destruct c; try discriminate Heqo. cbn in *.
          destruct (eq_dec p p0); cbn in Heqo; try discriminate Heqo. destruct e.
          remember (eq_rect (𝑯_Ty p) (Env (Term Σ)) ts (ΔI ▻▻ ΔO) prec) as ts'.
          destruct (env.catView ts') as [tsI' tsO'].
          destruct (env.eqb_hom_spec Term_eqb (@Term_eqb_spec Σ) tsI tsI'); try discriminate.
          apply noConfusion_inv in Heqo. cbn in Heqo. subst.
          apply instprop_formula_eqs_ctx in Heqs.
          f_equal; first f_equal.
          + change (env.map (fun Σ v => inst v ?ι) ?ts) with (inst ts ι).
            rewrite (@inst_eq_rect_indexed_r (Ctx Ty) (fun Δ Σ => Env (Term Σ) Δ) (Env Val)).
            rewrite inst_env_cat, Heqs, <- inst_env_cat.
            change (env.cat ?A ?B) with (env.cat A B). rewrite Heqts'.
            rewrite (@inst_eq_rect_indexed (Ctx Ty) (fun Δ Σ => Env (Term Σ) Δ) (Env Val)).
            now rewrite rew_opp_l.
          + now destruct is_duplicable.
        - apply option.wlp_map. revert IHh. apply option.wlp_monotonic; auto.
          intros [h' eqs] HYP ι Heqs. specialize (HYP ι Heqs).
          remember (inst (chunk_user p (eq_rect_r (fun c0 : Ctx Ty => Env (Term Σ) c0) (tsI ►► tsO) prec)) ι) as c'.
          change (inst (cons c h) ι) with (cons (inst c ι) (inst h ι)).
          cbn [fst heap_extractions]. right. apply List.in_map_iff.
          eexists (c', inst h' ι); auto.
      Qed.

    End PreciseUser.

    Section PrecisePtsreg.

      Context {Σ : LCtx} {σ} (r : 𝑹𝑬𝑮 σ).

      Equations(noeqns) match_chunk_ptsreg_precise (c : Chunk Σ) : option (Term Σ σ) :=
        match_chunk_ptsreg_precise (chunk_ptsreg r' t)
          with eq_dec_het r r' => {
            match_chunk_ptsreg_precise (chunk_ptsreg ?(r) t) (left eq_refl) :=
              Some t;
            match_chunk_ptsreg_precise (chunk_ptsreg r' t) (right _) := None
          };
        match_chunk_ptsreg_precise _ := None.

      Fixpoint find_chunk_ptsreg_precise (h : SHeap Σ) : option (Term Σ σ * SHeap Σ) :=
        match h with
        | nil => None
        | cons c h' =>
            match match_chunk_ptsreg_precise c with
            | Some t => Some (t, h')
            | None => option_map (base.prod_map id (cons c)) (find_chunk_ptsreg_precise h')
            end
        end.

      Lemma find_chunk_ptsreg_precise_spec (h : SHeap Σ) :
        option.wlp
          (fun '(t, h') =>
             forall ι : Valuation Σ,
             List.In
               (inst (chunk_ptsreg r t) ι, inst h' ι)
               (heap_extractions (inst h ι)))
          (find_chunk_ptsreg_precise h).
      Proof.
        induction h as [|c h]; [now constructor|]; cbn [find_chunk_ptsreg_precise].
        destruct match_chunk_ptsreg_precise eqn:?.
        - constructor. intros ι. clear IHh.
          destruct c; cbn in Heqo; try discriminate Heqo.
          destruct (eq_dec_het r r0); try discriminate Heqo.
          dependent elimination e. cbn in Heqo. dependent elimination Heqo.
          change (inst (cons ?c ?h) ι) with (cons (inst c ι) (inst h ι)).
          cbn. now left.
        - apply option.wlp_map. revert IHh. apply option.wlp_monotonic; auto.
          intros [t h'] HYP ι. specialize (HYP ι).
          change (inst (cons ?c ?h) ι) with (cons (inst c ι) (inst h ι)).
          cbn [fst heap_extractions]. right. apply List.in_map_iff.
          eexists (inst (T := Chunk) (chunk_ptsreg (V := Term Σ) r t) ι, inst h' ι).
          split; auto.
      Qed.

      Context (h : SHeap Σ) (t : Term Σ σ).

      Definition try_consume_chunk_ptsreg_precise :
        option (SHeap Σ * PathCondition Σ) :=
        option.map
          (fun '(t', h') => (h', ctx.nil ▻ formula_relop bop.eq t t'))
          (find_chunk_ptsreg_precise h).

      Lemma try_consume_chunk_ptsreg_precise_spec :
        option.wlp
          (fun '(h', eqs) =>
             forall ι : Valuation Σ,
             instprop eqs ι ->
             List.In
               (inst (chunk_ptsreg r t) ι, inst h' ι)
               (heap_extractions (inst h ι)))
          try_consume_chunk_ptsreg_precise.
      Proof.
        unfold try_consume_chunk_ptsreg_precise. apply option.wlp_map.
        generalize (find_chunk_ptsreg_precise_spec h).
        apply option.wlp_monotonic. intros [h' t'] HIn ι [_ Heq].
        specialize (HIn ι). cbn in Heq |- *. now rewrite Heq.
      Qed.

    End PrecisePtsreg.

    Definition try_consume_chunk_precise {Σ} (h : SHeap Σ) (c : Chunk Σ) :
      option (SHeap Σ * PathCondition Σ) :=
      match c with
      | chunk_user p ts =>
          match 𝑯_precise p with
          | Some (MkPrecise ΔI ΔO Δeq) =>
              match env.catView (rew Δeq in ts) with
              | env.isCat tsI tsO => try_consume_chunk_user_precise Δeq tsI tsO h
              end
          | None => None
          end
      | chunk_ptsreg r t => try_consume_chunk_ptsreg_precise r h t
      | _ => None
      end.

    Lemma try_consume_chunk_precise_spec {Σ} (h : SHeap Σ) (c : Chunk Σ) :
      option.wlp
        (fun '(h', eqs) =>
           forall ι : Valuation Σ,
           instprop eqs ι ->
           List.In (inst c ι, inst h' ι)
             (heap_extractions (inst h ι)))
        (try_consume_chunk_precise h c).
    Proof.
      destruct c; [| |constructor|constructor];
        cbn [try_consume_chunk_precise].
      - destruct (𝑯_precise p) as [[ΔI ΔO prec]|]; [|constructor].
        remember (eq_rect (𝑯_Ty p) (Env (Term Σ)) ts (ΔI ▻▻ ΔO) prec) as ts'.
        destruct (env.catView ts') as [tsI tsO].
        generalize (try_consume_chunk_user_precise_spec prec tsI tsO h).
        apply option.wlp_monotonic. intros [h' eqs].
        intros HIn ι Heqs. specialize (HIn ι Heqs).
        now rewrite Heqts', rew_opp_l in HIn.
      - apply try_consume_chunk_ptsreg_precise_spec.
    Qed.

  End Consume.

  Section Interpretation.
    Import iris.bi.interface.

    Context {HProp} `{PI : PredicateDef HProp}.

    Fixpoint interpret_chunk {Σ} (c : Chunk Σ) (ι : Valuation Σ) {struct c} : HProp :=
      match c with
      | chunk_user p ts => luser p (inst ts ι)
      | chunk_ptsreg r t => lptsreg r (inst t ι)
      | chunk_conj c1 c2 => interpret_chunk c1 ι ∗ interpret_chunk c2 ι
      | chunk_wand c1 c2 => interpret_chunk c1 ι -∗ interpret_chunk c2 ι
      end.

    Fixpoint interpret_scchunk (c : SCChunk) : HProp :=
      match c with
      | chunk_user p vs => luser p vs
      | chunk_ptsreg r v => lptsreg r v
      | chunk_conj c1 c2 => interpret_scchunk c1 ∗ interpret_scchunk c2
      | chunk_wand c1 c2 => interpret_scchunk c1 -∗ interpret_scchunk c2
      end.

    Definition interpret_scheap : SCHeap -> HProp :=
      List.fold_right (fun c h => interpret_scchunk c ∗ h)%I emp%I.
    #[global] Arguments interpret_scheap !h.

    Lemma interpret_scchunk_inst {Σ} (c : Chunk Σ) (ι : Valuation Σ) :
      interpret_scchunk (inst c ι) = interpret_chunk c ι.
    Proof.
      induction c; cbn [interpret_chunk];
        try rewrite <- IHc1, <- IHc2; reflexivity.
    Qed.

  End Interpretation.

  Section Erasure.
    Definition EChunk := GChunk ETerm.

    #[export] Instance Erase_Chunk : Erase Chunk EChunk :=
      fun Σ => map_GChunk (T1 := Term Σ) (fun _ t => erase t).
  End Erasure.
End ChunksOn.
