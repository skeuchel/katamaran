(******************************************************************************)
(* Copyright (c) 2019 Dominique Devriese, Georgy Lukyanov,                    *)
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

From Equations Require Import
     Equations.
From Katamaran Require Import
     Context
     Environment
     Notations
     Prelude
     Syntax.BinOps
     Syntax.Terms
     Syntax.TypeDecl
     Syntax.Variables
     Tactics.
From Stdlib Require Import Morphisms.

Import ctx.notations.
Import env.notations.
Import option.
Import option.notations.

Local Set Implicit Arguments.

Module Type GenOccursCheckOn
  (Import TY : Types)
  (Import TM : TermsOn TY).

  Local Abbreviation LCtx := (NCtx LVar Ty).

  Class SubstUniv (Sb : LCtx -> LCtx -> Type) :=
    MkSubstUniv {
        initSU : forall {Σ}, Sb [ctx] Σ
      ; transSU : forall {Σ1 Σ2 Σ3}, Sb Σ1 Σ2 -> Sb Σ2 Σ3 -> Sb Σ1 Σ3
      ; interpSU : forall {Σ1 Σ2}, Sb Σ1 Σ2 -> Sub Σ1 Σ2
      }.

  Class SubstSU (Sb : LCtx -> LCtx -> Type) (T : LCtx -> Type) :=
    substSU : forall {Σ1 Σ2}, T Σ1 -> Sb Σ1 Σ2 -> T Σ2.

  Fixpoint substSU_term `{SubstUniv Sb} {σ Σ1 Σ2} (t : Term Σ1 σ) (ζ : Sb Σ1 Σ2) {struct t} : Term Σ2 σ :=
    match t with
    | term_var ς                 => (interpSU ζ).[??ς]
    | term_val σ v               => term_val σ v
    | term_binop op t1 t2        => term_binop op (substSU_term t1 ζ) (substSU_term t2 ζ)
    | term_unop op t             => term_unop op (substSU_term t ζ)
    | term_tuple ts              => term_tuple (env.map (fun _ t => substSU_term t ζ) ts)
    | term_union U K t           => term_union U K (substSU_term t ζ)
    | term_record R ts           => term_record R (env.map (fun _ t => substSU_term t ζ) ts)
    end.

  #[export] Instance SubstSUTerm `{SubstUniv Sb} {σ} : SubstSU Sb (fun Σ => Term Σ σ) :=
    fun _ _ => substSU_term.

  #[export] Instance substSU_option `{SubstSU Sb T} : SubstSU Sb (Option T) :=
    fun {Σ1 Σ2} t σ => match t with
                       | Some t' => Some (substSU t' σ)
                       | None => None
                       end.

  Record MeetResult `{SubstUniv Sb} Σ Σ1 Σ2 :=
    MkMeetResult {
        Σ12 : LCtx
      ; meetLeft : Sb Σ1 Σ12
      ; meetRight : Sb Σ2 Σ12
      ; meetUp : Sb Σ12 Σ
      }.

  Class SubstUnivMeet Sb `{SubstUniv Sb} :=
    meetSU : forall {Σ Σ1 Σ2} (σ1 : Sb Σ1 Σ) (σ2 : Sb Σ2 Σ), MeetResult Σ Σ1 Σ2
  .
  Arguments SubstUnivMeet Sb {H}.

  #[export] Instance SubstSU_env `{SubstUniv Sb} {B : Set} {T : LCtx -> B -> Set} {Δ}
    (suT : forall b : B, SubstSU Sb (fun Σ => T Σ b)) :
      SubstSU Sb (fun Σ => Env (T Σ) Δ) :=
      fun Σ1 Σ2 ts ζ => env.map (fun b t => suT b _ _ t ζ) ts.

  #[export] Instance SubstSU_sub `{SubstUniv Sb} {Δ} :
    SubstSU Sb (Sub Δ) := fun Σ1 Σ2 => SubstSU_env (fun _ => SubstSUTerm) _.

  Lemma substSU_lookup `{SubstUniv Sb} {Γ Σ Σ' x σ} (xInΓ : x∷σ ∈ Γ) (ζ : Sb Σ Σ') (δ : SStore Γ Σ) :
      substSU δ.[?? x] ζ = (substSU δ ζ).[?? x].
    Proof.
      unfold substSU at 2, SubstSU_env.
      now rewrite env.lookup_map.
    Qed.

  #[export] Instance substSU_pair `{SubstSU Sb T1, SubstSU Sb T2} : SubstSU Sb (Pair T1 T2) :=
    fun {Σ1 Σ2} '(t1 , t2) σ => (substSU t1 σ , substSU t2 σ).

  Class SubstUnivLaws Sb `{SubstUniv Sb} : Prop :=
    MkSubstUnivLaws {
        interpTransSU : forall {Σ1 Σ2 Σ3} (σ1 : Sb Σ1 Σ2) (σ2 : Sb Σ2 Σ3),
          substSU (interpSU σ1) σ2 = interpSU (transSU σ1 σ2)
      ; transSU_assoc : forall {Σ1 Σ2 Σ3 Σ4} (σ1 : Sb Σ1 Σ2) (σ2 : Sb Σ2 Σ3) (σ3 : Sb Σ3 Σ4),
          transSU σ1 (transSU σ2 σ3) = transSU (transSU σ1 σ2) σ3
    }.
  Arguments SubstUnivLaws Sb {H}.

  Class SubstSULaws Sb T `{SubstUniv Sb, SubstSU Sb T} {sul : SubstUnivLaws Sb} : Prop :=
    substSU_trans : forall {Σ1 Σ2 Σ3} (σ1 : Sb Σ1 Σ2) (σ2 : Sb Σ2 Σ3) (t : T Σ1),
        substSU t (transSU σ1 σ2) = substSU (substSU t σ1) σ2.
  Arguments SubstSULaws Sb T {H H0 sul}.

  #[export] Instance substSULaws_option `{SubstSULaws Sb T} : SubstSULaws Sb (Option T).
  Proof.
    intros Σ1 Σ2 Σ3 ζ1 ζ2 [tu|]; last easy.
    cbn. now rewrite substSU_trans.
  Qed.

  #[export] Instance substSULaws_pair `{SubstSULaws Sb T1} {T2} {sSU2 : SubstSU Sb T2} {sSUL2 : SubstSULaws Sb T2} : SubstSULaws Sb (Pair T1 T2).
  Proof.
    intros Σ1 Σ2 Σ3 ζ1 ζ2 [t1 t2]; cbn; now rewrite !substSU_trans.
  Qed.

  Class SubstSubstSULaws `{SubstUniv Sb, SubstSU Sb T, Subst T} : Prop :=
    substSU_interpSU : forall {Σ1 Σ2} (σ : Sb Σ1 Σ2) (t : T Σ1),
        substSU t σ = subst t (interpSU σ).
  Arguments SubstSubstSULaws Sb {H} T {H0 H1}.

  #[export] Instance substSubstSUTermLaws `{SubstUniv Sb} {σ} :
    SubstSubstSULaws Sb (fun Σ => Term Σ σ).
  Proof.
    intros Σ1 Σ2 ζ t.
    induction t; cbn; f_equal; try assumption;
      (induction IH; first reflexivity); simpl;
      now f_equal.
  Qed.

  #[export] Instance substSubstSULaws_env `{SubstUniv Sb} {B : Set} {Δ}
    {T : LCtx -> B -> Set}
    {sT : forall (b : B), Subst (fun Σ => T Σ b)}
    {sST : forall (b : B), SubstSU Sb (fun Σ => T Σ b)}
    (ssuLT : forall (b : B), SubstSubstSULaws Sb (fun Σ => T Σ b)) :
    SubstSubstSULaws Sb (fun Σ => Env (T Σ) Δ).
  Proof.
    intros Σ1 Σ2 ζ t.
    eapply env.map_ext; intros.
    now eapply ssuLT.
  Qed.

  #[export] Instance substSubstSULaws_sub `{SubstUniv Sb} {Δ} :
      SubstSubstSULaws Sb (Sub Δ).
  Proof.
    eapply substSubstSULaws_env.
    intros.
    now eapply substSubstSUTermLaws.
  Qed.

  #[export] Instance substSUTermLaws `{SubstUniv Sb} {sSUL : SubstUnivLaws Sb} {σ} : SubstSULaws Sb (fun Σ => Term Σ σ).
  Proof.
    intros Σ1 Σ2 Σ3 σ1 σ2 t.
    rewrite ?substSU_interpSU.
    rewrite <-interpTransSU.
    rewrite substSU_interpSU.
    now rewrite subst_sub_comp.
  Qed.

  #[export] Instance substSU_list `{SubstSU Sb T} : SubstSU Sb (List T) :=
    fun _ _ ts ζ => List.map (fun t => substSU t ζ) ts.

  #[export] Instance substSULaws_list `{SubstSULaws Sb T} : SubstSULaws Sb (List T).
  Proof.
    intros Σ1 Σ2 Σ3 ζ1 ζ2 ts.
    induction ts; first reflexivity.
    refine (f_equal2 _ _ IHts).
    now apply substSU_trans.
  Qed.

  #[export,universes(polymorphic=yes)] Instance substSU_Const {Sb} {T : Type} : SubstSU Sb (Const T) :=
    fun Σ1 Σ2 v ζ => v.

  #[export,universes(polymorphic=yes)] Instance substSULaws_Const `{SubstUnivLaws Sb} {T : Type} : SubstSULaws Sb (Const T).
  Proof. easy. Qed.

  #[export] Instance substSULaws_env `{SubstUnivLaws Sb} {B : Set} {Δ}
    {T : LCtx -> B -> Set}
    {sT : forall (b : B), SubstSU Sb (fun Σ => T Σ b)}
    (suLT : forall (b : B), SubstSULaws Sb (fun Σ => T Σ b)) :
    SubstSULaws Sb (fun Σ => Env (T Σ) Δ).
  Proof.
    intros ? ? ? ζ1 ζ2 ts.
    induction ts; first reflexivity.
    cbn.
    f_equal; first assumption.
    now apply suLT.
  Qed.

  Class SubstUnivVar (Sb : LCtx -> LCtx -> Type) :=
    suVar : forall {x Σ} (xIn : x ∈ Σ), Sb [ x ]%ctx  Σ.
  (* Arguments SubstUnivVar Sb. *)

  Class SubstUnivVarUp Sb `{SubstUnivVar Sb} :=
    upSU : forall {Σ1 Σ2 x}, Sb Σ1 Σ2 -> Sb (Σ1 ▻ x) (Σ2 ▻ x)
  .
  Arguments SubstUnivVarUp Sb {H}.

  Class SubstUnivVarUpLaws `{SubstUniv Sb, SubstUnivVarUp Sb} : Prop :=
    upSU_sound : forall {Σ1 Σ2 x} (ζ : Sb Σ1 Σ2),
        interpSU (upSU (x := x) ζ) = sub_up1 (interpSU ζ)
  .
  Arguments SubstUnivVarUpLaws Sb {H H0 H1}.
  Class SubstUnivVarDown `{SubstUnivVar Sb} :=
    MkSubstUnivVarDown {
        wkVarSU : forall {Σ1 Σ2 x}, x ∈ Σ1 -> Sb Σ1 Σ2 -> x ∈ Σ2
      ; downSU : forall {Σ1 Σ2 x} (xIn : x ∈ Σ1) (σ : Sb Σ1 Σ2),
          let xIn' := wkVarSU xIn σ in Sb (Σ1 - x) (Σ2 - x)
      }.
  Arguments SubstUnivVarDown Sb {H}.

  Class SubstUnivVarLaws `{SubstUniv Sb, SubstUnivVar Sb} : Prop :=
    suVarSound : forall `(xIn : x ∈ Σ), interpSU (suVar xIn) = [ term_var_in xIn ]%env.
  Arguments SubstUnivVarLaws Sb {H} {H0}.

  Record BoxSb Sb (T : LCtx -> Type) (Σ : LCtx) : Type :=
    MkBoxSb {
        unboxSb : forall Σ', Sb Σ Σ' -> T Σ'
      }.
  Arguments MkBoxSb {Sb T Σ} unboxSb.
  Arguments unboxSb {Sb T Σ} b {Σ'} ζ.

  Inductive BoxSbLaws `{SubstUniv Sb, SubstSU Sb T} {Σ : LCtx} : BoxSb Sb T Σ -> Prop :=
  | MkBoxSbLaws (ub : forall Σ', Sb Σ Σ' -> T Σ') :
      (forall Σ1 Σ2 (ζ1 : Sb Σ Σ1) (ζ2 : Sb Σ1 Σ2), substSU (ub _ ζ1) ζ2 = ub _ (transSU ζ1 ζ2)) ->
      BoxSbLaws (MkBoxSb ub).

  Lemma unboxSbLaws `{SubstUniv Sb, SubstSU Sb T} {Σ : LCtx} (bv : BoxSb Sb T Σ)
    (bvl : BoxSbLaws bv) {Σ1 Σ2} (ζ1 : Sb Σ Σ1) (ζ2 : Sb Σ1 Σ2) :
    substSU (unboxSb bv ζ1) ζ2 = unboxSb bv (transSU ζ1 ζ2).
  Proof. now destruct bvl. Qed.


  Definition boxSb `{SubstSU Sb T} {Σ} (t : T Σ) : BoxSb Sb T Σ :=
    MkBoxSb (fun Σ' => substSU t).

  Lemma boxSbLaws `{SubstSULaws Sb T} {Σ} (t : T Σ) : BoxSbLaws (boxSb t).
  Proof.
    constructor. intros. now rewrite substSU_trans.
  Qed.

  #[export] Instance substSU_BoxSb `{SubstSU Sb T, SubstUniv Sb} : SubstSU Sb (BoxSb Sb T) :=
    fun _ _ t ζ => MkBoxSb (fun _ ζ' => unboxSb t (transSU ζ ζ')).

  Lemma substSU_BoxSbLaws  `{SubstSU Sb T, SubstUnivLaws Sb} {Σ1 Σ2} {t : BoxSb Sb T Σ1} {ζ : Sb Σ1 Σ2} :
    BoxSbLaws t -> BoxSbLaws (substSU t ζ).
  Proof.
    intros boxLt.
    constructor. intros.
    destruct boxLt as [ub Hub].
    now rewrite Hub, transSU_assoc.
  Qed.

  Record Weakened Sb {sSb : SubstUniv Sb} (T : LCtx -> Type) {sSUT : SubstSU Sb T} (Σ : LCtx) : Type :=
    MkWeakened {
        Σsupp : LCtx
      ; embedSupport : Sb Σsupp Σ
      ; wkVal : BoxSb Sb T Σsupp
      ; wkValBoxLaws : BoxSbLaws wkVal
      }.
  Arguments Weakened Sb {sSb} T {sSUT} Σ.
  Arguments MkWeakened {Sb sSb T sSUT Σ} {Σsupp} embedSupport wkVal wkValBoxLaws.

  Definition unWeaken {Σ Sb} {sSb : SubstUniv Sb} {T} {sSUT : SubstSU Sb T} (wv : Weakened Sb T Σ) : T Σ :=
    match wv with
    | MkWeakened ζ v _ => unboxSb v ζ
    end.

  Definition liftBoxUnOp {T1 T2} (f : forall {Σ'}, T1 Σ' -> T2 Σ') {Σ Sb} (bv : BoxSb Sb T1 Σ) : BoxSb Sb T2 Σ :=
    MkBoxSb (fun Σ' ζ => f (unboxSb bv ζ)).

  Lemma liftBoxUnOpLaws `{SubstUniv Sb, SubstSU Sb T1, SubstSU Sb T2}
    (f : forall {Σ'}, T1 Σ' -> T2 Σ')
    (fmono : forall {Σ1 Σ2} (ζ : Sb Σ1 Σ2) {t : T1 Σ1}, f (substSU t ζ) = substSU (f t) ζ)
    {Σ} (bv : BoxSb Sb T1 Σ)
    (bvl : BoxSbLaws bv) : BoxSbLaws (liftBoxUnOp (fun _ => f) bv).
  Proof.
    constructor; intros.
    now rewrite <-(unboxSbLaws bvl), fmono.
  Qed.

  Definition liftBoxBinOp {T1 T2 T3} (f : forall {Σ'}, T1 Σ' -> T2 Σ' -> T3 Σ') {Σ Sb}
    (bv1 : BoxSb Sb T1 Σ) (bv2 : BoxSb Sb T2 Σ) : BoxSb Sb T3 Σ :=
    MkBoxSb (fun Σ' ζ => f (unboxSb bv1 ζ) (unboxSb bv2 ζ)).

  Lemma liftBoxBinOpLaws `{SubstUniv Sb, SubstSU Sb T1, SubstSU Sb T2, SubstSU Sb T3}
    (f : forall {Σ'}, T1 Σ' -> T2 Σ' -> T3 Σ')
    (fmono : forall {Σ1 Σ2} (ζ : Sb Σ1 Σ2) (t1 : T1 Σ1) (t2 : T2 Σ1),
        substSU (f t1 t2) ζ = f (substSU t1 ζ) (substSU t2 ζ))
    {Σ} (bv1 : BoxSb Sb T1 Σ) (bv2 : BoxSb Sb T2 Σ)
    (bvl1 : BoxSbLaws bv1) (bvl2 : BoxSbLaws bv2) : BoxSbLaws (liftBoxBinOp (fun _ => f) bv1 bv2).
  Proof.
    constructor; intros.
    now rewrite <-(unboxSbLaws bvl1), <-(unboxSbLaws bvl2), fmono.
  Qed.

  Program Definition weakenInit `{SubstSULaws Sb T}
    {Σ} (v : T [ctx]) : Weakened Sb T Σ :=
    MkWeakened initSU (boxSb v) _.
  Next Obligation.
    constructor. intros. now rewrite substSU_trans.
  Qed.

  Class GenOccursCheck `{SubstUniv Sb} (T : LCtx -> Type) {sSUT : SubstSU Sb T} : Type :=
    gen_occurs_check : forall {Σ} (t : T Σ), Weakened Sb T Σ.
  Arguments GenOccursCheck {Sb H} T {sSUT}.

  #[export] Instance GenOccursCheck_Const `{SubstUnivMeet Sb, SubstUnivLaws Sb} {A} : GenOccursCheck (Const A) :=
    fun Σ v => weakenInit v.

  Program Definition liftUnOp `{SubstUniv Sb} {T1 T2 Σ} {_ : SubstSU Sb T1} {_ : SubstSU Sb T2}
    (f : forall {Σ'}, T1 Σ' -> T2 Σ')
    (fS : forall {Σ1 Σ2} (ζ : Sb Σ1 Σ2) t, f (substSU t ζ) = substSU (f t) ζ)
    (wv1 : Weakened Sb T1 Σ) : Weakened Sb T2 Σ :=
    match wv1 with
    | MkWeakened σ1 v1 _ => MkWeakened σ1 (liftBoxUnOp (fun _ => f) v1) _
    end.
  Next Obligation.
    intros. now eapply liftBoxUnOpLaws.
  Qed.

  Program Definition liftBinOp `{SubstUnivMeet Sb, SubstUnivLaws Sb} {T1 T2 T3 Σ}
    {sSbT1 : SubstSU Sb T1} {sSbT2 : SubstSU Sb T2} {sSbT3 : SubstSU Sb T3}
    (f : forall {Σ'}, T1 Σ' -> T2 Σ' -> T3 Σ')
    (fS : forall {Σ1 Σ2} (ζ : Sb Σ1 Σ2) v1 v2, substSU (f v1 v2) ζ = f (substSU v1 ζ) (substSU v2 ζ))
    (wv1 : Weakened Sb T1 Σ) (wv2 : Weakened Sb T2 Σ) : Weakened Sb T3 Σ :=
    match wv1 , wv2 with
    | MkWeakened σ1 v1 sL1 , MkWeakened σ2 v2 sL2 =>
        let '(MkMeetResult _ _ _ _ Σ12 σ1' σ2' σ') := meetSU σ1 σ2 in
        MkWeakened σ' (liftBoxBinOp (fun _ => f) (substSU v1 σ1') (substSU v2 σ2')) _
    end.
  Next Obligation.
    constructor. intros.
    rewrite fS.
    f_equal; now eapply unboxSbLaws, substSU_BoxSbLaws.
  Qed.

  Program Definition liftTernOp `{SubstUnivMeet Sb, SubstUnivLaws Sb} {T1 T2 T3 T4 Σ} {_ : SubstSU Sb T1} {_ : SubstSU Sb T2} {_ : SubstSU Sb T3} {_ : SubstSU Sb T4}
    (f : forall {Σ'}, T1 Σ' -> T2 Σ' -> T3 Σ' -> T4 Σ')
    (fS : forall {Σ1 Σ2} (ζ : Sb Σ1 Σ2) v1 v2 v3, substSU (f v1 v2 v3) ζ = f (substSU v1 ζ) (substSU v2 ζ) (substSU v3 ζ))
    (wv1 : Weakened Sb T1 Σ) (wv2 : Weakened Sb T2 Σ) (wv3 : Weakened Sb T3 Σ) : Weakened Sb T4 Σ :=
    liftBinOp (sSbT1 := substSU_pair) (fun _ '(v1 , v2) v3 => f v1 v2 v3) _ (liftBinOp (T3 := Pair T1 T2) (fun _ v1 v2 => (v1 , v2)) _ wv1 wv2) wv3.
  Next Obligation.
    now intros; destruct v1 as [v11 v12]; cbn.
  Qed.
  Next Obligation. now intros. Qed.

  #[export] Instance gen_occurs_check_env `{SubstUnivMeet Sb, SubstUnivLaws Sb}
    {I : Set} {T : LCtx -> I -> Set}
    {sT : forall i : I, SubstSU Sb (fun Σ : LCtx => T Σ i)}
    {sT : forall i : I, SubstSULaws Sb (fun Σ : LCtx => T Σ i)}
      {OCT : forall i, GenOccursCheck (fun Σ => T Σ i)} :
      forall {Γ : Ctx I}, GenOccursCheck (fun Σ => Env (T Σ) Γ) :=
      fix oc {Γ Σ} ts {struct ts} :=
      match ts with
      | env.nil         => weakenInit [env]
      | env.snoc ts _ t => liftBinOp (fun _ ts' t' => env.snoc (B := I) ts' _ t')
                             (fun _ _ _ _ _ => eq_refl)(oc ts) (gen_occurs_check (GenOccursCheck := OCT _) t)
      end.

  Lemma boxSbLaws_term_var `{SubstUniv Sb} {sSUM : SubstUnivMeet Sb} {sSUL : SubstUnivLaws Sb} {Σ x τ} (xIn : x∷τ ∈ Σ) : BoxSbLaws (boxSb (T := fun Σ => Term Σ τ) (term_var x)).
  Proof.
    constructor. intros. now rewrite substSU_trans.
  Qed.

  #[export] Instance gen_occurs_check_term `{SubstUniv Sb} {sSUM : SubstUnivMeet Sb} {sSUV : SubstUnivVar Sb} {sSUL : SubstUnivLaws Sb} :
    forall σ, GenOccursCheck (fun Σ => Term Σ σ) :=
    fix gen_occurs_check_term {τ Σ} (t : Term Σ τ) {struct t} :
      Weakened Sb (fun Σ => Term Σ τ) Σ :=
      match t with
      | term_var_in xIn => MkWeakened (suVar xIn) (boxSb (term_var_in ctx.in_zero)) (boxSbLaws_term_var ctx.in_zero)
      | term_val σ v => weakenInit (term_val σ v)
      | term_binop op t1 t2 =>
          liftBinOp (fun _ => term_binop op) (fun _ _ _ _ _ => eq_refl) (gen_occurs_check_term t1) (gen_occurs_check_term t2)
      | term_unop op t => liftUnOp (fun _ => term_unop op) (fun _ _ _ _ => eq_refl) (gen_occurs_check_term t)
      | term_tuple ts => liftUnOp (fun _ => term_tuple) (fun _ _ _ _ => eq_refl) (gen_occurs_check_env (OCT := @gen_occurs_check_term) ts)
      | term_union U K t0 => liftUnOp (fun _ => term_union U K) (fun _ _ _ _ => eq_refl) (gen_occurs_check_term t0)
      | term_record R ts =>
          liftUnOp (fun _ => term_record R) (fun _ _ _ _ => eq_refl)
            (gen_occurs_check_env (OCT := fun _ => @gen_occurs_check_term _) ts)
      end.

  #[export] Instance gen_occurs_check_list `{SubstUnivMeet Sb, SubstUnivLaws Sb} {T : LCtx -> Type} {sT : SubstSU Sb T} {sTL : SubstSULaws Sb T} {ocT : GenOccursCheck T} :
    GenOccursCheck (List T) :=
    fix oc {Σ} ls {struct ls} :=
      match ls with
      | nil => weakenInit nil
      | (l :: ls)%list => liftBinOp (fun _ => cons) (fun _ _ _ _ _ => eq_refl) (gen_occurs_check l) (oc ls)
      end.

  #[export] Instance gen_occurs_check_pair `{SubstUnivMeet Sb, SubstUnivLaws Sb}
    {AT} {BT} {_ : SubstSU Sb AT} {_ : SubstSU Sb BT} {_ : SubstSULaws Sb AT} {_ : SubstSULaws Sb BT}
    {_ : GenOccursCheck (Sb := Sb) AT} {_ : GenOccursCheck (Sb := Sb) BT} :
    GenOccursCheck (Pair AT BT) :=
    fun _ '(a,b) => liftBinOp (fun _ => pair) (fun _ _ _ _ _ => eq_refl) (gen_occurs_check a) (gen_occurs_check b).

  #[export] Instance gen_occurs_check_option `{SubstUnivMeet Sb, SubstUnivLaws Sb, SubstSULaws Sb AT} {_ : GenOccursCheck AT} :
    GenOccursCheck (Option AT) :=
    fun _ ma =>
      match ma with
      | Some a => liftUnOp (fun _ => Some) (fun _ _ _ _ => eq_refl) (gen_occurs_check a)
      | None   => weakenInit None
      end.

  #[export] Instance substSU_ctx `{SubstSU Sb A} :
    SubstSU Sb (fun Σ => Ctx (A Σ)) :=
    fix su {Σ1 Σ2} ts ζ :=
      match ts with
        [ctx] => [ctx]
      | ctx.snoc ts t => ctx.snoc (su ts ζ) (substSU t ζ)
      end.

  #[export] Instance substSULaws_ctx `{SubstSULaws Sb A} :
    SubstSULaws Sb (fun Σ => Ctx (A Σ)).
  Proof.
    intros Σ1 Σ2 Σ3 ζ1 ζ2 t.
    induction t; cbn; first easy.
    now rewrite IHt,?substSU_trans.
  Qed.

  #[export] Instance gen_occurscheck_ctx `{SubstSULaws Sb A} {sSUM : SubstUnivMeet Sb} {ocA : GenOccursCheck A} :
    GenOccursCheck (fun Σ => Ctx (A Σ)) :=
    fix oc {Σ} ys {struct ys} :=
      match ys with
      | ctx.nil       => weakenInit [ctx]
      | ctx.snoc ys y => liftBinOp (fun _ => ctx.snoc) (fun _ _ _ _ _ => eq_refl) (oc ys) (ocA _ y)
      end.

  Inductive WeakenedRefines `{SubstUniv Sb, SubstSU Sb T} {Σ} (R : T Σ -> T Σ -> Prop) (v : T Σ) : Weakened Sb T Σ -> Prop :=
  | MkWeakenedRefines Σsupp (ζsupp : Sb Σsupp Σ) bv (bvL : BoxSbLaws bv) :
    R (unboxSb bv ζsupp) v ->
    WeakenedRefines R v (MkWeakened ζsupp bv bvL).

  Lemma mkWeakenedRefines `{SubstUniv Sb, SubstSU Sb T} {Σ} (R : T Σ -> T Σ -> Prop)
    (v : T Σ) {Σsupp} (ζsupp : Sb Σsupp Σ) bv (bvL : BoxSbLaws bv) :
    R (unboxSb bv ζsupp) v -> WeakenedRefines R v (MkWeakened ζsupp bv bvL).
  Proof. intros HR. now constructor. Qed.

  Lemma weakenInitRefines `{SubstSULaws Sb T} {sSUM : SubstUnivMeet Sb} {Σ} R (v : T [ctx]) :
    R (substSU v initSU) (substSU v initSU) ->
    WeakenedRefines R (substSU v initSU) (weakenInit (Σ := Σ) v).
  Proof.
    intros HR.
    now apply mkWeakenedRefines.
  Qed.

  Class SubstUnivMeetLaws Sb `{SubstUnivMeet Sb} :=
    MkSubstUnivMeetLaws {
        meetSUCorrect : forall {Σ Σ1 Σ2} (σ1 : Sb Σ1 Σ) (σ2 : Sb Σ2 Σ),
        exists Σ12 meetLeft meetRight meetUp,
          MkMeetResult _ _ _ _ Σ12 meetLeft meetRight meetUp = meetSU σ1 σ2 /\
            σ1 = transSU meetLeft meetUp /\
            σ2 = transSU meetRight meetUp
      }.
  Arguments SubstUnivMeetLaws Sb {H} {H0}.

  Lemma liftUnOp_weakenedRefines' `{SubstUnivMeetLaws Sb, SubstUnivLaws Sb} {T1 T2 Σ} {R1 R2}
    {_ : SubstSU Sb T1} {_ : SubstSU Sb T2}
    (f1 : forall {Σ'}, T1 Σ' -> T2 Σ')
    (f2 : T1 Σ -> T2 Σ)
    (fS : forall {Σ1 Σ2} (ζ : Sb Σ1 Σ2) t, f1 (substSU t ζ) = substSU (f1 t) ζ)
    (fP : forall t1 t2, R1 t1 t2 -> R2 (f1 t1) (f2 t2))
    {v1} (wv1 : Weakened Sb T1 Σ) (wrv1 : WeakenedRefines R1 v1 wv1)
    : WeakenedRefines R2 (f2 v1) (liftUnOp (fun _ => f1) (fun _ _ => fS) wv1).
  Proof.
    destruct wrv1 as [? ζsupp1 bv1 bvl1 HR1]; cbn.
    apply mkWeakenedRefines.
    now apply fP.
  Qed.

  Lemma liftUnOp_weakenedRefines `{SubstUnivMeetLaws Sb, SubstUnivLaws Sb} {T1 T2 Σ} {R1 R2}
    {_ : SubstSU Sb T1} {_ : SubstSU Sb T2}
    (f : forall {Σ'}, T1 Σ' -> T2 Σ')
    (fS : forall {Σ1 Σ2} (ζ : Sb Σ1 Σ2) t, f (substSU t ζ) = substSU (f t) ζ)
    {fP : Proper (R1 ==> R2) f}
    {v1} (wv1 : Weakened Sb T1 Σ) (wrv1 : WeakenedRefines R1 v1 wv1)
      : WeakenedRefines R2 (f v1) (liftUnOp (fun _ => f) (fun _ _ => fS) wv1).
  Proof.
    eapply (liftUnOp_weakenedRefines' f (f _) fS fP wrv1).
  Qed.

  Lemma liftBinOp_weakenedRefines' `{SubstUnivMeetLaws Sb} {_ : SubstUnivLaws Sb} {T1 T2 T3 Σ}
    {R1} {R2 : T2 Σ -> T2 Σ -> Prop} {R3}
    {_ : SubstSU Sb T1} {_ : SubstSU Sb T2} {_ : SubstSU Sb T3}
    (f1 : T1 Σ -> T2 Σ -> T3 Σ)
    (f2 : forall {Σ'}, T1 Σ' -> T2 Σ' -> T3 Σ')
    (fmono2 : forall {Σ1 Σ2} (ζ : Sb Σ1 Σ2) (t1 : T1 Σ1) (t2 : T2 Σ1),
        substSU (f2 t1 t2) ζ = f2 (substSU t1 ζ) (substSU t2 ζ))
    (fP12 : forall t11 t21, R1 t11 t21 -> forall t12 t22,  R2 t12 t22 -> R3 (f2 t11 t12) (f1 t21 t22))
    {v1 v2}
    (wv1 : Weakened Sb T1 Σ) (wv2 : Weakened Sb T2 Σ)
    (wrv1 : WeakenedRefines R1 v1 wv1) (wrv2 : WeakenedRefines (T := T2) R2 v2 wv2)
      : WeakenedRefines R3 (f1 v1 v2) (liftBinOp (fun _ => f2) (fun _ _ => fmono2) wv1 wv2).
  Proof.
    destruct wrv1 as [? ζsupp1 bv1 bvl1 HR1], wrv2 as [? ζsupp2 bv2 bvl2 HR2]; cbn.
    change (fun H3 H4 : LCtx => Sb H3 H4) with Sb.
    destruct (meetSUCorrect ζsupp1 ζsupp2) as (Σ12 & ζ1 & ζ2 & ζ12 & [] & -> & ->); cbn.
    now apply mkWeakenedRefines, fP12.
  Qed.

  Lemma liftBinOp_weakenedRefines `{SubstUnivMeetLaws Sb} {_ : SubstUnivLaws Sb} {T1 T2 T3 Σ}
    {R1} {R2 : T2 Σ -> T2 Σ -> Prop} {R3}
    {_ : SubstSU Sb T1} {_ : SubstSU Sb T2} {_ : SubstSU Sb T3}
    (f : forall {Σ'}, T1 Σ' -> T2 Σ' -> T3 Σ')
    (fmono : forall {Σ1 Σ2} (ζ : Sb Σ1 Σ2) (t1 : T1 Σ1) (t2 : T2 Σ1),
        substSU (f t1 t2) ζ = f (substSU t1 ζ) (substSU t2 ζ))
    {fP : Proper (R1 ==> R2 ==> R3) f}
    {v1 v2}
    (wv1 : Weakened Sb T1 Σ) (wv2 : Weakened Sb T2 Σ)
    (wrv1 : WeakenedRefines R1 v1 wv1) (wrv2 : WeakenedRefines (T := T2) R2 v2 wv2)
      : WeakenedRefines R3 (f v1 v2) (liftBinOp (fun _ => f) (fun _ _ => fmono) wv1 wv2).
  Proof.
    eapply liftBinOp_weakenedRefines'; eassumption.
  Qed.

  Class GenOccursCheckLaws `{SubstUnivMeet Sb} {sSUL : SubstUnivLaws Sb}
    (T : LCtx -> Type) (R : forall Σ, T Σ -> T Σ -> Prop) {sT : SubstSU Sb T}  {ocT : GenOccursCheck T} : Prop :=
    MkGenOccursCheckLaws {
       oc_sound : forall {Σ} (t : T Σ), WeakenedRefines (R _) t (gen_occurs_check t)
      }.
  Arguments GenOccursCheckLaws {Sb} {H H0 sSUL} T R {sT ocT}.

  (* Hm, I seem to need something stronger to prove completeness... *)
  (* Lemma oc_univ {Sb} {sSb : SubstUnivMeet Sb} *)
  (*   (T : LCtx -> Type) {sT : Subst T} {_ : GenOccursCheckLaws T} *)
  (*   {Σ1 Σ} {σ : Sb Σ1 Σ} {t : T Σ1} : *)
  (*   let '(existT Σ1' (σ1 , ts')) := (gen_occurs_check (subst t (interpSU σ))) in *)
  (*   exists σt, σ = transSU σt σ1. *)
  (* Proof. *)
  (*   generalize (oc_sound (subst t (interpSU σ))). *)
  (*   destruct (gen_occurs_check (subst t (interpSU σ))) as (Σ' & (σ' , t')). *)
  (*   destruct (meetSU σ' σ) as [Σ12 σ1' σ2' σ'' corrσ1' corrσ2']. *)
  (*   rewrite <- corrσ1', <-corrσ2'. *)
  (*   rewrite ?interpTransSU. *)
  (* Abort.  *)

  (* TODO: automate proofs... *)
  (* Ltac occurs_check_mixin := *)
  (*   match goal with *)
  (*   | H: ?P |- ?P => exact H *)
  (*   | |- ?x = ?x => refine eq_refl *)
  (*   | |- ?x = ?y => *)
  (*       let hx := head x in *)
  (*       let hy := head y in *)
  (*       is_constructor hx; is_constructor hy; *)
  (*       first [ subst; refine eq_refl (* | f_equal *) ] *)
  (*   | |- wlp _ (occurs_check ?xIn ?t) => *)
  (*       generalize (occurs_check_sound xIn t); *)
  (*       apply wlp_monotonic; intros ? -> *)
  (*   | |- wp _ (occurs_check ?xIn (subst ?t _)) => *)
  (*       generalize (occurs_check_shift xIn t); *)
  (*       apply wp_monotonic; intros ? := *)
  (*   | |- OccursCheckLaws _ => *)
  (*       constructor; unfold OccursCheckShiftPoint, OccursCheckSoundPoint; *)
  (*       let x := fresh in *)
  (*       intros ? ? ? x; induction x *)
  (*   end. *)

  (* Ltac occurs_check_derive := *)
  (*   repeat *)
  (*     (try progress cbn; *)
  (*      first *)
  (*        [ option.tactics.mixin *)
  (*        | occurs_check_mixin]); *)
  (*   try progress cbn; try easy. *)
  (* Local Ltac derive := occurs_check_derive. *)

  #[export, refine] Instance gen_occurs_check_laws_env `{SubstUnivMeet Sb} {_ : SubstUnivLaws Sb} {_ : SubstUnivMeetLaws Sb}
    {I : Set} {T : LCtx -> I -> Set}
    {sT : forall i : I, SubstSU Sb (fun Σ : LCtx => T Σ i)}
    {slT : forall i : I, SubstSULaws Sb (fun Σ : LCtx => T Σ i)}
    {OCT : forall i, GenOccursCheck (Sb := Sb) (fun Σ => T Σ i)}
    {OCTL : forall i, GenOccursCheckLaws (Sb := Sb) (fun Σ => T Σ i) (fun _ => eq) } :
    forall {Γ : Ctx I}, GenOccursCheckLaws (Sb := Sb) (fun Σ => Env (T Σ) Γ) (fun _ => eq) :=
    fun {Γ} => MkGenOccursCheckLaws _ _ _ _ _.
  Proof.
    induction t.
    - now refine (weakenInitRefines eq [env] eq_refl).
    - refine (liftBinOp_weakenedRefines (R2 := eq)(fun _ ts' t' => ts' ► (b ↦ t')) _ IHt (oc_sound db));
      typeclasses eauto.
  Qed.

  #[export,refine] Instance gen_occurs_check_laws_term `{SubstUnivLaws Sb, SubstUnivVar Sb} {_ : SubstUnivMeet Sb} {_ : SubstUnivVarLaws Sb} {_ : SubstUnivMeetLaws Sb} {τ} :
    GenOccursCheckLaws (fun Σ => Term Σ τ) (fun _ => eq) :=
    MkGenOccursCheckLaws _ _ _ _ _.
  Proof.
    induction t; cbn.
    - refine (mkWeakenedRefines eq _ (suVar lIn) (boxSbLaws_term_var ctx.in_zero) _).
      cbn.
      now rewrite (suVarSound lIn).
    - now eapply mkWeakenedRefines.
    - eapply (liftBinOp_weakenedRefines (fun _ => term_binop op)); try eassumption.
      typeclasses eauto.
    - eapply (liftUnOp_weakenedRefines (fun _ => term_unop op)); try eassumption.
      typeclasses eauto.
    - eapply (liftUnOp_weakenedRefines (R1 := eq) (fun _ => term_tuple)).
      { typeclasses eauto. }
      induction IH; cbn.
      + refine (weakenInitRefines _ [env] eq_refl).
      + eapply (liftBinOp_weakenedRefines (fun _ E d => env.snoc E b d)); try eassumption.
        typeclasses eauto.
    - eapply (liftUnOp_weakenedRefines (fun _ => term_union U K)); try eassumption.
      typeclasses eauto.
    - eapply (liftUnOp_weakenedRefines (R1 := eq) (fun _ => term_record R)).
      + typeclasses eauto.
      + induction IH; cbn.
        * refine (weakenInitRefines _ [env] eq_refl).
        * refine (liftBinOp_weakenedRefines (fun _ E d => env.snoc E b d) _ IHIH q).
  Qed.

  #[export,refine] Instance gen_occurs_check_laws_list
    `{SubstUnivMeetLaws Sb} {T}
    {_ : SubstSU Sb T} {_ : SubstUnivLaws Sb}
    {_ : SubstSULaws Sb T}  {_ : GenOccursCheck T} {_ : GenOccursCheckLaws T (fun _ => eq)} :
    GenOccursCheckLaws (List T) (fun _ => eq) :=
    MkGenOccursCheckLaws _ _ _ _ _.
  Proof.
    induction t; first now refine (weakenInitRefines _ nil eq_refl).
    refine (liftBinOp_weakenedRefines (R1 := eq) (fun _ => cons) _ (oc_sound a) IHt);
    typeclasses eauto.
  Qed.

  #[export] Instance gen_occurs_check_laws_sub `{SubstUnivVarLaws Sb} {_ : SubstUnivMeet Sb} {_ : SubstUnivLaws Sb} {_ : SubstUnivMeetLaws Sb} {Σ} :
    GenOccursCheckLaws (Sub Σ)  (fun _ => eq) := gen_occurs_check_laws_env (T := fun Σ b => Term Σ (type b)).

  (* #[export,refine] Instance gen_occurs_check_laws_pair `{SubstUnivMeet Sb, SubstLaws AT, SubstLaws BT} {_ : SubstUnivLaws Sb} {_ : SubstUnivMeetLaws Sb} *)
  (*   {_ : GenOccursCheck AT} {_ : GenOccursCheckLaws AT} *)
  (*   {_ : GenOccursCheck BT} {_ : GenOccursCheckLaws BT} : *)
  (*   GenOccursCheckLaws (Pair AT BT) := *)
  (*   MkGenOccursCheckLaws _ _ _. *)
  (* Proof. *)
  (*   destruct t. *)
  (*   cbn. *)
  (*   destruct (oc_sound a) as (Σ1 & σ1 & a' & [] & Ha). *)
  (*   destruct (oc_sound b) as (Σ2 & σ2 & b' & [] & Hb). *)
  (*   destruct (meetSUCorrect σ1 σ2) as (Σ12 & σ1' & σ2' & σ' & [] & corrσ1 & corrσ2). *)
  (*   do 4 eexists; first easy. *)
  (*   change (substSU (?x , ?xs) ?σ) with (substSU x σ , substSU xs σ). *)
  (*   now rewrite <-?substSU_trans, <-corrσ1, <-corrσ2, <-Ha, <-Hb. *)
  (* Qed. *)

  (* #[export,refine] Instance gen_occurs_check_laws_option `{SubstUnivMeet Sb, SubstLaws AT} {_ : GenOccursCheck AT} {_ : GenOccursCheckLaws AT} : *)
  (*   GenOccursCheckLaws (Option AT) := *)
  (*   MkGenOccursCheckLaws _ _ _. *)
  (* Proof. *)
  (*   induction t; last now repeat eexists. *)
  (*   cbn. *)
  (*   destruct (oc_sound a) as (Σ1 & σ1 & a' & [] & Ha). *)
  (*   do 4 eexists; first easy. *)
  (*   change (substSU (Some ?x) ?σ) with (Some (substSU x σ))%list. *)
  (*   now f_equal. *)
  (* Qed. *)

  #[export] Instance gen_occurs_check_unit `{SubstUnivMeet Sb, SubstUnivLaws Sb} :
    GenOccursCheck Unit :=
    fun _ t => weakenInit tt.

  (* #[export,refine] Instance gen_occurs_check_laws_unit `{SubstUniv Sb} : *)
  (*   GenOccursCheckLaws Unit := *)
  (*   MkGenOccursCheckLaws _ _ _. *)
  (* Proof. *)
  (*   destruct t; now repeat eexists. *)
  (* Qed. *)

  (* #[export,refine] Instance gen_occurscheck_laws_ctx `{SubstUnivMeet Sb} {_ : SubstUnivLaws Sb} {_ : SubstUnivMeetLaws Sb} *)
  (*   `{SubstLaws A} {_ :GenOccursCheck A} {_ :GenOccursCheckLaws A} : *)
  (*   GenOccursCheckLaws (fun Σ => Ctx (A Σ)) := *)
  (*   MkGenOccursCheckLaws _ _ _. *)
  (* Proof. *)
  (*   induction t; first now repeat eexists. *)
  (*   cbn. *)
  (*   destruct IHt as (Σ1 & σ1 & a' & [] & Ht). *)
  (*   change (g _ ?t) with (gen_occurs_check t). *)
  (*   destruct (oc_sound b) as (Σ2 & σ2 & b' & [] & Hb). *)
  (*   destruct (meetSUCorrect σ1 σ2) as (Σ12 & σ1' & σ2' & σ' & [] & corrσ1 & corrσ2). *)
  (*   do 4 eexists; first easy. *)
  (*   change (substSU (?x ▻ ?xs) ?σ) with (substSU x σ ▻ substSU xs σ). *)
  (*   now rewrite <-?substSU_trans, <-corrσ1, <-corrσ2, <-Ht, <-Hb. *)
  (* Qed. *)

  Section Weakenings.
    Inductive WeakensTo : LCtx -> LCtx -> Set :=
    | WkNil : WeakensTo [ctx] [ctx]
    | WkSkipVar : forall {Σ1 Σ2} x, WeakensTo Σ1 Σ2 -> WeakensTo Σ1 (Σ2 ▻ x)
    | WkKeepVar : forall {Σ1 Σ2} x, WeakensTo Σ1 Σ2 -> WeakensTo (Σ1 ▻ x) (Σ2 ▻ x)
    .

    Fixpoint wkRefl {Σ} : WeakensTo Σ Σ :=
      match Σ with
      | [ctx] => WkNil
      | Σ ▻ x => WkKeepVar x wkRefl
      end.

    Definition wk1 {Σ b} : WeakensTo Σ (Σ ▻ b) := WkSkipVar b wkRefl.

    Fixpoint interpWk {Σ1 Σ2} (wk : WeakensTo Σ1 Σ2) : Sub Σ1 Σ2 :=
      match wk with
      | WkNil => [env]
      | WkSkipVar x wk => subst (interpWk wk) sub_wk1
      | WkKeepVar x wk => sub_up1 (interpWk wk)
      end.

    Equations(noeqns) transWk {Σ1 Σ2 Σ3} (wk12 : WeakensTo Σ1 Σ2) (wk23 : WeakensTo Σ2 Σ3) : WeakensTo Σ1 Σ3 :=
    | wk1 | WkSkipVar _ wk2 => WkSkipVar _ (transWk wk1 wk2)
    | WkNil | wk2 => wk2
    | WkSkipVar x wk1 | WkKeepVar _ wk2 => WkSkipVar _ (transWk wk1 wk2)
    | WkKeepVar x wk1 | WkKeepVar _ wk2 => WkKeepVar _ (transWk wk1 wk2)
    .
    #[global] Transparent transWk.
    Arguments transWk {Σ1 Σ2 Σ3} wk12 wk23 : simpl nomatch.

    Lemma interpTransWk {Σ1 Σ2 Σ3} (wk12 : WeakensTo Σ1 Σ2) (wk23 : WeakensTo Σ2 Σ3) :
      interpWk (transWk wk12 wk23) = subst (interpWk wk12) (interpWk wk23).
    Proof.
      revert Σ1 wk12.
      induction wk23 as [|? ? ? wk23 IH|? ? ? wk23 IH]; intros; [depelim wk12| |depelim wk12];
        cbn -[subst]; rewrite ?IH.
      - easy.
      - apply sub_comp_assoc.
      - rewrite !(sub_comp_assoc (interpWk wk12)).
        now rewrite sub_comp_wk1_comm.
      - apply sub_up1_comp.
    Qed.

    Fixpoint wkNilInit {Σ} : WeakensTo [ctx] Σ :=
      match Σ with
      | [ctx] => WkNil
      | Σ ▻ x => WkSkipVar x wkNilInit
      end.

    Fixpoint wkKeepCtx {Σ1 Σ2} (ζ : WeakensTo Σ1 Σ2) Δ :
      WeakensTo (Σ1 ▻▻ Δ) (Σ2 ▻▻ Δ) :=
      match Δ with
      | [ctx] => ζ
      | Δ' ▻ x => WkKeepVar x (wkKeepCtx ζ Δ')
      end.


    Lemma transWk_wkKeepCtx {Σ1 Σ2 Σ3} {ζ1 : WeakensTo Σ1 Σ2} {ζ2 : WeakensTo Σ2 Σ3} (Σ : LCtx) :
      wkKeepCtx (transWk ζ1 ζ2) Σ = transWk (wkKeepCtx ζ1 Σ) (wkKeepCtx ζ2 Σ).
    Proof.
      induction Σ; first easy.
      cbn; now rewrite IHΣ.
    Qed.

    Fixpoint wkKeepCtxRemove {Σ1 Σ2 b} {bIn1 : b ∈ Σ1} {bIn2 : b ∈ Σ2}
      (ζ : WeakensTo (ctx.remove bIn1) (ctx.remove bIn2)) Δ :
      WeakensTo (ctx.remove (ctx.in_cat_left Δ bIn1)) (ctx.remove (ctx.in_cat_left Δ bIn2)) :=
      match Δ with
      | [ctx] => ζ
      | Δ' ▻ x => WkKeepVar x (wkKeepCtxRemove ζ Δ')
      end.

    Lemma transWk_wkKeepCtxRemove {Σ1 Σ2 Σ3 b} {bIn1 : b ∈ Σ1} {bIn2 : b ∈ Σ2} {bIn3 : b ∈ Σ3}
      (ζ1 : WeakensTo (ctx.remove bIn1) (ctx.remove bIn2))
      (ζ2 : WeakensTo (ctx.remove bIn2) (ctx.remove bIn3)) Δ :
      transWk (wkKeepCtxRemove ζ1 Δ) (wkKeepCtxRemove ζ2 Δ) = wkKeepCtxRemove (transWk ζ1 ζ2) Δ.
    Proof. induction Δ; cbn; now f_equal. Qed.

    Lemma transWk_refl_2 `{σ : WeakensTo Σ1 Σ2}: transWk σ wkRefl = σ.
    Proof.
      induction σ; first easy; cbn;
        now f_equal.
    Qed.

    Lemma transWk_refl_1 `{σ : WeakensTo Σ1 Σ2}: transWk wkRefl σ = σ.
    Proof.
      induction σ; first easy; cbn;
        now f_equal.
    Qed.

    Lemma interpWk_wkRefl {Σ} : interpWk (wkRefl (Σ := Σ)) = sub_id _.
    Proof.
      induction Σ; first easy.
      cbn. rewrite IHΣ.
      now rewrite sub_up1_id.
    Qed.

    Inductive WeakenZeroView Σ2 b : forall Σ1, WeakensTo Σ1 (Σ2 ▻ b) -> Type :=
    | VarUnused : forall Σ1 (wk : WeakensTo Σ1 Σ2), WeakenZeroView (WkSkipVar b wk)
    | VarUsed : forall Σ1 (wk : WeakensTo Σ1 Σ2), WeakenZeroView (WkKeepVar b wk)
    .

    Equations(noeqns) weakenZeroView {Σ1 Σ2 b} (wk : WeakensTo Σ1 (Σ2 ▻ b)) : WeakenZeroView wk :=
    | WkSkipVar _ wk => VarUnused b wk
    | WkKeepVar _ wk => VarUsed b wk
    .

    Inductive WeakenNilView : forall Σ1, WeakensTo Σ1 [ctx] -> Type :=
    | WkNilViewNil : WeakenNilView WkNil
    .

    Equations(noeqns) weakenNilView {Σ1} (wk : WeakensTo Σ1 [ctx]) : WeakenNilView wk :=
    | WkNil => WkNilViewNil
    .

    Fixpoint wkRemove (Σ : LCtx) b (bIn : b ∈ Σ) : WeakensTo (Σ - b) Σ :=
      ctx.In_case (fun b Σ bIn => WeakensTo (Σ - b) Σ)
                  (fun b Σ => WkSkipVar _ wkRefl)
                  (fun b' Σ b bIn => WkKeepVar _ (wkRemove bIn))
                  bIn.
    Lemma interpWk_wkRemove : forall b (Σ : LCtx) (bIn : b ∈ Σ),
      interpWk (wkRemove bIn) = sub_shift bIn.
    Proof.
      eapply ctx.In_ind; intros.
      - cbn -[subst sub_wk1 sub_shift].
        now rewrite interpWk_wkRefl, sub_comp_id_left.
      - cbn -[subst sub_wk1 sub_shift].
        change ({| ctx.in_at := @ctx.in_at _ _ _ bIn;
                   ctx.in_valid := @ctx.in_valid _ _ _ bIn
                 |}) with bIn.
        rewrite H.
        now apply sub_shift_succ.
    Qed.


    Fixpoint wkSingleton {Σ : LCtx} {b} (bIn : b ∈ Σ) : WeakensTo [ b ]%ctx Σ :=
      ctx.In_case (fun b Σ bIn => WeakensTo [ b ]%ctx Σ)
                  (fun b Σ => WkKeepVar _ wkNilInit)
                  (fun b' Σ b bIn => WkSkipVar _ (wkSingleton bIn))
                  bIn.

    Equations(noeqns) wkVarZeroIn {Σ Σ' : LCtx} {b} (σ : WeakensTo (Σ' ▻ b)%ctx Σ) : b ∈ Σ :=
    | WkKeepVar _ _ => ctx.in_zero
    | WkSkipVar _ wk => ctx.in_succ (wkVarZeroIn wk)
    .

    Fixpoint weakenIn {Σ1 Σ2 : LCtx} (σ : WeakensTo Σ1 Σ2) : forall {b} (bIn : b ∈ Σ1), b ∈ Σ2 :=
      match σ with
      | WkNil => fun b (bIn : b ∈ [ctx]) => match ctx.view bIn with end
      | WkSkipVar _ σ' => fun b bIn => ctx.in_succ (weakenIn σ' bIn)
      | WkKeepVar _ σ' => fun b bIn => match ctx.view bIn with
                                     | ctx.isZero => ctx.in_zero
                                     | ctx.isSucc bIn' => ctx.in_succ (weakenIn σ' bIn')
                                     end
      end.
    Arguments weakenIn {Σ1 Σ2} σ {b} bIn : simpl nomatch.

    Lemma weakenIn_transWk {Σ b} (xIn : (b ∈ Σ)%katamaran) {Σ2 Σ3}
      (ζ1 : WeakensTo Σ Σ2) (ζ2 : WeakensTo Σ2 Σ3) :
      weakenIn ζ2 (weakenIn ζ1 xIn) = weakenIn (transWk ζ1 ζ2) xIn.
    Proof.
      revert Σ b xIn ζ1.
      induction ζ2; intros *.
      - dependent elimination ζ1; cbn.
        destruct (ctx.view xIn).
      - cbn.
        now f_equal.
      - dependent elimination ζ1.
        + cbn.
          now f_equal.
        + destruct (ctx.view xIn); cbn; first easy.
          f_equal.
          clear -IHζ2.
          refine (IHζ2 _ _ _ w0).
    Qed.

    Lemma weakenRemovePres {Σ1 Σ2} (wk : WeakensTo Σ1 Σ2) :
      forall {b} (bIn : b ∈ Σ1),
        let bIn' := weakenIn wk bIn in WeakensTo (Σ1 - b) (Σ2 - b).
    Proof.
      induction wk; intros b bIn.
      - destruct (ctx.view bIn).
      - apply WkSkipVar, IHwk.
      - destruct (ctx.view bIn); first easy.
        apply WkKeepVar, IHwk.
    Defined.
    Arguments weakenRemovePres {Σ1 Σ2} wk {b} bIn : simpl nomatch.

    Inductive WeakenRemoveView {Σ b} : forall {Σ1} (bIn : b ∈ Σ), WeakensTo Σ1 (Σ - b) -> Set :=
    | MkWeakenRemoveView : forall Σ1' (bIn' : b ∈ Σ1') (σ1' : WeakensTo Σ1' Σ),
        WeakenRemoveView (weakenIn σ1' bIn') (weakenRemovePres σ1' bIn').

    Definition weakenRemoveView : forall {b Σ} (bIn : b ∈ Σ) Σ1 (σ : WeakensTo Σ1 (Σ - b)), WeakenRemoveView bIn σ :=
      ctx.In_rect (fun b Σ bIn => forall Σ1 σ, WeakenRemoveView bIn σ)
        (fun b Σ Σ' σ => MkWeakenRemoveView ctx.in_zero (WkKeepVar _ σ))
                  (fun b Σ b' bIn IHbIn Σ1 σ =>
                     match weakenZeroView σ with
                     | VarUsed _ σ' =>
                         match IHbIn _ σ'
                               in WeakenRemoveView bIn σ'
                               return WeakenRemoveView (ctx.in_succ bIn) _ with
                         | (MkWeakenRemoveView bIn' σ1') =>
                             MkWeakenRemoveView (ctx.in_succ bIn') (WkKeepVar _ σ1')
                         end
                     | VarUnused _ σ' =>
                         match IHbIn _ σ'
                               in WeakenRemoveView bIn σ'
                               return WeakenRemoveView (ctx.in_succ bIn) _ with
                         | MkWeakenRemoveView bIn' σ1' =>
                             MkWeakenRemoveView bIn' (WkSkipVar _ σ1')
                         end
                     end
                  ).

    Inductive WeakenVarView {Σ2} {b} (bIn : b ∈ Σ2) : forall Σ1, WeakensTo Σ1 Σ2 -> Type :=
    | WeakenVarUnused : forall {Σ1} (wk : WeakensTo Σ1 (Σ2 - b)), WeakenVarView bIn (transWk wk (wkRemove bIn))
    | WeakenVarUsed : forall {Σ1} (bIn' : b ∈ Σ1) (wk : WeakensTo Σ1 Σ2), WeakenVarView bIn wk
    .

    Equations(noeqns) weakenVarView {Σ1 Σ2 b} (bIn2 : b ∈ Σ2) (wk : WeakensTo Σ1 Σ2) : WeakenVarView bIn2 wk :=
    | bIn2 | WkNil => match ctx.view bIn2 with end
    | bIn2 | WkSkipVar _ wk =>
               match ctx.view bIn2 with
               | ctx.isZero => _ (* WeakenVarUnused ctx.in_zero wk *)
               | ctx.isSucc bIn2' => let Hind := weakenVarView bIn2' wk in
                                     _
               end
    | bIn2 | WkKeepVar _ wk =>
               match ctx.view bIn2 with
               | ctx.isZero => WeakenVarUsed _ ctx.in_zero _
               | ctx.isSucc bIn2' => let Hind := weakenVarView bIn2' wk in
                                     _
               end
    .
    Next Obligation.
      intros. clear bIn2 b.
      replace (WkSkipVar x wk) with (transWk wk (wkRemove (b := x) ctx.in_zero)).
      eapply (WeakenVarUnused ctx.in_zero wk).
      cbn.
      now rewrite transWk_refl_2.
    Defined.
    Next Obligation.
      intros. clear bIn2 b.
      destruct Hind.
      - replace (WkSkipVar x (transWk wk (wkRemove bIn2')))
          with (transWk (WkSkipVar x wk) (wkRemove (ctx.in_succ bIn2'))).
        eapply (WeakenVarUnused (ctx.in_succ bIn2') (WkSkipVar x wk)).
        now simpl.
      - now eapply WeakenVarUsed.
    Defined.
    Next Obligation.
      intros. clear bIn2 b.
      destruct Hind.
      - replace (WkKeepVar x0 (transWk wk (wkRemove bIn2')))
          with (transWk (WkKeepVar x0 wk) (wkRemove (ctx.in_succ bIn2'))).
        eapply (WeakenVarUnused (ctx.in_succ bIn2') (WkKeepVar x0 wk)).
        now simpl.
      - now eapply WeakenVarUsed, ctx.in_succ.
    Defined.

    #[export] Instance substUniv_weaken : SubstUniv WeakensTo.
    Proof.
      econstructor.
      - intros. exact wkNilInit.
      - intros. eapply transWk; eassumption.
      - intros; now eapply interpWk.
    Defined.

    Definition extendMeetSkipSkip {Σ1 Σ2 Σ3 x} (meet : MeetResult Σ3 Σ1 Σ2) :
      MeetResult (Σ3 ▻ x) Σ1 Σ2 :=
      match meet with
        MkMeetResult _ _ _ _ Σ12 σ1' σ2' σ' => MkMeetResult _ _ _ _ Σ12 σ1' σ2' (WkSkipVar x σ')
      end.
    Definition extendMeetSkipKeep {Σ1 Σ2 Σ3 x} (meet : MeetResult Σ3 Σ1 Σ2) :
      MeetResult (Σ3 ▻ x) Σ1 (Σ2 ▻ x) :=
      match meet with
        MkMeetResult _ _ _ _ Σ12 σ1' σ2' σ' => MkMeetResult _ _ _ _ _ (WkSkipVar x σ1') (WkKeepVar _ σ2') (WkKeepVar x σ')
      end.
    Definition extendMeetKeepSkip {Σ1 Σ2 Σ3 x} (meet : MeetResult Σ3 Σ1 Σ2) :
      MeetResult (Σ3 ▻ x) (Σ1 ▻ x) Σ2 :=
      match meet with
        MkMeetResult _ _ _ _ Σ12 σ1' σ2' σ' => MkMeetResult _ _ _ _ _ (WkKeepVar x σ1') (WkSkipVar _ σ2') (WkKeepVar x σ')
      end.
    Definition extendMeetKeepKeep {Σ1 Σ2 Σ3 x} (meet : MeetResult Σ3 Σ1 Σ2) :
      MeetResult (Σ3 ▻ x) (Σ1 ▻ x) (Σ2 ▻ x) :=
      match meet with
        MkMeetResult _ _ _ _ Σ12 σ1' σ2' σ'  => MkMeetResult _ _ _ _ _ (WkKeepVar x σ1') (WkKeepVar _ σ2') (WkKeepVar x σ')
      end.
    Equations(noeqns) meetWk {Σ1 Σ2 Σ3} (wk13 : WeakensTo Σ1 Σ3) (wk23 : WeakensTo Σ2 Σ3) :
      MeetResult Σ3 Σ1 Σ2 :=
    | WkNil | WkNil => MkMeetResult _ _ _ _ _ WkNil WkNil WkNil
    | WkSkipVar x wk1 | WkSkipVar _ wk2 => extendMeetSkipSkip (meetWk wk1 wk2)
    | WkSkipVar x wk1 | WkKeepVar _ wk2 => extendMeetSkipKeep (meetWk wk1 wk2)
    | WkKeepVar x wk1 | WkSkipVar _ wk2 => extendMeetKeepSkip (meetWk wk1 wk2)
    | WkKeepVar x wk1 | WkKeepVar _ wk2 => extendMeetKeepKeep (meetWk wk1 wk2)
    .
    #[global] Transparent meetWk.
    Arguments meetWk {Σ1 Σ2 Σ3} wk13 wk23 : simpl nomatch.

    #[export] Instance substUnivMeet_weaken : SubstUnivMeet WeakensTo :=
      fun _ _ _ => meetWk.
    #[export] Instance substUnivMeetLaws_weaken : SubstUnivMeetLaws WeakensTo.
    Proof.
      constructor; intros Σ Σ1 Σ2 σ1 σ2.
      enough (exists Σ13 meetLeft meetRight meetUp,
                 MkMeetResult _ _ _ _ Σ13 meetLeft meetRight meetUp = meetWk σ1 σ2 /\
                 σ1 = transWk meetLeft meetUp /\ σ2 = transWk meetRight meetUp) by easy.
      revert Σ2 σ2.
      induction σ1 as [|? ? ? σ1 IH|? ? ? σ1 IH]; intros; depelim σ2;
        try destruct (IH _ σ2) as (? & ? & ? & ? & H & corrσ1 & corrσ2);
        cbn; try destruct H;
        (do 5 eexists; first easy);
        cbn; now split; f_equal.
    Qed.

    Definition wkVar : forall {x Σ}, x ∈ Σ -> WeakensTo [ x ]%ctx Σ :=
      ctx.In_rect (fun x Σ xIn => WeakensTo [ x ]%ctx Σ)
                  (fun x Σ => WkKeepVar x wkNilInit)
                  (fun x Σ y xIn wk => WkSkipVar y wk).

    Lemma interpWk_wkVar : forall {x Σ} {xIn : x ∈ Σ},
      interpWk (wkVar xIn) = [ term_var_in xIn ]%env.
    Proof.
      eapply ctx.In_ind.
      - intros.
        refine (f_equal (fun x => x.[b ↦ _]) _).
        match goal with |- ?env = [env] => now destruct (env.view env) end.
      - intros.
        change (interpWk (wkVar (ctx.in_succ bIn))) with
                 (subst (interpWk (wkVar bIn)) (sub_wk1 (b := b'))).
        rewrite H.
        cbn.
        now rewrite lookup_sub_wk1.
    Qed.

    Lemma transWk_assoc {Σ1 Σ2 Σ3 Σ4} (σ1 : WeakensTo Σ1 Σ2) (σ2 : WeakensTo Σ2 Σ3) (σ3 : WeakensTo Σ3 Σ4) :
      transWk σ1 (transWk σ2 σ3) = transWk (transWk σ1 σ2) σ3.
    Proof.
      revert Σ1 Σ2 σ1 σ2.
      induction σ3 as [|? ? ? σ3 IH|? ? ? σ3 IH]; intros.
      - depelim σ2. depelim σ1. reflexivity.
      - cbn. now f_equal.
      - depelim σ2.
        + cbn. now f_equal.
        + depelim σ1; cbn; now f_equal.
    Qed.

    #[export] Instance substUnivLaws_wk : SubstUnivLaws WeakensTo.
    Proof.
      constructor.
      - intros Σ1 Σ2 Σ3 σ1 σ2.
        change (substSU (interpSU σ1) σ2 = interpSU (transWk σ1 σ2)).
        revert Σ1 σ1.
        induction σ2 as [|? ? ? σ2 H|? ? ? σ2 H]; intros; [depelim σ1| |depelim σ1];
          cbn -[substSU];
        change (interpWk ?ζ) with (interpSU ζ).
        + easy.
        + now rewrite <-H, ?substSU_interpSU, sub_comp_assoc.
        + now rewrite <-H, ?substSU_interpSU, ?sub_comp_assoc, <-sub_comp_wk1_comm.
        + now rewrite <-H, ?substSU_interpSU, sub_up1_comp.
      - intros. now eapply transWk_assoc.
    Qed.

    Arguments SubstUnivLaws Sb {H}.
    #[export] Instance substUnivVar_weaken : SubstUnivVar WeakensTo :=
      (fun x Σ xIn => wkVar xIn).
    #[export] Instance substUnivVarUp_weaken : SubstUnivVarUp WeakensTo.
    Proof.
      intros Σ1 Σ2 x σ; now eapply WkKeepVar.
    Defined.
    #[export] Instance substUnivVarUpLaws_weaken : SubstUnivVarUpLaws WeakensTo.
    Proof.
      intros Σ1 Σ2 x ζ. now cbn.
    Qed.

    #[export] Instance substUnivVarDown_weaken : SubstUnivVarDown WeakensTo.
    Proof.
      refine (MkSubstUnivVarDown _ (fun _ _ _ xIn σ => weakenIn σ xIn) _).
      intros; eapply weakenRemovePres.
    Defined.

    #[export] Instance substUnivVarLaws_weaken : SubstUnivVarLaws WeakensTo :=
      (fun _ _ xIn => interpWk_wkVar).

    Fixpoint restrictEnv {D} {Σ1 Σ2 : LCtx} (wk : WeakensTo Σ1 Σ2) :
      Env D Σ2 -> Env D Σ1.
    Proof.
      induction wk; first easy.
      intros e. eapply IHwk, env.tail. now eassumption.
      intros e. destruct (env.view e) as [e v].
      apply env.snoc; last easy.
      now eapply IHwk.
    Qed.

    Program Definition elimWeakenedVarZero {T} {_ : SubstSU WeakensTo T} {_ : SubstSULaws WeakensTo T} {Σ b}
      (funused : forall Σs, T Σs -> T Σs)
      (funusedM : forall {Σ1 Σ2} (ζ : WeakensTo Σ1 Σ2) (t : T Σ1), funused Σ2 (substSU t ζ) = substSU (funused Σ1 t) ζ)
      (fused : forall Σs, T (Σs ▻ b) -> T Σs)
      (wv : Weakened WeakensTo T (Σ ▻ b)) : Weakened WeakensTo T Σ :=
      match wv with
        MkWeakened σ1 v vL =>
          match weakenZeroView σ1 in @WeakenZeroView _ _ Σ1 σ1 return (forall (v' : BoxSb WeakensTo T Σ1), BoxSbLaws v' -> Weakened WeakensTo T Σ) with
          | VarUnused _ σ1' => fun v' vL' => MkWeakened σ1' (liftBoxUnOp funused v') _
          | VarUsed _ σ1' => fun v' vL' => MkWeakened σ1' (boxSb (fused _ (unboxSb v' wkRefl))) _
          end v vL
      end.
    Next Obligation.
      intros. now apply liftBoxUnOpLaws.
    Qed.
    Next Obligation.
      intros. apply boxSbLaws.
    Qed.

    Program Definition elimWeakenedVar {T1 T2} {_ : SubstSU WeakensTo T1} {_ : SubstSU WeakensTo T2} {_ : SubstSULaws WeakensTo T2}
      {Σ b} {bIn : b ∈ Σ}
      (f : forall Σs {bIn' : b ∈ Σs}, T1 (Σs - b) -> T2 Σs)
      (wv : Weakened WeakensTo T1 (Σ - b)) : Weakened WeakensTo T2 Σ :=
      match wv with
        MkWeakened σ1 v vL =>
          match weakenRemoveView bIn σ1 in @WeakenRemoveView _ _ Σ1 bIn σ1
                return (forall (v : BoxSb WeakensTo T1 Σ1), BoxSbLaws v -> Weakened WeakensTo T2 Σ) with
          | @MkWeakenRemoveView _ _ Σ1' bIn' σ1' =>
              fun v' vL' => MkWeakened σ1' (boxSb (f _ (unboxSb v' wkRefl))) _
          end v vL
      end.
    Next Obligation.
      intros. apply boxSbLaws.
    Qed.


    Lemma weakenRemovePres_wkRemove {Σ1 Σ2 b} (bIn : b ∈ Σ1) (σ : WeakensTo Σ1 Σ2) :
      transWk (weakenRemovePres σ bIn) (wkRemove (weakenIn σ bIn)) =
        transWk (wkRemove bIn) σ.
    Proof.
      revert b bIn.
      induction σ; intros b bIn.
      - destruct (ctx.view bIn).
      - exact (f_equal (WkSkipVar x) (IHσ b bIn)).
      - destruct (ctx.view bIn).
        + cbn.
          now rewrite transWk_refl_1, transWk_refl_2.
        + exact (f_equal (WkKeepVar x) (IHσ b i)).
    Qed.

    Lemma subst_weakenRemovePres_wkRemove {Σ1 Σ2 b} (bIn : b ∈ Σ1) (σ : WeakensTo Σ1 Σ2) :
      subst (interpWk (weakenRemovePres σ bIn)) (interpWk (wkRemove (weakenIn σ bIn))) =
        subst (interpWk (wkRemove bIn)) (interpWk σ).
    Proof.
      now rewrite <-?interpTransWk, weakenRemovePres_wkRemove.
    Qed.

    Lemma weakenRemovePres_transWk {Σ x σ} (xIn : (x∷σ ∈ Σ)%katamaran) {Σ2 Σ3}
      (ζ1 : WeakensTo Σ Σ2) (ζ2 : WeakensTo Σ2 Σ3)
      (P : forall xIn0 : (x∷σ ∈ Σ3)%katamaran, WeakensTo (Σ - x∷σ) (Σ3 - x∷σ) -> Prop) :
      P (weakenIn (transWk ζ1 ζ2) xIn) (weakenRemovePres (transWk ζ1 ζ2) xIn) ->
      P (weakenIn ζ2 (weakenIn ζ1 xIn)) (transWk (weakenRemovePres ζ1 xIn) (weakenRemovePres ζ2 (weakenIn ζ1 xIn))).
    Proof.
      revert Σ ζ1 xIn P.
      induction ζ2; intros Σ ζ1 xIn P.
      - destruct (weakenNilView ζ1), (ctx.view xIn).
      - simpl.
        now refine (IHζ2 _ ζ1 xIn (fun xIn ζ => P (ctx.in_succ xIn) (WkSkipVar x0 ζ))).
      - destruct (weakenZeroView ζ1).
        + simpl.
          now refine (IHζ2 _ wk xIn (fun xIn ζ => P (ctx.in_succ xIn) (WkSkipVar x0 ζ))).
        + destruct (ctx.view xIn).
          * now simpl.
          * simpl.
            now refine (IHζ2 _ wk i (fun xIn ζ => P (ctx.in_succ xIn) (WkKeepVar x0 ζ))).
    Qed.

    Lemma elimWeakenedVarZero_weakenedRefines
      {T Σ} {b}
      {R1 R2}
      {_ : SubstSU WeakensTo T} {_ : SubstSULaws WeakensTo T}
      (funused : forall Σs, T Σs -> T Σs)
      (funusedM : forall {Σ1 Σ2} (ζ : WeakensTo Σ1 Σ2) (t : T Σ1), funused Σ2 (substSU t ζ) = substSU (funused Σ1 t) ζ)
      (fused : forall Σs, T (Σs ▻ b) -> T Σs)
      (fusedM : forall {Σ1 Σ2} (ζ : WeakensTo Σ1 Σ2) (t : T (Σ1 ▻ b)), fused _ (substSU t (WkKeepVar b ζ)) = substSU (fused _ t) ζ)
      (fusedP : Proper (R1 ==> R2) (fused Σ))
      {funusedP : forall t1 t2, R1 (substSU t1 (WkSkipVar b wkRefl)) t2 -> R2 (funused Σ t1) (fused Σ t2)}
      {v1} (wv1 : Weakened WeakensTo T (Σ ▻ b)) (wrv1 : WeakenedRefines R1 v1 wv1)
      : WeakenedRefines R2 (fused _ v1) (elimWeakenedVarZero funused (fun _ _ => funusedM) fused wv1).
    Proof.
      destruct wrv1 as [? ζsupp1 bv1 bvl1 HR1]; cbn.
      destruct (weakenZeroView ζsupp1); apply mkWeakenedRefines; cbn.
      - eapply funusedP.
        rewrite unboxSbLaws by easy; cbn.
        now rewrite transWk_refl_2.
      - rewrite <-fusedM.
        apply fusedP.
        rewrite unboxSbLaws by easy; cbn.
        now rewrite transWk_refl_1.
    Qed.

    Lemma elimWeakenedVar_weakenedRefines {T1 T2} {_ : SubstSU WeakensTo T1} {_ : SubstSU WeakensTo T2} {_ : SubstSULaws WeakensTo T2}
      {Σ b} {bIn : b ∈ Σ} {R1 R2}
      (f1 : forall Σs  {bIn' : b ∈ Σs}, T1 (Σs - b) -> T2 Σs)
      (f2 : T1 (Σ - b) -> T2 Σ)
      (f1M : forall {Σ1 Σ2} {bIn' : b ∈ Σ1} (ζ : WeakensTo Σ1 Σ2) (t : T1 (Σ1 - b)),
          f1 _ (substSU t (weakenRemovePres ζ bIn')) = substSU (f1 _ t) ζ)
      (fP : forall t1 t2, R1 t1 t2 -> R2 (f1 _ t1) (f2 t2))
      {v1} (wv1 : Weakened WeakensTo T1 (Σ - b)) (wrv1 : WeakenedRefines R1 v1 wv1)
      : WeakenedRefines R2 (f2 v1) (elimWeakenedVar f1 wv1).
    Proof.
      destruct wrv1 as [? ζsupp1 bv1 bvl1 HR1]; cbn.
      destruct (weakenRemoveView bIn ζsupp1); apply mkWeakenedRefines; cbn.
      rewrite <-f1M.
      apply fP.
      now rewrite unboxSbLaws, transWk_refl_1.
    Qed.

  End Weakenings.

  Section Substitutions.
    #[export] Instance substUniv_Sub : SubstUniv Sub := MkSubstUniv Sub (fun _ => [env]) (fun Σ1 Σ2 Σ3 ζ1 ζ2 => subst ζ1 ζ2) (fun _ _ ζ => ζ).
  End Substitutions.


  Section BackwardsCompat.
    Definition old_occurs_check {T} {sT : SubstSU WeakensTo T} {gocT : GenOccursCheck (Sb := WeakensTo) T}
      {Σ x} (xIn : x ∈ Σ) (t : T Σ) : option (T (Σ - x)) :=
      let '(MkWeakened ζ t' tL') := gen_occurs_check (T := T) (Sb := WeakensTo) t in
      match weakenVarView xIn ζ with
      | WeakenVarUnused _ ζ' =>
          fun t' => Some (unboxSb t' ζ')
      | WeakenVarUsed _ _ _ => fun _ => None
      end t'.

    Lemma old_occurs_check_sound {T R} {sT : SubstSU WeakensTo T}
      {gocT : GenOccursCheck (Sb := WeakensTo) T}
      {gocLT : GenOccursCheckLaws (Sb := WeakensTo) T R}
      {Σ x} (xIn : x ∈ Σ) (t : T Σ) :
      wlp (fun t' => R _ (substSU (SubstSU := sT) t' (wkRemove xIn)) t)
        (old_occurs_check (T := T) xIn t).
    Proof.
      unfold old_occurs_check.
      destruct (oc_sound t) as [Σsupp ζ t' tL' HR]; cbn.
      destruct (weakenVarView xIn ζ).
      - eapply wlp_some.
        now rewrite unboxSbLaws.
      - now eapply wlp_none.
    Qed.

  End BackwardsCompat.
End GenOccursCheckOn.
