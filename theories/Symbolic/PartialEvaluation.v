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

From Stdlib Require Import
     Arith.PeanoNat
     Bool.Bool
     Classes.Morphisms
     Classes.RelationClasses
     List
     NArith.BinNat
     ZArith.BinInt
     PArith
     Ring
     Ring_polynom
     micromega.Lia.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Base
     Bitvector
     Symbolic.Instantiation
     Syntax.Terms.

Import (notations) stdpp.base.
Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.
Local Set Transparent Obligations.
Local Unset Elimination Schemes.
Local Set Equations Transparent.

Section Util.
  Lemma jump_of_succ_nat_length {A : Type} {def : A} {lo l : list A} :
    BinList.jump (Pos.of_succ_nat (length lo)) (def :: lo ++ l) = l.
  Proof.
    revert def.
    induction lo; intros def; cbn; [easy|].
    rewrite BinList.jump_succ; cbn.
    rewrite BinList.jump_tl; cbn.
    now apply IHlo.
  Qed.

  Lemma nth_length_prefix {o} {A} {def} {lo l : list A} : o = Pos.of_succ_nat (length lo) -> BinList.nth def o (lo ++ l) = hd def l.
  Proof.
    intros ->.
    change (lo ++ l) with (tl (def ::(lo ++ l))).
    rewrite BinList.nth_jump.
    f_equal.
    now apply jump_of_succ_nat_length.
  Qed.

  Lemma nth_succ {i} {A} {def t} {ts : list A} :
    BinList.nth def (Pos.succ i) (t :: ts) = BinList.nth def i ts.
  Proof.
    change (t :: ts)%list with (tl (def :: t :: ts)).
    rewrite BinList.nth_jump.
    replace ((Pos.succ i)) with (i + 1)%positive by lia.
    rewrite BinList.jump_add.
    cbn.
    now rewrite <-BinList.nth_jump.
  Qed.

  Lemma nth_lookup {i} {A} {def} {ts la : list A} {t} :
      ts !! i = Some t ->
      BinList.nth def (Pos.of_succ_nat i) (ts ++ la) = t.
  Proof.
    revert i.
    induction ts; intros i; first inversion 1.
    destruct i; inversion 1; first easy; cbn.
    rewrite nth_succ.
    now eapply IHts.
  Qed.

  Fixpoint plusNatPos (n : nat) (p : positive) : positive :=
    match n with
    | 0 => p
    | S n => Pos.succ (plusNatPos n p)
    end.

  Lemma plusNatPos_of_succ_nat {n m} : plusNatPos n (Pos.of_succ_nat m) = Pos.of_succ_nat (n + m).
  Proof. induction n; cbn; now f_equal. Qed.
End Util.

Module Type PartialEvaluationOn (Import B : Base).

  Section WithLCtx.
    Context {Σ : LCtx}.

    #[local] Ltac lsolve :=
      try progress cbn;
      first
        [ intros ?; reflexivity
        | try (progress autorewrite with katamaran);
          try easy;
          auto with core katamaran ].

    Class TermRing (σ : Ty) :=
      MkTermRing {
          tmr_zero : Val σ
        ; tmr_one : Val σ
        ; tmr_plus : BinOp σ σ σ
        ; tmr_times : BinOp σ σ σ
        ; tmr_minus : BinOp σ σ σ
        ; tmr_negate : UnOp σ σ
        ; tmr_of_Z : Z -> Val σ
        ; tmr_ring_morph : ring_morph (term_val (Σ := Σ) σ tmr_zero) (term_val σ tmr_one)
                             (term_binop tmr_plus) (term_binop tmr_times) (term_binop tmr_minus)
                             (term_unop tmr_negate) base.equiv 0%Z 1%Z
                             Z.add Z.mul Z.sub Z.opp Z.eqb (λ c : Z, term_val σ (tmr_of_Z c))
        ; tmr_ring_theory : ring_theory (term_val (Σ := Σ) σ tmr_zero) (term_val σ tmr_one) (term_binop tmr_plus) (term_binop tmr_times) (term_binop tmr_minus) (term_unop tmr_negate) base.equiv
        ; tmr_ring_eq_ext : ring_eq_ext (term_binop (Σ := Σ) tmr_plus) (term_binop tmr_times) (term_unop tmr_negate) base.equiv
        }.

    #[program,export] Instance TermRing_int : TermRing ty.int := {
        tmr_zero := 0%Z
      ; tmr_one := 1%Z
      ; tmr_plus := bop.plus
      ; tmr_times := bop.times
      ; tmr_minus := bop.minus
      ; tmr_negate := uop.neg
      ; tmr_of_Z := id
      ; tmr_ring_theory := Term_int_ring_theory
      ; tmr_ring_eq_ext := Term_int_ring_eq_ext
      }.
    Next Obligation.
      constructor; try reflexivity; intros;
        rewrite ?term_binop_val, ?term_unop_val; try reflexivity.
      now apply Z.eqb_eq in H.
    Qed.

    #[program, export] Instance TermRing_bv {n} : TermRing (ty.bvec n) := {
        tmr_zero := bv.zero
      ; tmr_one := bv.one
      ; tmr_plus := bop.bvadd
      ; tmr_times := bop.bvmul
      ; tmr_minus := bop.bvsub
      ; tmr_negate := uop.negate
      ; tmr_of_Z := bv.of_Z
      ; tmr_ring_theory := Term_bv_ring_theory Σ n
      ; tmr_ring_eq_ext := Term_bv_ring_eq_ext Σ n
      }.
    Next Obligation.
      constructor; try reflexivity; rewrite ?term_binop_val, ?term_unop_val; intros.
      - now rewrite bv.of_Z_one.
      - rewrite term_binop_val; cbn; now rewrite bv.of_Z_add.
      - rewrite term_binop_val; cbn; now rewrite bv.of_Z_sub.
      - rewrite term_binop_val; cbn; now rewrite bv.of_Z_mul.
      - rewrite term_unop_val; cbn; now rewrite bv.of_Z_negate.
      - apply Z.eqb_eq in H; now subst.
    Qed.

    Definition evalPExprTm `{TermRing σ} : list (Term Σ σ) -> PExpr Z -> Term Σ σ :=
      PEeval (term_val σ tmr_zero)
        (term_val σ tmr_one)
        (term_binop tmr_plus)
        (term_binop tmr_times)
        (term_binop tmr_minus)
        (term_unop tmr_negate)
        (fun c => term_val σ (tmr_of_Z c))
        id_phi_N (pow_N (term_val (Σ := Σ) σ tmr_one) (term_binop tmr_times)).

    Definition RQuote (σ : Ty) : Type := list (Term Σ σ) -> positive -> PExpr Z * list (Term Σ σ).

    Definition RQuoteValid `{TermRing σ} (t : Term Σ σ) (q : RQuote σ): Prop :=
      forall lo o, match q lo o with
                     (poly , ln) => o = Pos.of_succ_nat (length lo) -> forall la, evalPExprTm (lo ++ ln ++ la) poly ≡ t
                  end.

    Definition Term_Quote_def {σ} (t : Term Σ σ) : RQuote σ :=
      fun ts o =>
        match find_index (fun t' => Term_eqb t t') ts with
        | None => (PEX Z o , [ t ]%list)
        | Some i => (PEX Z (Pos.of_succ_nat i) , []%list)
        end.

    Lemma Term_Quote_def_Valid `{TermRing σ} {t : Term Σ σ} : RQuoteValid t (Term_Quote_def t).
    Proof.
      intros ts o.
      unfold Term_Quote_def.
      destruct (find_index_spec (fun t' => Term_eqb t t') ts) as [i Hlkpi|];
        intros Ho la; cbn.
      - rewrite (nth_lookup (t := t)); first reflexivity.
        destruct Hlkpi as [a Ha].
        destruct (Term_eqb_spec t a); inversion Ha; now subst.
      - now rewrite nth_length_prefix.
    Qed.

    Definition Term_Quote_unop {n} (comb : PExpr Z -> PExpr Z) (q1 : RQuote n) : RQuote n :=
      fun ts o => let (pol1 , ts1) := q1 ts o in
                  (comb pol1 , ts1).

    Lemma Term_Quote_unop_Valid `{TermRing σ} {op : UnOp σ σ}
      {comb} {t1} {q1} :
      (forall env pol1, evalPExprTm env (comb pol1) = term_unop op (evalPExprTm env pol1)) ->
      RQuoteValid t1 q1 ->
      RQuoteValid (term_unop op t1) (Term_Quote_unop comb q1).
    Proof.
      intros Hcomb Hq1 ts o; unfold Term_Quote_unop; cbn.
      generalize (Hq1 ts o); destruct q1 as [pol1 l1].
      intros.
      now rewrite Hcomb, H0.
    Qed.

    Definition Term_Quote_bin `{TermRing σ} (comb : PExpr Z -> PExpr Z -> PExpr Z) (q1 : RQuote σ) (q2 : RQuote σ) : RQuote σ :=
      fun ts o => let (pol1 , ts1) := q1 ts o in
                  let (pol2 , ts2) := q2 (app ts ts1) (plusNatPos (length ts1) o) in
                  ((comb pol1 pol2) , app ts1 ts2).

    Lemma Term_Quote_bin_Valid `{TermRing σ} {op : BinOp σ σ σ}
      {comb} {t1 t2} {q1 q2} :
      (forall env pol1 pol2, evalPExprTm env (comb pol1 pol2) = term_binop op (evalPExprTm env pol1) (evalPExprTm env pol2)) ->
      RQuoteValid t1 q1 -> RQuoteValid t2 q2 ->
      RQuoteValid (term_binop op t1 t2) (Term_Quote_bin comb q1 q2).
    Proof.
      intros Hcomb Hq1 Hq2 ts o; unfold Term_Quote_bin; cbn.
      generalize (Hq1 ts o); destruct q1 as [pol1 l1].
      intros Hl1.
      generalize (Hq2 (ts ++ l1) (plusNatPos (length l1) o)); destruct q2 as [pol2 l2].
      intros Hl2 Ho l3.
      rewrite Hcomb.
      eapply proper_term_binop.
      - now rewrite <-List.app_assoc, (Hl1 Ho _).
      - rewrite !List.app_assoc, <-List.app_assoc.
        apply Hl2.
        subst.
        now rewrite plusNatPos_of_succ_nat, length_app, Nat.add_comm.
    Qed.

    Definition CanonTerm σ : Type :=
      match σ with
      | ty.bvec n => RQuote σ
      | ty.int => RQuote σ
      | _ => Term Σ σ
      end.

    #[export] Instance equiv_CanonTerm {σ} : base.Equiv (CanonTerm σ)
      := match σ with
         | ty.bvec n => (eq ==> eq ==> base.prod_relation eq base.equiv)%signature
         | ty.int => (eq ==> eq ==> base.prod_relation eq base.equiv)%signature
         | _ => base.equiv
         end.

    Definition CanonTermRep {σ : Ty} : CanonTerm σ -> Term Σ σ -> Prop :=
      match σ with
      | ty.bvec n => fun ct t => RQuoteValid t ct
      | ty.int => fun ct t => RQuoteValid t ct
      | _ => fun ct t => ct ≡ t
      end.

    #[export] Instance proper_tl_equiv `{base.Equiv A} :
      Proper (base.equiv ==> base.equiv) (@tl A).
    Proof. intros l1 l2 Hl. destruct Hl; cbn; [constructor|easy]. Qed.

    #[export] Instance proper_hd_equiv {A} {_ : base.Equiv A} :
      Proper (base.equiv ==> base.equiv ==> base.equiv) (@hd A).
    Proof. intros def1 def2 Hdef l1 l2 Hl. now destruct Hl. Qed.

    #[export] Instance proper_jump_equiv `{base.Equiv A} :
      Proper (eq ==> base.equiv ==> base.equiv) (@BinList.jump A).
    Proof.
      intros p ? <-.
      induction p; cbn;
        intros l1 l2 Hl;
        try do 2 apply IHp;
        now try apply proper_tl_equiv.
    Qed.

    Lemma proper_pow_pos `{base.Equiv A} :
      Proper ((base.equiv ==> base.equiv ==> base.equiv) ==> base.equiv ==> eq ==> base.equiv) (@pow_pos A).
    Proof.
      intros m1 m2 Hm x1 x2 Hx n ? <-.
      induction n; cbn.
      - apply Hm; [easy|].
        apply Hm; now apply IHn.
      - apply Hm; now apply IHn.
      - easy.
    Qed.

    Lemma proper_pow_N `{base.Equiv A} :
      Proper (base.equiv ==> (base.equiv ==> base.equiv ==> base.equiv) ==> base.equiv ==> eq ==> base.equiv) (@pow_N A).
    Proof.
      intros o1 o2 Ho m1 m2 Hm x1 x2 Hx n ? <-.
      destruct n; cbn; [easy|].
      now apply proper_pow_pos.
    Qed.

    #[export] Instance proper_nth_equiv `{base.Equiv A} :
      Proper (base.equiv ==> eq ==> base.equiv ==> base.equiv) (@BinList.nth A).
    Proof.
      intros def1 def2 Hdef x ? <-.
      induction x; intros l1 l2 Hl; cbn.
      - apply IHx, proper_jump_equiv; first easy.
        now apply proper_tl_equiv.
      - now apply IHx, proper_jump_equiv.
      - now apply proper_hd_equiv.
    Qed.

    #[export] Instance proper_evalPExprTm `{TermRing σ} :
      Proper (base.equiv ==> eq ==> base.equiv) (evalPExprTm (σ := σ)).
    Proof.
      intros env1 env2 Henv expr ? <-.
      induction expr; cbn; try easy.
      - now rewrite Henv.
      - now rewrite IHexpr1, IHexpr2.
      - now rewrite IHexpr1, IHexpr2.
      - now rewrite IHexpr1, IHexpr2.
      - now rewrite IHexpr.
      - apply proper_pow_N; try easy.
        apply proper_term_binop.
    Qed.

    Instance proper_CanonTermRep `{TermRing σ} : Proper (base.equiv ==> base.equiv ==> iff) (@CanonTermRep σ).
    Proof.
      intros x1 x2 Hx y1 y2 Hy.
      destruct σ; cbn; try now rewrite Hx, Hy;
        cbn.
      - split; intros Hrqv lo o; specialize (Hrqv lo o); specialize (Hx lo _ eq_refl o _ eq_refl);
        destruct (x1 lo o), (x2 lo o), Hx; cbn in *; subst.
        + intros -> la.
          rewrite <-Hy, <-H1.
          now apply Hrqv.
        + intros -> la.
          rewrite Hy, H1.
          now apply Hrqv.
      - split; intros Hrqv lo o; specialize (Hrqv lo o); specialize (Hx lo _ eq_refl o _ eq_refl);
        destruct (x1 lo o), (x2 lo o), Hx; cbn in *; subst.
        + intros -> la.
          rewrite <-Hy, <-H1.
          now apply Hrqv.
        + intros -> la.
          rewrite Hy, H1.
          now apply Hrqv.
    Qed.

    Equations(noeqns) peval_append {σ} (t1 t2 : Term Σ (ty.list σ)) : Term Σ (ty.list σ) :=
    | term_val _ v1                 | term_val _ v2 := term_val (ty.list σ) (app v1 v2);
    (* TODO: recurse over the value instead *)
    | term_val _ nil                | t2 := t2;
    | term_val _ (cons v vs)        | t2 := term_binop bop.cons (term_val σ v) (term_binop bop.append (term_val (ty.list σ) vs) t2);
    | term_binop bop.cons t11 t12 | t2 := term_binop bop.cons t11 (term_binop bop.append t12 t2);
    | t1                            | t2 := term_binop bop.append t1 t2.

    Definition peval_and_val (t : Term Σ ty.bool) (v : Val ty.bool) :
      Term Σ ty.bool := if v then t else term_val ty.bool false.
    Definition peval_or_val (t : Term Σ ty.bool) (v : Val ty.bool) :
      Term Σ ty.bool := if v then term_val ty.bool true else t.

    Lemma peval_and_val_sound (t : Term Σ ty.bool)
      (v : Val ty.bool) :
      peval_and_val t v ≡ term_binop bop.and t (term_val ty.bool v).
    Proof.
      destruct v; cbn; intros ι; cbn.
      - now rewrite andb_true_r.
      - now rewrite andb_false_r.
    Qed.

    Lemma peval_or_val_sound (t : Term Σ ty.bool)
      (v : Val ty.bool) :
      peval_or_val t v ≡ term_binop bop.or t (term_val ty.bool v).
    Proof.
      destruct v; cbn; intros ι; cbn.
      - now rewrite orb_true_r.
      - now rewrite orb_false_r.
    Qed.

    Equations(noeqns) peval_and (t1 t2 : Term Σ ty.bool) : Term Σ ty.bool :=
    | term_val _ b  , t2            => peval_and_val t2 b
    | t1            , term_val _ b  => peval_and_val t1 b
    | t1            , t2            => term_binop bop.and t1 t2.

    Equations(noeqns) peval_or (t1 t2 : Term Σ ty.bool) : Term Σ ty.bool :=
    | term_val _ b  , t2            => peval_or_val t2 b
    | t1            , term_val _ b  => peval_or_val t1 b
    | t1            , t2            => term_binop bop.or t1 t2.

    Equations(noeqns) peval_plus (t1 t2 : Term Σ ty.int) : Term Σ ty.int :=
    | term_val _ v1  , term_val _ v2    => term_val ty.int (v1 + v2)%Z
    | term_val _ 0%Z , t2               => t2
    | t1             , term_val _ 0%Z   => t1
    | t1             , term_val _ v2    => term_binop bop.plus (term_val ty.int v2) t1
    | t1             , t2               => term_binop bop.plus t1 t2.

    Equations(noeqns) peval_bvadd {n} (t1 t2 : Term Σ (ty.bvec n)) : Term Σ (ty.bvec n) :=
    | term_val _ v1          , term_val _ v2          => term_val (ty.bvec n) (bv.add v1 v2)
    | term_val _ (bv.mk 0 _) , t2                     => t2
    | t1                     , term_val _ (bv.mk 0 _) => t1
    | t1                     , term_val _ v2          => term_binop bop.bvadd (term_val (ty.bvec n) v2) t1
    | t1                     , t2                     => term_binop bop.bvadd t1 t2.

    Definition peval_bvand_val_default {m} (t : Term Σ (ty.bvec m))
      (v : Val (ty.bvec m)) : Term Σ (ty.bvec m) :=
      let z := bv.zero in
      if eq_dec z v
      then term_val (ty.bvec m) z
      else
        if eq_dec (bv.ones m) v
        then t
        else term_binop bop.bvand t (term_val (ty.bvec m) v).

    Section WithPevalBvandVal.

      Variable peval_bvand_val :
        (forall [m],  Term Σ (ty.bvec m) → Val (ty.bvec m) → Term Σ (ty.bvec m)).

      Definition peval_bvand_bvapp_val {m1 m2} (t1 : Term Σ (ty.bvec m1))
        (t2 : Term Σ (ty.bvec m2)) (v : Val (ty.bvec (m1+m2))) :
        Term Σ (ty.bvec (m1+m2)) :=
        let (v1,v2) := bv.appView m1 m2 v in
        term_bvapp (peval_bvand_val t1 v1) (peval_bvand_val t2 v2).

      Definition peval_bvand_bvcons_val {m} (t1 : Term Σ ty.bool)
        (t2 : Term Σ (ty.bvec m)) (v : Val (ty.bvec (S m))) :
        Term Σ (ty.bvec (S m)) :=
        let (v1,v2) := bv.view v in
        term_binop bop.bvcons (peval_and_val t1 v1) (peval_bvand_val t2 v2).

    End WithPevalBvandVal.

    Equations(noeqns) peval_bvand_val [m] (t : Term Σ (ty.bvec m)) (v : Val (ty.bvec m)) :
      Term Σ (ty.bvec m) :=
    | term_val _ v1               , v2 => term_val (ty.bvec _) (bv.land v1 v2)
    | term_binop bop.bvapp t1 t2  , v  => peval_bvand_bvapp_val peval_bvand_val t1 t2 v
    | term_binop bop.bvcons t1 t2 , v  => peval_bvand_bvcons_val peval_bvand_val t1 t2 v
    | t , v  => peval_bvand_val_default t v.

    Equations(noeqns) peval_bvand {n} (t1 t2 : Term Σ (ty.bvec n)) : Term Σ (ty.bvec n) :=
    | term_val _ v1               , term_val _ v2 => term_val (ty.bvec _) (bv.land v1 v2)
    | term_binop bop.bvapp t1 t2  , term_val _ v  => peval_bvand_bvapp_val peval_bvand_val t1 t2 v
    | term_binop bop.bvcons t1 t2 , term_val _ v  => peval_bvand_bvcons_val peval_bvand_val t1 t2 v
    | term_val _ v                , term_binop bop.bvapp t1 t2 => peval_bvand_bvapp_val peval_bvand_val t1 t2 v
    | term_val _ v                , term_binop bop.bvcons t1 t2 => peval_bvand_bvcons_val peval_bvand_val t1 t2 v
    | t1 , t2  => term_binop bop.bvand t1 t2.

    Definition peval_bvor_val_default {m} (t : Term Σ (ty.bvec m))
      (v : Val (ty.bvec m)) : Term Σ (ty.bvec m) :=
      let o := bv.ones m in
      if eq_dec o v
      then term_val (ty.bvec m) o
      else
        if eq_dec bv.zero v
        then t
        else term_binop bop.bvor t (term_val (ty.bvec m) v).

    Section WithPevalBvorVal.

      Variable peval_bvor_val :
        (forall [m],  Term Σ (ty.bvec m) → Val (ty.bvec m) → Term Σ (ty.bvec m)).

      Definition peval_bvor_bvapp_val {m1 m2} (t1 : Term Σ (ty.bvec m1))
        (t2 : Term Σ (ty.bvec m2)) (v : Val (ty.bvec (m1+m2))) :
        Term Σ (ty.bvec (m1+m2)) :=
        let (v1,v2) := bv.appView m1 m2 v in
        term_bvapp (peval_bvor_val t1 v1) (peval_bvor_val t2 v2).

      Definition peval_bvor_bvcons_val {m} (t1 : Term Σ ty.bool)
        (t2 : Term Σ (ty.bvec m)) (v : Val (ty.bvec (S m))) :
        Term Σ (ty.bvec (S m)) :=
        let (v1,v2) := bv.view v in
        term_binop bop.bvcons (peval_or_val t1 v1) (peval_bvor_val t2 v2).

    End WithPevalBvorVal.

    Equations(noeqns) peval_bvor_val [m] (t : Term Σ (ty.bvec m)) (v : Val (ty.bvec m)) :
      Term Σ (ty.bvec m) :=
    | term_val _ v1               , v2 => term_val (ty.bvec _) (bv.lor v1 v2)
    | term_binop bop.bvapp t1 t2  , v  => peval_bvor_bvapp_val peval_bvor_val t1 t2 v
    | term_binop bop.bvcons t1 t2 , v  => peval_bvor_bvcons_val peval_bvor_val t1 t2 v
    | t , v  => peval_bvor_val_default t v.

    Equations(noeqns) peval_bvor {n} (t1 t2 : Term Σ (ty.bvec n)) : Term Σ (ty.bvec n) :=
    | term_val _ v1               , term_val _ v2 => term_val (ty.bvec _) (bv.lor v1 v2)
    | term_binop bop.bvapp t1 t2  , term_val _ v  => peval_bvor_bvapp_val peval_bvor_val t1 t2 v
    | term_binop bop.bvcons t1 t2 , term_val _ v  => peval_bvor_bvcons_val peval_bvor_val t1 t2 v
    | term_val _ v                , term_binop bop.bvapp t1 t2 => peval_bvor_bvapp_val peval_bvor_val t1 t2 v
    | term_val _ v                , term_binop bop.bvcons t1 t2 => peval_bvor_bvcons_val peval_bvor_val t1 t2 v
    | t1 , t2  => term_binop bop.bvor t1 t2.

    Definition peval_bvapp_val_r {m n} (t1 : Term Σ (ty.bvec m)) (v : Val (ty.bvec n)) : Term Σ (ty.bvec (m+n)) :=
      match eq_dec n 0 with
      | left e =>
          eq_rect_r (fun l => Term Σ (ty.bvec l)) t1
            (eq_trans (f_equal (Nat.add m) e) (transparent.nat_add_0_r m))
      | right _ => term_bvapp t1 (term_val (ty.bvec n) v)
      end.

    Equations(noeqns) peval_bvapp {m n} (t1 : Term Σ (ty.bvec m)) (t2 : Term Σ (ty.bvec n)) : Term Σ (ty.bvec (m+n)) :=
    | term_val _ v1 | term_val _ v2 => term_val (ty.bvec _) (bv.app v1 v2)
    | term_bvapp t11 t12 , t2 => eq_rect _ (fun l => Term Σ (ty.bvec l))
                                   (term_bvapp t11 (term_bvapp t12 t2)) _
                                   (transparent.nat_add_assoc _ _ _)
    | t1 , term_val _ v2 => peval_bvapp_val_r t1 v2
    | t1 , t2 => term_bvapp t1 t2.

    Section WithPevalBvdrop.

      Variable peval_bvdrop_eq :
        ∀ m n mn : nat, Term Σ (ty.bvec mn) → m + n = mn → Term Σ (ty.bvec n).

      Definition peval_bvdrop_bvapp {m n} [k l] :
        Term Σ (ty.bvec k) → Term Σ (ty.bvec l) → m + n = k + l → Term Σ (ty.bvec n) :=
        match nat_compare m k with
        | EQ mk   => fun _ t2 e =>
                       eq_rect_r (fun l => Term Σ (ty.bvec l)) t2
                         (transparent.nat_add_cancel_l n l mk e)
        | LT m' d => fun t1 t2 e =>
                       eq_rect_r (fun l => Term Σ (ty.bvec l))
                         (term_bvapp (peval_bvdrop_eq m' (S d) t1 eq_refl) t2)
                         (transparent.nat_add_cancel_l n (S d + l) m'
                            (eq_trans e (eq_sym (transparent.nat_add_assoc m' (S d) l))))
        | GT k' d => fun t1 t2 e =>
                       eq_rect (S d + n) (fun l => Term Σ (ty.bvec l) → Term Σ (ty.bvec n))
                         (fun t3 => peval_bvdrop_eq (S d) n t3 eq_refl)
                         l
                         (transparent.nat_add_cancel_l (S d + n) l k'
                            (eq_trans (transparent.nat_add_assoc k' (S d) n) e)) t2
        end.

      Definition peval_bvdrop_bvcons {m n} [k] (t1 : Term Σ ty.bool)
        (t2 : Term Σ (ty.bvec k)) : m + n = S k → Term Σ (ty.bvec n) :=
        match m with
        | 0   => fun e => eq_rect_r (fun l => Term Σ (ty.bvec l)) (term_bvcons t1 t2) e
        | S m => fun e => peval_bvdrop_eq m n t2 (eq_add_S (m + n) k e)
        end.

      Definition peval_bvdrop_bvdrop {m n} [k l] (t1 : Term Σ (ty.bvec (k + l)))
        (e : m + n = l) : Term Σ (ty.bvec n) :=
        peval_bvdrop_eq (k + m) n t1
          (eq_trans
             (eq_sym (transparent.nat_add_assoc k m n))
             (f_equal (Init.Nat.add k) e)).

    End WithPevalBvdrop.

    Definition peval_bvdrop_val {m n} [k] (v : Val (ty.bvec k))
      (e : m + n = k) : Term Σ (ty.bvec n) :=
      term_val (ty.bvec _) (bv.drop m (eq_rect_r bv v e)).

    Definition peval_bvdrop_default m {n} mn (t : Term Σ (ty.bvec mn)) (e : m + n = mn) :
      Term Σ (ty.bvec n) :=
      match eq_dec 0 m with
      | left em0 => eq_rect_r (fun l => Term Σ (ty.bvec l)) t
                      (eq_trans (f_equal (fun m => m + n) em0) e)
      | right _ =>
          match eq_dec n 0 with
          | left e0n => term_val (ty.bvec n) (eq_rect_r bv bv.nil e0n)
          | right _ => term_bvdrop m (eq_rect_r (fun l => Term Σ (ty.bvec l)) t e)
          end
      end.

    Fixpoint peval_bvdrop_eq m {n} mn (t : Term Σ (ty.bvec mn)) (e : m + n = mn) {struct t} :
      Term Σ (ty.bvec n) :=
      Term_bvec_case (fun mn _ => m + n = mn → Term Σ (ty.bvec n))
        (fun (*var*) _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*val*) k v e => peval_bvdrop_val v e)
        (fun (*bvadd*) _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*bvsub*) _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*bvmul*) _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*bvand*) _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*bvor*) _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*bvxor*) _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*shiftr*) _ _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*shift*) _ _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*bvapp*) k l t1 t2 e => peval_bvdrop_bvapp peval_bvdrop_eq t1 t2 e)
        (fun (*bvcons*) k t1 t2 e => peval_bvdrop_bvcons peval_bvdrop_eq t1 t2 e)
        (fun (*u_v_s*) _ _ _ _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*bvnot*) _ _ _ => peval_bvdrop_default _ t e)
        (fun (*negate*) _ _ _ => peval_bvdrop_default _ t e)
        (fun (*sext*) _ _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*zext*) _ _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*g_s_i*) _ _ _ => peval_bvdrop_default _ t e)
        (fun (*truncate*) _ _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*v_s*) _ _ _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*bvdrop*) k l t1 e => peval_bvdrop_bvdrop peval_bvdrop_eq t1 e)
        (fun (*bvtake*) _ _ _ _ => peval_bvdrop_default _ t e)
        t e.

    Definition peval_bvdrop m {n} (t : Term Σ (ty.bvec (m + n))) :
      Term Σ (ty.bvec n) := peval_bvdrop_eq m t eq_refl.

    Section WithPevalBvtake.

      Variable peval_bvtake_eq :
        ∀ m n mn : nat, Term Σ (ty.bvec mn) → m + n = mn → Term Σ (ty.bvec m).

      Definition peval_bvtake_bvapp {m n} [k l] :
        Term Σ (ty.bvec k) → Term Σ (ty.bvec l) → m + n = k + l → Term Σ (ty.bvec m) :=
        match nat_compare m k with
        | EQ mk   => fun t1 _ _ => t1
        | LT m' d => fun t1 _ _ => peval_bvtake_eq m' (S d) t1 eq_refl
        | GT k' d => fun t1 t2 e =>
                       term_bvapp t1
                         (peval_bvtake_eq (S d) n t2
                            (transparent.nat_add_cancel_l (S d + n) l k'
                               (eq_trans (transparent.nat_add_assoc k' (S d) n) e)))
        end.

      Definition peval_bvtake_bvcons {m n} [k] (t1 : Term Σ ty.bool)
        (t2 : Term Σ (ty.bvec k)) : m + n = S k → Term Σ (ty.bvec m) :=
        match m with
        | 0   => fun _ => term_val (ty.bvec 0) bv.nil
        | S m => fun e => term_bvcons t1
                            (peval_bvtake_eq m n t2 (eq_add_S (m + n) k e))
        end.

      Definition peval_bvtake_bvtake {m n} [k l]
        (t1 : Term Σ (ty.bvec (k + l))) (e : m + n = k) : Term Σ (ty.bvec m) :=
        let e1 : (m+n)+l = k+l := f_equal (fun j => j + l) e in
        let e2 : m+(n+l) = k+l := eq_trans (transparent.nat_add_assoc m n l) e1 in
        peval_bvtake_eq m (n + l) t1 e2.

    End WithPevalBvtake.

    Definition peval_bvtake_val {m n} [k] (v : Val (ty.bvec k))
      (e : m + n = k) : Term Σ (ty.bvec m) :=
      term_val (ty.bvec _) (bv.take m (eq_rect_r bv v e)).

    Definition peval_bvtake_default m {n} mn (t : Term Σ (ty.bvec mn))
      (e : m + n = mn) : Term Σ (ty.bvec m) :=
      match eq_dec m 0 with
      | left em0 => eq_rect_r (fun l => Term Σ (ty.bvec l))
                      (term_val (ty.bvec 0) bv.nil) em0
      | right _ =>
          match eq_dec 0 n with
          | left e0n =>
              eq_rect_r (fun l => Term Σ (ty.bvec l)) t
                (eq_trans
                   (eq_trans (eq_sym (transparent.nat_add_0_r m))
                      (f_equal (Nat.add m) e0n)) e)
          | right _ => term_bvtake m (eq_rect_r (fun l => Term Σ (ty.bvec l)) t e)
          end
      end.

    Fixpoint peval_bvtake_eq m {n} mn (t : Term Σ (ty.bvec mn)) (e : m + n = mn) {struct t} :
      Term Σ (ty.bvec m) :=
      Term_bvec_case (fun (**) n0 _ => m + n = n0 → Term Σ (ty.bvec m))
        (fun (*var*) _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*val*) k v e => peval_bvtake_val v e)
        (fun (*bvadd*) _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*bvsub*) _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*bvmul*) _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*bvand*) _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*bvor*) _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*bvxor*) _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*shiftr*) _ _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*shift*) _ _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*bvapp*) k l t1 t2 e => peval_bvtake_bvapp peval_bvtake_eq t1 t2 e)
        (fun (*bvcons*) k t1 t2 e => peval_bvtake_bvcons peval_bvtake_eq t1 t2 e)
        (fun (*u_v_s*) _ _ _ _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*bvnot*) _ _ _ => peval_bvtake_default _ t e)
        (fun (*negate*) _ _ _ => peval_bvtake_default _ t e)
        (fun (*sext*) _ _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*zext*) _ _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*g_s_i*) _ _ _ => peval_bvtake_default _ t e)
        (fun (*truncate*) _ _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*v_s*) _ _ _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*bvdrop*) _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*bvtake*) k l t1 e1 => peval_bvtake_bvtake peval_bvtake_eq t1 e1)
        t e.

    Definition peval_bvtake m {n} (t : Term Σ (ty.bvec (m + n))) :
      Term Σ (ty.bvec m) := peval_bvtake_eq m t eq_refl.

    Definition peval_update_vector_subrange {n} s l {p : IsTrue (s + l <=? n)%nat} :
      Term Σ (ty.bvec n) -> Term Σ (ty.bvec l) -> Term Σ (ty.bvec n) :=
      match bv.leview (s + l) n with
      | bv.is_le k =>
          fun tslk tl =>
            peval_bvapp
              (peval_bvapp (peval_bvtake s (peval_bvtake (s+l) tslk)) tl)
              (peval_bvdrop (s+l) tslk)
      end.
    #[global] Arguments peval_update_vector_subrange {n} s l {p}.

    Equations(noeqns) peval_binop' {σ1 σ2 σ} (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) : Term Σ σ :=
    | op | term_val _ v1 | term_val _ v2 := term_val σ (bop.eval op v1 v2);
    | op | t1            | t2            := term_binop op t1 t2.

    Definition peval_binop {σ1 σ2 σ} (op : BinOp σ1 σ2 σ) :
      Term Σ σ1 → Term Σ σ2 → Term Σ σ :=
      match op with
      | bop.append => peval_append
      | bop.and    => peval_and
      | bop.or     => peval_or
      | bop.plus   => peval_plus
      | bop.bvadd  => peval_bvadd
      | bop.bvand  => peval_bvand
      | bop.bvor   => peval_bvor
      | bop.bvapp  => peval_bvapp
      | bop.update_vector_subrange s l => peval_update_vector_subrange s l
      | op         => peval_binop' op
      end.

    Lemma peval_append_sound {σ} (t1 t2 : Term Σ (ty.list σ)) :
      peval_append t1 t2 ≡ term_binop bop.append t1 t2.
    Proof.
      destruct t1 using Term_list_case; try constructor.
      destruct t2 using Term_list_case;
        first [constructor | destruct v; constructor].
    Qed.

    Lemma peval_and_sound (t1 t2 : Term Σ ty.bool) :
      peval_and t1 t2 ≡ term_binop bop.and t1 t2.
    Proof with lsolve.
      depelim t1.
      - depelim t2; lsolve. apply peval_and_val_sound.
      - now destruct v.
      - depelim t2; lsolve. apply peval_and_val_sound.
      - depelim t2; lsolve. apply peval_and_val_sound.
    Qed.

    Lemma peval_or_sound (t1 t2 : Term Σ ty.bool) :
      peval_or t1 t2 ≡ term_binop bop.or t1 t2.
    Proof with lsolve.
      depelim t1.
      - depelim t2; lsolve. apply peval_or_val_sound.
      - now destruct v.
      - depelim t2; lsolve. apply peval_or_val_sound.
      - depelim t2; lsolve. apply peval_or_val_sound.
    Qed.

    Lemma peval_plus_sound (t1 t2 : Term Σ ty.int) :
      peval_plus t1 t2 ≡ term_binop bop.plus t1 t2.
    Proof.
      depelim t1; depelim t2; lsolve;
        try destruct v; try destruct v0; intros ι; cbn; lia.
    Qed.

    Lemma peval_bvadd_sound {n} (t1 t2 : Term Σ (ty.bvec n)) :
      peval_bvadd t1 t2 ≡ term_binop bop.bvadd t1 t2.
    Proof.
      depelim t1; depelim t2; lsolve;
        repeat
          match goal with
          | |- context[match ?v with bv.mk _ _ => _ end] =>
              is_var v; destruct v as [[|p] i]; try destruct i
          end; intros ι; cbn; auto;
        first
          [ symmetry; apply bv.add_zero_l
          | symmetry; apply bv.add_zero_r
          | now apply bv.add_comm
          ].
    Qed.

    Lemma peval_bvand_val_default_sound {n} (t : Term Σ (ty.bvec n))
      (v : Val (ty.bvec n)) :
      peval_bvand_val_default t v ≡
      term_binop bop.bvand t (term_val (ty.bvec n) v).
    Proof.
      unfold peval_bvand_val_default.
      destruct (eq_dec bv.zero v).
      { subst. intros ι; cbn. now rewrite bv.land_zero_r. }
      destruct (eq_dec (bv.ones n) v).
      { subst. intros ι; cbn. now rewrite bv.land_ones_r. }
      { reflexivity. }
    Qed.

    Hint Resolve peval_bvand_val_default_sound : core.

    Lemma peval_bvand_val_sound {n} (t : Term Σ (ty.bvec n))
      (v : Val (ty.bvec n)) :
      peval_bvand_val t v ≡ term_binop bop.bvand t (term_val (ty.bvec n) v).
    Proof.
      revert v. induction n, t using Term_bvec_rect; intros; cbn - [bv.cons]; lsolve.
      - unfold peval_bvand_bvapp_val. destruct bv.appView.
        rewrite IHt1, IHt2.
        intros ι. cbn. now rewrite bv.land_app.
      - unfold peval_bvand_bvcons_val. destruct bv.view.
        rewrite peval_and_val_sound, IHt1.
        intros ι. cbn - [bv.cons]. now rewrite bv.land_cons.
    Qed.

    Lemma peval_bvand_sound {n} (t1 t2 : Term Σ (ty.bvec n)) :
      peval_bvand t1 t2 ≡ term_binop bop.bvand t1 t2.
    Proof.
      destruct n, t1 using Term_bvec_case; cbn - [bv.cons]; lsolve;
        [destruct n, t2 using Term_bvec_case|depelim t2..]; cbn - [bv.cons]; lsolve.
      - unfold peval_bvand_bvapp_val. destruct bv.appView.
        rewrite !peval_bvand_val_sound.
        intros ι. cbn. rewrite bv.land_app.
        f_equal; now rewrite bv.land_comm.
      - unfold peval_bvand_bvcons_val. destruct bv.view.
        rewrite peval_and_val_sound, peval_bvand_val_sound.
        intros ι. cbn - [bv.cons]. rewrite bv.land_cons.
        f_equal. now rewrite andb_comm.
        now rewrite bv.land_comm.
      - unfold peval_bvand_bvapp_val. destruct bv.appView.
        rewrite !peval_bvand_val_sound.
        intros ι. cbn. now rewrite bv.land_app.
      - unfold peval_bvand_bvcons_val. destruct bv.view.
        rewrite peval_and_val_sound, peval_bvand_val_sound.
        intros ι. cbn - [bv.cons]. now rewrite bv.land_cons.
    Qed.

    Lemma peval_bvor_val_default_sound {n} (t : Term Σ (ty.bvec n))
      (v : Val (ty.bvec n)) :
      peval_bvor_val_default t v ≡
      term_binop bop.bvor t (term_val (ty.bvec n) v).
    Proof.
      unfold peval_bvor_val_default.
      destruct (eq_dec (bv.ones n) v).
      { subst. intros ι; cbn. now rewrite bv.lor_ones_r. }
      destruct (eq_dec bv.zero v).
      { subst. intros ι; cbn. now rewrite bv.lor_zero_r. }
      { reflexivity. }
    Qed.

    Hint Resolve peval_bvor_val_default_sound : core.

    Lemma peval_bvor_val_sound {n} (t : Term Σ (ty.bvec n))
      (v : Val (ty.bvec n)) :
      peval_bvor_val t v ≡ term_binop bop.bvor t (term_val (ty.bvec n) v).
    Proof.
      revert v. induction n, t using Term_bvec_rect; intros; cbn - [bv.cons]; lsolve.
      - unfold peval_bvor_bvapp_val. destruct bv.appView.
        rewrite IHt1, IHt2.
        intros ι. cbn. now rewrite bv.lor_app.
      - unfold peval_bvor_bvcons_val. destruct bv.view.
        rewrite peval_or_val_sound, IHt1.
        intros ι. cbn - [bv.cons]. now rewrite bv.lor_cons.
    Qed.

    Lemma peval_bvor_sound {n} (t1 t2 : Term Σ (ty.bvec n)) :
      peval_bvor t1 t2 ≡ term_binop bop.bvor t1 t2.
    Proof.
      destruct n, t1 using Term_bvec_case; cbn - [bv.cons]; lsolve;
        [destruct n, t2 using Term_bvec_case|depelim t2..]; cbn - [bv.cons]; lsolve.
      - unfold peval_bvor_bvapp_val. destruct bv.appView.
        rewrite !peval_bvor_val_sound.
        intros ι. cbn. rewrite bv.lor_app.
        f_equal; now rewrite bv.lor_comm.
      - unfold peval_bvor_bvcons_val. destruct bv.view.
        rewrite peval_or_val_sound, peval_bvor_val_sound.
        intros ι. cbn - [bv.cons]. rewrite bv.lor_cons.
        f_equal. now rewrite orb_comm.
        now rewrite bv.lor_comm.
      - unfold peval_bvor_bvapp_val. destruct bv.appView.
        rewrite !peval_bvor_val_sound.
        intros ι. cbn. now rewrite bv.lor_app.
      - unfold peval_bvor_bvcons_val. destruct bv.view.
        rewrite peval_or_val_sound, peval_bvor_val_sound.
        intros ι. cbn - [bv.cons]. now rewrite bv.lor_cons.
    Qed.

    Lemma peval_bvapp_val_r_sound [m n] (t1 : Term Σ (ty.bvec m))
      (v : Val (ty.bvec n)) :
      peval_bvapp_val_r t1 v ≡ term_bvapp t1 (term_val (ty.bvec n) v).
    Proof.
      unfold peval_bvapp_val_r. destruct eq_dec.
      - intros ι. cbn. subst. rewrite eq_trans_refl_l.
        rewrite (inst_eq_rect_indexed_r
                   (instTA := fun l => @inst_term (ty.bvec l))).
        destruct (bv.view v). now rewrite bv.app_nil_r.
      - reflexivity.
    Qed.

    #[local] Hint Resolve peval_bvapp_val_r_sound : core.

    Lemma peval_bvapp_sound {m n} (t1 : Term Σ (ty.bvec m)) (t2 : Term Σ (ty.bvec n)) :
      peval_bvapp t1 t2 ≡ term_bvapp t1 t2.
    Proof.
      destruct m, t1 using Term_bvec_case; depelim t2; lsolve;
        first
          [ intros ι; cbn; rewrite bv.app_app;
            now destruct transparent.nat_add_assoc
          | now rewrite peval_bvapp_val_r_sound ].
    Qed.

    Lemma peval_bvdrop_default_sound {m n mn} (t : Term Σ (ty.bvec mn))
      (e : m + n = mn) :
      peval_bvdrop_default m t e ≡
      term_bvdrop m (eq_rect_r (fun l => Term Σ (ty.bvec l)) t e).
    Proof.
      unfold peval_bvdrop_default.
      destruct eq_dec.
       { now subst. }
      destruct eq_dec.
      { subst; intros ι; cbn - [Val].
        now destruct (bv.view (bv.drop m (inst (Inst := inst_term) t ι))). }
      reflexivity.
    Qed.

    #[local] Hint Resolve peval_bvdrop_default_sound : core.

    Lemma peval_bvdrop_eq_sound [mn : nat] (t : Term Σ (ty.bvec mn)) :
      ∀ m n (e : m + n = mn),
        peval_bvdrop_eq m t e ≡
        term_bvdrop m (eq_rect_r (fun l => Term Σ (ty.bvec l)) t e).
    Proof.
      induction mn , t using Term_bvec_rect; cbn - [Val]; intros m0 n0 e; auto.
      - (*val*)
        now subst.
      - (*bvapp*)
        unfold peval_bvdrop_bvapp. destruct nat_compare.
        + pose proof (transparent.nat_add_cancel_l _ _ _ e). subst.
          destruct (uip eq_refl (transparent.nat_add_cancel_l n n n1 e)).
          destruct (uip eq_refl e); cbn.
          intros ι. cbn - [Val]. now rewrite bv.drop_app.
        + revert t1 IHt1 e. generalize (S m). clear m. intros m t1 IHt1 e.
          assert (n0 = m + n) as ->.
          { rewrite <- transparent.nat_add_assoc in e.
            now apply transparent.nat_add_cancel_l in e. }
          destruct (uip (transparent.nat_add_assoc n1 m n) e).
          rewrite eq_trans_sym_inv_r.
          destruct (uip eq_refl (transparent.nat_add_cancel_l (m + n) (m + n) n1 eq_refl)).
          cbn. rewrite IHt1. intros ι; cbn - [Val]. clear.
          rewrite (inst_eq_rect_indexed_r
                     (instTA := fun l => @inst_term (ty.bvec l))).
          cbn - [Val]. generalize (inst t2 ι). generalize (inst t1 ι).
          intros y z. clear. destruct (bv.appView n1 m y) as [x y].
          rewrite bv.app_app. rewrite rew_opp_l. now rewrite !bv.drop_app.
        + revert e. generalize (S m). clear m. intros m e.
          assert (m + n0 = n) as <-.
          { rewrite <- transparent.nat_add_assoc in e.
            now apply transparent.nat_add_cancel_l in e. }
          destruct (uip (eq_sym (transparent.nat_add_assoc n1 m n0)) e).
          rewrite eq_trans_sym_inv_r.
          destruct (uip eq_refl (transparent.nat_add_cancel_l (m + n0) (m + n0) n1 eq_refl)).
          cbn. rewrite IHt2. cbn. intros ι. cbn - [Val].
          rewrite !(inst_eq_rect_indexed_r
                      (instTA := fun l => @inst_term (ty.bvec l))).
          cbn - [Val]. generalize (inst t2 ι). generalize (inst t1 ι). clear.
          intros x y.
          destruct (bv.appView m n0 y) as [y z].
          rewrite !bv.drop_app.
          rewrite <- (bv.drop_app (bv.app x y) z) at 1. f_equal.
          rewrite bv.app_app.
          unfold eq_rect_r. now rewrite eq_sym_involutive.
      - (*bvcons*)
        destruct m0; cbn.
        + easy.
        + rewrite IHt1. clear IHt1.
          assert (f_equal S (eq_add_S (m0 + n0) n e) = e) by apply uip.
          rewrite <- H at 2.
          destruct (eq_add_S (m0 + n0) n e). cbn.
          intros ι; cbn. now rewrite bv.drop_cons.
      - (*bvdrop*)
        unfold peval_bvdrop_bvdrop. rewrite IHt. clear IHt. subst. cbn.
        intros ι; cbn - [Val].
        rewrite !(inst_eq_rect_indexed_r
                    (instTA := fun l => @inst_term (ty.bvec l))).
        rewrite bv.drop_drop. f_equal.
        unfold eq_rect_r. now rewrite eq_sym_involutive.
    Qed.

    Lemma peval_bvdrop_sound {m n} (t : Term Σ (ty.bvec (m + n))) :
      peval_bvdrop m t ≡ term_bvdrop m t.
    Proof. unfold peval_bvdrop. apply peval_bvdrop_eq_sound. Qed.

    Lemma peval_bvtake_default_sound {m n mn} (t : Term Σ (ty.bvec mn)) :
      forall (e : m + n = mn),
        peval_bvtake_default m t e ≡
        term_bvtake m (eq_rect_r (fun l => Term Σ (ty.bvec l)) t e).
    Proof.
      unfold peval_bvtake_default. intros e.
      destruct eq_dec.
      { now subst. }
      destruct eq_dec.
      { subst; intros ι; cbn. rewrite bv.take_full.
        generalize (transparent.nat_add_0_r m). revert t.
        generalize (m+0). now intros; subst. }
      reflexivity.
    Qed.

    #[local] Hint Resolve peval_bvtake_default_sound : core.
    Lemma peval_bvtake_eq_sound {mn} (t : Term Σ (ty.bvec mn)) :
      forall m n (e : m + n = mn),
        peval_bvtake_eq m t e ≡
        term_bvtake m (eq_rect_r (fun l => Term Σ (ty.bvec l)) t e).
    Proof.
      induction mn ,t using Term_bvec_rect; cbn - [Val]; intros m0 n0 e; auto.
      - (*val*)
        now subst.
      - (*bvapp*)
        unfold peval_bvtake_bvapp. destruct nat_compare.
        + pose proof (transparent.nat_add_cancel_l _ _ _ e). subst.
          destruct (uip eq_refl e); cbn.
          intros ι. cbn - [Val]. now rewrite bv.take_app.
        + rewrite IHt1. clear IHt1 IHt2.
          assert (n0 = S m + n) as ->.
          { rewrite <- transparent.nat_add_assoc in e.
            now apply transparent.nat_add_cancel_l in e. }
          destruct (uip (transparent.nat_add_assoc n1 (S m) n) e).
          intros ι. cbn - [Val].
          rewrite (inst_eq_rect_indexed_r
                     (instTA := fun l => @inst_term (ty.bvec l))).
          cbn - [Val]. generalize (inst t2 ι). generalize (inst t1 ι).
          intros v1 v2.
          rewrite <- (bv.take_app v1 v2) at 1. now rewrite bv.take_take.
        + rewrite IHt2. clear IHt1 IHt2.
          revert e. generalize (S m). clear m. intros m e.
          assert (m + n0 = n) as <-.
          { rewrite <- transparent.nat_add_assoc in e.
            now apply transparent.nat_add_cancel_l in e. }
          destruct (uip (eq_sym (transparent.nat_add_assoc n1 m n0)) e).
          rewrite eq_trans_sym_inv_r.
          destruct (uip eq_refl (transparent.nat_add_cancel_l (m + n0) (m + n0) n1 eq_refl)).
          intros ι. cbn - [Val].
          rewrite !(inst_eq_rect_indexed_r
                      (instTA := fun l => @inst_term (ty.bvec l))).
          cbn - [Val]. generalize (inst t2 ι). generalize (inst t1 ι). clear.
          intros x y.
          destruct (bv.appView m n0 y) as [y z].
          rewrite bv.take_app.
          rewrite <- (bv.take_app (bv.app x y) z). f_equal.
          rewrite bv.app_app.
          unfold eq_rect_r. now rewrite eq_sym_involutive.
      - (*bvcons*)
        destruct m0; cbn.
        + easy.
        + rewrite IHt1. clear IHt1.
          assert (f_equal S (eq_add_S (m0 + n0) n e) = e) by apply uip.
          rewrite <- H at 2.
          destruct (eq_add_S (m0 + n0) n e). cbn.
          intros ι; cbn. now rewrite bv.take_cons.
      - (*bvtake*)
        unfold peval_bvtake_bvtake. rewrite IHt. clear IHt. subst. cbn.
        intros ι; cbn - [Val]. rewrite bv.take_take. f_equal.
        now rewrite !(inst_eq_rect_indexed_r
                    (instTA := fun l => @inst_term (ty.bvec l))).
    Qed.

    Lemma peval_bvtake_sound {m n} (t : Term Σ (ty.bvec (m + n))) :
      peval_bvtake m t ≡ term_bvtake m t.
    Proof. unfold peval_bvtake. apply peval_bvtake_eq_sound. Qed.

    Lemma peval_update_vector_subrange_sound {n s l} (p : IsTrue (s + l <=? n))
      (t1 : Term Σ (ty.bvec n)) (t2 : Term Σ (ty.bvec l)) :
      peval_update_vector_subrange s l t1 t2 ≡
      term_binop (bop.update_vector_subrange s l) t1 t2.
    Proof.
      intros ι. cbn - [Val].
      unfold peval_update_vector_subrange, bv.update_vector_subrange.
      destruct bv.leview; cbn - [Val].
      repeat
        (rewrite ?peval_bvapp_sound, ?peval_bvtake_sound,
           ?peval_bvdrop_sound; cbn - [Val]).
      destruct bv.appView.
      destruct bv.appView.
      now rewrite ?bv.take_app, ?bv.drop_app.
    Qed.

    Lemma peval_binop'_sound {σ1 σ2 σ} (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) :
      peval_binop' op t1 t2 ≡ term_binop op t1 t2.
    Proof.
      unfold peval_binop'.
      now repeat
        match goal with
        | |- context[match ?t with _ => _ end] => destruct t
        end.
    Qed.

    Hint Resolve peval_binop'_sound peval_append_sound peval_and_sound
      peval_or_sound peval_plus_sound peval_bvadd_sound peval_bvand_sound
      peval_bvor_sound peval_bvapp_sound peval_update_vector_subrange_sound
      : core.

    Lemma peval_binop_sound {σ1 σ2 σ} (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) :
      peval_binop op t1 t2 ≡ term_binop op t1 t2.
    Proof. destruct op; cbn [peval_binop]; auto. Qed.

    Equations(noeqns) peval_not (t : Term Σ ty.bool) : Term Σ ty.bool :=
    | term_val _ v                    => term_val ty.bool (negb v)
    | term_binop bop.and t1 t2        => term_binop bop.or (peval_not t1) (peval_not t2)
    | term_binop bop.or t1 t2         => term_binop bop.and (peval_not t1) (peval_not t2)
    | term_binop (bop.relop op) t1 t2 => term_relop_neg op t1 t2
    | t                               => term_unop uop.not t.

    Definition peval_unsigned_bvapp {m1 m2} (t1 : Term Σ (ty.bvec m1))
      (t2 : Term Σ (ty.bvec m2)) : Term Σ ty.int :=
      term_binop bop.plus (term_unsigned t1)
        (term_binop bop.times (term_unsigned t2)
           (term_val ty.int (2 ^ Z.of_nat m1)%Z)).

    Equations(noeqns) peval_unsigned {m} (t : Term Σ (ty.bvec m)) : Term Σ ty.int :=
    | term_val _ v                => term_val ty.int (bv.unsigned v)
    | term_binop bop.bvapp t1 t2  => peval_unsigned_bvapp t1 t2
    | t                           => term_unop uop.unsigned t.


    Definition peval_vector_subrange {n} start len {p : IsTrue (start + len <=? n)} :
      Term Σ (ty.bvec n) -> Term Σ (ty.bvec len) :=
      match bv.leview (start + len) n with
      | bv.is_le k => fun t => peval_bvdrop start
                                 (peval_bvtake (start + len) t)
      end.

    Definition peval_unop' {σ1 σ2} (op : UnOp σ1 σ2) (t : Term Σ σ1) : Term Σ σ2 :=
      match term_get_val t with
      | Some v => term_val σ2 (uop.eval op v)
      | None   => term_unop op t
      end.

    Definition peval_zext {m n : nat} {p : IsTrue (m <=? n)}
      (t : Term Σ (ty.bvec m)) : Term Σ (ty.bvec n) :=
      match eq_dec n m with
      | left e => eq_rect_r (fun n => Term Σ (ty.bvec n)) t e
      | right _ => term_zext t
      end.

    Definition peval_unop {σ1 σ2} (op : UnOp σ1 σ2) : Term Σ σ1 -> Term Σ σ2 :=
      match op with
      | uop.not                       => peval_not
      | uop.unsigned                  => peval_unsigned
      | uop.vector_subrange start len => peval_vector_subrange start len
      | uop.bvdrop m                  => peval_bvdrop m
      | uop.bvtake m                  => peval_bvtake m
      | uop.zext                      => peval_zext
      | op                            => peval_unop' op
      end.

    (* Note that we evaluate polynomials using the peval_binop' functions.
     * This gets rid of some remaining redexes left by the ring solver, particularly it tends to produce
     * `term_unop uop.negate (term_val ty.int 1%Z)` rather than `(term_val ty.int (-1)%Z)`.
     *)
    Definition evalPolTm `{TermRing σ} : list (Term Σ σ) -> Pol Z -> Term Σ σ :=
      Pphi_dev (term_val σ tmr_zero)
        (term_val σ tmr_one)
        (peval_binop' tmr_plus)
        (peval_binop' tmr_times)
        (peval_binop' tmr_minus)
        (peval_unop' tmr_negate)
        0%Z 1%Z Z.eqb
        (fun c => term_val σ (tmr_of_Z c))
        get_signZ.

    Definition CanonTerm_to_Term {σ} : CanonTerm σ -> Term Σ σ :=
      match σ return CanonTerm σ -> Term Σ σ with
      | ty.bvec n => fun ct =>
                       match ct nil 1%positive with
                       | (pexpr , env) =>
                           evalPolTm (H := TermRing_bv) env (norm_aux 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Z.eqb pexpr)
                       end
      | ty.int => fun ct =>
                    match ct nil 1%positive with
                    | (pexpr , env) =>
                        evalPolTm env (norm_aux 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Z.eqb pexpr)
                    end
      | _σ => fun t => t
      end.

    Lemma peval_not_sound (t : Term Σ ty.bool) :
      peval_not t ≡ term_unop uop.not t.
    Proof. induction t using Term_bool_ind; lsolve; now apply proper_term_binop. Qed.

    Lemma peval_unsigned_bvapp_sound [m1 m2] (t1 : Term Σ (ty.bvec m1))
      (t2 : Term Σ (ty.bvec m2)) :
      peval_unsigned_bvapp t1 t2 ≡ term_unsigned (term_bvapp t1 t2).
    Proof. intros ι; cbn. now rewrite bv.unsigned_app. Qed.
    #[local] Hint Resolve peval_unsigned_bvapp_sound : core.

    Lemma peval_unsigned_sound {m} (t : Term Σ (ty.bvec m)) :
      peval_unsigned t ≡ term_unop uop.unsigned t.
    Proof. depelim t; lsolve. depelim op; lsolve. Qed.

    Lemma peval_unop'_sound {σ1 σ2} (op : UnOp σ1 σ2) (t : Term Σ σ1) :
      peval_unop' op t ≡ term_unop op t.
    Proof. unfold peval_unop'; destruct (term_get_val_spec t); subst; easy. Qed.

    Lemma peval_vector_subrange_sound' {n} start len {p : IsTrue (start + len <=? n)}
      (t : Term Σ (ty.bvec n)) :
      peval_vector_subrange start len t ≡
      term_vector_subrange start len t.
    Proof.
      unfold peval_vector_subrange, term_vector_subrange. destruct bv.leview.
      now rewrite peval_bvdrop_sound, peval_bvtake_sound.
    Qed.

    Lemma peval_vector_subrange_sound {n} start len {p : IsTrue (start + len <=? n)}
      (t : Term Σ (ty.bvec n)) :
      peval_vector_subrange start len t ≡
      term_unop (uop.vector_subrange start len) t.
    Proof.
      rewrite peval_vector_subrange_sound'. intros ι; cbn.
      unfold term_vector_subrange, bv.vector_subrange.
      now destruct bv.leview.
    Qed.

    Lemma peval_zext_sound {m n} {p : IsTrue (m <=? n)} (t : Term Σ (ty.bvec m)) :
      peval_zext (p :=p) t ≡ term_zext t.
    Proof.
      intros ι. cbn. unfold peval_zext, bv.zext.
      destruct bv.leview eqn:?. destruct eq_dec.
      - clear Heql. assert (k = 0) by lia. subst.
        assert (e = transparent.nat_add_0_r m) by apply uip.
        subst. unfold bv.zext'. rewrite bv.app_nil_r.
        refine (inst_eq_rect_indexed (T := fun n Σ => Term Σ (ty.bvec n)) _ _ ι).
      - cbn. unfold bv.zext. now rewrite Heql.
    Qed.

    Lemma peval_unop_sound {σ1 σ2} (op : UnOp σ1 σ2) (t : Term Σ σ1) :
      peval_unop op t ≡ term_unop op t.
    Proof.
      destruct op; cbn [peval_unop];
        auto using peval_unop'_sound, peval_not_sound, peval_unsigned_sound,
                 peval_bvdrop_sound, peval_bvtake_sound,
                   peval_vector_subrange_sound, peval_zext_sound.
    Qed.

    Definition peval_union {U K} (t : Term Σ (unionk_ty U K)) : Term Σ (ty.union U) :=
      match term_get_val t with
      | Some v => term_val (ty.union U) (unionv_fold U (existT K v))
      | None   => term_union U K t
      end.

    Lemma peval_union_sound {U K} (t : Term Σ (unionk_ty U K)) :
      peval_union t ≡ term_union U K t.
    Proof. unfold peval_union. destruct (term_get_val_spec t); now subst. Qed.

    Import option.notations.
    Fixpoint peval_record' {rfs : NCtx recordf Ty} (ts : NamedEnv (Term Σ) rfs) {struct ts} : option (NamedEnv Val rfs) :=
      match ts with
      | nenv.nil         => Some [env]
      | nenv.snoc ts _ t => vs <- peval_record' ts ;;
                           v  <- term_get_val t ;;
                           Some (nenv.snoc vs _ v)
      end.

    Definition peval_record R (ts : NamedEnv (Term Σ) (recordf_ty R)) : Term Σ (ty.record R) :=
      match peval_record' ts with
      | Some a => term_val (ty.record R) (recordv_fold R a)
      | None => term_record R ts
      end.

    Lemma peval_record'_sound {rfs : NCtx recordf Ty} (ts : NamedEnv (Term Σ) rfs) :
      option.wlp (fun vs => forall ι, inst ts ι = vs) (peval_record' ts).
    Proof.
      induction ts; cbn.
      - now constructor.
      - rewrite option.wlp_bind. revert IHts.
        apply option.wlp_monotonic. intros vs IHvs.
        rewrite option.wlp_bind. generalize (term_get_val_spec db).
        apply option.wlp_monotonic. intros v IHv. constructor.
        intros ι. specialize (IHvs ι). subst. reflexivity.
    Qed.

    Lemma peval_record_sound {R} ts :
      peval_record R ts ≡ term_record R ts.
    Proof.
      unfold peval_record. destruct (peval_record'_sound ts); [|reflexivity].
      intros ι; cbn. now f_equal.
    Qed.

    Lemma tmr_ring_morph_peval' `{TermRing σ}
      {rm : ring_morph (term_val (Σ := Σ) σ tmr_zero) (term_val σ tmr_one)
         (term_binop tmr_plus) (term_binop tmr_times) (term_binop tmr_minus)
         (term_unop tmr_negate) base.equiv 0%Z 1%Z
         Z.add Z.mul Z.sub Z.opp Z.eqb (λ c : Z, term_val σ (tmr_of_Z c))} :
      ring_morph (term_val (Σ := Σ) σ tmr_zero) (term_val σ tmr_one)
        (peval_binop' tmr_plus) (peval_binop' tmr_times) (peval_binop' tmr_minus)
        (peval_unop' tmr_negate) base.equiv 0%Z 1%Z
        Z.add Z.mul Z.sub Z.opp Z.eqb (λ c : Z, term_val σ (tmr_of_Z c)).
    Proof.
      constructor; intros; rewrite ?peval_binop'_sound, ?peval_unop'_sound.
      - apply (morph0 rm).
      - apply (morph1 rm).
      - apply (morph_add rm).
      - apply (morph_sub rm).
      - apply (morph_mul rm).
      - apply (morph_opp rm).
      - now apply (morph_eq rm).
    Qed.

    Lemma tmr_ring_theory_peval' `{TermRing σ}
      {rt : ring_theory (term_val (Σ := Σ) σ tmr_zero) (term_val σ tmr_one) (term_binop tmr_plus) (term_binop tmr_times) (term_binop tmr_minus) (term_unop tmr_negate) base.equiv} :
      ring_theory (term_val (Σ := Σ) σ tmr_zero) (term_val σ tmr_one) (peval_binop' tmr_plus) (peval_binop' tmr_times) (peval_binop' tmr_minus) (peval_unop' tmr_negate) base.equiv.
    Proof.
      constructor; intros; rewrite ?peval_binop'_sound, ?peval_unop'_sound.
      - apply (Radd_0_l rt).
      - apply (Radd_comm rt).
      - apply (Radd_assoc rt).
      - apply (Rmul_1_l rt).
      - apply (Rmul_comm rt).
      - apply (Rmul_assoc rt).
      - apply (Rdistr_l rt).
      - apply (Rsub_def rt).
      - apply (Ropp_def rt).
    Qed.

    Lemma tmr_ring_eq_ext_peval' `{TermRing σ}
      {ree : ring_eq_ext (term_binop (Σ := Σ) tmr_plus) (term_binop tmr_times) (term_unop tmr_negate) base.equiv} :
      ring_eq_ext (peval_binop' tmr_plus) (peval_binop' tmr_times) (peval_unop' tmr_negate) base.equiv.
    Proof.
      constructor; repeat intros ? ? ?; rewrite ?peval_binop'_sound, ?peval_unop'_sound.
      - now apply (Radd_ext ree).
      - now apply (Rmul_ext ree).
      - now apply (Ropp_ext ree).
    Qed.

    Lemma Pphi_more_proper `{equivR : base.Equiv R, !Reflexive (≡@{R})} :
      Proper (eq ==> (base.equiv ==> base.equiv ==> base.equiv) ==> (base.equiv ==> base.equiv ==> base.equiv) ==> forall_relation (fun C => eq ==> base.equiv ==> eq ==> base.equiv)) (@Pphi R).
    Proof.
      intros r0 ? <- radd1 radd2 Hradd rmul1 rmul2 Hrmul C phi1 ? <- env1 env2 Henv pol ? <-.
      revert r0 radd1 radd2 Hradd rmul1 rmul2 Hrmul phi1 env1 env2 Henv.
      induction pol;
        intros r0 radd1 radd2 Hradd rmul1 rmul2 Hrmul phi1 env1 env2 Henv;
        cbn.
      - reflexivity.
      - apply IHpol; eauto; now apply proper_jump_equiv.
      - apply Hradd.
        apply Hrmul.
        now apply IHpol1.
        apply proper_pow_pos; try easy.
        now apply proper_hd_equiv.
        apply IHpol2; try easy.
        now apply proper_tl_equiv.
    Qed.

    Lemma evalPol_norm_aux `{tmr : TermRing σ} {p : PExpr Z} (l : list (Term Σ σ)) :
      evalPolTm l (norm_aux 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Z.eqb p) ≡ evalPExprTm l p.
    Proof.
      unfold evalPolTm, evalPExprTm.
      rewrite Pphi_dev_ok;
        try eauto using tmr_ring_morph_peval', tmr_ring_theory_peval', tmr_ring_eq_ext_peval', tmr_ring_eq_ext, Rth_ARth, tmr_ring_theory, tmr_ring_morph, get_signZ_th with typeclass_instances.
      rewrite norm_aux_spec;
        try eauto using tmr_ring_eq_ext, Rth_ARth, tmr_ring_theory, tmr_ring_morph, get_signZ_th, pow_N_th with typeclass_instances.
      apply Pphi_more_proper; try easy;
        repeat intros ? ? ?;
        rewrite peval_binop'_sound;
        now apply proper_term_binop.
    Qed.

    Lemma CanonTermRep_adeq {σ : Ty} {ct : CanonTerm σ} {t} : CanonTermRep ct t -> CanonTerm_to_Term ct ≡ t.
    Proof.
      destruct σ; intros; cbn; try trivial;
        specialize (H []%list 1%positive);
        destruct (ct []%list 1%positive);
        rewrite evalPol_norm_aux;
        now rewrite <-(H eq_refl nil), app_nil_r.
    Qed.

    Lemma Term_Quote_bin_sound {n} {op : BinOp (ty.bvec n) (ty.bvec n) (ty.bvec n)}
      {comb} {ct1 t1 ct2 t2} :
      (forall env pol1 pol2, evalPExprTm env (comb pol1 pol2) = term_binop op (evalPExprTm env pol1) (evalPExprTm env pol2)) ->
      CanonTermRep (σ := ty.bvec n) ct1 t1 ->
      CanonTermRep (σ := ty.bvec n) ct2 t2 ->
      CanonTermRep (σ := ty.bvec n) (Term_Quote_bin comb ct1 ct2) (term_binop op t1 t2).
    Proof.
      intros Hcomb.
      now eapply Term_Quote_bin_Valid.
    Qed.

    Definition CanonTerm_def {σ : Ty} : Term Σ σ -> CanonTerm σ :=
      match σ with
      | ty.bvec n => Term_Quote_def
      | ty.int => Term_Quote_def
      | _ => fun t => t
      end.

    Lemma CanonTerm_def_sound {σ : Ty} {t : Term Σ σ} :
      CanonTermRep (CanonTerm_def t) t.
    Proof.
      destruct σ; try reflexivity;
      apply Term_Quote_def_Valid.
    Qed.

    Definition peval2_val {σ : Ty} : Val σ -> CanonTerm σ :=
      match σ with
      | ty.bvec n => fun v l p => (PEc (bv.unsigned v) , nil)
      | ty.int => fun v l p => (PEc v , nil)
      | _ => term_val _
      end.

    Lemma peval2_val_sound {σ : Ty} {v : Val σ} : CanonTermRep (peval2_val v) (term_val _ v).
    Proof. destruct σ; try reflexivity;
           intros lo ? -> la; cbn; try reflexivity.
           now rewrite bv.of_Z_unsigned.
    Qed.

    Definition peval2_binop {σ1 σ2 σ3 : Ty} (op : BinOp σ1 σ2 σ3) :
      CanonTerm σ1 -> CanonTerm σ2 -> CanonTerm σ3 :=
      match op in BinOp σ1 σ2 σ3 return CanonTerm σ1 -> CanonTerm σ2 -> CanonTerm σ3 with
      | bop.plus => Term_Quote_bin (@PEadd _)
      | bop.minus => Term_Quote_bin (@PEsub _)
      | bop.times => Term_Quote_bin (@PEmul _)
      | bop.land => fun t1 t2 => CanonTerm_def (peval_binop bop.land (CanonTerm_to_Term t1) (CanonTerm_to_Term t2))
      | bop.and => peval_binop bop.and
      | bop.or => peval_binop bop.or
      | bop.pair => fun t1 t2 => peval_binop bop.pair (CanonTerm_to_Term t1) (CanonTerm_to_Term t2)
      | bop.cons => fun t1 t2 => peval_binop bop.cons (CanonTerm_to_Term t1) t2
      | bop.append => fun t1 t2 => peval_binop bop.append t1 t2
      | bop.shiftr => fun t1 t2 => CanonTerm_def (peval_binop bop.shiftr (CanonTerm_to_Term t1) (CanonTerm_to_Term t2))
      | bop.shiftl => fun t1 t2 => CanonTerm_def (peval_binop bop.shiftl (CanonTerm_to_Term t1) (CanonTerm_to_Term t2))
      | bop.bvadd => Term_Quote_bin (@PEadd _)
      | bop.bvsub => Term_Quote_bin (@PEsub _)
      | bop.bvmul => Term_Quote_bin (@PEmul _)
      | bop.bvand => fun t1 t2 => CanonTerm_def (peval_binop bop.bvand (CanonTerm_to_Term t1) (CanonTerm_to_Term t2))
      | bop.bvor => fun t1 t2 => CanonTerm_def (peval_binop bop.bvor (CanonTerm_to_Term t1) (CanonTerm_to_Term t2))
      | bop.bvxor => fun t1 t2 => CanonTerm_def (peval_binop bop.bvxor (CanonTerm_to_Term t1) (CanonTerm_to_Term t2))
      | bop.bvapp => fun t1 t2 => CanonTerm_def (peval_binop bop.bvapp (CanonTerm_to_Term t1) (CanonTerm_to_Term t2))
      | bop.bvcons => fun t1 t2 => CanonTerm_def (peval_binop bop.bvcons t1 (CanonTerm_to_Term t2))
      | (bop.update_vector_subrange s l) => fun t1 t2 => CanonTerm_def (peval_binop (bop.update_vector_subrange s l) (CanonTerm_to_Term t1) (CanonTerm_to_Term t2))
      | bop.relop rop => fun t1 t2 => peval_binop (bop.relop rop) (CanonTerm_to_Term t1) (CanonTerm_to_Term t2)
      end.

    Lemma peval2_binop_sound {σ1 σ2 σ3 : Ty} {op : BinOp σ1 σ2 σ3}
      {ct1 : CanonTerm σ1} {t1} {ct2 : CanonTerm σ2} {t2} :
      CanonTermRep ct1 t1 ->
      CanonTermRep ct2 t2 ->
      CanonTermRep (peval2_binop op ct1 ct2) (term_binop op t1 t2).
    Proof.
      destruct op; intros H1 H2; cbn [peval2_binop].
      - now eapply Term_Quote_bin_Valid.
      - now eapply Term_Quote_bin_Valid.
      - now eapply Term_Quote_bin_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), <-peval_binop_sound.
        now eapply Term_Quote_def_Valid.
      - now rewrite peval_binop_sound, H1, H2.
      - now rewrite peval_binop_sound, <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2).
      - now rewrite peval_binop_sound, <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2).
      - now rewrite peval_binop_sound, <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2).
      - now rewrite peval_binop_sound, <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2).
      - rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), <-peval_binop_sound.
        now eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), <-peval_binop_sound.
        now eapply Term_Quote_def_Valid.
      - now eapply Term_Quote_bin_Valid.
      - now eapply Term_Quote_bin_Valid.
      - now eapply Term_Quote_bin_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), <-peval_binop_sound.
        now eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), <-peval_binop_sound.
        now eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), <-peval_binop_sound.
        now eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), <-peval_binop_sound.
        now eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), <-peval_binop_sound.
        now eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), <-peval_binop_sound.
        now eapply Term_Quote_def_Valid.
      - now rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), peval_binop_sound.
    Qed.

    Definition peval2_unop {σ1 σ2 : Ty} (op : UnOp σ1 σ2) :
      CanonTerm σ1 -> CanonTerm σ2 :=
      match op in UnOp σ1 σ2 return CanonTerm σ1 -> CanonTerm σ2 with
      | uop.inl => fun t1 => peval_unop uop.inl (CanonTerm_to_Term t1)
      | uop.inr => fun t1 => peval_unop uop.inr (CanonTerm_to_Term t1)
      | uop.neg => Term_Quote_unop (@PEopp _)
      | uop.not => peval_unop uop.not
      | uop.rev => fun t1 => peval_unop uop.rev (CanonTerm_to_Term t1)
      | uop.sext => fun t1 => CanonTerm_def (peval_unop uop.sext (CanonTerm_to_Term t1))
      | uop.zext => fun t1 => CanonTerm_def (peval_unop uop.zext (CanonTerm_to_Term t1))
      | uop.get_slice_int => fun t1 => CanonTerm_def (peval_unop uop.get_slice_int (CanonTerm_to_Term t1))
      | uop.signed => fun t1 => CanonTerm_def (peval_unop uop.signed (CanonTerm_to_Term t1))
      | uop.unsigned => fun t1 => CanonTerm_def (peval_unop uop.unsigned (CanonTerm_to_Term t1))
      | uop.truncate m => fun t1 => CanonTerm_def (peval_unop (uop.truncate m) (CanonTerm_to_Term t1))
      | uop.vector_subrange s l => fun t1 => CanonTerm_def (peval_unop (uop.vector_subrange s l) (CanonTerm_to_Term t1))
      | uop.bvnot => fun t1 => CanonTerm_def (peval_unop uop.bvnot (CanonTerm_to_Term t1))
      | uop.bvdrop m => fun t1 => CanonTerm_def (peval_unop (uop.bvdrop m) (CanonTerm_to_Term t1))
      | uop.bvtake m => fun t1 => CanonTerm_def (peval_unop (uop.bvtake m) (CanonTerm_to_Term t1))
      | uop.negate => Term_Quote_unop (@PEopp _)
      end.

    Lemma peval2_unop_sound {σ1 σ2 : Ty} {op : UnOp σ1 σ2}
      {ct1 : CanonTerm σ1} {t1} :
      CanonTermRep ct1 t1 ->
      CanonTermRep (peval2_unop op ct1) (term_unop op t1).
    Proof.
      destruct op; intros H1; cbn [peval2_unop].
      - now rewrite peval_unop_sound, <-(CanonTermRep_adeq H1).
      - now rewrite peval_unop_sound, <-(CanonTermRep_adeq H1).
      - now eapply Term_Quote_unop_Valid.
      - now rewrite peval_unop_sound, <-(CanonTermRep_adeq H1).
      - now rewrite peval_unop_sound, <-(CanonTermRep_adeq H1).
      - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound.
        eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound.
        eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound.
        eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound.
        eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound.
        eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound.
        eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound.
        eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound.
        eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound.
        eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound.
        eapply Term_Quote_def_Valid.
      - now eapply Term_Quote_unop_Valid.
    Qed.

    (*
     * peval2 runs the ring solver normalizer on ring expressions of type `bvec n` and `int` and
     * runs custom partial evaluation functions on other terms.
     *
     * In order to maximize sharing identical unknown subterms in quoted ring expressions, we keep
     * them in quoting monad form (`RQuote σ`, where we have access to already-quoted unknown subterms)
     * until they are destructed using a non-ring operator.
     * To this end, `CanonTerm σ` is `RQuote σ` for `σ = ty.int` or `σ = ty.bvec n` but it is `Term Σ σ`
     * for other types.
     * Once quoted terms are destructed using a non-ring expression, the quoting monad and ring solver normalizer are
     * run by CanonTerm_to_Term.
     *)
    Fixpoint peval2 [σ] (t : Term Σ σ) : CanonTerm σ :=
      match t with
      | term_var ς                 => CanonTerm_def (term_var ς)
      | term_val _ v               => peval2_val v
      | term_binop op t1 t2        => peval2_binop op (peval2 t1) (peval2 t2)
      | term_unop op t             => peval2_unop op (peval2 t)
      | term_tuple ts              => term_tuple (env.map (fun b t => CanonTerm_to_Term (peval2 t)) ts)
      | term_union U K t           => peval_union (CanonTerm_to_Term (peval2 t))
      | term_record R ts           => peval_record R (nenv.map (fun b t => CanonTerm_to_Term (peval2 t)) ts)
      end.

    Lemma peval2_sound [σ] (t : Term Σ σ) :
      CanonTermRep (peval2 t) t.
    Proof.
      induction t; cbn.
      - now eapply CanonTerm_def_sound.
      - eapply peval2_val_sound.
      - now eapply peval2_binop_sound.
      - now eapply peval2_unop_sound.
      - apply proper_term_tuple.
        induction IH; [reflexivity|]; cbn.
        apply proper_env_snoc; first trivial.
        now apply CanonTermRep_adeq.
      - etransitivity; [apply peval_union_sound|apply proper_term_union].
        now apply CanonTermRep_adeq.
      - rewrite peval_record_sound.
        apply proper_term_record.
        induction IH; cbn; [reflexivity|].
        apply proper_namedenv_snoc; first trivial.
        now apply CanonTermRep_adeq.
    Qed.


    (* This is the top-level partial evaluation function.
     * It delegates to peval2 to do the real work, but only does so when it
     * reaches a term whose type cannot be meta-level polymorphic.
     *
     * Specifically, it does not run peval2 on variables, values and (recursively) list elements.
     * These terms cannot be reduced further anyway, but also their type may be polymorphically
     * quantified in Gallina.
     * Passing such terms to peval2 would make peval2 pattern match on their type, which would produce
     * a neutral Gallina term that Rocq cannot evaluate further, which in turn quickly leads to huge VCs.
     * An example verification that depends on this is
     * `valid_contract_length` in test/Example.v
     *
     * The types of other terms is fixed anyway (for example the type of term_binop is fixed for all binops
     * except bop.cons) and pattern matching on the type will reduce fine.
     *)
    Fixpoint peval [σ] (t : Term Σ σ) : Term Σ σ :=
      let res_poly :=
        match t in Term _ σ return option (Term Σ σ) with
          term_var x => Some (term_var x)
        | term_val σ v => Some (term_val _ v)
        | @term_binop _ σ1 σ2 _ op t1 t2 =>
            (match op in BinOp σ1 σ2 σ3 return Term Σ σ1 -> Term Σ σ2 -> option (Term Σ σ3) with
             | bop.cons => fun t1 t2 => Some (peval_binop' bop.cons (peval t1) (peval t2))
             | _ => fun _ _ => None
             end) t1 t2
        | _ => None
        end in
          match res_poly with
            Some t => t
          | None => CanonTerm_to_Term (peval2 t)
          end.

    Lemma peval_sound [σ] (t : Term Σ σ) :
      peval t ≡ t.
    Proof.
      induction t; try reflexivity.
      - destruct op; try (eapply CanonTermRep_adeq; eapply peval2_sound).
        cbn. now rewrite peval_binop'_sound, IHt1, IHt2.
      - eapply CanonTermRep_adeq; eapply peval2_sound.
      - eapply CanonTermRep_adeq; eapply peval2_sound.
      - eapply CanonTermRep_adeq; eapply peval2_sound.
      - eapply CanonTermRep_adeq; eapply peval2_sound.
    Qed.
    #[global] Arguments peval [σ] t : simpl never.

    Definition pevals [Δ] : Env (Term Σ) Δ -> Env (Term Σ) Δ :=
      env.map (fun σ  t => peval t).

    Lemma pevals_sound [Δ] (ts : Env (Term Σ) Δ) :
      pevals ts ≡ ts.
    Proof.
      induction ts; [reflexivity|]; cbn.
      apply proper_env_snoc; auto using peval_sound.
    Qed.

  End WithLCtx.

  Example test_zext x :
    let t := term_var_in ctx.in_zero in
    @peval [x∷ty.bvec 32] _ (term_zext t) = t.
  Proof. reflexivity. Abort.

End PartialEvaluationOn.

(* Local Variables: *)
(* proof-omit-proofs-option: t *)
(* End: *)
