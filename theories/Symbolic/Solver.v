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
     Classes.Morphisms_Prop
     Classes.RelationClasses
     NArith.BinNat
     Relations.Relation_Definitions
     ZArith.BinInt.

From Katamaran Require Import
     Base
     Bitvector
     Prelude
     Syntax.Predicates
     Symbolic.Propositions
     Symbolic.UnifLogic
     Symbolic.Worlds.

From Equations Require Import
     Equations.

Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.
Local Set Equations Transparent.

Module Type GenericSolverOn
  (Import B : Base)
  (Import P : PredicateKit B)
  (Import W : WorldsMixin B P)
  (Import S : SolverKit B P W)
  (Import SP : SymPropOn B P W)
  (Import UL : UnifLogicOn B P W)
  (Import LSP : LogSymPropOn B P W SP UL).

  Import iris.bi.interface iris.proofmode.proofmode proofmode LogicalSoundness.
  Import AutorewriteUnifLogic.

  Module Import GenericSolver.
    Import option.notations.
    Import DList.

    (* A boolean term as a formula, keeping its propositional structure. *)
    Fixpoint formula_of_bool [Σ] (t : Term Σ ty.bool) : Formula Σ :=
      Term_bool_case (fun _ => Formula Σ)
        (fun (*var*) ς _        => formula_bool (term_var ς))
        (fun (*val*) b          => if b then formula_true else formula_false)
        (fun (*and*) t1 t2      => formula_and (formula_of_bool t1) (formula_of_bool t2))
        (fun (*or*)  t1 t2      => formula_or (formula_of_bool t1) (formula_of_bool t2))
        (fun (*rel*) σ op t1 t2 => formula_relop op t1 t2)
        (fun (*not*) t1         => formula_of_bool_neg t1)
        t
    with
    formula_of_bool_neg [Σ] (t : Term Σ ty.bool) : Formula Σ :=
      Term_bool_case (fun _ => Formula Σ)
        (fun (*var*) ς _        => formula_bool (term_unop uop.not (term_var ς)))
        (fun (*val*) b          => if b then formula_false else formula_true)
        (fun (*and*) t1 t2      => formula_or (formula_of_bool_neg t1) (formula_of_bool_neg t2))
        (fun (*or*)  t1 t2      => formula_and (formula_of_bool_neg t1) (formula_of_bool_neg t2))
        (fun (*rel*) σ op t1 t2 => formula_relop_neg op t1 t2)
        (fun (*not*) t1         => formula_of_bool t1)
        t.

    Fixpoint simplify_bool [Σ] (t : Term Σ ty.bool) : DList Σ :=
      Term_bool_case (fun _ => DList Σ)
        (fun (*var*) ς _        => singleton (formula_bool (term_var ς)))
        (fun (*val*) b          => if b then empty else error)
        (fun (*and*) t1 t2      => cat (simplify_bool t1) (simplify_bool t2))
        (fun (*or*)  t1 t2      => singleton (formula_or (formula_of_bool t1) (formula_of_bool t2)))
        (fun (*rel*) σ op t1 t2 => singleton (formula_relop op t1 t2))
        (fun (*not*) t1         => simplify_bool_neg t1)
        t
    with
    simplify_bool_neg [Σ] (t : Term Σ ty.bool) : DList Σ :=
      Term_bool_case (fun _ => DList Σ)
        (fun (*var*) ς _        => singleton (formula_bool (term_unop uop.not (term_var ς))))
        (fun (*val*) b          => if b then error else empty)
        (fun (*and*) t1 t2      => singleton (formula_or (formula_of_bool_neg t1) (formula_of_bool_neg t2)))
        (fun (*or*)  t1 t2      => cat (simplify_bool_neg t1) (simplify_bool_neg t2))
        (fun (*rel*) σ op t1 t2 => singleton (formula_relop_neg op t1 t2))
        (fun (*not*) t1         => simplify_bool t1)
        t.

    Lemma formula_of_bool_instprop {Σ} (ι : Valuation Σ) (t : Term Σ ty.bool) :
      (instprop (formula_of_bool t) ι <-> inst (T := STerm ty.bool) t ι = true) /\
      (instprop (formula_of_bool_neg t) ι <-> inst (T := STerm ty.bool) t ι = false).
    Proof.
      induction t using Term_bool_ind; cbn.
      - destruct env.lookup; intuition.
      - destruct b; cbn; intuition.
      - destruct IHt1 as [-> ->], IHt2 as [-> ->].
        destruct (inst t1 ι), (inst t2 ι); cbn; intuition.
      - destruct IHt1 as [-> ->], IHt2 as [-> ->].
        destruct (inst t1 ι), (inst t2 ι); cbn; intuition.
      - split; [apply bop.eval_relop_equiv|apply instprop_formula_relop_neg].
      - destruct IHt as [-> ->]. destruct (inst t ι); cbn; intuition.
    Qed.

    Lemma formula_of_bool_spec {w : World} (t : Term w ty.bool) :
      (instpred (formula_of_bool t) ⊣⊢ repₚ (T := fun Σ => Term Σ ty.bool) true t) ∧
      (instpred (formula_of_bool_neg t) ⊣⊢ repₚ (T := fun Σ => Term Σ ty.bool) false t).
    Proof.
      split; constructor; intros ι _; rewrite instpred_prop; apply formula_of_bool_instprop.
    Qed.

    Lemma simplify_bool_spec_combined {w : World} (t : Term w ty.bool) :
      (instpred (simplify_bool t) ⊣⊢ repₚ (T := fun Σ => Term Σ ty.bool) true t) ∧
      (instpred (simplify_bool_neg t) ⊣⊢ repₚ (T := fun Σ => Term Σ ty.bool) false t).
    Proof.
      induction t using Term_bool_ind; cbn; arw.
      - destruct b; arw.
      - split.
        + now destruct IHt1 as [-> _], IHt2 as [-> _].
        + exact (proj2 (formula_of_bool_spec (term_and t1 t2))).
      - split.
        + exact (proj1 (formula_of_bool_spec (term_or t1 t2))).
        + destruct IHt1 as [_ ->], IHt2 as [_ ->]; arw.
    Qed.

    Lemma simplify_bool_spec [w : World] (t : Term w ty.bool) :
      instpred (simplify_bool t) ⊣⊢ instpred (formula_bool t).
    Proof. apply simplify_bool_spec_combined. Qed.

    Lemma simplify_bool_neg_spec [w : World] (t : Term w ty.bool) :
      instpred (simplify_bool_neg t) ⊣⊢ repₚ (T := fun Σ => Term Σ ty.bool) false t.
    Proof. apply simplify_bool_spec_combined. Qed.
    #[local] Opaque simplify_bool simplify_bool_neg.
    #[local] Hint Rewrite simplify_bool_spec simplify_bool_neg_spec : uniflogic.

    Definition simplify_eqb {Σ σ} (t1 t2 : Term Σ σ) : DList Σ :=
      let num t :=
        match t with
        | term_var _       => 1
        | term_val _ _     => 2
        | term_binop _ _ _ => 3
        | term_unop _ _    => 4
        | term_tuple _     => 5
        | term_union _ _ _ => 6
        | term_record _ _  => 7
        end%positive in
      if Term_eqb t1 t2
      then empty
      else
        if (num t1 <=? num t2)%positive
        then dlist_eq t1 t2
        else dlist_eq t2 t1.

    Lemma simplify_eqb_spec [w : World] [σ] (t1 t2 : STerm σ w) :
      instpred (simplify_eqb t1 t2) ⊣⊢ instpred (formula_eq t1 t2).
    Proof.
      unfold simplify_eqb.
      destruct (Term_eqb_spec t1 t2); subst; arw.
      destruct Pos.leb; arw.
    Qed.
    #[local] Hint Rewrite simplify_eqb_spec : uniflogic.
    #[local] Opaque simplify_eqb.

    Section SimplifyEq.

      Context {Σ : LCtx}.

      Definition simplify_eq_binop_default_val {σ1 σ2 σ} (op : BinOp σ1 σ2 σ)
        (t1 : Term Σ σ1) (t2 : Term Σ σ2) (v : Val σ) : DList Σ :=
        dlist_eq (term_val σ v) (term_binop op t1 t2).

      Definition simplify_eq_unop_default_val {σ1 σ2} (op : UnOp σ1 σ2)
        (t : Term Σ σ1) (v : Val σ2) : DList Σ :=
        dlist_eq (term_val _ v) (term_unop op t).

      Definition simplify_eq_binop_and_val (t1 t2 : Term Σ ty.bool)
        (v : Val ty.bool) : DList Σ :=
        if v
        then simplify_bool (term_binop bop.and t1 t2)
        else simplify_bool_neg (term_binop bop.and t1 t2).

      Definition simplify_eq_binop_or_val (t1 t2 : Term Σ ty.bool)
        (v : Val ty.bool) : DList Σ :=
        if v
        then simplify_bool (term_binop bop.or t1 t2)
        else simplify_bool_neg (term_binop bop.or t1 t2).

      Definition simplify_eq_unop_not_val (t : Term Σ ty.bool) (v : Val ty.bool) :
        DList Σ :=
        if v then simplify_bool_neg t else simplify_bool t.

      Definition simplify_eq_binop_relop_val {σ} (op : RelOp σ)
        (t1 t2 : Term Σ σ) (v : Val ty.bool) : DList Σ :=
        if v
        then singleton (formula_relop op t1 t2)
        else singleton (formula_relop_neg op t1 t2).

      Section WithSimplifyEqVal.

        Variable simplify_eq_val : ∀ [σ] (t : Term Σ σ) (v : Val σ), DList Σ.

        Definition simplify_eq_binop_pair_val {σ1 σ2} (t1 : Term Σ σ1)
          (t2 : Term Σ σ2) (v : Val (ty.prod σ1 σ2)) : DList Σ :=
          let (v1, v2) := v in
          cat (simplify_eq_val t1 v1) (simplify_eq_val t2 v2).

        Definition simplify_eq_binop_cons_val {σ} (t1 : Term Σ σ)
          (t2 : Term Σ (ty.list σ)) (v : Val (ty.list σ)) : DList Σ :=
          match v with
          | nil        => error
          | cons vh vl => cat (simplify_eq_val t1 vh) (simplify_eq_val t2 vl)
          end.

        Definition simplify_eq_binop_bvapp_val {m n} (t1 : Term Σ (ty.bvec m))
          (t2 : Term Σ (ty.bvec n)) (v : Val (ty.bvec (m + n))) : DList Σ :=
          let (v1,v2) := bv.appView _ _ v in
          cat (simplify_eq_val t1 v1) (simplify_eq_val t2 v2).

        Definition simplify_eq_binop_bvcons_val {m} (t1 : Term Σ ty.bool)
          (t2 : Term Σ (ty.bvec m)) (v : Val (ty.bvec (S m))) : DList Σ :=
          let (v1,v2) := bv.view v in
          cat (simplify_eq_val t1 v1) (simplify_eq_val t2 v2).

        (* Simplifies equations of the form (term_binop op t1 t2 = v). *)
        Definition simplify_eq_binop_val [σ σ1 σ2] (op : BinOp σ1 σ2 σ) :
          Term Σ σ1 → Term Σ σ2 → Val σ → DList Σ :=
          match op with
          | bop.plus => simplify_eq_binop_default_val bop.plus
          | bop.minus => simplify_eq_binop_default_val bop.minus
          | bop.times => simplify_eq_binop_default_val bop.times
          | bop.land => simplify_eq_binop_default_val bop.land
          | bop.and => simplify_eq_binop_and_val
          | bop.or => simplify_eq_binop_or_val
          | bop.pair => simplify_eq_binop_pair_val
          | bop.cons => simplify_eq_binop_cons_val
          | bop.append => simplify_eq_binop_default_val bop.append
          | bop.shiftr => simplify_eq_binop_default_val bop.shiftr
          | bop.shiftl => simplify_eq_binop_default_val bop.shiftl
          | bop.bvadd => simplify_eq_binop_default_val bop.bvadd
          | bop.bvsub => simplify_eq_binop_default_val bop.bvsub
          | bop.bvmul => simplify_eq_binop_default_val bop.bvmul
          | bop.bvand => simplify_eq_binop_default_val bop.bvand
          | bop.bvor => simplify_eq_binop_default_val bop.bvor
          | bop.bvxor => simplify_eq_binop_default_val bop.bvxor
          | bop.bvapp => simplify_eq_binop_bvapp_val
          | bop.bvcons => simplify_eq_binop_bvcons_val
          | bop.update_vector_subrange s l =>
              simplify_eq_binop_default_val (bop.update_vector_subrange s l)
          | bop.relop op => simplify_eq_binop_relop_val op
          end.

        Definition simplify_eq_unop_inl_val {σ1 σ2} (t : Term Σ σ1)
          (v : Val (ty.sum σ1 σ2)) : DList Σ :=
          match v with
          | inl vl => simplify_eq_val t vl
          | inr _  => error
          end.

        Definition simplify_eq_unop_inr_val {σ1 σ2} (t : Term Σ σ2)
          (v : Val (ty.sum σ1 σ2)) : DList Σ :=
          match v with
          | inl _  => error
          | inr vr => simplify_eq_val t vr
          end.

        Definition simplify_eq_unop_neg_val (t : Term Σ ty.int) (v : Val ty.int) :
          DList Σ := simplify_eq_val t (Z.opp v).

        Definition simplify_eq_unop_signed_val {n} (t : Term Σ (ty.bvec n))
          (v : Val ty.int) : DList Σ :=
          if ((- 2 ^ (Z.of_nat n) <=? 2 * v) &&& (2 * v <? 2 ^ Z.of_nat n))%Z
          then simplify_eq_val t (bv.of_Z v)
          else error.

        Definition simplify_eq_unop_unsigned_val {n} (t : Term Σ (ty.bvec n))
          (v : Val ty.int) : DList Σ :=
          if ((0 <=? v) &&& (v <? 2 ^ Z.of_nat n))%Z
          then simplify_eq_val t (bv.of_Z v)
          else error.

        Definition simplify_eq_unop_val {σ1 σ2} (op : UnOp σ1 σ2) :
          Term Σ σ1 → Val σ2 → DList Σ :=
          match op with
          | uop.inl => simplify_eq_unop_inl_val
          | uop.inr => simplify_eq_unop_inr_val
          | uop.neg => simplify_eq_unop_neg_val
          | uop.not => simplify_eq_unop_not_val
          | uop.rev => simplify_eq_unop_default_val uop.rev
          | uop.sext => simplify_eq_unop_default_val uop.sext
          | uop.zext => simplify_eq_unop_default_val uop.zext
          | uop.get_slice_int => simplify_eq_unop_default_val uop.get_slice_int
          | uop.signed => simplify_eq_unop_signed_val
          | uop.unsigned => simplify_eq_unop_unsigned_val
          | uop.truncate m => simplify_eq_unop_default_val (uop.truncate m)
          | uop.vector_subrange s l => simplify_eq_unop_default_val (uop.vector_subrange s l)
          | uop.bvnot => simplify_eq_unop_default_val uop.bvnot
          | uop.bvdrop m => simplify_eq_unop_default_val (uop.bvdrop m)
          | uop.bvtake m => simplify_eq_unop_default_val (uop.bvtake m)
          | uop.negate => simplify_eq_unop_default_val uop.negate
          end.

        Definition simplify_eq_tuple_val {σs} (ts : Env (Term Σ) σs)
          (vs : Val (ty.tuple σs)) : DList Σ :=
          env.Env_rect
            (fun σs _ => Val (ty.tuple σs) → DList Σ)
            (fun _ => empty)
            (fun τs _ IHts τ t (vτsτ : Val (ty.tuple (τs ▻ τ))) =>
               let (vτs, vτ) := vτsτ in
               cat (IHts vτs) (simplify_eq_val t vτ))
            ts vs.

        Definition simplify_eq_union_val [U] [K1 : unionk U]
          (t1 : Term Σ (unionk_ty U K1)) (v2 : Val (ty.union U)) : DList Σ :=
          let (K2, v2) := unionv_unfold U v2 in
          match eq_dec K1 K2 with
          | left e  => let v2' := eq_rect_r (fun K1 => Val (unionk_ty U K1)) v2 e in
                       simplify_eq_val t1 v2'
          | right _ => error
          end.

        Definition simplify_eq_record_val (R : recordi)
          (ts : NamedEnv (Term Σ) (recordf_ty R)) (v : Val (ty.record R)) :
          DList Σ :=
          env.Env_rect
            (fun Δ _ => NamedEnv Val Δ → DList Σ)
            (fun _ => empty)
            (fun Δ _ IHts b t vs =>
               let (vsΔ,vb) := env.view vs in
               cat (IHts vsΔ) (simplify_eq_val t vb))
            ts
            (recordv_unfold R v).

      End WithSimplifyEqVal.

      Fixpoint simplify_eq_val [σ] (t : Term Σ σ) (v : Val σ) : DList Σ :=
        match t with
        | term_var x          => fun _ => dlist_eq t (term_val _ v)
        | term_val σ v        => fun v' => if eq_dec v v' then empty else error
        | term_binop op t1 t2 => simplify_eq_binop_val simplify_eq_val op t1 t2
        | term_unop op t      => simplify_eq_unop_val simplify_eq_val op t
        | term_tuple ts       => simplify_eq_tuple_val simplify_eq_val ts
        | term_union U K t    => simplify_eq_union_val simplify_eq_val t
        | term_record R ts    => simplify_eq_record_val simplify_eq_val R ts
        end v.


      Definition simplify_eq_binop_default {σ1 σ2 σ} (op : BinOp σ1 σ2 σ)
        (t1 : Term Σ σ1) (t2 : Term Σ σ2) (t : Term Σ σ) : DList Σ :=
        simplify_eqb (term_binop op t1 t2) t.

      Definition simplify_eq_binop_minus (tl1 : Term Σ ty.int)
        (tl2 : Term Σ ty.int) (tr : Term Σ ty.int) : DList Σ :=
        dlist_eq (term_val ty.int 0) (term_minus tr (term_minus tl1 tl2)).

      Definition simplify_eq_binop_times (tl1 : Term Σ ty.int)
        (tl2 : Term Σ ty.int) (tr : Term Σ ty.int) : DList Σ :=
        dlist_eq (term_val ty.int 0) (term_minus tr (term_times tl1 tl2)).

      Definition simplify_eq_unop_default {σ1 σ2} (op : UnOp σ1 σ2)
        (t1 : Term Σ σ1) (t : Term Σ σ2) : DList Σ :=
        simplify_eqb (term_unop op t1) t.

      Section WithSimplifyEq.

        Variable simplify_eq : forall [σ] (t1 t2 : Term Σ σ), DList Σ.

        Definition simplify_eq_binop_plus (tl1 : Term Σ ty.int)
          (tl2 : Term Σ ty.int) (tr : Term Σ ty.int) : DList Σ :=
          let default := dlist_eq (term_val ty.int 0)
                           (term_minus tr (term_plus tl1 tl2)) in
          Term_int_case (fun _ => DList Σ)
            (fun (*var*) _ _ => default)
            (fun (*val*) v => simplify_eq_val (term_plus tl1 tl2) v)
            (fun (*plus*) tr1 tr2 =>
               if Term_eqb tl1 tr1 then simplify_eq tl2 tr2 else
                 if Term_eqb tl2 tr2 then simplify_eq tl1 tr1 else
                   if Term_eqb tl1 tr2 then simplify_eq tl2 tr1 else
                     if Term_eqb tl2 tr1 then simplify_eq tl1 tr2 else
                       default)
            (fun (*minus*) tr1 tr2 =>
               if Term_eqb tl1 tr1 then simplify_eq tl2 (term_neg tr2) else
                 if Term_eqb tl2 tr1 then simplify_eq tl1 (term_neg tr2) else
                   default)
            (fun (*times*) tr1 tr2 => default)
            (fun (*land*) tr1 tr2 => default)
            (fun (*neg*) tr' => default)
            (fun (*signed*) n _ => default)
            (fun (*unsigned*) n _ => default)
            tr.

        Definition simplify_eq_binop_and (tl1 : Term Σ ty.bool)
          (tl2 : Term Σ ty.bool) (tr : Term Σ ty.bool) : DList Σ :=
          let tl := term_and tl1 tl2 in
          let default := dlist_eq tl tr in
          Term_bool_case (fun _ => DList Σ)
            (fun (*var*) _ _ => dlist_eq tr tl)
            (fun (*val*) v => simplify_eq_val tl v)
            (fun (*and*) tr1 tr2 =>
               if Term_eqb tl1 tr1 && Term_eqb tl2 tr2
               then empty else default)
            (fun (*or*) _ _ => default)
            (fun (*relop*) _ _ _ _ => default)
            (fun (*not*) _ => default)
            tr.

        Definition simplify_eq_binop_or (tl1 : Term Σ ty.bool)
          (tl2 : Term Σ ty.bool) (tr : Term Σ ty.bool) : DList Σ :=
          let tl := term_or tl1 tl2 in
          let default := dlist_eq tl tr in
          Term_bool_case (fun _ => DList Σ)
            (fun (*var*) _ _ => dlist_eq tr tl)
            (fun (*val*) v => simplify_eq_val tl v)
            (fun (*and*) _ _ => default)
            (fun (*or*) tr1 tr2 =>
               if Term_eqb tl1 tr1 && Term_eqb tl2 tr2
               then empty else default)
            (fun (*relop*) _ _ _ _ => default)
            (fun (*not*) _ => default)
            tr.

        Definition simplify_eq_binop_pair {σ1 σ2} (t1 : Term Σ σ1)
          (t2 : Term Σ σ2) (t : Term Σ (ty.prod σ1 σ2)) : DList Σ :=
          Term_prod_case (fun _ => DList Σ)
            (fun (*var*) _ _      => dlist_eq t (term_pair t1 t2))
            (fun (*val*) v        => simplify_eq_val (term_pair t1 t2) v)
            (fun (*pair*) t1' t2' => cat (simplify_eq t1 t1') (simplify_eq t2 t2'))
            t.

        Definition simplify_eq_binop_cons {σ} (t1 : Term Σ σ)
          (t2 : Term Σ (ty.list σ)) (t : Term Σ (ty.list σ)) : DList Σ :=
          Term_list_case (fun _ => DList Σ)
            (fun (*var*) _ _ => dlist_eq t (term_cons t1 t2))
            (fun (*val*) v => simplify_eq_val (term_cons t1 t2) v)
            (fun (*cons*) t1' t2' => cat (simplify_eq t1 t1') (simplify_eq t2 t2'))
            (fun (*append*) _ _ => dlist_eq (term_cons t1 t2) t)
            (fun (*rev*) _ => dlist_eq (term_cons t1 t2) t)
            t.

        Definition simplify_eq_binop_append {σ} (tl1 : Term Σ (ty.list σ))
          (tl2 : Term Σ (ty.list σ)) (tr : Term Σ (ty.list σ)) : DList Σ :=
          Term_list_case (fun _ => DList Σ)
            (fun (*var*) _ _ => dlist_eq tr (term_append tl1 tl2))
            (fun (*val*) v => simplify_eq_val (term_append tl1 tl2) v)
            (fun (*cons*) t1' t2' => dlist_eq tr (term_append tl1 tl2))
            (fun (*append*) tr1 tr2 =>
               if Term_eqb tl1 tr1 then simplify_eq tl2 tr2 else
                 if Term_eqb tl2 tr2 then simplify_eq tl1 tr1 else
                   dlist_eq (term_append tl1 tl2) tr)
            (fun (*rev*) _ => dlist_eq (term_append tl1 tl2) tr)
            tr.

        Definition simplify_eq_binop_bvapp' {m n} (t1 : Term Σ (ty.bvec m))
          (t2 : Term Σ (ty.bvec n)) mn (t : Term Σ (ty.bvec mn))
          (e : m + n = mn) : DList Σ :=
          let default {mn} (_ : m + n = mn) : DList Σ :=
            dlist_eq (term_bvapp t1 t2)
              (eq_rect_r (fun l => Term Σ (ty.bvec l)) t e) in
          Term_bvec_case (fun mn t => m + n = mn -> DList Σ)
            (fun (*var*) _ _ _ _ =>
               dlist_eq
                 (eq_rect_r (fun l => Term Σ (ty.bvec l)) t e)
                 (term_bvapp t1 t2))
            (fun (*val*) n v e =>
               simplify_eq_val (term_bvapp t1 t2)
                 (eq_rect_r (fun l => Val (ty.bvec l)) v e))
            (fun (*bvadd*) _ _ _ => default)
            (fun (*bvsub*) _ _ _ => default)
            (fun (*bvmul*) _ _ _ => default)
            (fun (*bvand*) _ _ _ => default)
            (fun (*bvor*) _ _ _ => default)
            (fun (*bvxor*) _ _ _ => default)
            (fun (*shiftr*) _ _ _ _ => default)
            (fun (*shiftl*) _ _ _ _ => default)
            (fun (*bvapp*) m' n' =>
               match eq_dec m m' with
               | left em =>
                   match em with
                   | eq_refl =>
                       fun t1' t2' e' =>
                         let en  : n = n' :=
                           transparent.nat_add_cancel_l n n' m e' in
                         let t2' : Term Σ (ty.bvec n) :=
                           eq_rect_r (fun l => Term Σ (ty.bvec l)) t2' en in
                         cat
                           (simplify_eq t1 t1')
                           (simplify_eq t2 t2')
                   end
               | right _ => fun _ _ => default
               end)
            (fun (*bvcons*) _ _ _ => default)
            (fun (*update_vector_subrange*) _ _ _ _ _ _ => default)
            (fun (*bvnote*) _ _ => default)
            (fun (*negate*) _ _ => default)
            (fun (*sext*) _ _ _ _ => default)
            (fun (*zext*) _ _ _ _ => default)
            (fun (*get_slice_int*) _ _ => default)
            (fun (*truncate*) _ _ _ _ => default)
            (fun (*vector_subrange*) _ _ _ _ _ => default)
            (fun (*bvdrop*) _ _ _ => default)
            (fun (*bvtake*) _ _ _ => default)
            t e.

        Definition simplify_eq_binop_bvapp {m n} (t1 : Term Σ (ty.bvec m))
          (t2 : Term Σ (ty.bvec n)) (t : Term Σ (ty.bvec (m + n))) : DList Σ :=
          simplify_eq_binop_bvapp' t1 t2 t eq_refl.

        Definition simplify_eq_binop_bvcons' {m} (t1 : Term Σ ty.bool)
          (t2 : Term Σ (ty.bvec m)) sm (t : Term Σ (ty.bvec sm))
          (e : S m = sm) : DList Σ :=
          let default {sm} (_ : S m = sm) : DList Σ :=
            dlist_eq (term_bvcons t1 t2)
              (eq_rect_r (fun l => Term Σ (ty.bvec l)) t e) in
          Term_bvec_case (fun sm t => S m = sm -> DList Σ)
            (fun (*var*) _ _ _ _ =>
               dlist_eq
                 (eq_rect_r (fun l => Term Σ (ty.bvec l)) t e)
                 (term_bvcons t1 t2))
            (fun (*val*) n v e =>
               simplify_eq_val (term_bvcons t1 t2)
                 (eq_rect_r (fun l => Val (ty.bvec l)) v e))
            (fun (*bvadd*) _ _ _ => default)
            (fun (*bvsub*) _ _ _ => default)
            (fun (*bvmul*) _ _ _ => default)
            (fun (*bvand*) _ _ _ => default)
            (fun (*bvor*) _ _ _ => default)
            (fun (*bvxor*) _ _ _ => default)
            (fun (*shiftr*) _ _ _ _ => default)
            (fun (*shiftl*) _ _ _ _ => default)
            (fun (*bvapp*) _ _ _ _ => default)
            (fun (*bvcons*) m' t1' t2' e2 =>
               let e' : m = m' := eq_add_S m m' e2 in
               let t2' := eq_rect_r (fun l => Term Σ (ty.bvec l)) t2' e' in
               cat (simplify_eq t1 t1') (simplify_eq t2 t2'))
            (fun (*update_vector_subrange*) _ _ _ _ _ _ => default)
            (fun (*bvnote*) _ _ => default)
            (fun (*negate*) _ _ => default)
            (fun (*sext*) _ _ _ _ => default)
            (fun (*zext*) _ _ _ _ => default)
            (fun (*get_slice_int*) _ _ => default)
            (fun (*truncate*) _ _ _ _ => default)
            (fun (*vector_subrange*) _ _ _ _ _ => default)
            (fun (*bvdrop*) _ _ _ => default)
            (fun (*bvtake*) _ _ _ => default)
            t e.

        Definition simplify_eq_binop_bvcons {m} (t1 : Term Σ ty.bool)
          (t2 : Term Σ (ty.bvec m)) (t : Term Σ (ty.bvec (S m))) : DList Σ :=
          simplify_eq_binop_bvcons' t1 t2 t eq_refl.

        Fixpoint simplify_eq_relop {σ} (op : RelOp σ) (tl1 tl2 : Term Σ σ)
          (tr : Term Σ ty.bool) {struct tr} : DList Σ :=
          let tl := term_binop (bop.relop op) tl1 tl2 in
          Term_bool_case (fun _ => DList Σ)
            (fun (*var*) _ _ => dlist_eq tr tl)
            (fun (*val*) v => simplify_eq_val tl v)
            (fun (*and*) tr1 tr2 => dlist_eq tl tr)
            (fun (*or*) tr1 tr2 => dlist_eq tl tr)
            (fun (*relop*) _ op tr1 tr2 => dlist_eq tl tr)
            (fun (*not*) tr' =>
               match op with
               | bop.eq     => fun tl1 tl2 => simplify_eq_relop bop.neq tl1 tl2 tr'
               | bop.neq    => fun tl1 tl2 => simplify_eq_relop bop.eq tl1 tl2 tr'
               | bop.le     => fun tl1 tl2 => simplify_eq_relop bop.lt tl2 tl1 tr'
               | bop.lt     => fun tl1 tl2 => simplify_eq_relop bop.le tl2 tl1 tr'
               | bop.bvsle  => fun tl1 tl2 => simplify_eq_relop bop.bvslt tl2 tl1 tr'
               | bop.bvslt  => fun tl1 tl2 => simplify_eq_relop bop.bvsle tl2 tl1 tr'
               | bop.bvule  => fun tl1 tl2 => simplify_eq_relop bop.bvult tl2 tl1 tr'
               | bop.bvult  => fun tl1 tl2 => simplify_eq_relop bop.bvule tl2 tl1 tr'
               end tl1 tl2)
            tr.

        Definition simplify_eq_binop {σ1 σ2 σ} (op : BinOp σ1 σ2 σ) :
          Term Σ σ1 -> Term Σ σ2 -> Term Σ σ -> DList Σ :=
          match op in BinOp σ1 σ2 σ
                return Term Σ σ1 -> Term Σ σ2 -> Term Σ σ -> DList Σ
          with
          | bop.plus => simplify_eq_binop_plus
          | bop.minus => simplify_eq_binop_minus
          | bop.times => simplify_eq_binop_times
          | bop.land => simplify_eq_binop_default bop.land
          | bop.and => simplify_eq_binop_and
          | bop.or => simplify_eq_binop_or
          | bop.pair => simplify_eq_binop_pair
          | bop.cons => simplify_eq_binop_cons
          | bop.append => simplify_eq_binop_append
          | bop.shiftr => simplify_eq_binop_default bop.shiftr
          | bop.shiftl => simplify_eq_binop_default bop.shiftl
          | bop.bvadd => simplify_eq_binop_default bop.bvadd
          | bop.bvsub => simplify_eq_binop_default bop.bvsub
          | bop.bvmul => simplify_eq_binop_default bop.bvmul
          | bop.bvand => simplify_eq_binop_default bop.bvand
          | bop.bvor => simplify_eq_binop_default bop.bvor
          | bop.bvxor => simplify_eq_binop_default bop.bvxor
          | bop.bvapp => simplify_eq_binop_bvapp
          | bop.bvcons => simplify_eq_binop_bvcons
          | bop.update_vector_subrange s l =>
              simplify_eq_binop_default (bop.update_vector_subrange s l)
          | bop.relop rop => simplify_eq_relop rop
          end.

        Definition simplify_eq_unop_inl {σ1 σ2} (t1 : Term Σ σ1)
          (t : Term Σ (ty.sum σ1 σ2)) : DList Σ :=
          Term_sum_case (fun _ => DList Σ)
            (fun (*var*) x _ => simplify_eq_unop_default uop.inl t1 t)
            (fun (*val*) v   => simplify_eq_val (term_inl t1) v)
            (fun (*inl*) t1' => simplify_eq t1 t1')
            (fun (*inr*) t2  => error)
            t.

        Definition simplify_eq_unop_inr {σ1 σ2} (t2 : Term Σ σ2)
          (t : Term Σ (ty.sum σ1 σ2)) : DList Σ :=
          Term_sum_case (fun _ => DList Σ)
            (fun (*var*) x _ => simplify_eq_unop_default uop.inr t2 t)
            (fun (*val*) v   => simplify_eq_val (term_inr t2) v)
            (fun (*inl*) t1  => error)
            (fun (*inr*) t2' => simplify_eq t2 t2')
            t.

        Definition simplify_eq_unop_get_slice_int {m} (tl : Term Σ ty.int)
          (tr : Term Σ (ty.bvec m)) : DList Σ :=
          let tl := term_get_slice_int tl in
          if Term_eqb tl tr then empty else dlist_eq tl tr.

        Definition simplify_eq_unop_signed {m} (tl : Term Σ (ty.bvec m))
          (tr : Term Σ ty.int) : DList Σ :=
          let default := dlist_eq (term_val ty.int 0)
                           (term_minus tr (term_signed tl)) in
          Term_int_case (fun _ => DList Σ)
            (fun (*var*) _ _ => default)
            (fun (*val*) v => simplify_eq_val (term_signed tl) v)
            (fun (*plus*) tr1 tr2 => default)
            (fun (*minus*) tr1 tr2 => default)
            (fun (*times*) tr1 tr2 => default)
            (fun (*land*) tr1 tr2 => default)
            (fun (*neg*) tr' => default)
            (fun (*signed*) n =>
               match eq_dec m n with
               | left e => match e with eq_refl => simplify_eq tl end
               | right _ => fun _ => default
               end)
            (fun (*unsigned*) n tr' => default)
            tr.

        Definition simplify_eq_unop {σ1 σ2} (op : UnOp σ1 σ2) :
          Term Σ σ1 -> Term Σ σ2 -> DList Σ :=
          match op with
          | uop.inl => simplify_eq_unop_inl
          | uop.inr => simplify_eq_unop_inr
          | uop.neg => simplify_eq_unop_default uop.neg
          | uop.not => simplify_eq_unop_default uop.not
          | uop.rev => simplify_eq_unop_default uop.rev
          | uop.sext => simplify_eq_unop_default uop.sext
          | uop.zext => simplify_eq_unop_default uop.zext
          | uop.get_slice_int => simplify_eq_unop_get_slice_int
          | uop.signed => simplify_eq_unop_signed
          | uop.unsigned => simplify_eq_unop_default uop.unsigned
          | uop.truncate n => simplify_eq_unop_default (uop.truncate n)
          | uop.vector_subrange s l => simplify_eq_unop_default (uop.vector_subrange s l)
          | uop.bvnot => simplify_eq_unop_default uop.bvnot
          | uop.bvdrop m => simplify_eq_unop_default (uop.bvdrop m)
          | uop.bvtake m => simplify_eq_unop_default (uop.bvtake m)
          | uop.negate => simplify_eq_unop_default uop.negate
          end.

        Equations(noeqns) formula_eqs_ctx {Δ}
          (δ δ' : Env (Term Σ) Δ) : DList Σ :=
        | env.nil,        env.nil          => empty
        | env.snoc δ _ t, env.snoc δ' _ t' =>
            cat (formula_eqs_ctx δ δ') (simplify_eq t t').

        Equations(noeqns) formula_eqs_nctx {N} {Δ : NCtx N Ty}
          (δ δ' : NamedEnv (Term Σ) Δ) : DList Σ :=
        | env.nil,        env.nil          => empty
        | env.snoc δ _ t, env.snoc δ' _ t' =>
            cat (formula_eqs_nctx δ δ') (simplify_eq t t').

        Definition simplify_eq_tuple {σs} (tls : Env (Term Σ) σs)
          (tr : Term Σ (ty.tuple σs)) : DList Σ :=
          Term_tuple_case (fun _ => DList Σ)
            ((*var*)  fun x xIn => dlist_eq (term_tuple tls) tr)
            ((*val*)  fun v     => simplify_eq_val (term_tuple tls) v)
            ((*tuple*)fun trs   => formula_eqs_ctx tls trs)
            tr.

        Definition simplify_eq_record {R}
          (tls : NamedEnv (Term Σ) (recordf_ty R)) (tr : Term Σ (ty.record R)) :
          DList Σ :=
          Term_record_case (fun _ => DList Σ)
            (fun (*var*) _ _    => dlist_eq tr (term_record R tls))
            (fun (*val*) v      => simplify_eq_record_val simplify_eq_val R tls v)
            (fun (*record*) trs => formula_eqs_nctx tls trs)
            tr.

        Definition simplify_eq_union [U] [K1 : unionk U]
          (t1 : Term Σ (unionk_ty U K1)) (t2 : Term Σ (ty.union U)) : DList Σ :=
          Term_union_case (fun _ => DList Σ)
            ((*var*) fun x In    => dlist_eq t2 (term_union U K1 t1))
            ((*val*) fun v       => simplify_eq_val (term_union U K1 t1) v)
            ((*union*)
              fun K2 t3 =>
                match eq_dec K1 K2 with
                | left e  => simplify_eq t1
                               (eq_rect_r (fun K => Term Σ (unionk_ty U K)) t3 e)
                | right _ => error
                end)
            t2.

      End WithSimplifyEq.

      Fixpoint simplify_eq [σ] (tl : Term Σ σ) (tr : Term Σ σ) : DList Σ :=
        match tl in Term _ σ return Term Σ σ → DList Σ with
        | term_var _          => fun _ => simplify_eqb tl tr
        | term_val _ v        => fun tr => simplify_eq_val tr v
        | term_binop op t1 t2 => simplify_eq_binop simplify_eq op t1 t2
        | term_unop op t1     => simplify_eq_unop simplify_eq op t1
        | term_tuple tls      => simplify_eq_tuple simplify_eq tls
        | term_union U K tl   => simplify_eq_union simplify_eq tl
        | term_record R tls   => simplify_eq_record simplify_eq tls
        end tr.

    End SimplifyEq.

    Section SimplifyEqSpec.

      Context [w : World].

      Lemma simplify_eq_binop_default_val_spec [σ σ1 σ2] (op : BinOp σ1 σ2 σ)
        (t1 : Term w σ1) (t2 : Term w σ2) (v : Val σ) :
          instpred (simplify_eq_binop_default_val op t1 t2 v) ⊣⊢
          repₚ v (term_binop op t1 t2).
      Proof. unfold simplify_eq_binop_default_val; arw. Qed.

      Lemma simplify_eq_unop_default_val_spec [σ1 σ2] (op : UnOp σ1 σ2)
        (t : Term w σ1) (v : Val σ2) :
        instpred (simplify_eq_unop_default_val op t v) ⊣⊢
        repₚ v (term_unop op t).
      Proof. unfold simplify_eq_unop_default_val; arw. Qed.

      #[local] Hint Resolve simplify_eq_binop_default_val_spec
        simplify_eq_unop_default_val_spec : core.

      Lemma simplify_eq_val_spec [σ] (t : STerm σ w) (v : Val σ) :
        instpred (simplify_eq_val t v) ⊣⊢ repₚ v t.
      Proof.
        induction t; cbn [simplify_eq_val]; auto.
        - arw.
        - destruct eq_dec; arw.
        - destruct op; cbn; auto.
          + (*and*) destruct v; cbn; arw; arw_slow.
          + (*or*) destruct v; cbn; arw; arw_slow.
          + (*pair*) destruct v; cbn; arw. now rewrite IHt1 IHt2.
          + (*cons*) destruct v; cbn; arw. now rewrite IHt1 IHt2; arw.
          + (*bvapp*) unfold simplify_eq_binop_bvapp_val.
            destruct bv.appView; arw. now rewrite IHt1 IHt2.
          + (*bvcons*) unfold simplify_eq_binop_bvcons_val.
            destruct bv.view; arw. now rewrite IHt1 IHt2.
          + (*relop*) destruct v; cbn; arw.
        - destruct op; cbn; auto.
          + (*inl*) destruct v; cbn; arw; arw_slow.
          + (*inr*) destruct v; cbn; arw; arw_slow.
          + (*neg*) unfold simplify_eq_unop_neg_val; arw.
          + (*not*) destruct v; cbn; arw.
          + (*signed*)
            rewrite /simplify_eq_unop_signed_val -andb_lazy_alt.
            destruct andb eqn:H; arw.
            * rewrite IHt. constructor. intros ι Hpc. cbn.
              rewrite bv.signed_eq_z. intuition; lia.
            * rewrite instpred_dlist_error.
              iSplit; [iIntros ([])|].
              iIntros "Hsimpl".
              iDestruct (repₚ_inversion_term_signed with "Hsimpl")
                as "(%bv & %Heq & Hrep)".
              pose proof (bv.signed_bounds bv). lia.
          + (*unsigned*)
            rewrite /simplify_eq_unop_unsigned_val -andb_lazy_alt.
            destruct andb eqn:H; arw.
            * rewrite IHt. constructor. intros ι Hpc. cbn.
              rewrite bv.unsigned_eq_z. intuition; lia.
            * rewrite instpred_dlist_error.
              iSplit; [iIntros ([])|].
              iIntros "Hsimpl".
              iDestruct (repₚ_inversion_term_unsigned with "Hsimpl")
                as "(%bv & %Heq & Hrep)".
              pose proof (bv.unsigned_bounds bv). lia.
        - induction IH.
          + now destruct v.
          + destruct v as [vs v]; arw.
            apply bi.sep_proper; eauto.
        - unfold simplify_eq_union_val.
          destruct unionv_unfold as [K2 v2] eqn:?.
          apply (f_equal (unionv_fold U)) in Heqs.
          rewrite unionv_fold_unfold in Heqs. subst.
          destruct eq_dec as [->|e]; arw.
          now rewrite (repₚ_unionv_neq e).
        - rewrite -(recordv_fold_unfold R v).
          rewrite repₚ_term_record.
          generalize (recordv_unfold R v); intros vs.
          unfold simplify_eq_record_val.
          rewrite recordv_unfold_fold.
          induction IH; destruct (env.view vs); arw.
          arw_slow. apply bi.sep_proper; auto.
      Qed.
      #[local] Opaque simplify_eq_val.
      #[local] Hint Resolve simplify_eq_val_spec : core.

      Lemma simplify_eq_binop_default_spec [σ1 σ2 σ] (op : BinOp σ1 σ2 σ)
        (t1 : Term w σ1) (t2 : Term w σ2) (t : Term w σ) :
        instpred (simplify_eq_binop_default op t1 t2 t) ⊣⊢
        eqₚ (term_binop op t1 t2) t.
      Proof. unfold simplify_eq_binop_default; arw. Qed.

      Lemma simplify_eq_unop_default_spec [σ1 σ] (op : UnOp σ1 σ)
        (t1 : Term w σ1) (t : Term w σ) :
        instpred (simplify_eq_unop_default op t1 t) ⊣⊢
        eqₚ (term_unop op t1) t.
      Proof. unfold simplify_eq_unop_default; arw. Qed.

      #[local] Hint Resolve simplify_eq_unop_default_spec
        simplify_eq_binop_default_spec : core.

      Lemma eqₚ_term_not_relop {σ} (op : RelOp σ) (t1 t2 : STerm σ w) tr :
        eqₚ (term_not (term_binop (bop.relop op) t1 t2)) tr ⊣⊢
        eqₚ (term_relop_neg op t1 t2) tr.
      Proof.
        unfold eqₚ. constructor. intros ι _.
        now rewrite term_negb_relop.
      Qed.

      Lemma simplify_eq_spec [σ] (tl tr : Term w σ) :
        instpred (simplify_eq tl tr) ⊣⊢ eqₚ tl tr.
      Proof.
        induction tl; cbn; arw.
        - destruct op; cbn; auto.
          + (*plus*)
            destruct tr using Term_int_case; cbn; arw;
              try (constructor; intros ι _; cbn; lia).
            * destruct (Term_eqb_spec tl1 tr1); subst.
              { rewrite IHtl2. constructor; intros ι _; cbn. lia. }
              destruct (Term_eqb_spec tl2 tr2); subst.
              { rewrite IHtl1. constructor; intros ι _; cbn. lia. }
              destruct (Term_eqb_spec tl1 tr2); subst.
              { rewrite IHtl2. constructor; intros ι _; cbn. lia. }
              destruct (Term_eqb_spec tl2 tr1); subst.
              { rewrite IHtl1. constructor; intros ι _; cbn. lia. }
              arw. constructor; intros ι _; cbn; lia.
            * destruct (Term_eqb_spec tl1 tr1); subst.
              { rewrite IHtl2. constructor; intros ι _; cbn. lia. }
              destruct (Term_eqb_spec tl2 tr1); subst.
              { rewrite IHtl1. constructor; intros ι _; cbn. lia. }
              arw. constructor; intros ι _; cbn; lia.
          + (*minus*) unfold simplify_eq_binop_minus. arw.
            constructor; intros ι _; cbn. lia.
          + (*times*) unfold simplify_eq_binop_times. arw.
            constructor; intros ι _; cbn. lia.
          + (*and*)
            destruct tr using Term_bool_case; cbn; arw.
            destruct (Term_eqb_spec tl1 tr1); cbn; subst; arw.
            destruct (Term_eqb_spec tl2 tr2); subst; arw.
          + (*or*)
            destruct tr using Term_bool_case; cbn; arw.
            destruct (Term_eqb_spec tl1 tr1); cbn; subst; arw.
            destruct (Term_eqb_spec tl2 tr2); subst; arw.
          + (*pair*) destruct tr using Term_prod_case; cbn; auto; arw.
            now rewrite IHtl1 IHtl2 -eqₚ_term_prod.
          + (*cons*) destruct tr using Term_list_case; cbn; auto; arw.
            rewrite IHtl1 IHtl2. arw_slow.
          + (*append*)
            destruct tr using Term_list_case; cbn; auto; arw.
            destruct (Term_eqb_spec tl1 tr1). subst; cbn; arw.
            { rewrite IHtl2. constructor; intros ι _; cbn.
              now rewrite app_inv_head_iff. }
            destruct (Term_eqb_spec tl2 tr2). subst; cbn; arw.
            { rewrite IHtl1. constructor; intros ι _; cbn.
              now rewrite app_inv_tail_iff. }
            arw.
          + (*bvapp*)
            assert (∀ mn (t : Term w (ty.bvec mn)) (e : m + n = mn),
                     instpred (simplify_eq_binop_bvapp' simplify_eq
                                 tl1 tl2 t e) ⊣⊢
                     eqₚ (term_binop bop.bvapp tl1 tl2)
                       (eq_rect_r (fun l => Term w (ty.bvec l)) t e)); eauto.
            intros mn t e. destruct mn, t using Term_bvec_case; subst; cbn; arw.
            destruct eq_dec; arw; subst.
            destruct transparent.nat_add_cancel_l, (uip eq_refl e); cbn.
            arw. rewrite IHtl1 IHtl2. arw_slow.
          + (*bvcons*)
            assert (∀ sm (t : Term w (ty.bvec sm)) (e : S m = sm),
                      instpred (simplify_eq_binop_bvcons' simplify_eq
                                  tl1 tl2 t e) ⊣⊢
                      eqₚ (term_binop bop.bvcons tl1 tl2)
                        (eq_rect_r (fun l => Term w (ty.bvec l)) t e)); eauto.
            intros sm t e. destruct sm, t using Term_bvec_case; subst; cbn; arw.
            rewrite IHtl1 IHtl2. dependent elimination e; arw; arw_slow.
          + (*relop*)
            clear IHtl1 IHtl2. revert r tl1 tl2.
            induction tr using Term_bool_ind; cbn; intros rop tl1 tl2; arw.
            rewrite eqₚ_term_not eqₚ_term_not_relop.
            destruct rop; cbn; auto.
        - destruct op; cbn; auto.
          + (*inl*) destruct tr using Term_sum_case; cbn; auto; arw; arw_slow.
          + (*inr*) destruct tr using Term_sum_case; cbn; auto; arw; arw_slow.
          + (*get_slice_int*)
            unfold simplify_eq_unop_get_slice_int.
            destruct (Term_eqb_spec (term_get_slice_int tl) tr); subst; arw.
          + (*signed*)
            destruct tr using Term_int_case; cbn; arw;
              try (constructor; intros ι _; cbn; lia).
            destruct eq_dec; subst; arw;
              try (constructor; intros ι _; cbn; lia).
            rewrite IHtl. arw.
            constructor; intros ι _; cbn.
            split. congruence. apply bv.signed_inj.
        - destruct tr using Term_tuple_case; cbn; arw.
          induction IH; cbn; destruct (env.view ts0); cbn; arw.
          rewrite eqₚ_term_tuple_snoc. now apply bi.sep_proper.
        - destruct tr using Term_union_case; cbn; arw.
          destruct eq_dec; subst; arw.
          + now rewrite eqₚ_unionv_fold.
          + now rewrite eqₚ_term_union_neq.
        - destruct tr using Term_record_case; cbn; arw; arw_slow.
          + rewrite -(recordv_fold_unfold R v).
            rewrite repₚ_term_record.
            generalize (recordv_unfold R v); intros vs.
            unfold simplify_eq_record_val.
            rewrite recordv_unfold_fold.
            induction IH; destruct (env.view vs); arw.
            arw_slow. apply bi.sep_proper; auto.
          + induction IH; destruct (env.view ts0); arw.
            arw_slow. apply bi.sep_proper; auto.
      Qed.

    End SimplifyEqSpec.
    #[global] Arguments simplify_eq {Σ σ} tl tr.
    #[export] Hint Rewrite simplify_eq_spec : uniflogic.

    Definition simplify_relopb {Σ σ} (op : RelOp σ)
      (t1 t2 : STerm σ Σ) : DList Σ :=
      match term_get_val t1 , term_get_val t2 with
      | Some v1 , Some v2 => if bop.eval_relop_val op v1 v2 then empty else error
      | _       , _       => singleton (formula_relop op t1 t2)
      end.

    Definition simplify_relopb_spec {w : World} {σ} (op : RelOp σ)
      (t1 t2 : STerm σ w) :
      instpred (simplify_relopb op t1 t2) ⊣⊢ instpred (formula_relop op t1 t2).
    Proof.
      unfold simplify_relopb.
      destruct (term_get_val_spec t1) as [v1|]; arw; try now rewrite formula_relop_term'. subst.
      destruct (term_get_val_spec t2) as [v2|]; arw; try now rewrite formula_relop_term'. subst.
      destruct (bop.eval_relop_val_spec op v1 v2); arw.
    Qed.
    #[local] Opaque simplify_relopb.
    #[export] Hint Rewrite @simplify_relopb_spec : uniflogic.

    Definition peval_formula_le' {Σ} (t : Term Σ ty.int) : Formula Σ :=
      let default := formula_le (term_val ty.int 0%Z) t in
      Term_int_case (fun _ => Formula Σ)
        (fun (*var*) l lIn => default)
        (fun (*val*) v => if (0 <=? v)%Z then formula_true else formula_false)
        (fun (*plus*) _ _ => default)
        (fun (*minus*) _ _ => default)
        (fun (*times*) _ _ => default)
        (fun (*land*) _ _ => default)
        (fun (*neg*) _ => default)
        (fun (*signed*) _ _ => default)
        (fun (*unsigned*) _ _ => formula_true)
        t.

    Definition peval_formula_le {Σ} (t1 t2 : Term Σ ty.int) : Formula Σ :=
      peval_formula_le' (peval (term_minus t2 t1)).

    Definition peval_formula_lt {Σ} (t1 t2 : Term Σ ty.int) : Formula Σ :=
      peval_formula_le (term_plus t1 (term_val ty.int 1%Z)) t2.

    Definition peval_formula_relop_neg {Σ σ} (op : RelOp σ) :
      Term Σ σ → Term Σ σ → Formula Σ :=
      match op in (RelOp t) return (Term Σ t → Term Σ t → Formula Σ) with
      | @bop.eq _ σ0 => formula_neq
      | @bop.neq _ σ0 => formula_eq
      | bop.le => flip peval_formula_lt
      | bop.lt => flip peval_formula_le
      | @bop.bvsle _ n => flip formula_bvslt
      | @bop.bvslt _ n => flip formula_bvsle
      | @bop.bvule _ n => flip formula_bvult
      | @bop.bvult _ n => flip formula_bvule
      end.

    Lemma peval_formula_le'_spec [w : World] (t : Term w ty.int) :
      instpred (peval_formula_le' t) ⊣⊢
      instpred (formula_le (term_val ty.int 0%Z) t).
    Proof.
      destruct t using Term_int_case; cbn; try reflexivity.
      - constructor; intros ι _; cbn.
        destruct (Z.leb_spec 0 i);
          intuition; try easy; lia.
      - constructor; intros ι _; cbn.
        intuition. apply bv.unsigned_bounds. constructor.
    Qed.

    Lemma peval_formula_le_spec [w : World] (t1 t2 : Term w ty.int) :
      instpred (peval_formula_le t1 t2) ⊣⊢ instpred (formula_le t1 t2).
    Proof.
      unfold peval_formula_le. rewrite peval_formula_le'_spec.
      constructor; intros ι _. cbn. rewrite peval_sound. cbn. lia.
    Qed.

    Lemma peval_formula_lt_spec [w : World] (t1 t2 : Term w ty.int) :
      instpred (peval_formula_lt t1 t2) ⊣⊢ instpred (formula_lt t1 t2).
    Proof.
      unfold peval_formula_lt. rewrite peval_formula_le_spec.
      constructor; intros ι _; cbn. lia.
    Qed.

    #[local] Hint Rewrite peval_formula_le_spec peval_formula_lt_spec : uniflogic.

    Lemma instpred_peval_formula_relop_neg [w : World] {σ} (op : RelOp σ)
      (t1 t2 : Term w σ) :
      instpred (peval_formula_relop_neg op t1 t2) ⊣⊢
      repₚ (T := STerm ty.bool) false (term_binop (bop.relop op) t1 t2).
    Proof.
      destruct op; cbn; arw;
        rewrite ?formula_relop_term' ?rep_binop_neq_eq ?rep_binop_lt_ge
          ?rep_binop_slt_sge ?rep_binop_slt_sge ?rep_binop_ult_uge; easy.
    Qed.

    Definition simplify_le {Σ} (t1 t2 : Term Σ ty.int) : DList Σ :=
      singleton (peval_formula_le t1 t2).

    Definition simplify_bvule {Σ n} (t1 t2 : Term Σ (ty.bvec n)) : DList Σ :=
      let default := fun _ : () => simplify_relopb bop.bvule (peval t1) (peval t2) in
      match term_get_val t1 with
      | Some v => if bv.eqb v bv.zero then empty else default ()
      | _ => default ()
      end.

    Definition simplify_bvult {Σ n} (t1 t2 : Term Σ (ty.bvec n)) : DList Σ :=
      let default := fun _ : () => simplify_relopb bop.bvult (peval t1) (peval t2) in
       match term_get_val t2 with
       | Some v => if bv.eqb v bv.zero then singleton formula_false else default ()
       | _ => default ()
       end.

    Lemma True_bientails [w : World] (P : Pred w) : (⊢ P) -> True ⊣⊢ P.
    Proof. intros [HP]. constructor. intros ι Hpc. now specialize (HP ι Hpc). Qed.

    Lemma False_bientails [w : World] (P : Pred w) : (⊢ ¬ P) -> False ⊣⊢ P.
    Proof. intros [HP]. constructor. intros ι Hpc. now specialize (HP ι Hpc I). Qed.

    Lemma simplify_bvule_spec [w : World] [n] (s t : Term w (ty.bvec n)) :
      instpred (simplify_bvule s t) ⊣⊢ instpred (formula_relop bop.bvule s t).
    Proof. unfold simplify_bvule. arw.
           destruct (term_get_val_spec s); arw.
           destruct (bv.eqb_spec a bv.zero); arw.
           - rewrite instpred_dlist_empty.
             apply True_bientails.
             constructor; intros; subst; cbn.
             now apply bv.zero_ule.
           - now rewrite ?peval_sound formula_relop_term'.
           - now rewrite ?peval_sound formula_relop_term'.
    Qed.

    Lemma simplify_bvult_spec [w : World] [n] (s t : Term w (ty.bvec n)) :
      instpred (simplify_bvult s t) ⊣⊢ instpred (formula_relop bop.bvult s t).
    Proof. unfold simplify_bvult.
           destruct (term_get_val_spec t); arw.
           destruct (bv.eqb_spec a bv.zero); arw.
           - apply False_bientails.
             constructor; intros; subst; cbn.
             now apply bv.ult_zero.
           - now rewrite ?peval_sound formula_relop_term'.
           - now rewrite ?peval_sound formula_relop_term'.
    Qed.

    #[export] Hint Resolve simplify_bvult_spec simplify_bvule_spec : core.

    Definition simplify_lt {Σ} (t1 t2 : Term Σ ty.int) : DList Σ :=
      singleton (peval_formula_lt t1 t2).

    Lemma simplify_le_spec [w : World] (s t : Term w ty.int) :
      instpred (simplify_le s t) ⊣⊢ instpred (formula_relop bop.le s t).
    Proof. unfold simplify_le. arw. now rewrite formula_relop_term'. Qed.

    Lemma simplify_lt_spec [w : World] (s t : Term w ty.int) :
      instpred (simplify_lt s t) ⊣⊢ instpred (formula_relop bop.lt s t).
    Proof. unfold simplify_lt. arw. now rewrite formula_relop_term'. Qed.

    #[export] Hint Resolve simplify_le_spec simplify_lt_spec : core.

    Definition smart_or {Σ} (F1 F2 : Formula Σ) : Formula Σ :=
      match F1 , F2 with
      | formula_false , _ => F2
      | _ , formula_false => F1
      | formula_true , _ => formula_true
      | _ , formula_true => formula_true
      | _ , _ => formula_or F1 F2
      end.

    Lemma smart_or_spec {w : World} (F1 F2 : Formula w) :
      instpred (smart_or F1 F2) ⊣⊢ instpred (formula_or F1 F2).
    Proof.
      destruct F1, F2; cbn;
        now rewrite ?bi.True_or ?bi.or_True ?bi.or_False ?bi.False_or.
    Qed.
    #[export] Hint Rewrite @smart_or_spec : uniflogic.

    (* Negation, pushed through ∧ and ∨; None for formulas without one. *)
    Fixpoint formula_negate {Σ} (F : Formula Σ) : option (Formula Σ) :=
      match F with
      | formula_user _ _       => None
      | formula_bool t         => Some (formula_bool (term_not t))
      | formula_prop _ _       => None
      | formula_relop op t1 t2 => Some (formula_relop_neg op t1 t2)
      | formula_true           => Some formula_false
      | formula_false          => Some formula_true
      | formula_and F1 F2      => F1' <- formula_negate F1 ;;
                                  F2' <- formula_negate F2 ;;
                                  Some (smart_or F1' F2')
      | formula_or F1 F2       => F1' <- formula_negate F1 ;;
                                  F2' <- formula_negate F2 ;;
                                  Some (formula_and F1' F2')
      end.

    (* Negation of a conjunction of formulas: the disjunction of their negations. *)
    Fixpoint pathcondition_negate {Σ} (C : PathCondition Σ) : option (Formula Σ) :=
      match C with
      | [ctx] => Some formula_false
      | C ▻ F => C' <- pathcondition_negate C ;;
                 F' <- formula_negate F ;;
                 Some (smart_or C' F')
      end.

    Lemma instprop_smart_or {Σ} (F1 F2 : Formula Σ) (ι : Valuation Σ) :
      instprop (smart_or F1 F2) ι <-> instprop F1 ι \/ instprop F2 ι.
    Proof. destruct F1, F2; cbn; intuition. Qed.

    (* Negatable formulas are decidable, so De Morgan holds constructively. *)
    Lemma formula_negate_spec {Σ} (F : Formula Σ) :
      option.wlp
        (fun F' => forall ι, (instprop F' ι <-> ~ instprop F ι) /\
                             (instprop F ι \/ instprop F' ι))
        (formula_negate F).
    Proof.
      induction F; cbn; rewrite ?option.wlp_some ?option.wlp_none; auto.
      1-4: intros ι; cbn.
      - destruct (inst t ι); cbn; intuition.
      - rewrite instprop_formula_relop_neg bop.eval_relop_equiv.
        destruct bop.eval_relop_val; intuition.
      - intuition.
      - intuition.
      - destruct IHF1 as [F1' HF1|]; cbn; [|constructor].
        destruct IHF2 as [F2' HF2|]; cbn; [|constructor].
        constructor; intros ι; specialize (HF1 ι); specialize (HF2 ι).
        rewrite instprop_smart_or; intuition.
      - destruct IHF1 as [F1' HF1|]; cbn; [|constructor].
        destruct IHF2 as [F2' HF2|]; cbn; [|constructor].
        constructor; intros ι; specialize (HF1 ι); specialize (HF2 ι).
        cbn; intuition.
    Qed.

    Lemma pathcondition_negate_spec {Σ} (C : PathCondition Σ) :
      option.wlp
        (fun F' => forall ι, (instprop F' ι <-> ~ instprop C ι) /\
                             (instprop C ι \/ instprop F' ι))
        (pathcondition_negate C).
    Proof.
      induction C as [|C IHC F]; cbn.
      - constructor; cbn; intuition.
      - destruct IHC as [C' HC|]; cbn; [|constructor].
        destruct (formula_negate_spec F) as [F' HF|]; cbn; [|constructor].
        constructor; intros ι; specialize (HC ι); specialize (HF ι).
        rewrite instprop_smart_or; cbn; intuition.
    Qed.

    Lemma instpred_pathcondition_negate {w : World} (C : PathCondition w) :
      option.wlp (fun F => instpred F ⊣⊢ ¬ instpred C) (pathcondition_negate C).
    Proof.
      destruct (pathcondition_negate_spec C) as [F HF|]; constructor.
      constructor; intros ι _; specialize (HF ι); pred_unfold.
      rewrite !instpred_prop; intuition.
    Qed.

    Lemma instpred_formula_neq {w : World} {σ} (t1 t2 : STerm σ w) :
      instpred (formula_neq t1 t2) ⊣⊢ ¬ instpred (formula_eq t1 t2).
    Proof. now constructor. Qed.

    (* Decide t1 ≠ t2 by negating what simplify_eq makes of t1 = t2. *)
    Definition simplify_neq {Σ σ} (t1 t2 : STerm σ Σ) : DList Σ :=
      match run (simplify_eq t1 t2) with
      | None => empty
      | Some [ctx] => error
      | Some C => match pathcondition_negate C with
                  | Some F => singleton F
                  | None => singleton (formula_neq t1 t2)
                  end
      end.

    Lemma simplify_neq_spec {w : World} {σ} (t1 t2 : STerm σ w) :
      instpred (simplify_neq t1 t2) ⊣⊢ instpred (formula_neq t1 t2).
    Proof.
      unfold simplify_neq. pose proof (simplify_eq_spec t1 t2) as Heq.
      rewrite <- instpred_run in Heq. rewrite instpred_formula_neq.
      change (instpred (formula_eq t1 t2)) with (eqₚ t1 t2). rewrite <- Heq.
      destruct run as [[|C F]|].
      2: destruct (instpred_pathcondition_negate (C ▻ F)) as [F' HF|].
      2: now rewrite instpred_dlist_singleton HF.
      2: now rewrite instpred_dlist_singleton instpred_formula_neq Heq.
      all: cbn; now rewrite ?bi.True_impl.
    Qed.
    #[local] Opaque simplify_neq.
    #[export] Hint Rewrite @simplify_neq_spec : uniflogic.

    Definition simplify_relop {Σ σ} (op : RelOp σ) :
      forall (t1 t2 : STerm σ Σ), DList Σ :=
      match op in RelOp σ return forall (t1 t2 : STerm σ Σ), DList Σ with
      | bop.eq => fun t1 t2 => simplify_eq (peval t1) (peval t2)
      | bop.neq => fun t1 t2 => simplify_neq (peval t1) (peval t2)
      | bop.le => simplify_le
      | bop.lt => simplify_lt
      | bop.bvule => simplify_bvule
      | bop.bvult => simplify_bvult
      | op     => fun t1 t2 => simplify_relopb op (peval t1) (peval t2)
      end.

    Lemma simplify_relop_spec {w : World} {σ} (op : RelOp σ) (t1 t2 : STerm σ w) :
      instpred (simplify_relop op t1 t2) ⊣⊢ instpred (formula_relop op t1 t2).
    Proof.
      unfold simplify_relop.
      destruct op; arw; rewrite ?formula_relop_term' ?peval_sound; arw; arw_slow.
      constructor; intros ι _; cbn. now rewrite ?peval_sound.
    Qed.
    #[export] Hint Rewrite @simplify_relop_spec : uniflogic.

    Definition smart_and {Σ} (F1 F2 : Formula Σ) : Formula Σ :=
      match F1 , F2 with
      | formula_true , _ => F2
      | _ , formula_true => F1
      | formula_false , _ => formula_false
      | _ , formula_false => formula_false
      | _ , _ => formula_and F1 F2
      end.

    Lemma smart_and_spec {w : World} (F1 F2 : Formula w) :
      instpred (smart_and F1 F2) ⊣⊢ instpred (formula_and F1 F2).
    Proof.
      destruct F1, F2; cbn;
        now rewrite ?bi.True_sep ?bi.sep_True ?bi.sep_False ?bi.False_sep.
    Qed.
    #[export] Hint Rewrite @smart_and_spec : uniflogic.

    Lemma smart_and_spec' {w : World} (F1 F2 : Formula w) :
      instpred_formula (smart_and F1 F2) ⊣⊢ instpred (formula_and F1 F2).
    Proof. apply smart_and_spec. Qed.
    #[export] Hint Rewrite @smart_and_spec' : uniflogic.

    Definition PathCondition_to_Formula [Σ] : PathCondition Σ -> Formula Σ :=
      ctx.Ctx_rect (fun _ => Formula Σ) formula_true (fun PC FPC F' => smart_and FPC F').

    Lemma PathCondition_to_Formula_sound [w : World] (P : PathCondition w) :
      instpred (PathCondition_to_Formula P) ⊣⊢ instpred P.
    Proof.
      induction P; first done; cbn; arw; cbn.
      unfold instpred_inst_formula, instpred in IHP; cbn in IHP.
      now rewrite IHP.
    Qed.
    #[export] Hint Rewrite @PathCondition_to_Formula_sound : uniflogic.

    Program Definition PathCondition_to_DList [Σ] (pc : PathCondition Σ) : DList Σ :=
      MkDList (fun k => Some (pc ▻▻ k)) _.
    Next Obligation. intros; cbn. now rewrite instprop_cat. Qed.

    Fixpoint simplify_formula {Σ} (fml : Formula Σ) : DList Σ :=
      match fml with
      | formula_user p ts      => singleton (formula_user p (pevals ts))
      | formula_bool t         => simplify_bool (peval t)
      | formula_prop ζ P       => singleton fml
      | formula_relop op t1 t2 => simplify_relop op t1 t2
      | formula_true           => empty
      | formula_false          => error
      | formula_and F1 F2      => cat (simplify_formula F1) (simplify_formula F2)
      | formula_or F1 F2       => match DList.run (simplify_formula F1) with
                                  | Some []%ctx => empty
                                  | None => simplify_formula F2
                                  | Some F1' => match DList.run (simplify_formula F2) with
                                                | Some []%ctx => empty
                                                | None => PathCondition_to_DList F1'
                                                | Some F2' => singleton (formula_or (PathCondition_to_Formula F1') (PathCondition_to_Formula F2'))
                                         end
                                  end
      end.

    Lemma PathCondition_to_Formula_sound' [w : World] (P : PathCondition w) :
      instpred_formula (PathCondition_to_Formula P) ⊣⊢ instpred P.
    Proof. now apply PathCondition_to_Formula_sound. Qed.
    #[export] Hint Rewrite @PathCondition_to_Formula_sound' : uniflogic.

    Lemma PathCondition_to_DList_sound [w : World] (P : PathCondition w) :
      instpred (PathCondition_to_DList P) ⊣⊢ instpred P.
    Proof. reflexivity. Qed.
    #[export] Hint Rewrite @PathCondition_to_DList_sound : uniflogic.

    Fixpoint simplify_pathcondition {Σ} (C : PathCondition Σ) : DList Σ :=
      match C with
      | [ctx] => empty
      | C ▻ F => cat (simplify_pathcondition C) (simplify_formula F)
      end.

    Lemma simplify_formula_spec {w : World} (F : Formula w) :
      instpred (simplify_formula F) ⊣⊢ instpred F.
    Proof.
      induction F; arw; cbn; rewrite ?pevals_sound ?peval_sound ?formula_relop_term'; arw.
      - now rewrite IHF1 IHF2.
      - pose proof (instpred_run (simplify_formula F1)) as HrF1.
        pose proof (instpred_run (simplify_formula F2)) as HrF2.
        destruct run as [PC|].
        + destruct PC as [|PCrest1 F11]; cbn in *.
          { iSplit; iIntros "_"; [|now cbn].
            now iLeft; iApply IHF1; iApply HrF1. }
          destruct run as [PC|].
          destruct PC as [|PCrest2 F22]; cbn in *.
          { iSplit; iIntros "_"; [|now cbn].
            now iRight; iApply IHF2; iApply HrF2. }
          rewrite instpred_dlist_singleton.
          { change (instpred_formula ?F) with (instpred F).
            rewrite -IHF2 -HrF2.
            rewrite -IHF1 -HrF1.
            now arw.
          }
          change (instpred_formula ?F) with (instpred F).
          rewrite -IHF2 -HrF2 bi.or_False.
          now rewrite -IHF1 -HrF1.
        + change (instpred_formula F1) with (instpred F1).
          rewrite -IHF1 -HrF1; cbn.
          now rewrite bi.False_or.
    Qed.
    #[export] Hint Rewrite @simplify_formula_spec : uniflogic.

    Lemma simplify_pathcondition_spec {w : World} (C : PathCondition w) :
      instpred (w := w) (run (simplify_pathcondition C)) ⊣⊢ instpred C.
    Proof.
      change (instpred (simplify_pathcondition C) ⊣⊢ instpred C).
      induction C as [|C IHC F]; arw.
      now rewrite IHC.
    Qed.
    #[export] Hint Rewrite @simplify_pathcondition_spec : uniflogic.

    Definition occurs_check_lt {Σ x} (xIn : (x ∈ Σ)%katamaran) {σ} (t : Term Σ σ) : option (Term (Σ - x) σ) :=
      match t with
      | term_var_in yIn =>
        if Nat.ltb (ctx.in_at xIn) (ctx.in_at yIn) then occurs_check xIn t else None
      | _ => occurs_check xIn t
      end.

    Lemma occurs_check_lt_sound {Σ x} (xIn : (x ∈ Σ)%katamaran) {σ} (t : Term Σ σ) (t' : Term (Σ - x) σ) :
      occurs_check_lt xIn t = Some t' -> t = subst t' (sub_shift xIn).
    Proof.
      unfold occurs_check_lt. intros Hwlp.
      pose proof (occurs_check_sound xIn t) as H.
      unfold OccursCheckSoundPoint in H.
      rewrite option.wlp_forall in H. apply H. clear H.
      destruct t; auto. destruct (Nat.ltb _ _); auto.
      discriminate.
    Qed.

    Equations(noeqns) try_unify_bool {w : World} (t : Term w ty.bool) :
      option { w' & Tri w w' } :=
      try_unify_bool (@term_var _ x σ xIn) :=
        Some (existT _ (tri_cons x (term_val ty.bool true) tri_id));
      try_unify_bool (term_unop uop.not (@term_var _ x σ xIn)) :=
        Some (existT _ (tri_cons x (term_val ty.bool false) tri_id));
      try_unify_bool _ :=
        None.

    Definition try_unify_eq {w : World} {σ} (t1 t2 : Term w σ) :
      option { w' & Tri w w' } :=
      match t1 with
      | @term_var _ ς σ ςInΣ =>
        fun t2 : Term w σ =>
          match occurs_check_lt ςInΣ t2 with
          | Some t => Some (existT _ (tri_cons ς t tri_id))
          | None => None
          end
      | _ => fun _ => None
      end t2.

    Definition try_unify_formula {w : World} (fml : Formula w) :
      option { w' & Tri w w' } :=
      match fml with
      | formula_bool t => try_unify_bool t
      | formula_relop bop.eq t1 t2 =>
        match try_unify_eq t1 t2 with
        | Some r => Some r
        | None => try_unify_eq t2 t1
        end
      | _ => None
      end.

    Lemma try_unify_bool_spec {w : World} (t : Term w ty.bool) :
      option.wlp
        (fun '(existT w' ν) => repₚ (T := STerm ty.bool) true t ⊣⊢ inst_triangular ν)
        (try_unify_bool t).
    Proof.
      induction t using Term_bool_ind; cbn; try constructor; auto.
      - rewrite inst_triangular_knowing.
        rewrite (knowing_trans (w2 := wsubst _ _ _)).
        rewrite knowing_id knowing_acc_subst_right.
        now crushPredEntails3.
      - induction t using Term_bool_ind; cbn; try constructor.
        rewrite inst_triangular_knowing (knowing_trans (ω23 := acc_refl)) knowing_id knowing_acc_subst_right.
        unfold assuming; crushPredEntails3; cbn;
          now apply negb_true_iff.
    Qed.

    Lemma try_unify_eq_spec {w : World} {σ} (t1 t2 : Term w σ) :
      option.wlp
        (fun '(existT w' ν) => eqₚ t1 t2 ⊣⊢ inst_triangular ν)
        (try_unify_eq t1 t2).
    Proof.
      unfold try_unify_eq. destruct t1; cbn; try (constructor; auto; fail).
      destruct occurs_check_lt eqn:Heq; constructor; auto.
      apply occurs_check_lt_sound in Heq.
      rewrite inst_triangular_knowing (knowing_trans (ω23 := acc_refl)) knowing_id knowing_acc_subst_right assuming_True bi.sep_True.
      now subst.
    Qed.

    Lemma try_unify_formula_spec {w : World} (fml : Formula w) :
      option.wlp
        (fun '(existT w' ν) => instpred fml ⊣⊢ inst_triangular ν) (try_unify_formula fml).
    Proof.
      unfold try_unify_formula; destruct fml; cbn; try (constructor; auto; fail).
      - apply try_unify_bool_spec.
      - destruct rop; try constructor; cbn.
        destruct (try_unify_eq_spec t1 t2) as [[w' ν] HYP|]. constructor. auto.
        destruct (try_unify_eq_spec t2 t1) as [[w' ν] HYP|]; constructor.
        rewrite <-HYP.
        now unfold eqₚ.
    Qed.

    Definition unify_formula {w0 : World} (F : Formula w0) :
      { w1 & Tri w0 w1 * PathCondition w1 }%type :=
      match try_unify_formula F with
      | Some (existT w1 ν01) => existT w1 (ν01 , ctx.nil)
      | None => existT w0 (tri_id , ctx.nil ▻ F)
      end.

    Lemma unify_formula_spec {w0 : World} (fml : Formula w0) :
      match unify_formula fml with
      | existT w1 (ν01 , fmls) =>
         (instpred fml) ⊣⊢ knowing (acc_triangular ν01) (instpred fmls)
      end.
    Proof.
      unfold unify_formula.
      destruct (try_unify_formula_spec fml).
      - destruct a as [w1 ν01].
        now rewrite H inst_triangular_knowing.
      - now rewrite knowing_id instpred_singleton.
    Qed.

    Fixpoint unify_pathcondition {w0 : World} (C : PathCondition w0) :
      { w1 & Tri w0 w1 * PathCondition w1 }%type.
    Proof.
      destruct C as [|C F].
      - exists w0. split. apply tri_id. apply ctx.nil.
      - destruct (unify_pathcondition w0 C) as (w1 & ν01 & C1).
        clear unify_pathcondition C.
        destruct (unify_formula (persist F (acc_triangular ν01))) as (w2 & ν12 & C2).
        exists w2. split. apply (tri_comp ν01 ν12).
        refine (persist C1 (acc_triangular ν12) ▻▻ C2).
    Defined.

    Lemma instprop_cat_pred `{H : InstProp A} (w : World) (C1 C2 : Ctx (A w)) :
      instprop (C1 ▻▻ C2) ⊣⊢ (instprop C1 : Pred w) ∗ instprop C2.
    Proof.
      constructor. intros. now rewrite instprop_cat.
    Qed.

    Lemma knowing_tri_comp {w0 w1 w2} {ν01 : Tri w0 w1} {ν12 : Tri w1 w2} {P} :
      knowing (acc_triangular (tri_comp ν01 ν12)) P ⊣⊢ knowing (acc_trans (acc_triangular ν01) (acc_triangular ν12)) P.
    Proof.
      apply knowing_resp_sub_acc.
      now rewrite sub_acc_trans !sub_acc_triangular sub_triangular_comp.
    Qed.


    Lemma unify_pathcondition_spec {w0 : World} (C0 : PathCondition w0) :
      match unify_pathcondition C0 with
      | existT w1 (ν01 , C1) =>
          instpred C0 ⊣⊢ knowing (acc_triangular ν01) (instpred C1)
      end.
    Proof.
      induction C0 as [|C0 IHC F0]; cbn.
      - now rewrite knowing_id.
      - destruct unify_pathcondition as (w1 & ν01 & C1).
        pose proof (unify_formula_spec (persist F0 (acc_triangular ν01))) as IHF.
        destruct (unify_formula (persist F0 (acc_triangular ν01))) as (w2 & ν12 & C2).
        change (instpred_ctx C0) with (instpred C0).
        rewrite IHC.
        rewrite knowing_tri_comp.
        rewrite instpred_cat.
        rewrite knowing_trans.
        rewrite knowing_absorb_forgetting.
        rewrite instpred_persist in IHF.
        rewrite IHF.
        rewrite instpred_persist.
        apply knowing_proper_bientails.
        rewrite (bi.sep_comm _ (instpred C2)).
        rewrite <-knowing_absorb_forgetting.
        now rewrite bi.sep_comm.
    Qed.

    Open Scope lazy_bool_scope.
    Equations(noind) formula_eqb {Σ} (f1 f2 : Formula Σ) : bool :=
      formula_eqb (formula_bool t1) (formula_bool t2) := Term_eqb t1 t2;
      formula_eqb (@formula_relop _ σ op1 t11 t12) (@formula_relop _ τ op2 t21 t22) with eq_dec σ τ => {
        formula_eqb (@formula_relop _ σ op1 t11 t12) (@formula_relop _ ?(σ) op2 t21 t22) (left eq_refl) :=
          (if eq_dec op1 op2 then true else false) &&& Term_eqb t11 t21 &&& Term_eqb t12 t22;
        formula_eqb (@formula_relop _ σ op1 t11 t12) (@formula_relop _ τ op2 t21 t22) (right _) := false
      };
      formula_eqb (@formula_user _ p ts1) (@formula_user _ q ts2) with 𝑷_eq_dec p q => {
        formula_eqb (@formula_user _ p ts1) (@formula_user _ ?(p) ts2) (left eq_refl) :=
          env.eqb_hom (@Term_eqb _) ts1 ts2;
        formula_eqb (@formula_user _ p ts1) (@formula_user _ q ts2) (right _) := false
      };
      formula_eqb formula_true formula_true := true;
      formula_eqb formula_false formula_false := true;
      formula_eqb (formula_or f1 f2) (formula_or f3 f4) :=
        formula_eqb f1 f3 &&& formula_eqb f2 f4;
      formula_eqb (formula_and f1 f2) (formula_and f3 f4) :=
        formula_eqb f1 f3 &&& formula_eqb f2 f4;
      formula_eqb _ _ := false.

    Lemma formula_eqb_spec {Σ} (f1 f2 : Formula Σ) :
      BoolSpec (f1 = f2) True (formula_eqb f1 f2).
    Proof.
      revert f2. induction f1; intros f2;
        dependent elimination f2; simp formula_eqb;
        repeat
          match goal with
          | |- BoolSpec _ _ false   => constructor; auto
          | |- BoolSpec _ _ true   => try (constructor; congruence; fail)
          | |- context[eq_dec _ _ ] => destruct eq_dec; subst; cbn
          | |- context[Term_eqb ?t1 ?t2] =>
              destruct (Term_eqb_spec t1 t2); cbn;
              try (constructor; congruence; fail)
          | IH: forall f2 : Formula _, BoolSpec _ _ (formula_eqb ?f f2)
            |- context[formula_eqb ?f ?f2] =>
              specialize (IH f2); destruct IH
          end.
      - destruct 𝑷_eq_dec.
        + destruct e; cbn.
          destruct (env.eqb_hom_spec (@Term_eqb Σ) (@Term_eqb_spec Σ) ts ts0);
            constructor; [congruence|easy].
        + now constructor.
    Qed.

    Fixpoint formula_simplifies {Σ} (hyp : Formula Σ) (fact : Formula Σ) : option (Formula Σ) :=
      if formula_eqb hyp fact then Some formula_true else
      match hyp with
        formula_and hyp1 hyp2 => match formula_simplifies hyp1 fact , formula_simplifies hyp2 fact with
                                 | Some hyp1' , Some hyp2' => Some (smart_and hyp1' hyp2')
                                 | Some hyp1' , None => Some (smart_and hyp1' hyp2)
                                 | None , Some hyp2' => Some (smart_and hyp1 hyp2')
                                 | None , None => None
                                 end
      | formula_or hyp1 hyp2 => match formula_simplifies hyp1 fact , formula_simplifies hyp2 fact with
                                | Some hyp1' , Some hyp2' => Some (smart_or hyp1' hyp2')
                                | Some hyp1' , None => Some (smart_or hyp1' hyp2)
                                | None , Some hyp2' => Some (smart_or hyp1 hyp2')
                                | None , None => None
                                end
      | formula_relop op t1 t2 =>
          let hyp' := peval_formula_relop_neg op t1 t2 in
          if formula_eqb hyp' fact then Some formula_false else None
      | _ => None
      end.

    Lemma bi_wand_iff_true {w} {P : Pred w} : P ⊢ P ∗-∗ True.
    Proof. iIntros "HP"; iSplit; now iIntros. Qed.

    Lemma bi_wand_iff_sep {w} {P1 P2 Q1 Q2 : Pred w} : (P1 ∗-∗ Q1) ∗ (P2 ∗-∗ Q2) ⊢ P1 ∗ P2 ∗-∗ Q1 ∗ Q2.
    Proof.
      iIntros "[H1 H2]". iSplit.
      - iIntros "[HP1 HP2]". now iSplitL "H1 HP1"; [iApply "H1"|iApply "H2"].
      - iIntros "[HQ1 HQ2]". now iSplitL "H1 HQ1"; [iApply "H1"|iApply "H2"].
    Qed.

    Lemma bi_wand_iff_sep_l {w} {P Q R : Pred w} : P ∗-∗ Q ⊢ R ∗ P ∗-∗ R ∗ Q.
    Proof.
      iIntros "HPQ". iApply (bi_wand_iff_sep with "[HPQ]"). iFrame.
      now iApply bi.wand_iff_refl.
    Qed.

    #[local] Hint Rewrite @formula_relop_term' : uniflogic.

    Lemma bi_wand_iff_or {w} {P1 P2 Q1 Q2 : Pred w} : (P1 ∗-∗ Q1) ∗ (P2 ∗-∗ Q2) ⊢ P1 ∨ P2 ∗-∗ Q1 ∨ Q2.
    Proof.
      iIntros "[H1 H2]"; iSplit.
      - iIntros "[HP1|HP2]"; [iLeft|iRight]; [now iApply "H1"|now iApply "H2"].
      - iIntros "[HQ1|HQ2]"; [iLeft|iRight]; [now iApply "H1"|now iApply "H2"].
    Qed.

    #[local] Hint Rewrite instpred_peval_formula_relop_neg : uniflogic.

    Lemma formula_simplifies_spec {w : World} (hyp fact : Formula w) :
      option.wlp (fun hyp' => ⊢ instpred fact -∗ (instpred hyp ∗-∗ instpred hyp'))
        (formula_simplifies hyp fact).
    Proof.
      induction hyp; cbn;
        repeat match goal with
          | |- context[ formula_eqb ?F1 ?F2] => destruct (formula_eqb_spec F1 F2); subst
          | H : option.wlp _ (formula_simplifies ?hyp ?F)|- context[ formula_simplifies ?hyp ?F ] => destruct H
        end; try (now eapply option.wlp_none); try eapply option.wlp_some; cbn;
        try (now iApply bi_wand_iff_true);
        arw; cbn; iIntros "#Hfact";
        (iApply bi_wand_iff_or || iApply bi_wand_iff_sep); iSplit;
        try now (iApply H || iApply H0 || iApply H1 || iApply bi.wand_iff_refl).
      - iIntros "#Hfact'".
        iDestruct (repₚ_antisym_left with "Hfact Hfact'") as "%Heq".
        discriminate.
      - iIntros ([]).
    Qed.

    Fixpoint assumption_formula {Σ} (C : PathCondition Σ) (F : Formula Σ) (k : PathCondition Σ) {struct C} : PathCondition Σ :=
      match C with
      | [ctx]  => k ▻ F
      | C ▻ F' => match formula_simplifies F F' with
                  | Some F2 => assumption_formula C F2 k
                  | None => assumption_formula C F k
                  end
      end.

    Fixpoint assumption_pathcondition {Σ} (C : PathCondition Σ) (Fs : PathCondition Σ) (k : PathCondition Σ) {struct Fs} : PathCondition Σ :=
      match Fs with
      | [ctx]  => k
      | Fs ▻ F => assumption_formula C F (assumption_pathcondition C Fs k)
      end.

    Lemma assumption_formula_spec {w : World} (C : PathCondition w) (F : Formula w) (k : PathCondition w) :
      ⊢ instpred C -∗ instpred k ∗ instpred F ∗-∗ instpred (assumption_formula C F k).
    Proof.
      revert F; induction C as [|C ? F']; intros F; cbn; auto.
      iIntros "[#HC #HF']".
      destruct (formula_simplifies_spec F F');
        subst; [|now iApply IHC].
      iPoseProof (IHC a with "HC") as "HC'".
      iPoseProof (H with "HF'") as "HF".
      iApply (bi.wand_iff_trans).
      iFrame "HC'".
      now iApply (bi_wand_iff_sep_l with "HF").
    Qed.

    Lemma assumption_pathcondition_spec {w : World} (C : PathCondition w) (FS : PathCondition w) (k : PathCondition w) :
      instpred C -∗ ((instpred (w := w) k ∗ instpred FS ∗-∗ instpred (assumption_pathcondition C FS k))).
    Proof.
      induction FS as [|FS ? F]; cbn; iIntros "#HC".
      - rewrite bi.sep_emp.
        now iApply bi.wand_iff_refl.
      - iPoseProof (assumption_formula_spec C F (assumption_pathcondition C FS k) with "HC") as "HCF".
        iPoseProof (IHFS with "HC") as "HCFS".
        iApply (bi.wand_iff_trans with "[HCFS HCF]").
        iSplitR "HCF"; last iExact "HCF".
        iSplit.
        + iIntros "(Hk & HFS & HF)"; iFrame.
          iApply "HCFS".
          now iFrame.
        + iIntros "(HFS & HF)".
          iDestruct "HCFS" as "[_ HCFS2]".
          iDestruct ("HCFS2" with "HFS") as "(Hk & HFS)".
          now iFrame.
    Qed.

    (* Linear bounds: int (in)equalities and unsigned bitvector comparisons
       become bounds on a linear form; a new formula is dropped if the
       bounds of the path condition on the same form entail it. *)
    Section LinearBounds.
      Context {Σ : LCtx}.

      (* Σ c·t, without repeated atoms or zero coefficients. *)
      Definition Lin : Type := list (Term Σ ty.int * Z).

      Definition lin_eval (ι : Valuation Σ) : Lin -> Z :=
        fold_right (fun '(t, c) acc => c * inst (T := STerm ty.int) t ι + acc)%Z 0%Z.

      Fixpoint lin_add_mono (t : Term Σ ty.int) (c : Z) (l : Lin) : Lin :=
        match l with
        | nil => if Z.eqb c 0 then nil else cons (t, c) nil
        | cons (t', c') l' =>
            if Term_eqb t t'
            then let c'' := (c + c')%Z in
                 if Z.eqb c'' 0 then l' else cons (t', c'') l'
            else cons (t', c') (lin_add_mono t c l')
        end.

      Definition lin_add (l1 l2 : Lin) : Lin :=
        fold_right (fun '(t, c) acc => lin_add_mono t c acc) l2 l1.

      Definition lin_neg : Lin -> Lin :=
        map (fun '(t, c) => (t, Z.opp c)).

      Definition lin_eqb (l1 l2 : Lin) : bool :=
        Nat.eqb (length l1) (length l2) &&
        match lin_add l1 (lin_neg l2) with nil => true | _ => false end.

      (* A linear form with a constant: Σ c·t + k. *)
      Definition LinK : Type := Lin * Z.

      Definition lin_atom (t : Term Σ ty.int) (s : Z) (lk : LinK) : LinK :=
        let '(l, k) := lk in (lin_add_mono t s l, k).

      Definition lin_const (i : Z) (s : Z) (lk : LinK) : LinK :=
        let '(l, k) := lk in (l, k + s * i)%Z.

      (* The value of a linear form lies in [lo, hi], or differs from a. *)
      Inductive Range : Type :=
      | range_in (lo hi : option Z)
      | range_out (a : Z).

      Definition Cstr : Type := Lin * Range.

      Definition lin_gcd (l : Lin) : Z :=
        fold_right (fun '(_, c) g => Z.gcd c g) 0%Z l.

      (* Divide by the gcd g of the coefficients, rounding the bounds inward. *)
      Definition cstr_normalize (c : Cstr) : Cstr :=
        let '(l, r) := c in
        let g := lin_gcd l in
        if (g <=? 1)%Z then c else
          (map (fun '(t, c) => (t, c / g)%Z) l,
            match r with
            | range_in lo hi =>
                range_in (option_map (fun a => Z.opp (Z.opp a / g)) lo)
                  (option_map (fun b => b / g) hi)
            | range_out a =>
                if (a mod g =? 0)%Z then range_out (a / g) else range_in None None
            end)%Z.

      (* 0 ⋈ l + k *)
      Definition cstr_ge (lk : LinK) : Cstr :=
        let '(l, k) := lk in (l, range_in (Some (Z.opp k)) None).
      Definition cstr_eq (lk : LinK) : Cstr :=
        let '(l, k) := lk in (l, range_in (Some (Z.opp k)) (Some (Z.opp k))).
      Definition cstr_ne (lk : LinK) : Cstr :=
        let '(l, k) := lk in (l, range_out (Z.opp k)).

      (* The negation, if it is a single constraint. *)
      Definition cstr_negate (c : Cstr) : option Cstr :=
        let '(l, r) := c in
        match r with
        | range_in (Some a) None => Some (l, range_in None (Some (Z.pred a)))
        | range_in None (Some b) => Some (l, range_in (Some (Z.succ b)) None)
        | range_in (Some a) (Some b) => if (a =? b)%Z then Some (l, range_out a) else None
        | range_in None None => None
        | range_out a => Some (l, range_in (Some a) (Some a))
        end.

      Definition Interval : Type := option Z * option Z.

      Definition lo_max (a b : option Z) : option Z :=
        match a, b with
        | Some x, Some y => Some (Z.max x y)
        | Some x, None => Some x
        | None, b => b
        end.
      Definition hi_min (a b : option Z) : option Z :=
        match a, b with
        | Some x, Some y => Some (Z.min x y)
        | Some x, None => Some x
        | None, b => b
        end.

      (* Bounds every valuation satisfies: unsigned values are nonnegative.
         No upper bound: the width may be symbolic. *)
      Definition term_is_unsigned (t : Term Σ ty.int) : bool :=
        Term_int_case (fun _ => bool)
          (fun _ _ => false) (fun _ => false) (fun _ _ => false) (fun _ _ => false)
          (fun _ _ => false) (fun _ _ => false) (fun _ => false) (fun _ _ => false)
          (fun _ _ => true) t.

      Definition lin_default (l : Lin) : Interval :=
        match l with
        | nil => (Some 0%Z, Some 0%Z)
        | cons (t, c) nil =>
            if term_is_unsigned t
            then if (c =? 1)%Z then (Some 0%Z, None)
                 else if (c =? -1)%Z then (None, Some 0%Z)
                 else (None, None)
            else (None, None)
        | _ => (None, None)
        end.

      (* Narrow i by the hypotheses on l (or on -l). *)
      Definition lin_interval (hyps : list Cstr) (l : Lin) : Interval :=
        fold_right
          (fun '(l', r) '(lo, hi) =>
             match r with
             | range_in lo' hi' =>
                 if lin_eqb l l' then (lo_max lo lo', hi_min hi hi')
                 else if lin_eqb l (lin_neg l') then
                        (lo_max lo (option_map Z.opp hi'), hi_min hi (option_map Z.opp lo'))
                 else (lo, hi)
             | range_out _ => (lo, hi)
             end)
          (lin_default l) hyps.

      Inductive Verdict : Type := entailed | contradicted | unknown.

      Definition le_opt (a b : option Z) : bool :=
        match a, b with
        | Some x, Some y => (x <=? y)%Z
        | _, _ => false
        end.

      Definition decide_range (i : Interval) (r : Range) : Verdict :=
        let '(lo, hi) := i in
        if le_opt (option_map Z.succ hi) lo then contradicted else
        match r with
        | range_in flo fhi =>
            if (match flo with None => true | Some _ => le_opt flo lo end) &&
               (match fhi with None => true | Some _ => le_opt hi fhi end)
            then entailed
            else if le_opt (option_map Z.succ fhi) lo || le_opt (option_map Z.succ hi) flo ||
                    le_opt (option_map Z.succ fhi) flo
            then contradicted
            else unknown
        | range_out a =>
            if le_opt (Some (Z.succ a)) lo || le_opt (option_map Z.succ hi) (Some a)
            then entailed
            else if le_opt (Some a) lo && le_opt hi (Some a) then contradicted
            else unknown
        end.

      Definition decide_cstr (hyps : list Cstr) (c : Cstr) : Verdict :=
        decide_range (lin_interval hyps (fst c)) (snd c).

      Section WithHyps.
        Variable hyps : list Cstr.

        (* t = x + c for a literal c. *)
        Definition bvadd_const {n} (t : Term Σ (ty.bvec n)) : option (Term Σ (ty.bvec n) * Z) :=
          Term_bvec_case (fun n _ => option (Term Σ (ty.bvec n) * Z))
            (fun _ _ _ => None) (fun _ _ => None)
            (fun n t1 t2 =>
               match term_get_val t2 with
               | Some c => Some (t1, bv.unsigned c)
               | None => match term_get_val t1 with
                         | Some c => Some (t2, bv.unsigned c)
                         | None => None
                         end
               end)
            (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None)
            (fun _ _ _ => None) (fun _ _ _ _ => None) (fun _ _ _ _ => None)
            (fun _ _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ _ _ _ => None)
            (fun _ _ => None) (fun _ _ => None) (fun _ _ _ _ => None) (fun _ _ _ _ => None)
            (fun _ _ => None) (fun _ _ _ _ => None) (fun _ _ _ _ _ => None)
            (fun _ _ _ => None) (fun _ _ _ => None) t.

        (* unsigned (x + c) is unsigned x + c, or that minus 2^n, if the
           bounds on unsigned x show which. *)
        Definition lin_unsigned {n} (t : Term Σ (ty.bvec n)) (s : Z) (lk : LinK) : LinK :=
          match term_get_val t with
          | Some v => lin_const (bv.unsigned v) s lk
          | None =>
              let default := lin_atom (term_unsigned t) s lk in
              match bvadd_const t with
              | Some (x, c) =>
                  let ux := term_unsigned x in
                  let '(lo, hi) := lin_interval hyps (cons (ux, 1%Z) nil) in
                  let m := (2 ^ Z.of_nat n)%Z in
                  if le_opt (option_map (fun h => h + c + 1)%Z hi) (Some m)
                  then lin_atom ux s (lin_const c s lk)
                  else match lo with
                       | Some l => if (0 <? l)%Z && (m <=? l + c)%Z
                                   then lin_atom ux s (lin_const (c - m) s lk)
                                   else default
                       | None => default
                       end
              | None => default
              end
          end.

        (* lin_term t s lk denotes s·t + lk. *)
        Definition lin_term : Term Σ ty.int -> Z -> LinK -> LinK :=
          Term_int_rect (fun _ => Z -> LinK -> LinK)
            (fun x xIn => lin_atom (term_var_in xIn))
            (fun i => lin_const i)
            (fun t1 t2 r1 r2 s lk => r1 s (r2 s lk))
            (fun t1 t2 r1 r2 s lk => r1 s (r2 (Z.opp s) lk))
            (fun t1 t2 r1 r2 s lk =>
               match term_get_val t1, term_get_val t2 with
               | Some c, _ => r2 (s * c)%Z lk
               | _, Some c => r1 (s * c)%Z lk
               | None, None => lin_atom (term_times t1 t2) s lk
               end)
            (fun t1 t2 _ _ => lin_atom (term_binop bop.land t1 t2))
            (fun t r s => r (Z.opp s))
            (fun n t => lin_atom (term_unop uop.signed t))
            (fun n t => lin_unsigned t).

        (* t2 - t1 as a linear form, for ints and (unsigned) bitvectors. *)
        Definition lin_diff {σ} : Term Σ σ -> Term Σ σ -> option LinK :=
          match σ as σ return Term Σ σ -> Term Σ σ -> option LinK with
          | ty.int    => fun t1 t2 => Some (lin_term t2 1 (lin_term t1 (-1) (nil, 0%Z)))
          | ty.bvec n => fun t1 t2 => Some (lin_unsigned t2 1 (lin_unsigned t1 (-1) (nil, 0%Z)))
          | _         => fun _ _ => None
          end.

        Definition relop_cstr {σ} (op : RelOp σ) : Term Σ σ -> Term Σ σ -> option Cstr :=
          match op with
          | bop.eq    => fun t1 t2 => option_map cstr_eq (lin_diff t1 t2)
          | bop.neq   => fun t1 t2 => option_map cstr_ne (lin_diff t1 t2)
          | bop.le    => fun t1 t2 => Some (cstr_ge (lin_term t2 1 (lin_term t1 (-1) (nil, 0%Z))))
          | bop.lt    => fun t1 t2 => Some (cstr_ge (lin_term t2 1 (lin_term t1 (-1) (nil, (-1)%Z))))
          | bop.bvule => fun t1 t2 => Some (cstr_ge (lin_unsigned t2 1 (lin_unsigned t1 (-1) (nil, 0%Z))))
          | bop.bvult => fun t1 t2 => Some (cstr_ge (lin_unsigned t2 1 (lin_unsigned t1 (-1) (nil, (-1)%Z))))
          | _         => fun _ _ => None
          end.

        Definition formula_cstr (F : Formula Σ) : option Cstr :=
          match F with
          | formula_relop op t1 t2 => option_map cstr_normalize (relop_cstr op t1 t2)
          | _ => None
          end.

        Definition formula_disj (F : Formula Σ) : option (Cstr * Cstr) :=
          match F with
          | formula_or F1 F2 =>
              match formula_cstr F1, formula_cstr F2 with
              | Some c1, Some c2 => Some (c1, c2)
              | _, _ => None
              end
          | _ => None
          end.

      End WithHyps.

      (* Hypotheses: single constraints and binary disjunctions of them. *)
      Definition Hyps : Type := list Cstr * list (Cstr * Cstr).

      (* Unit propagation: a disjunction with one refuted side gives the other. *)
      Definition propagate (ds : list (Cstr * Cstr)) (cs : list Cstr) : list Cstr :=
        fold_right
          (fun '(c1, c2) acc =>
             match decide_cstr cs c1 with
             | contradicted => cons c2 acc
             | _ => match decide_cstr cs c2 with
                    | contradicted => cons c1 acc
                    | _ => acc
                    end
             end) cs ds.

      Definition hyps_add (h : Hyps) (F : Formula Σ) : Hyps :=
        let '(cs, ds) := h in
        match formula_cstr cs F with
        | Some c => (cons c cs, ds)
        | None => match formula_disj cs F with
                  | Some d => (cs, cons d ds)
                  | None => (cs, ds)
                  end
        end.

      Definition pathcondition_hyps (C : PathCondition Σ) : Hyps :=
        ctx.Ctx_rect (fun _ => Hyps) (nil, nil) (fun _ h F => hyps_add h F) C.

      (* Decide the atoms of F from the bounds; in F1 ∧ F2 and F1 ∨ F2, the
         second part is simplified knowing F1, resp. ¬F1. *)
      Fixpoint bsimp (ds : list (Cstr * Cstr)) (cs : list Cstr) (F : Formula Σ) : Formula Σ :=
        match F with
        | formula_relop op t1 t2 =>
            match formula_cstr cs F with
            | Some c => match decide_cstr cs c with
                        | entailed     => formula_true
                        | contradicted => formula_false
                        | unknown      => F
                        end
            | None => F
            end
        | formula_and F1 F2 =>
            let F1' := bsimp ds cs F1 in
            let cs2 := match formula_cstr cs F1' with
                       | Some c => propagate ds (cons c cs)
                       | None => cs
                       end in
            smart_and F1' (bsimp ds cs2 F2)
        | formula_or F1 F2 =>
            let F1' := bsimp ds cs F1 in
            let cs2 := match option.bind (formula_cstr cs F1') cstr_negate with
                       | Some c => propagate ds (cons c cs)
                       | None => cs
                       end in
            smart_or F1' (bsimp ds cs2 F2)
        | _ => F
        end.

      Fixpoint bounds_pathcondition (h : Hyps) (C : PathCondition Σ) :
        option (Hyps * PathCondition Σ) :=
        match C with
        | [ctx] => Some (h, [ctx])
        | C ▻ F =>
            '(h', C') <- bounds_pathcondition h C ;;
            let '(cs, ds) := h' in
            match bsimp ds (propagate ds cs) F with
            | formula_true  => Some (h', C')
            | formula_false => None
            | F'            => Some (hyps_add h' F', C' ▻ F')
            end
        end.

      Section Sound.
        Variable (ι : Valuation Σ).

        Lemma lin_add_mono_eval t c l :
          lin_eval ι (lin_add_mono t c l) = (c * inst (T := STerm ty.int) t ι + lin_eval ι l)%Z.
        Proof.
          induction l as [|[t' c'] l IH]; cbn.
          - destruct (Z.eqb_spec c 0); cbn; subst; lia.
          - destruct (Term_eqb_spec t t'); subst.
            + destruct (Z.eqb_spec (c + c') 0); cbn; lia.
            + cbn. rewrite IH. lia.
        Qed.

        Lemma lin_add_eval l1 l2 :
          lin_eval ι (lin_add l1 l2) = (lin_eval ι l1 + lin_eval ι l2)%Z.
        Proof.
          induction l1 as [|[t c] l1 IH]; cbn; [lia|].
          rewrite lin_add_mono_eval. fold (lin_add l1 l2). rewrite IH. lia.
        Qed.

        Lemma lin_neg_eval l : lin_eval ι (lin_neg l) = Z.opp (lin_eval ι l).
        Proof. induction l as [|[t c] l IH]; cbn; lia. Qed.

        Lemma lin_eqb_sound l1 l2 : lin_eqb l1 l2 = true -> lin_eval ι l1 = lin_eval ι l2.
        Proof.
          unfold lin_eqb. intros [_ H]%andb_prop.
          destruct lin_add eqn:E; [|discriminate].
          apply (f_equal (lin_eval ι)) in E.
          rewrite lin_add_eval lin_neg_eval in E. cbn in E. lia.
        Qed.

        Definition lk_eval (lk : LinK) : Z := let '(l, k) := lk in (lin_eval ι l + k)%Z.

        Lemma lin_atom_eval t s lk :
          lk_eval (lin_atom t s lk) = (s * inst (T := STerm ty.int) t ι + lk_eval lk)%Z.
        Proof. destruct lk; cbn. rewrite lin_add_mono_eval. lia. Qed.

        Lemma lin_const_eval i s lk : lk_eval (lin_const i s lk) = (s * i + lk_eval lk)%Z.
        Proof. destruct lk; cbn. lia. Qed.

        Definition lo_ok (lo : option Z) (v : Z) : Prop :=
          match lo with Some a => (a <= v)%Z | None => True end.
        Definition hi_ok (hi : option Z) (v : Z) : Prop :=
          match hi with Some b => (v <= b)%Z | None => True end.
        Definition range_holds (v : Z) (r : Range) : Prop :=
          match r with
          | range_in lo hi => lo_ok lo v /\ hi_ok hi v
          | range_out a => v <> a
          end.
        Definition cstr_holds (c : Cstr) : Prop :=
          range_holds (lin_eval ι (fst c)) (snd c).

        Lemma cstr_holds_dec c : cstr_holds c \/ ~ cstr_holds c.
        Proof.
          destruct c as [l [lo hi|a]]; unfold cstr_holds; cbn.
          - destruct lo, hi; cbn; lia.
          - lia.
        Qed.

        Definition interval_holds (i : Interval) (v : Z) : Prop :=
          lo_ok (fst i) v /\ hi_ok (snd i) v.

        Lemma term_is_unsigned_spec t :
          term_is_unsigned t = true -> (0 <= inst (T := STerm ty.int) t ι)%Z.
        Proof.
          destruct t using Term_int_case; cbn; try discriminate.
          intros _. apply bv.unsigned_bounds.
        Qed.

        Lemma lin_default_spec l : interval_holds (lin_default l) (lin_eval ι l).
        Proof.
          destruct l as [|[t c] [|]]; cbn; try easy.
          destruct term_is_unsigned eqn:Hu; cbn; try easy.
          apply term_is_unsigned_spec in Hu. unfold interval_holds.
          destruct (Z.eqb_spec c 1); cbn; [lia|].
          destruct (Z.eqb_spec c (-1)); cbn; [lia|easy].
        Qed.

        Lemma lin_interval_spec hyps l : Forall cstr_holds hyps ->
          interval_holds (lin_interval hyps l) (lin_eval ι l).
        Proof.
          induction 1 as [|[l' r] hyps Hc _ IH]; [apply lin_default_spec|].
          unfold lin_interval; cbn [fold_right]; fold (lin_interval hyps l).
          destruct lin_interval as [lo hi].
          destruct IH as [IHlo IHhi]. cbn in IHlo, IHhi.
          destruct r as [lo' hi'|a]; [|easy].
          destruct Hc as [Hlo Hhi]; cbn in Hlo, Hhi.
          unfold interval_holds.
          destruct (lin_eqb l l') eqn:E1.
          - apply lin_eqb_sound in E1. rewrite <-E1 in Hlo, Hhi.
            split; cbn.
            + destruct lo, lo'; cbn in *; lia.
            + destruct hi, hi'; cbn in *; lia.
          - destruct (lin_eqb l (lin_neg l')) eqn:E2; [|easy].
            apply lin_eqb_sound in E2. rewrite lin_neg_eval in E2.
            split; cbn.
            + destruct lo, hi'; cbn in *; lia.
            + destruct hi, lo'; cbn in *; lia.
        Qed.

        Lemma decide_range_spec i r v : interval_holds i v ->
          match decide_range i r with
          | entailed => range_holds v r
          | contradicted => ~ range_holds v r
          | unknown => True
          end.
        Proof.
          destruct i as [lo hi]. unfold interval_holds; cbn [fst snd]. intros [Hlo Hhi].
          destruct r as [flo fhi|a]; destruct lo, hi; try destruct flo; try destruct fhi;
            cbn in *;
            repeat match goal with |- context[Z.leb ?x ?y] => destruct (Z.leb_spec x y) end;
            cbn; intuition lia.
        Qed.

        Lemma decide_cstr_spec hyps c : Forall cstr_holds hyps ->
          match decide_cstr hyps c with
          | entailed => cstr_holds c
          | contradicted => ~ cstr_holds c
          | unknown => True
          end.
        Proof. intros H. apply decide_range_spec, lin_interval_spec, H. Qed.

        Lemma bvadd_const_spec {n} (t : Term Σ (ty.bvec n)) x c :
          bvadd_const t = Some (x, c) ->
          exists cv : bv n, bv.unsigned cv = c /\
            inst (T := STerm (ty.bvec n)) t ι = bv.add (inst (T := STerm (ty.bvec n)) x ι) cv.
        Proof.
          revert x c. pattern n, t. revert n t.
          apply Term_bvec_case; cbn; intros; try discriminate.
          destruct (term_get_val_spec t2) as [c2|]; subst.
          - inversion H; subst. now exists c2.
          - destruct (term_get_val_spec t1) as [c1|]; subst; [|discriminate].
            inversion H; subst. exists c1. split; [easy|]. apply bv.add_comm.
        Qed.

        Section WithHyps.
          Variable (hyps : list Cstr).
          Hypothesis (Hhyps : Forall cstr_holds hyps).

          Lemma lin_unsigned_eval {n} (t : Term Σ (ty.bvec n)) s lk :
            lk_eval (lin_unsigned hyps t s lk) =
              (s * @bv.unsigned n (inst (T := STerm (ty.bvec n)) t ι) + lk_eval lk)%Z.
          Proof.
            unfold lin_unsigned. destruct (term_get_val_spec t) as [v|]; subst.
            { now rewrite lin_const_eval. }
            destruct bvadd_const as [[x c]|] eqn:Ea; [|now rewrite lin_atom_eval].
            destruct (@bvadd_const_spec n t x c Ea) as (cv & <- & Ht).
            pose proof (lin_interval_spec (cons (term_unsigned x, 1%Z) nil) Hhyps) as Hi.
            destruct lin_interval as [lo hi].
            destruct Hi as [Hlo Hhi]; cbn [fst snd lin_eval fold_right] in Hlo, Hhi.
            change (inst (term_unsigned x) ι) with
              (@bv.unsigned n (inst (T := STerm (ty.bvec n)) x ι)) in Hlo, Hhi.
            pose proof (bv.unsigned_bounds cv).
            match type of Hlo with
            | context[@bv.unsigned _ ?e] => pose proof (bv.unsigned_bounds e); set (vx := e) in *
            end.
            destruct (le_opt _ (Some _)) eqn:Es.
            - rewrite lin_atom_eval lin_const_eval.
              change (inst (term_unsigned x) ι) with (@bv.unsigned n vx).
              rewrite Ht.
              destruct hi; cbn in Es, Hhi; [|discriminate].
              apply Z.leb_le in Es.
              rewrite <-bv.unsigned_add_small; lia.
            - destruct lo as [l|]; [|now rewrite lin_atom_eval].
              destruct (Z.ltb_spec 0 l); cbn; [|now rewrite lin_atom_eval].
              destruct (Z.leb_spec (2 ^ Z.of_nat n) (l + bv.unsigned cv)); cbn;
                [|now rewrite lin_atom_eval].
              rewrite lin_atom_eval lin_const_eval.
              change (inst (term_unsigned x) ι) with (@bv.unsigned n vx).
              rewrite Ht.
              cbn in Hlo. rewrite <-bv.unsigned_add_large; lia.
          Qed.

          Lemma lin_term_eval t : forall s lk,
            lk_eval (lin_term hyps t s lk) = (s * inst (T := STerm ty.int) t ι + lk_eval lk)%Z.
          Proof.
            induction t using Term_int_rect; intros s lk; cbn.
            - now rewrite lin_atom_eval.
            - now rewrite lin_const_eval.
            - rewrite IHt1 IHt2. lia.
            - rewrite IHt1 IHt2. lia.
            - destruct (term_get_val_spec t1) as [c1|]; subst.
              + rewrite IHt2. cbn. lia.
              + destruct (term_get_val_spec t2) as [c2|]; subst.
                * rewrite IHt1. cbn. lia.
                * now rewrite lin_atom_eval.
            - now rewrite lin_atom_eval.
            - rewrite IHt. lia.
            - now rewrite lin_atom_eval.
            - now rewrite lin_unsigned_eval.
          Qed.

          Lemma lin_diff_eq {σ} (t1 t2 : Term Σ σ) lk : lin_diff hyps t1 t2 = Some lk ->
            (inst (T := STerm σ) t1 ι = inst (T := STerm σ) t2 ι <-> lk_eval lk = 0%Z).
          Proof.
            destruct σ; cbn; try discriminate; intros [= <-].
            - rewrite !lin_term_eval. cbn. lia.
            - rewrite !lin_unsigned_eval. cbn. split.
              + intros ->. lia.
              + intros H. apply bv.unsigned_inj. lia.
          Qed.

          Lemma cstr_ge_spec lk : cstr_holds (cstr_ge lk) <-> (0 <= lk_eval lk)%Z.
          Proof. destruct lk; cbn; intuition lia. Qed.
          Lemma cstr_eq_spec lk : cstr_holds (cstr_eq lk) <-> lk_eval lk = 0%Z.
          Proof. destruct lk; cbn; intuition lia. Qed.
          Lemma cstr_ne_spec lk : cstr_holds (cstr_ne lk) <-> lk_eval lk <> 0%Z.
          Proof. destruct lk; cbn; intuition lia. Qed.

          Lemma relop_cstr_spec {σ} (op : RelOp σ) t1 t2 c : relop_cstr hyps op t1 t2 = Some c ->
            instprop (formula_relop op t1 t2) ι <-> cstr_holds c.
          Proof.
            destruct op; cbn; intros H; try discriminate.
            - destruct lin_diff eqn:E; cbn in H; inversion H; subst.
              rewrite cstr_eq_spec. now apply lin_diff_eq.
            - destruct lin_diff eqn:E; cbn in H; inversion H; subst.
              rewrite cstr_ne_spec. apply lin_diff_eq in E. intuition.
            - inversion H; subst. rewrite cstr_ge_spec !lin_term_eval. cbn. lia.
            - inversion H; subst. rewrite cstr_ge_spec !lin_term_eval. cbn. lia.
            - inversion H; subst.
              rewrite cstr_ge_spec !lin_unsigned_eval bv.ule_iff_unsigned_le. cbn. lia.
            - inversion H; subst.
              rewrite cstr_ge_spec !lin_unsigned_eval bv.ult_iff_unsigned_lt. cbn. lia.
          Qed.
        End WithHyps.

        Lemma lin_gcd_divide l t c : In (t, c) l -> (lin_gcd l | c)%Z.
        Proof.
          induction l as [|[t' c'] l IH]; cbn; [easy|].
          intros [[= -> ->]|HIn].
          - apply Z.gcd_divide_l.
          - eapply Z.divide_trans; [apply Z.gcd_divide_r|]. now apply IH.
        Qed.

        Lemma lin_eval_div g l : (0 < g)%Z -> (forall t c, In (t, c) l -> (g | c)%Z) ->
          lin_eval ι l = (g * lin_eval ι (map (fun '(t, c) => (t, c / g)%Z) l))%Z.
        Proof.
          intros Hg. induction l as [|[t c] l IH]; cbn; intros Hdiv; [lia|].
          rewrite IH. 2: { intros t' c' H'. apply (Hdiv t' c'). now right. }
          destruct (Hdiv t c (or_introl eq_refl)) as [q ->].
          rewrite Z.div_mul; lia.
        Qed.

        Lemma div_lo g a v : (0 < g)%Z -> ((a <= g * v)%Z <-> (- (- a / g) <= v)%Z).
        Proof.
          intros Hg. pose proof (Z.div_mod (- a) g ltac:(lia)).
          pose proof (Z.mod_pos_bound (- a) g Hg).
          set (q := (- a / g)%Z) in *. set (r := (- a mod g)%Z) in *. nia.
        Qed.

        Lemma div_hi g b v : (0 < g)%Z -> ((g * v <= b)%Z <-> (v <= b / g)%Z).
        Proof.
          intros Hg. pose proof (Z.div_mod b g ltac:(lia)).
          pose proof (Z.mod_pos_bound b g Hg).
          set (q := (b / g)%Z) in *. set (r := (b mod g)%Z) in *. nia.
        Qed.

        Lemma div_out (g a v : Z) : (0 < g)%Z ->
          ((g * v <> a)%Z <-> if (a mod g =? 0)%Z then v <> (a / g)%Z else True).
        Proof.
          intros Hg. pose proof (Z.div_mod a g ltac:(lia)).
          pose proof (Z.mod_pos_bound a g Hg).
          set (q := (a / g)%Z) in *. set (r := (a mod g)%Z) in *.
          clearbody q r. subst a.
          destruct (Z.eqb_spec r 0) as [->|Hr].
          - rewrite Z.add_0_r. split.
            + intros H1 ->. now apply H1.
            + intros H1 H2. apply H1. apply Z.mul_reg_l in H2; lia.
          - split; [easy|]. intros _ H1.
            assert (v - q <= 0 \/ 1 <= v - q)%Z as [Hvq|Hvq] by lia; nia.
        Qed.

        Lemma cstr_normalize_spec c : cstr_holds (cstr_normalize c) <-> cstr_holds c.
        Proof.
          destruct c as [l r]. unfold cstr_normalize.
          destruct (Z.leb_spec (lin_gcd l) 1); [reflexivity|].
          unfold cstr_holds; cbn [fst snd].
          assert (Hl := lin_eval_div (g := lin_gcd l) l ltac:(lia) (lin_gcd_divide l)).
          rewrite Hl. set (v := lin_eval ι _). clearbody v.
          destruct r as [lo hi|a]; cbn.
          - destruct lo, hi; cbn; try rewrite (div_lo (g := lin_gcd l));
              try rewrite (div_hi (g := lin_gcd l)); try lia; tauto.
          - rewrite (div_out (g := lin_gcd l)); [|lia].
            destruct (Z.eqb_spec (a mod lin_gcd l) 0); cbn; tauto.
        Qed.

        Lemma formula_cstr_spec hyps F c : Forall cstr_holds hyps ->
          formula_cstr hyps F = Some c -> instprop F ι <-> cstr_holds c.
        Proof.
          intros Hh. destruct F; cbn; try discriminate.
          destruct relop_cstr eqn:E; cbn; intros [= <-].
          rewrite cstr_normalize_spec. now apply (relop_cstr_spec Hh).
        Qed.

        Definition disj_holds (d : Cstr * Cstr) : Prop :=
          cstr_holds (fst d) \/ cstr_holds (snd d).

        Lemma formula_disj_spec hyps F d : Forall cstr_holds hyps ->
          formula_disj hyps F = Some d -> instprop F ι <-> disj_holds d.
        Proof.
          intros Hh. destruct F; cbn; try discriminate.
          destruct formula_cstr eqn:E1; [|discriminate].
          destruct (formula_cstr hyps F2) eqn:E2; [|discriminate].
          intros [= <-]. unfold disj_holds; cbn.
          rewrite (formula_cstr_spec F1 Hh E1) (formula_cstr_spec F2 Hh E2). tauto.
        Qed.

        Lemma cstr_negate_spec c c' : cstr_negate c = Some c' -> cstr_holds c' <-> ~ cstr_holds c.
        Proof.
          destruct c as [l [[a|] [b|]|a]]; cbn; try discriminate.
          - destruct (Z.eqb_spec a b); [|discriminate]. intros [= <-]. subst.
            unfold cstr_holds; cbn. lia.
          - intros [= <-]. unfold cstr_holds; cbn. lia.
          - intros [= <-]. unfold cstr_holds; cbn. lia.
          - intros [= <-]. unfold cstr_holds; cbn. lia.
        Qed.

        Lemma propagate_spec ds cs : Forall disj_holds ds -> Forall cstr_holds cs ->
          Forall cstr_holds (propagate ds cs).
        Proof.
          intros Hds Hcs. induction Hds as [|[c1 c2] ds Hd _ IH]; cbn; [easy|].
          pose proof (decide_cstr_spec c1 Hcs) as H1.
          pose proof (decide_cstr_spec c2 Hcs) as H2.
          unfold disj_holds in Hd; cbn in Hd.
          destruct decide_cstr; [| constructor; [tauto|easy] |];
            destruct (decide_cstr cs c2); try easy; constructor; tauto.
        Qed.

        Definition hyps_holds (h : Hyps) : Prop :=
          Forall cstr_holds (fst h) /\ Forall disj_holds (snd h).

        Lemma hyps_add_spec h F : hyps_holds h -> instprop F ι -> hyps_holds (hyps_add h F).
        Proof.
          destruct h as [cs ds]. intros [Hcs Hds] HF. unfold hyps_add.
          destruct formula_cstr eqn:E.
          - split; [|easy]. constructor; [|easy]. now apply (formula_cstr_spec F Hcs E).
          - destruct formula_disj eqn:E'; [|easy].
            split; [easy|]. constructor; [|easy]. now apply (formula_disj_spec F Hcs E').
        Qed.

        Lemma pathcondition_hyps_spec C : instprop C ι -> hyps_holds (pathcondition_hyps C).
        Proof.
          induction C as [|C IH F]; cbn; [split; constructor|].
          intros [HC HF]. apply hyps_add_spec; auto.
        Qed.

        Lemma smart_and_instprop F1 F2 :
          instprop (smart_and F1 F2) ι <-> instprop F1 ι /\ instprop F2 ι.
        Proof. destruct F1, F2; cbn; tauto. Qed.

        Lemma smart_or_instprop F1 F2 :
          instprop (smart_or F1 F2) ι <-> instprop F1 ι \/ instprop F2 ι.
        Proof. destruct F1, F2; cbn; tauto. Qed.

        Lemma bsimp_spec ds F : Forall disj_holds ds -> forall cs, Forall cstr_holds cs ->
          instprop (bsimp ds cs F) ι <-> instprop F ι.
        Proof.
          intros Hds. induction F; intros cs Hcs; cbn [bsimp]; try reflexivity.
          - destruct formula_cstr as [c|] eqn:E; [|reflexivity].
            pose proof (formula_cstr_spec _ Hcs E) as HF.
            pose proof (decide_cstr_spec c Hcs) as Hd.
            destruct decide_cstr; cbn; tauto.
          - rewrite smart_and_instprop. rewrite (IHF1 cs Hcs).
            destruct formula_cstr as [c|] eqn:E.
            + pose proof (formula_cstr_spec _ Hcs E) as HF1. rewrite IHF1 in HF1; [|easy].
              split; intros [H1 H2]; split; try easy.
              * rewrite IHF2 in H2; [easy|]. apply propagate_spec; [easy|].
                constructor; [now apply HF1|easy].
              * rewrite IHF2; [easy|]. apply propagate_spec; [easy|].
                constructor; [now apply HF1|easy].
            + now rewrite (IHF2 cs Hcs).
          - rewrite smart_or_instprop. rewrite (IHF1 cs Hcs).
            destruct (option.bind (formula_cstr cs (bsimp ds cs F1)) cstr_negate) as [c'|] eqn:E.
            + destruct formula_cstr as [c|] eqn:Ec; cbn in E; [|discriminate].
              pose proof (formula_cstr_spec _ Hcs Ec) as HF1. rewrite IHF1 in HF1; [|easy].
              pose proof (@cstr_negate_spec c c' E) as Hn.
              destruct (cstr_holds_dec c) as [Hc|Hc].
              * cbn. split; intros _; left; now apply HF1.
              * assert (Forall cstr_holds (propagate ds (cons c' cs))) as Hcs2.
                { apply propagate_spec; [easy|]. constructor; [now apply Hn|easy]. }
                rewrite (IHF2 _ Hcs2). cbn. tauto.
            + now rewrite (IHF2 cs Hcs).
        Qed.

        Lemma bounds_pathcondition_spec h C : hyps_holds h ->
          match bounds_pathcondition h C with
          | Some (h', C') =>
              (instprop C ι <-> instprop C' ι) /\ (instprop C' ι -> hyps_holds h')
          | None => ~ instprop C ι
          end.
        Proof.
          intros Hh. induction C as [|C IH F]; cbn; [tauto|].
          destruct bounds_pathcondition as [[[cs ds] C']|]; cbn; [|intuition].
          destruct IH as [IHiff IHh].
          assert (HF : instprop C' ι ->
                       instprop (bsimp ds (propagate ds cs) F) ι <-> instprop F ι).
          { intros HC'. destruct (IHh HC') as [Hcs Hds].
            apply bsimp_spec; [easy|]. now apply propagate_spec. }
          assert (Hgen : forall F', (instprop C' ι -> instprop F' ι <-> instprop F ι) ->
            (instprop_ctx C ι /\ instprop F ι <-> instprop (C' ▻ F') ι) /\
            (instprop (C' ▻ F') ι -> hyps_holds (hyps_add (cs, ds) F'))).
          { intros F' HF'.
            change (instprop (C' ▻ F') ι) with (instprop C' ι /\ instprop F' ι). split.
            - split; intros [HC HFt].
              + assert (instprop C' ι) by now apply IHiff. split; [easy|]. now apply HF'.
              + split; [now apply IHiff|]. now apply HF'.
            - intros [HC' HFt]. apply hyps_add_spec; [now apply IHh|exact HFt]. }
          destruct (bsimp ds (propagate ds cs) F) eqn:E; try exact (Hgen _ HF).
          - split; [|assumption]. split; [intros [HC _]; now apply IHiff|].
            intros HC'. split; [now apply IHiff|]. now apply HF.
          - intros [HC HFt]. apply (HF (proj1 IHiff HC)) in HFt. exact HFt.
        Qed.

      End Sound.

    End LinearBounds.

    Definition bounds_check {Σ} (hyps C : PathCondition Σ) : option (PathCondition Σ) :=
      option_map snd (bounds_pathcondition (pathcondition_hyps hyps) C).

    Lemma bounds_check_spec {w : World} (C : PathCondition w) :
      option.spec
        (fun C' => instpred C' ⊣⊢ instpred C)
        (instpred C ⊢ False)
        (bounds_check (wco w) C).
    Proof.
      unfold bounds_check.
      pose proof (fun ι (Hpc : instprop (wco w) ι) =>
                    bounds_pathcondition_spec (ι := ι) C
                      (@pathcondition_hyps_spec _ ι (wco w) Hpc)) as H.
      destruct bounds_pathcondition as [[h' C']|]; constructor.
      - constructor. intros ι Hpc. rewrite !instpred_prop. symmetry. apply (H ι Hpc).
      - constructor. intros ι Hpc HC. rewrite instpred_prop in HC. now apply (H ι Hpc).
    Qed.

    Definition solver_generic : Solver :=
      fun w0 C0 =>
        match DList.run (simplify_pathcondition C0) with
        | Some C1 =>
            match bounds_check (wco w0) (assumption_pathcondition (wco w0) C1 ctx.nil) with
            | Some C2 => Some (unify_pathcondition C2)
            | None => None
            end
        | None => None
        end.

    Lemma solver_generic_spec : SolverSpec solver_generic.
    Proof.
      unfold solver_generic. intros w C0.
      pose proof (simplify_pathcondition_spec C0) as Hequiv.
      destruct run as [C0'|]; cbn.
      - assert (Hassumption : instpred (assumption_pathcondition (wco w) C0' ctx.nil) ⊣⊢
                                instpred (Some C0')).
        { pose proof (assumption_pathcondition_spec (wco w) C0' ctx.nil) as Hassumption.
          iPoseProof wco_valid as "Hwco".
          iDestruct (Hassumption with "Hwco") as "Hassumption".
          rewrite bi.emp_sep.
          now iApply (bi.wand_iff_sym with "Hassumption"). }
        destruct (bounds_check_spec (assumption_pathcondition (wco w) C0' ctx.nil))
          as [C2 HC2|HnC2]; constructor.
        + pose proof (unify_pathcondition_spec C2) as Hunify.
          destruct (unify_pathcondition C2) as (w1 & ν01 & C1).
          rewrite <-Hunify. rewrite HC2. now rewrite Hassumption.
        + rewrite <-Hequiv. now rewrite <-Hassumption.
      - constructor. now rewrite <-Hequiv.
    Qed.

  End GenericSolver.

  Lemma solver_compose_spec {s1 s2} (spec1 : SolverSpec s1) (spec2 : SolverSpec s2) : SolverSpec (solver_compose s1 s2).
  Proof.
    unfold SolverSpec, solver_compose. intros w0 fmls0.
    apply option.spec_bind.
    generalize (spec1 w0 fmls0); clear spec1.
    apply option.spec_monotonic; auto.
    intros (w1 & ν01 & fmls1) H1.
    apply option.spec_map.
    generalize (spec2 w1 fmls1); clear spec2.
    apply option.spec_monotonic; auto.
    - intros (w2 & ν12 & fmls2) H2.
      rewrite knowing_tri_comp.
      rewrite knowing_trans.
      now rewrite H2.
    - intros Hfmls1.
      now rewrite <-H1, Hfmls1, knowing_pure.
  Qed.


  Definition combined_solver : Solver :=
    let g   := solver_generic in
    let gg  := solver_compose g g in
    let ggu := solver_compose gg solver in
    solver_compose ggu (solver_compose ggu gg).

  Lemma combined_solver_spec : SolverSpec combined_solver.
  Proof.
    unfold combined_solver.
    auto using solver_compose_spec, solver_generic_spec, solver_spec.
  Qed.

End GenericSolverOn.

(* Local Variables: *)
(* proof-omit-proofs-option: t *)
(* End: *)
