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
  (Import GLOBAL : GlobalState)
  (Import P      : PredicateKit GLOBAL)
  (Import W      : WorldsMixin GLOBAL P)
  (Import S      : SolverKit GLOBAL P W)
  (Import SP     : SymPropOn GLOBAL P W)
  (Import UL     : UnifLogicOn GLOBAL P W)
  (Import LSP    : LogSymPropOn GLOBAL P W SP UL).

  Import iris.bi.interface iris.proofmode.proofmode proofmode LogicalSoundness.
  Import AutorewriteUnifLogic.

  Module Import GenericSolver.
    Import option.notations.
    Import DList.

    Fixpoint simplify_bool [Σ] (t : Term Σ ty.bool) : DList Σ :=
      Term_bool_case (fun _ => DList Σ)
        (fun (*var*) ς _        => singleton (formula_bool (term_var ς)))
        (fun (*val*) b          => if b then empty else error)
        (fun (*and*) t1 t2      => cat (simplify_bool t1) (simplify_bool t2))
        (fun (*or*)  t1 t2      => singleton (formula_bool (term_binop bop.or t1 t2)))
        (fun (*rel*) σ op t1 t2 => singleton (formula_relop op t1 t2))
        (fun (*not*) t1         => simplify_bool_neg t1)
        t
    with
    simplify_bool_neg [Σ] (t : Term Σ ty.bool) : DList Σ :=
      Term_bool_case (fun _ => DList Σ)
        (fun (*var*) ς _        => singleton (formula_bool (term_unop uop.not (term_var ς))))
        (fun (*val*) b          => if b then error else empty)
        (fun (*and*) t1 t2      => singleton (formula_bool (term_binop bop.or (term_unop uop.not t1) (term_unop uop.not t2))))
        (fun (*or*)  t1 t2      => cat (simplify_bool_neg t1) (simplify_bool_neg t2))
        (fun (*rel*) σ op t1 t2 => singleton (formula_relop_neg op t1 t2))
        (fun (*not*) t1         => simplify_bool t1)
        t.

    Lemma simplify_bool_spec_combined {w : World} (t : Term w ty.bool) :
      (instpred (simplify_bool t) ⊣⊢ repₚ (T := fun Σ => Term Σ ty.bool) true t) ∧
      (instpred (simplify_bool_neg t) ⊣⊢ repₚ (T := fun Σ => Term Σ ty.bool) false t).
    Proof.
      induction t using Term_bool_ind; cbn; arw.
      - destruct b; arw.
      - split.
        + now destruct IHt1 as [-> _], IHt2 as [-> _].
        + (* need to find a confluent rewrite strategy... *)
          now rewrite -(term_negb_involutive (term_binop bop.and _ _))
                         repₚ_term_not' term_not_and.
      - destruct IHt1 as [_ ->], IHt2 as [_ ->]; arw.
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

    Definition simplify_relop {Σ σ} (op : RelOp σ) :
      forall (t1 t2 : STerm σ Σ), DList Σ :=
      match op in RelOp σ return forall (t1 t2 : STerm σ Σ), DList Σ with
      | bop.eq => fun t1 t2 => simplify_eq (peval t1) (peval t2)
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

    Definition solver_generic : Solver :=
      fun w0 C0 =>
        match DList.run (simplify_pathcondition C0) with
        | Some C1 => Some (unify_pathcondition (assumption_pathcondition (wco w0) C1 ctx.nil))
        | None => None
        end.

    Lemma solver_generic_spec : SolverSpec solver_generic.
    Proof.
      unfold solver_generic. intros w C0.
      pose proof (simplify_pathcondition_spec C0) as Hequiv.
      destruct run as [C0'|]; constructor; cbn.
      - pose proof (unify_pathcondition_spec (assumption_pathcondition (wco w) C0' ctx.nil)) as Hunify.
        destruct (unify_pathcondition (assumption_pathcondition (wco w) C0' ctx.nil)) as (w1 & ν01 & C1).
        rewrite <-Hunify.
        rewrite <-Hequiv.
        pose proof (assumption_pathcondition_spec (wco w) C0' ctx.nil) as Hassumption.
        iPoseProof wco_valid as "Hwco".
        iDestruct (Hassumption with "Hwco") as "Hassumption".
        rewrite bi.emp_sep.
        now iApply (bi.wand_iff_sym with "Hassumption").
      - now rewrite <-Hequiv.
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
