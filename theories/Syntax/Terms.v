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
     Unicode.Utf8
     ssr.ssrbool.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Context
     Environment
     Notations
     Prelude
     Bitvector
     Syntax.BinOps
     Syntax.TypeDecl
     Syntax.UnOps
     Syntax.Variables
     Tactics.

Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.
Local Set Transparent Obligations.
Local Unset Elimination Schemes.

(* Case analysis on types and operators for the Term_*_case functions. These
   helpers are global, so the impossible cases are not part of every copy of
   TermsOn. T is the term family, the mk* arguments its constructors. *)
Module cases.
  #[local] Unset Implicit Arguments.

  Section WithTypeDeclKit.
    Context {TDC : TypeDeclKit} (T : Ty → Type).

    #[local] Abbreviation MkBinOp :=
      (∀ σ1 σ2 σ3, BinOp σ1 σ2 σ3 → T σ1 → T σ2 → T σ3) (only parsing).
    #[local] Abbreviation MkUnOp :=
      (∀ σ1 σ2, UnOp σ1 σ2 → T σ1 → T σ2) (only parsing).

    Section Int.
      Context (P : T ty.int → Type).

      Definition motive_int (σ : Ty) : T σ → Type :=
        match σ with
        | ty.int => P
        | _      => fun _ => unit
        end.

      Definition intro_int {F : Ty → Type} (mk : ∀ σ, F σ → T σ)
        (f : ∀ x, P (mk ty.int x)) (σ : Ty) : ∀ x, motive_int σ (mk σ x) :=
        match σ with
        | ty.int => f
        | _      => fun _ => tt
        end.

      Definition binop_int (mk : MkBinOp)
        (pplus : ∀ x y, P (mk _ _ _ bop.plus x y))
        (pminus : ∀ x y, P (mk _ _ _ bop.minus x y))
        (ptimes : ∀ x y, P (mk _ _ _ bop.times x y))
        (pland : ∀ x y, P (mk _ _ _ bop.land x y))
        σ1 σ2 σ3 (op : BinOp σ1 σ2 σ3) : ∀ x y, motive_int σ3 (mk _ _ _ op x y) :=
        match op with
        | bop.plus  => pplus
        | bop.minus => pminus
        | bop.times => ptimes
        | bop.land  => pland
        | _         => fun _ _ => tt
        end.

      Definition unop_int (mk : MkUnOp)
        (pneg : ∀ x, P (mk _ _ uop.neg x))
        (psigned : ∀ n x, P (mk _ _ (@uop.signed _ n) x))
        (punsigned : ∀ n x, P (mk _ _ (@uop.unsigned _ n) x))
        σ1 σ2 (op : UnOp σ1 σ2) : ∀ x, motive_int σ2 (mk _ _ op x) :=
        match op with
        | uop.neg      => pneg
        | uop.signed   => psigned _
        | uop.unsigned => punsigned _
        | _            => fun _ => tt
        end.
    End Int.

    (* The index is not a variable: compare it with an equation. *)
    Section List.
      Context (σ : Ty) (P : T (ty.list σ) → Type).

      #[local] Abbreviation cast e x :=
        (eq_rect_r (fun τ => T (ty.list τ)) x e) (only parsing).

      Definition motive_list (s : Ty) : T s → Type :=
        match s with
        | ty.list τ => fun x => ∀ e : σ = τ, P (cast e x)
        | _         => fun _ => unit
        end.

      Definition intro_list {F : Ty → Type} (mk : ∀ σ, F σ → T σ)
        (f : ∀ x, P (mk (ty.list σ) x)) (s : Ty) : ∀ x, motive_list s (mk s x) :=
        match s with
        | ty.list τ => fun x e =>
            match e in _ = τ return ∀ x, P (cast e (mk (ty.list τ) x)) with
            | eq_refl => f
            end x
        | _ => fun _ => tt
        end.

      Definition binop_list (mk : MkBinOp)
        (pcons : ∀ x y, P (mk _ _ _ bop.cons x y))
        (pappend : ∀ x y, P (mk _ _ _ bop.append x y))
        σ1 σ2 σ3 (op : BinOp σ1 σ2 σ3) : ∀ x y, motive_list σ3 (mk _ _ _ op x y) :=
        match op with
        | @bop.cons _ τ => fun x y e =>
            match e in _ = τ return ∀ x y, P (cast e (mk _ _ _ (@bop.cons _ τ) x y)) with
            | eq_refl => pcons
            end x y
        | @bop.append _ τ => fun x y e =>
            match e in _ = τ return ∀ x y, P (cast e (mk _ _ _ (@bop.append _ τ) x y)) with
            | eq_refl => pappend
            end x y
        | _ => fun _ _ => tt
        end.

      Definition unop_list (mk : MkUnOp)
        (prev : ∀ x, P (mk _ _ uop.rev x))
        σ1 σ2 (op : UnOp σ1 σ2) : ∀ x, motive_list σ2 (mk _ _ op x) :=
        match op with
        | @uop.rev _ τ => fun x e =>
            match e in _ = τ return ∀ x, P (cast e (mk _ _ (@uop.rev _ τ) x)) with
            | eq_refl => prev
            end x
        | _ => fun _ => tt
        end.
    End List.

    Section Bool.
      Context (P : T ty.bool → Type).

      Definition motive_bool (σ : Ty) : T σ → Type :=
        match σ with
        | ty.bool => P
        | _       => fun _ => unit
        end.

      Definition intro_bool {F : Ty → Type} (mk : ∀ σ, F σ → T σ)
        (f : ∀ x, P (mk ty.bool x)) (σ : Ty) : ∀ x, motive_bool σ (mk σ x) :=
        match σ with
        | ty.bool => f
        | _       => fun _ => tt
        end.

      Definition binop_bool (mk : MkBinOp)
        (pand : ∀ x y, P (mk _ _ _ bop.and x y))
        (por : ∀ x y, P (mk _ _ _ bop.or x y))
        (prel : ∀ σ (op : RelOp σ) x y, P (mk _ _ _ (bop.relop op) x y))
        σ1 σ2 σ3 (op : BinOp σ1 σ2 σ3) : ∀ x y, motive_bool σ3 (mk _ _ _ op x y) :=
        match op with
        | bop.and      => pand
        | bop.or       => por
        | bop.relop op => prel _ op
        | _            => fun _ _ => tt
        end.

      Definition unop_bool (mk : MkUnOp)
        (pnot : ∀ x, P (mk _ _ uop.not x))
        σ1 σ2 (op : UnOp σ1 σ2) : ∀ x, motive_bool σ2 (mk _ _ op x) :=
        match op with
        | uop.not => pnot
        | _       => fun _ => tt
        end.
    End Bool.

    Section Bvec.
      Context (P : ∀ n, T (ty.bvec n) → Type).

      Definition motive_bvec (σ : Ty) : T σ → Type :=
        match σ with
        | ty.bvec n => P n
        | _         => fun _ => unit
        end.

      Definition intro_bvec {F : Ty → Type} (mk : ∀ σ, F σ → T σ)
        (f : ∀ n x, P n (mk (ty.bvec n) x)) (σ : Ty) : ∀ x, motive_bvec σ (mk σ x) :=
        match σ with
        | ty.bvec n => f n
        | _         => fun _ => tt
        end.

      Definition binop_bvec (mk : MkBinOp)
        (pbvadd : ∀ n x y, P n (mk _ _ _ (@bop.bvadd _ n) x y))
        (pbvsub : ∀ n x y, P n (mk _ _ _ (@bop.bvsub _ n) x y))
        (pbvmul : ∀ n x y, P n (mk _ _ _ (@bop.bvmul _ n) x y))
        (pbvand : ∀ n x y, P n (mk _ _ _ (@bop.bvand _ n) x y))
        (pbvor : ∀ n x y, P n (mk _ _ _ (@bop.bvor _ n) x y))
        (pbvxor : ∀ n x y, P n (mk _ _ _ (@bop.bvxor _ n) x y))
        (pshiftr : ∀ n m x y, P n (mk _ _ _ (@bop.shiftr _ n m) x y))
        (pshiftl : ∀ n m x y, P n (mk _ _ _ (@bop.shiftl _ n m) x y))
        (pbvapp : ∀ n1 n2 x y, P (n1 + n2) (mk _ _ _ (@bop.bvapp _ n1 n2) x y))
        (pbvcons : ∀ n x y, P (S n) (mk _ _ _ (@bop.bvcons _ n) x y))
        (pupdate_subrange : ∀ n s l p x y,
            P n (mk _ _ _ (@bop.update_vector_subrange _ n s l p) x y))
        σ1 σ2 σ3 (op : BinOp σ1 σ2 σ3) : ∀ x y, motive_bvec σ3 (mk _ _ _ op x y) :=
        match op with
        | bop.bvadd                             => pbvadd _
        | bop.bvsub                             => pbvsub _
        | bop.bvmul                             => pbvmul _
        | bop.bvand                             => pbvand _
        | bop.bvor                              => pbvor _
        | bop.bvxor                             => pbvxor _
        | bop.shiftr                            => pshiftr _ _
        | bop.shiftl                            => pshiftl _ _
        | bop.bvapp                             => pbvapp _ _
        | bop.bvcons                            => pbvcons _
        | @bop.update_vector_subrange _ n s l p => pupdate_subrange n s l p
        | _                                     => fun _ _ => tt
        end.

      Definition unop_bvec (mk : MkUnOp)
        (pbvnot : ∀ n x, P n (mk _ _ (@uop.bvnot _ n) x))
        (pnegate : ∀ n x, P n (mk _ _ (@uop.negate _ n) x))
        (psext : ∀ n m p x, P n (mk _ _ (@uop.sext _ m n p) x))
        (pzext : ∀ n m p x, P n (mk _ _ (@uop.zext _ m n p) x))
        (pgetslice : ∀ n x, P n (mk _ _ (@uop.get_slice_int _ n) x))
        (ptruncate : ∀ n m p x, P n (mk _ _ (@uop.truncate _ m n p) x))
        (psubrange : ∀ s l m p x, P l (mk _ _ (@uop.vector_subrange _ m s l p) x))
        (pbvdrop : ∀ m n x, P n (mk _ _ (@uop.bvdrop _ m n) x))
        (pbvtake : ∀ m n x, P m (mk _ _ (@uop.bvtake _ m n) x))
        σ1 σ2 (op : UnOp σ1 σ2) : ∀ x, motive_bvec σ2 (mk _ _ op x) :=
        match op with
        | uop.bvnot                      => pbvnot _
        | uop.negate                     => pnegate _
        | @uop.sext _ m n p              => psext n m p
        | @uop.zext _ m n p              => pzext n m p
        | @uop.get_slice_int _ n         => pgetslice n
        | @uop.truncate _ n m p          => ptruncate m n p
        | @uop.vector_subrange _ n s l p => psubrange s l n p
        | @uop.bvdrop _ m n              => pbvdrop m n
        | @uop.bvtake _ m n              => pbvtake m n
        | _                              => fun _ => tt
        end.
    End Bvec.

    Section Prod.
      Context (σ1 σ2 : Ty) (P : T (ty.prod σ1 σ2) → Type).

      #[local] Abbreviation cast e1 e2 x :=
        (eq_rect_r (fun τ1 => T (ty.prod τ1 σ2))
           (eq_rect_r (fun τ2 => T (ty.prod _ τ2)) x e2) e1) (only parsing).

      Definition motive_prod (s : Ty) : T s → Type :=
        match s with
        | ty.prod τ1 τ2 => fun x => ∀ (e1 : σ1 = τ1) (e2 : σ2 = τ2), P (cast e1 e2 x)
        | _             => fun _ => unit
        end.

      Definition intro_prod {F : Ty → Type} (mk : ∀ σ, F σ → T σ)
        (f : ∀ x, P (mk (ty.prod σ1 σ2) x)) (s : Ty) : ∀ x, motive_prod s (mk s x) :=
        match s with
        | ty.prod τ1 τ2 => fun x e1 e2 =>
            match e1 in _ = τ1 return ∀ x, P (cast e1 e2 (mk (ty.prod τ1 τ2) x)) with
            | eq_refl =>
                match e2 in _ = τ2 return ∀ x, P (cast eq_refl e2 (mk (ty.prod σ1 τ2) x)) with
                | eq_refl => f
                end
            end x
        | _ => fun _ => tt
        end.

      Definition binop_prod (mk : MkBinOp)
        (ppair : ∀ x y, P (mk _ _ _ bop.pair x y))
        a b c (op : BinOp a b c) : ∀ x y, motive_prod c (mk _ _ _ op x y) :=
        match op with
        | @bop.pair _ τ1 τ2 => fun x y e1 e2 =>
            match e1 in _ = τ1 return ∀ x y, P (cast e1 e2 (mk _ _ _ (@bop.pair _ τ1 τ2) x y)) with
            | eq_refl =>
                match e2 in _ = τ2 return ∀ x y, P (cast eq_refl e2 (mk _ _ _ (@bop.pair _ σ1 τ2) x y)) with
                | eq_refl => ppair
                end
            end x y
        | _ => fun _ _ => tt
        end.

      (* A lone _ would not split on op, so name one constructor. *)
      Definition unop_prod (mk : MkUnOp) a b (op : UnOp a b) : ∀ x, motive_prod b (mk _ _ op x) :=
        match op with
        | uop.neg => fun _ => tt
        | _       => fun _ => tt
        end.
    End Prod.

    Section Sum.
      Context (σ1 σ2 : Ty) (P : T (ty.sum σ1 σ2) → Type).

      #[local] Abbreviation cast e1 e2 x :=
        (eq_rect_r (fun τ1 => T (ty.sum τ1 σ2))
           (eq_rect_r (fun τ2 => T (ty.sum _ τ2)) x e2) e1) (only parsing).

      Definition motive_sum (s : Ty) : T s → Type :=
        match s with
        | ty.sum τ1 τ2 => fun x => ∀ (e1 : σ1 = τ1) (e2 : σ2 = τ2), P (cast e1 e2 x)
        | _            => fun _ => unit
        end.

      Definition intro_sum {F : Ty → Type} (mk : ∀ σ, F σ → T σ)
        (f : ∀ x, P (mk (ty.sum σ1 σ2) x)) (s : Ty) : ∀ x, motive_sum s (mk s x) :=
        match s with
        | ty.sum τ1 τ2 => fun x e1 e2 =>
            match e1 in _ = τ1 return ∀ x, P (cast e1 e2 (mk (ty.sum τ1 τ2) x)) with
            | eq_refl =>
                match e2 in _ = τ2 return ∀ x, P (cast eq_refl e2 (mk (ty.sum σ1 τ2) x)) with
                | eq_refl => f
                end
            end x
        | _ => fun _ => tt
        end.

      Definition binop_sum (mk : MkBinOp) a b c (op : BinOp a b c) :
        ∀ x y, motive_sum c (mk _ _ _ op x y) :=
        match op with
        | bop.plus => fun _ _ => tt
        | _        => fun _ _ => tt
        end.

      Definition unop_sum (mk : MkUnOp)
        (pinl : ∀ x, P (mk _ _ uop.inl x))
        (pinr : ∀ x, P (mk _ _ uop.inr x))
        a b (op : UnOp a b) : ∀ x, motive_sum b (mk _ _ op x) :=
        match op with
        | @uop.inl _ τ1 τ2 => fun x e1 e2 =>
            match e1 in _ = τ1 return ∀ x, P (cast e1 e2 (mk _ _ (@uop.inl _ τ1 τ2) x)) with
            | eq_refl =>
                match e2 in _ = τ2 return ∀ x, P (cast eq_refl e2 (mk _ _ (@uop.inl _ σ1 τ2) x)) with
                | eq_refl => pinl
                end
            end x
        | @uop.inr _ τ1 τ2 => fun x e1 e2 =>
            match e1 in _ = τ1 return ∀ x, P (cast e1 e2 (mk _ _ (@uop.inr _ τ1 τ2) x)) with
            | eq_refl =>
                match e2 in _ = τ2 return ∀ x, P (cast eq_refl e2 (mk _ _ (@uop.inr _ σ1 τ2) x)) with
                | eq_refl => pinr
                end
            end x
        | _ => fun _ => tt
        end.
    End Sum.

    Section Tuple.
      Context (σs : Ctx Ty) (P : T (ty.tuple σs) → Type).

      #[local] Abbreviation cast e x :=
        (eq_rect_r (fun i => T (ty.tuple i)) x e) (only parsing).

      Definition motive_tuple (s : Ty) : T s → Type :=
        match s with
        | ty.tuple i => fun x => ∀ e : σs = i, P (cast e x)
        | _          => fun _ => unit
        end.

      Definition intro_tuple {F : Ty → Type} (mk : ∀ σ, F σ → T σ)
        (f : ∀ x, P (mk (ty.tuple σs) x)) (s : Ty) : ∀ x, motive_tuple s (mk s x) :=
        match s with
        | ty.tuple i => fun x e =>
            match e in _ = i return ∀ x, P (cast e (mk (ty.tuple i) x)) with
            | eq_refl => f
            end x
        | _ => fun _ => tt
        end.

      Definition binop_tuple (mk : MkBinOp) a b c (op : BinOp a b c) :
        ∀ x y, motive_tuple c (mk _ _ _ op x y) :=
        match op with
        | bop.plus => fun _ _ => tt
        | _        => fun _ _ => tt
        end.

      Definition unop_tuple (mk : MkUnOp) a b (op : UnOp a b) :
        ∀ x, motive_tuple b (mk _ _ op x) :=
        match op with
        | uop.neg => fun _ => tt
        | _       => fun _ => tt
        end.

      Definition ctor_tuple {F : Ctx Ty → Type} (mk : ∀ i, F i → T (ty.tuple i))
        (f : ∀ x, P (mk σs x)) (i : Ctx Ty) : ∀ x, motive_tuple (ty.tuple i) (mk i x) :=
        fun x e =>
          match e in _ = i return ∀ x, P (cast e (mk i x)) with
          | eq_refl => f
          end x.
    End Tuple.

    Section Union.
      Context (U : unioni) (P : T (ty.union U) → Type).

      #[local] Abbreviation cast e x :=
        (eq_rect_r (fun i => T (ty.union i)) x e) (only parsing).

      Definition motive_union (s : Ty) : T s → Type :=
        match s with
        | ty.union i => fun x => ∀ e : U = i, P (cast e x)
        | _          => fun _ => unit
        end.

      Definition intro_union {F : Ty → Type} (mk : ∀ σ, F σ → T σ)
        (f : ∀ x, P (mk (ty.union U) x)) (s : Ty) : ∀ x, motive_union s (mk s x) :=
        match s with
        | ty.union i => fun x e =>
            match e in _ = i return ∀ x, P (cast e (mk (ty.union i) x)) with
            | eq_refl => f
            end x
        | _ => fun _ => tt
        end.

      Definition binop_union (mk : MkBinOp) a b c (op : BinOp a b c) :
        ∀ x y, motive_union c (mk _ _ _ op x y) :=
        match op with
        | bop.plus => fun _ _ => tt
        | _        => fun _ _ => tt
        end.

      Definition unop_union (mk : MkUnOp) a b (op : UnOp a b) :
        ∀ x, motive_union b (mk _ _ op x) :=
        match op with
        | uop.neg => fun _ => tt
        | _       => fun _ => tt
        end.

      Definition ctor_union {F : unioni → Type} {G : ∀ i, F i → Type} (mk : ∀ i (K : F i), G i K → T (ty.union i))
        (f : ∀ K x, P (mk U K x)) (i : unioni) : ∀ K x, motive_union (ty.union i) (mk i K x) :=
        fun K x e =>
          match e in _ = i return ∀ K x, P (cast e (mk i K x)) with
          | eq_refl => f
          end K x.
    End Union.

    Section Record.
      Context (R : recordi) (P : T (ty.record R) → Type).

      #[local] Abbreviation cast e x :=
        (eq_rect_r (fun i => T (ty.record i)) x e) (only parsing).

      Definition motive_record (s : Ty) : T s → Type :=
        match s with
        | ty.record i => fun x => ∀ e : R = i, P (cast e x)
        | _           => fun _ => unit
        end.

      Definition intro_record {F : Ty → Type} (mk : ∀ σ, F σ → T σ)
        (f : ∀ x, P (mk (ty.record R) x)) (s : Ty) : ∀ x, motive_record s (mk s x) :=
        match s with
        | ty.record i => fun x e =>
            match e in _ = i return ∀ x, P (cast e (mk (ty.record i) x)) with
            | eq_refl => f
            end x
        | _ => fun _ => tt
        end.

      Definition binop_record (mk : MkBinOp) a b c (op : BinOp a b c) :
        ∀ x y, motive_record c (mk _ _ _ op x y) :=
        match op with
        | bop.plus => fun _ _ => tt
        | _        => fun _ _ => tt
        end.

      Definition unop_record (mk : MkUnOp) a b (op : UnOp a b) :
        ∀ x, motive_record b (mk _ _ op x) :=
        match op with
        | uop.neg => fun _ => tt
        | _       => fun _ => tt
        end.

      Definition ctor_record {F : recordi → Type} (mk : ∀ i, F i → T (ty.record i))
        (f : ∀ x, P (mk R x)) (i : recordi) : ∀ x, motive_record (ty.record i) (mk i x) :=
        fun x e =>
          match e in _ = i return ∀ x, P (cast e (mk i x)) with
          | eq_refl => f
          end x.
    End Record.

  End WithTypeDeclKit.
End cases.

Module Type TermsOn (Import TY : Types).

  Local Abbreviation PCtx := (NCtx PVar Ty).
  Local Abbreviation LCtx := (NCtx LVar Ty).

  Inductive Term (Σ : LCtx) : Ty → Set :=
  | term_var     (l : LVar) (σ : Ty) {lIn : l∷σ ∈ Σ} : Term Σ σ
  | term_val     (σ : Ty) : Val σ → Term Σ σ
  | term_binop   {σ1 σ2 σ3} (op : BinOp σ1 σ2 σ3) (t1 : Term Σ σ1) (t2 : Term Σ σ2) : Term Σ σ3
  | term_unop    {σ1 σ2} (op : UnOp σ1 σ2) (t : Term Σ σ1) : Term Σ σ2
  | term_tuple   {σs} (ts : Env (Term Σ) σs) : Term Σ (ty.tuple σs)
  | term_union   {U : unioni} (K : unionk U) (t : Term Σ (unionk_ty U K)) : Term Σ (ty.union U)
  | term_record  (R : recordi) (ts : NamedEnv (Term Σ) (recordf_ty R)) : Term Σ (ty.record R).
  #[global] Arguments term_var {_} _ {_ _}.
  #[global] Arguments term_val {_} _ _.
  #[global] Arguments term_tuple {_ _} ts.
  #[global] Arguments term_union {_} U K t.
  #[global] Arguments term_record {_} R ts.
  Bind Scope term_scope with Term.
  Derive NoConfusion Signature for Term.

  (* Abbreviations  *)
  Abbreviation term_var_in lIn := (@term_var _ _ _ lIn) (only parsing).

  (* BinOp *)
  Abbreviation term_plus := (term_binop bop.plus).
  Abbreviation term_times := (term_binop bop.times).
  Abbreviation term_minus := (term_binop bop.minus).
  Abbreviation term_land := (term_binop bop.land).
  Abbreviation term_and := (term_binop bop.and).
  Abbreviation term_or := (term_binop bop.or).
  Abbreviation term_pair := (term_binop bop.pair).
  Abbreviation term_cons := (term_binop bop.cons).
  Abbreviation term_append := (term_binop bop.append).
  Abbreviation term_shiftr := (term_binop bop.shiftr).
  Abbreviation term_shiftl := (term_binop bop.shiftl).
  Abbreviation term_bvadd := (term_binop bop.bvadd).
  Abbreviation term_bvsub := (term_binop bop.bvsub).
  Abbreviation term_bvmul := (term_binop bop.bvmul).
  Abbreviation term_bvand := (term_binop bop.bvand).
  Abbreviation term_bvor := (term_binop bop.bvor).
  Abbreviation term_bvxor := (term_binop bop.bvxor).
  Abbreviation term_bvapp := (term_binop bop.bvapp).
  Abbreviation term_bvcons := (term_binop bop.bvcons).

  (* RelOp *)
  Abbreviation term_eq := (term_binop (bop.relop bop.eq)).
  Abbreviation term_neq := (term_binop (bop.relop bop.neq)).
  Abbreviation term_le := (term_binop (bop.relop bop.le)).
  Abbreviation term_lt := (term_binop (bop.relop bop.lt)).
  Abbreviation term_bvsle := (term_binop (bop.relop bop.bvsle)).
  Abbreviation term_bvslt := (term_binop (bop.relop bop.bvslt)).
  Abbreviation term_bvule := (term_binop (bop.relop bop.bvule)).
  Abbreviation term_bvult := (term_binop (bop.relop bop.bvult)).

  (* UnOp *)
  Abbreviation term_inl := (term_unop uop.inl).
  Abbreviation term_inr := (term_unop uop.inr).
  Abbreviation term_neg := (term_unop uop.neg).
  Abbreviation term_not := (term_unop uop.not).
  Abbreviation term_rev := (term_unop uop.rev).
  Abbreviation term_sext := (term_unop uop.sext).
  Abbreviation term_zext := (term_unop uop.zext).
  Abbreviation term_get_slice_int := (term_unop uop.get_slice_int).
  Abbreviation term_signed := (term_unop uop.signed).
  Abbreviation term_unsigned := (term_unop uop.unsigned).
  Abbreviation term_bvnot := (term_unop uop.bvnot).
  Abbreviation term_bvdrop m := (term_unop (uop.bvdrop m)).
  Abbreviation term_bvtake m := (term_unop (uop.bvtake m)).
  Abbreviation term_negate := (term_unop uop.negate).

  Section DerivedConstructions.

    Definition term_enum {Σ} (E : enumi) (k : enumt E) : Term Σ (ty.enum E) :=
      term_val (ty.enum E) k.
    #[global] Arguments term_enum {_} _ _.

    Fixpoint term_list {Σ σ} (ts : list (Term Σ σ)) : Term Σ (ty.list σ) :=
      match ts with
      | nil       => term_val (ty.list σ) nil
      | cons t ts => term_cons t (term_list ts)
      end.

    Fixpoint term_bvec {Σ n} (ts : Vector.t (Term Σ ty.bool) n) : Term Σ (ty.bvec n) :=
      match ts with
      | Vector.nil       => term_val (ty.bvec 0) bv.nil
      | Vector.cons t ts => term_bvcons t (term_bvec ts)
      end.

    Definition term_relop_neg [Σ σ] (op : RelOp σ) :
      (∀ (t1 t2 : Term Σ σ), Term Σ ty.bool) :=
      match op with
      | bop.eq     => term_neq
      | bop.neq    => term_eq
      | bop.le     => Basics.flip term_lt
      | bop.lt     => Basics.flip term_le
      | bop.bvsle  => Basics.flip term_bvslt
      | bop.bvslt  => Basics.flip term_bvsle
      | bop.bvule  => Basics.flip term_bvult
      | bop.bvult  => Basics.flip term_bvule
      end.

    Definition term_truncate {Σ n} (m : nat) {p : IsTrue (m <=? n)} :
      Term Σ (ty.bvec n) -> Term Σ (ty.bvec m) :=
      match bv.leview m n with
      | bv.is_le k => term_bvtake m
      end.

    Definition term_vector_subrange {Σ n} s l {p : IsTrue (s+l <=? n)} :
      Term Σ (ty.bvec n) -> Term Σ (ty.bvec l) :=
      match bv.leview (s+l) n with
      | bv.is_le k => fun t => term_bvdrop s (term_bvtake (s+l) t)
      end.

    Definition term_update_vector_subrange {Σ n} s l {p : IsTrue (s+l <=? n)} :
      Term Σ (ty.bvec n) -> Term Σ (ty.bvec l) -> Term Σ (ty.bvec n) :=
      match bv.leview (s+l) n with
      | bv.is_le k =>
          fun t u =>
            term_bvapp
              (term_bvapp (term_bvtake s (term_bvtake (s+l) t)) u)
              (term_bvdrop (s+l) t)
      end.

  End DerivedConstructions.

  Section Term_rect.

    Context [Σ] (P : ∀ [σ : Ty], Term Σ σ → Type).

    Let PE : ∀ (σs : Ctx Ty), Env (Term Σ) σs → Type :=
      fun σs es => env.All P es.
    Let PNE : ∀ (σs : NCtx recordf Ty), NamedEnv (Term Σ) σs → Type :=
      fun σs es => env.All (fun b t => P t) es.

    Hypothesis (pvar : ∀ (l : LVar) (σ : Ty) (lIn : l∷σ ∈ Σ), P (term_var l)).
    Hypothesis (pval : ∀ [σ] (v : Val σ), P (term_val σ v)).
    Hypothesis (pbinop : (∀ [σ1 σ2 σ3 ] (op : BinOp σ1 σ2 σ3)
                            (t1 : Term Σ σ1) (t2 : Term Σ σ2),
                            P t1 → P t2 → P (term_binop op t1 t2))).
    Hypothesis (punop : (∀ [σ1 σ2] (op : UnOp σ1 σ2) (t : Term Σ σ1),
                           P t → P (term_unop op t))).
    Hypothesis (ptuple : (∀ [σs] (ts : Env (Term Σ) σs) (IH : PE ts),
                            P (term_tuple ts))).
    Hypothesis (punion : (∀ [U] (K : unionk U) (t : Term Σ (unionk_ty U K)),
                            P t → P (term_union U K t))).
    Hypothesis (precord : (∀ [R] (ts : NamedEnv (Term Σ) (recordf_ty R))
                             (IH : PNE ts), P (term_record R ts))).

    Fixpoint Term_rect [σ] (t : Term Σ σ) {struct t} : P t :=
      match t with
      | term_var_in lIn     => pvar lIn
      | term_val σ v        => pval v
      | term_binop op t1 t2 => pbinop op (Term_rect t1) (Term_rect t2)
      | term_unop op t      => punop op (Term_rect t)
      | term_tuple ts       => ptuple (env.all_intro Term_rect ts)
      | term_union U K t    => punion K (Term_rect t)
      | term_record R ts    =>
          precord (env.all_intro (fun b => Term_rect (σ := type b)) ts)
      end.

  End Term_rect.

  Definition Term_rec Σ (P : ∀ σ, Term Σ σ → Set) := @Term_rect _ P.
  Definition Term_ind Σ (P : ∀ σ, Term Σ σ → Prop) := @Term_rect _ P.

  Register Scheme Term_rect as rect_dep for Term.
  Register Scheme Term_rec as rec_dep for Term.
  Register Scheme Term_ind as ind_dep for Term.

  Section Term_int_case.

    Context {Σ : LCtx} (P : Term Σ ty.int → Type).

    Hypothesis (pvar : ∀ (l : LVar) (lIn : l∷ty.int ∈ Σ), P (term_var l)).
    Hypothesis (pval : ∀ (i : Val ty.int), P (term_val ty.int i)).
    Hypothesis (pplus : ∀ (t1 t2 : Term Σ ty.int), P (term_binop bop.plus t1 t2)).
    Hypothesis (pminus : ∀ (t1 t2 : Term Σ ty.int), P (term_binop bop.minus t1 t2)).
    Hypothesis (ptimes : ∀ (t1 t2 : Term Σ ty.int), P (term_binop bop.times t1 t2)).
    Hypothesis (pland : ∀ (t1 t2 : Term Σ ty.int), P (term_binop bop.land t1 t2)).
    Hypothesis (pneg : ∀ (t : Term Σ ty.int), P (term_unop uop.neg t)).
    Hypothesis (psigned : ∀ [n] (t : Term Σ (ty.bvec n)), P (term_unop uop.signed t)).
    Hypothesis (punsigned : ∀ [n] (t : Term Σ (ty.bvec n)), P (term_unop uop.unsigned t)).

    Definition Term_int_case (t : Term Σ ty.int) : P t :=
      match t as t' in Term _ σ return cases.motive_int (Term Σ) P σ t' with
      | @term_var _ l σ lIn => cases.intro_int _ P (@term_var Σ l) (@pvar l) σ lIn
      | term_val σ v        => cases.intro_int _ P (@term_val Σ) pval σ v
      | term_binop op t1 t2 =>
          cases.binop_int _ P (@term_binop Σ) pplus pminus ptimes pland _ _ _ op t1 t2
      | term_unop op t      =>
          cases.unop_int _ P (@term_unop Σ) pneg psigned punsigned _ _ op t
      | _                   => tt
      end.

  End Term_int_case.

  Section Term_int_rect.

    Context {Σ : LCtx} (P : Term Σ ty.int → Type).

    Hypothesis (pvar : ∀ (l : LVar) (lIn : l∷ty.int ∈ Σ), P (term_var l)).
    Hypothesis (pval : ∀ (i : Val ty.int), P (term_val ty.int i)).
    Hypothesis (pplus : (∀ (t1 t2 : Term Σ ty.int),
                           P t1 → P t2 → P (term_binop bop.plus t1 t2))).
    Hypothesis (pminus : (∀ (t1 t2 : Term Σ ty.int),
                            P t1 → P t2 → P (term_binop bop.minus t1 t2))).
    Hypothesis (ptimes : (∀ (t1 t2 : Term Σ ty.int),
                            P t1 → P t2 → P (term_binop bop.times t1 t2))).
    Hypothesis (pland : (∀ (t1 t2 : Term Σ ty.int),
                           P t1 → P t2 → P (term_binop bop.land t1 t2))).
    Hypothesis (pneg : ∀ (t : Term Σ ty.int), P t → P (term_unop uop.neg t)).
    Hypothesis (psigned : (∀ [n] (t : Term Σ (ty.bvec n)),
                             P (term_unop uop.signed t))).
    Hypothesis (punsigned : (∀ [n] (t : Term Σ (ty.bvec n)),
                               P (term_unop uop.unsigned t))).

    Fixpoint Term_int_rect (t : Term Σ ty.int) {struct t} : P t :=
      Term_int_case P pvar pval
        (fun t1 t2 => pplus (Term_int_rect t1) (Term_int_rect t2))
        (fun t1 t2 => pminus (Term_int_rect t1) (Term_int_rect t2))
        (fun t1 t2 => ptimes (Term_int_rect t1) (Term_int_rect t2))
        (fun t1 t2 => pland (Term_int_rect t1) (Term_int_rect t2))
        (fun t1 => pneg (Term_int_rect t1))
        psigned punsigned t.

  End Term_int_rect.

  Section Term_bool_case.

    Context {Σ : LCtx} (P : Term Σ ty.bool → Type).

    Hypothesis (pvar : ∀ (l : LVar) (lIn : l∷ty.bool ∈ Σ), P (term_var l)).
    Hypothesis (pval : ∀ (v : Val ty.bool), P (term_val ty.bool v)).
    Hypothesis (pand : ∀ (t1 t2 : Term Σ ty.bool), P (term_binop bop.and t1 t2)).
    Hypothesis (por : ∀ (t1 t2 : Term Σ ty.bool), P (term_binop bop.or t1 t2)).
    Hypothesis (prel : (∀ [σ] (op : RelOp σ) (t1 t2 : Term Σ σ),
                          P (term_binop (bop.relop op) t1 t2))).
    Hypothesis (pnot : ∀ t : Term Σ ty.bool, P (term_unop uop.not t)).

    Definition Term_bool_case (t : Term Σ ty.bool) : P t :=
      match t as t' in Term _ σ return cases.motive_bool (Term Σ) P σ t' with
      | @term_var _ l σ lIn => cases.intro_bool _ P (@term_var Σ l) (@pvar l) σ lIn
      | term_val σ v        => cases.intro_bool _ P (@term_val Σ) pval σ v
      | term_binop op t1 t2 => cases.binop_bool _ P (@term_binop Σ) pand por prel _ _ _ op t1 t2
      | term_unop op t      => cases.unop_bool _ P (@term_unop Σ) pnot _ _ op t
      | _                   => tt
      end.

  End Term_bool_case.

  Section Term_bool_ind.

    Context {Σ : LCtx} (P : Term Σ ty.bool → Type).

    Hypothesis (pvar : ∀ (l : LVar) (lIn : l∷ty.bool ∈ Σ), P (term_var l)).
    Hypothesis (pval : ∀ (b : Val ty.bool), P (term_val ty.bool b)).
    Hypothesis (pand : ∀ (t1 t2 : Term Σ ty.bool), P t1 → P t2 → P (term_binop bop.and t1 t2)).
    Hypothesis (por : ∀ e1 e2, P e1 → P e2 → P (term_binop bop.or e1 e2)).
    Hypothesis (prel : ∀ σ (op : RelOp σ) e1 e2, P (term_binop (bop.relop op) e1 e2)).
    Hypothesis (pnot : ∀ e, P e → P (term_unop uop.not e)).

    Fixpoint Term_bool_ind (t : Term Σ ty.bool) : P t :=
      Term_bool_case P pvar pval
        (fun t1 t2 => pand (Term_bool_ind t1) (Term_bool_ind t2))
        (fun t1 t2 => por (Term_bool_ind t1) (Term_bool_ind t2))
        prel
        (fun t1 => pnot (Term_bool_ind t1))
        t.

  End Term_bool_ind.

  Section Term_list_case.

    Context {Σ σ} (P : Term Σ (ty.list σ) → Type).

    Hypothesis (pvar : ∀ (l : LVar) (lIn : l∷ty.list σ ∈ Σ), P (term_var l)).
    Hypothesis (pval : ∀ (v : Val (ty.list σ)), P (term_val (ty.list σ) v)).
    Hypothesis (pcons : ∀ (t1 : Term Σ σ) (t2 : Term Σ (ty.list σ)), P (term_binop bop.cons t1 t2)).
    Hypothesis (pappend : ∀ (t1 : Term Σ (ty.list σ)) (t2 : Term Σ (ty.list σ)), P (term_binop bop.append t1 t2)).
    Hypothesis (prev : ∀ (t : Term Σ (ty.list σ)), P (term_unop uop.rev t)).

    Definition Term_list_case (t : Term Σ (ty.list σ)) : P t :=
      match t as t' in Term _ s return cases.motive_list (Term Σ) σ P s t' with
      | @term_var _ l s lIn => cases.intro_list _ σ P (@term_var Σ l) (@pvar l) s lIn
      | term_val s v        => cases.intro_list _ σ P (@term_val Σ) pval s v
      | term_binop op t1 t2 =>
          cases.binop_list _ σ P (@term_binop Σ) pcons pappend _ _ _ op t1 t2
      | term_unop op t      => cases.unop_list _ σ P (@term_unop Σ) prev _ _ op t
      | _                   => tt
      end eq_refl.

  End Term_list_case.

  Section Term_prod_case.

    Context {Σ σ1 σ2} (P : Term Σ (ty.prod σ1 σ2) → Type).

    Hypothesis (pvar : ∀ (l : LVar) (lIn : l∷ty.prod σ1 σ2 ∈ Σ), P (term_var l)).
    Hypothesis (pval : ∀ (v : Val (ty.prod σ1 σ2)), P (term_val (ty.prod σ1 σ2) v)).
    Hypothesis (ppair : ∀ (t1 : Term Σ σ1) (t2 : Term Σ σ2), P (term_binop bop.pair t1 t2)).

    Definition Term_prod_case (t : Term Σ (ty.prod σ1 σ2)) : P t :=
      match t as t' in Term _ s return cases.motive_prod (Term Σ) σ1 σ2 P s t' with
      | @term_var _ l s lIn => cases.intro_prod _ σ1 σ2 P (@term_var Σ l) (@pvar l) s lIn
      | term_val s v        => cases.intro_prod _ σ1 σ2 P (@term_val Σ) pval s v
      | term_binop op t1 t2 => cases.binop_prod _ σ1 σ2 P (@term_binop Σ) ppair _ _ _ op t1 t2
      | term_unop op t      => cases.unop_prod _ σ1 σ2 P (@term_unop Σ) _ _ op t
      | _                   => tt
      end eq_refl eq_refl.

  End Term_prod_case.

  Section Term_sum_case.

    Context {Σ σ1 σ2} (P : Term Σ (ty.sum σ1 σ2) → Type).

    Hypothesis (pvar : ∀ (ς : LVar) (ςInΣ : ς∷ty.sum σ1 σ2 ∈ Σ), P (term_var ς)).
    Hypothesis (pval : ∀ (v : Val (ty.sum σ1 σ2)), P (term_val (ty.sum σ1 σ2) v)).
    Hypothesis (pinl : ∀ (t1 : Term Σ σ1), P (term_unop uop.inl t1)).
    Hypothesis (pinr : ∀ (t2 : Term Σ σ2), P (term_unop uop.inr t2)).

    Definition Term_sum_case (t : Term Σ (ty.sum σ1 σ2)) : P t :=
      match t as t' in Term _ s return cases.motive_sum (Term Σ) σ1 σ2 P s t' with
      | @term_var _ l s lIn => cases.intro_sum _ σ1 σ2 P (@term_var Σ l) (@pvar l) s lIn
      | term_val s v        => cases.intro_sum _ σ1 σ2 P (@term_val Σ) pval s v
      | term_binop op t1 t2 => cases.binop_sum _ σ1 σ2 P (@term_binop Σ) _ _ _ op t1 t2
      | term_unop op t      => cases.unop_sum _ σ1 σ2 P (@term_unop Σ) pinl pinr _ _ op t
      | _                   => tt
      end eq_refl eq_refl.

  End Term_sum_case.

  Section Term_bvec_case.

    Context {Σ : LCtx} (P : ∀ n, Term Σ (ty.bvec n) → Type).

    Hypothesis (pvar : ∀ n (l : LVar) (lIn : l∷ty.bvec n ∈ Σ), P (term_var l)).
    Hypothesis (pval : ∀ n (v : Val (ty.bvec n)), P (term_val (ty.bvec n) v)).
    Hypothesis (pbvadd : ∀ n (t1 t2 : Term Σ (ty.bvec n)), P (term_binop bop.bvadd t1 t2)).
    Hypothesis (pbvsub : ∀ n (t1 t2 : Term Σ (ty.bvec n)), P (term_binop bop.bvsub t1 t2)).
    Hypothesis (pbvmul : ∀ n (t1 t2 : Term Σ (ty.bvec n)), P (term_binop bop.bvmul t1 t2)).
    Hypothesis (pbvand : ∀ n (t1 t2 : Term Σ (ty.bvec n)), P (term_binop bop.bvand t1 t2)).
    Hypothesis (pbvor : ∀ n (t1 t2 : Term Σ (ty.bvec n)), P (term_binop bop.bvor t1 t2)).
    Hypothesis (pbvxor : ∀ n (t1 t2 : Term Σ (ty.bvec n)), P (term_binop bop.bvxor t1 t2)).
    Hypothesis (pshiftr : ∀ n m (t1 : Term Σ (ty.bvec n)) (t2 : Term Σ (ty.bvec m)), P (term_binop bop.shiftr t1 t2)).
    Hypothesis (pshiftl : ∀ n m (t1 : Term Σ (ty.bvec n)) (t2 : Term Σ (ty.bvec m)), P (term_binop bop.shiftl t1 t2)).
    Hypothesis (pbvapp : ∀ n1 n2 (t1 : Term Σ (ty.bvec n1)) (t2 : Term Σ (ty.bvec n2)), P (term_binop bop.bvapp t1 t2)).
    Hypothesis (pbvcons : ∀ n (t1 : Term Σ ty.bool) (t2 : Term Σ (ty.bvec n)), P (term_binop bop.bvcons t1 t2)).
    Hypothesis (pupdate_subrange :
                 ∀ {n s l : nat} {pf : IsTrue (s + l <=? n)}
                   (t1 : Term Σ (ty.bvec n)) (t2 : Term Σ (ty.bvec l)),
                  P (term_binop (bop.update_vector_subrange s l) t1 t2)).
    Hypothesis (pbvnot : ∀ n (t : Term Σ (ty.bvec n)), P (term_unop uop.bvnot t)).
    Hypothesis (pnegate : ∀ n (t : Term Σ (ty.bvec n)), P (term_unop uop.negate t)).
    Hypothesis (psext : ∀ n m (pf : IsTrue (m <=? n)) (t : Term Σ (ty.bvec m)), P (term_unop (uop.sext (p := pf)) t)).
    Hypothesis (pzext : ∀ n m (pf : IsTrue (m <=? n)) (t : Term Σ (ty.bvec m)), P (term_unop (uop.zext (p := pf)) t)).
    Hypothesis (pgetslice : ∀ n (t : Term Σ ty.int), P (term_unop (uop.get_slice_int (n := n)) t)).
    Hypothesis (ptruncate : ∀ n m (pf : IsTrue (n <=? m)) (t : Term Σ (ty.bvec m)), P (term_unop (uop.truncate n) t)).
    Hypothesis (psubrange : ∀ s l m (pf : IsTrue (s + l <=? m)) (t : Term Σ (ty.bvec m)), P (term_unop (uop.vector_subrange s l) t)).
    Hypothesis (pbvdrop : ∀ m n (t : Term Σ (ty.bvec (m + n))), P (term_unop (uop.bvdrop m) t)).
    Hypothesis (pbvtake : ∀ m n (t : Term Σ (ty.bvec (m + n))), P (term_unop (uop.bvtake m) t)).

    Definition Term_bvec_case [n] (t : Term Σ (ty.bvec n)) : P t :=
      match t as t' in Term _ σ return cases.motive_bvec (Term Σ) P σ t' with
      | @term_var _ l σ lIn => cases.intro_bvec _ P (@term_var Σ l) (fun n => @pvar n l) σ lIn
      | term_val σ v        => cases.intro_bvec _ P (@term_val Σ) pval σ v
      | term_binop op t1 t2 =>
          cases.binop_bvec _ P (@term_binop Σ) pbvadd pbvsub pbvmul pbvand pbvor pbvxor
            pshiftr pshiftl pbvapp pbvcons (@pupdate_subrange) _ _ _ op t1 t2
      | term_unop op t      =>
          cases.unop_bvec _ P (@term_unop Σ) pbvnot pnegate psext pzext pgetslice
            ptruncate psubrange pbvdrop pbvtake _ _ op t
      | _                   => tt
      end.

  End Term_bvec_case.

  Section Term_bvec_rect.

    Context {Σ : LCtx} (P : ∀ n, Term Σ (ty.bvec n) → Type).

    Hypothesis (pvar : ∀ n (ς : LVar) (ςInΣ : ς∷ty.bvec n ∈ Σ), P (term_var ς)).
    Hypothesis (pval : ∀ n (v : Val (ty.bvec n)), P (term_val (ty.bvec n) v)).
    Hypothesis (pbvadd : ∀ n (t1 t2 : Term Σ (ty.bvec n)), P t1 → P t2 → P (term_binop bop.bvadd t1 t2)).
    Hypothesis (pbvsub : ∀ n (t1 t2 : Term Σ (ty.bvec n)), P t1 → P t2 → P (term_binop bop.bvsub t1 t2)).
    Hypothesis (pbvmul : ∀ n (t1 t2 : Term Σ (ty.bvec n)), P t1 → P t2 → P (term_binop bop.bvmul t1 t2)).
    Hypothesis (pbvand : ∀ n (t1 t2 : Term Σ (ty.bvec n)), P t1 → P t2 → P (term_binop bop.bvand t1 t2)).
    Hypothesis (pbvor : ∀ n (t1 t2 : Term Σ (ty.bvec n)), P t1 → P t2 → P (term_binop bop.bvor t1 t2)).
    Hypothesis (pbvxor : ∀ n (t1 t2 : Term Σ (ty.bvec n)), P t1 → P t2 → P (term_binop bop.bvxor t1 t2)).
    Hypothesis (pshiftr : ∀ n m (t1 : Term Σ (ty.bvec n)) (t2 : Term Σ (ty.bvec m)), P t1 → P t2 → P (term_binop bop.shiftr t1 t2)).
    Hypothesis (pshiftl : ∀ n m (t1 : Term Σ (ty.bvec n)) (t2 : Term Σ (ty.bvec m)), P t1 → P t2 → P (term_binop bop.shiftl t1 t2)).
    Hypothesis (pbvapp : ∀ m n (t1 : Term Σ (ty.bvec m)) (t2 : Term Σ (ty.bvec n)), P t1 → P t2 → P (term_binop bop.bvapp t1 t2)).
    Hypothesis (pbvcons : ∀ n (t1 : Term Σ ty.bool) (t2 : Term Σ (ty.bvec n)), P t2 → P (term_binop bop.bvcons t1 t2)).
    Hypothesis (pupdate_subrange :
                 ∀ {s l m} (p : IsTrue (s + l <=? m))
                   (t1 : Term Σ (ty.bvec m)) (t2 : Term Σ (ty.bvec l)),
                  P t1 → P t2 → P (term_binop (bop.update_vector_subrange s l) t1 t2)).
    Hypothesis (pbvnot : ∀ n (t : Term Σ (ty.bvec n)), P t → P (term_unop uop.bvnot t)).
    Hypothesis (pnegate : ∀ n (t : Term Σ (ty.bvec n)), P t → P (term_unop uop.negate t)).
    Hypothesis (psext : ∀ n m (pf : IsTrue (m <=? n)) (t : Term Σ (ty.bvec m)), P t → P (term_unop (uop.sext (p := pf)) t)).
    Hypothesis (pzext : ∀ n m (pf : IsTrue (m <=? n)) (t : Term Σ (ty.bvec m)), P t → P (term_unop (uop.zext (p := pf)) t)).
    Hypothesis (pgetslice : ∀ n (t : Term Σ ty.int), P (term_unop (uop.get_slice_int (n := n)) t)).
    Hypothesis (ptruncate : ∀ n m (pf : IsTrue (n <=? m)) (t : Term Σ (ty.bvec m)), P t → P (term_unop (uop.truncate n) t)).
    Hypothesis (psubrange : ∀ s l m (pf : IsTrue (s + l <=? m)) (t : Term Σ (ty.bvec m)), P t → P (term_unop (uop.vector_subrange s l) t)).
    Hypothesis (pbvdrop : ∀ m n (t : Term Σ (ty.bvec (m + n))), P t → P (term_unop (uop.bvdrop m) t)).
    Hypothesis (pbvtake : ∀ m n (t : Term Σ (ty.bvec (m + n))), P t → P (term_unop (uop.bvtake m) t)).

    Fixpoint Term_bvec_rect [n : nat] (t : Term Σ (ty.bvec n)) {struct t} : P t :=
      Term_bvec_case P
        (ltac:(intros; apply pvar))
        (ltac:(intros; apply pval))
        (ltac:(intros; apply pbvadd; auto))
        (ltac:(intros; apply pbvsub; auto))
        (ltac:(intros; apply pbvmul; auto))
        (ltac:(intros; apply pbvand; auto))
        (ltac:(intros; apply pbvor; auto))
        (ltac:(intros; apply pbvxor; auto))
        (ltac:(intros; apply pshiftr; auto))
        (ltac:(intros; apply pshiftl; auto))
        (ltac:(intros; apply pbvapp; auto))
        (ltac:(intros; apply pbvcons; auto))
        (ltac:(intros; apply pupdate_subrange; auto))
        (ltac:(intros; apply pbvnot; auto))
        (ltac:(intros; apply pnegate; auto))
        (ltac:(intros; apply psext; auto))
        (ltac:(intros; apply pzext; auto))
        (ltac:(intros; apply pgetslice; auto))
        (ltac:(intros; apply ptruncate; auto))
        (ltac:(intros; apply psubrange; auto))
        (ltac:(intros; apply pbvdrop; auto))
        (ltac:(intros; apply pbvtake; auto))
        t.

  End Term_bvec_rect.

  Section Term_tuple_case.

    Context {Σ σs} (P : Term Σ (ty.tuple σs) → Type).

    Hypothesis (pvar : ∀ (l : LVar) (lIn : l∷ty.tuple σs ∈ Σ), P (term_var l)).
    Hypothesis (pval : ∀ (v : Val (ty.tuple σs)), P (term_val (ty.tuple σs) v)).
    Hypothesis (ptuple : ∀ (ts : Env (Term Σ) σs), P (term_tuple ts)).

    Definition Term_tuple_case (t : Term Σ (ty.tuple σs)) : P t :=
      match t as t' in Term _ s return cases.motive_tuple (Term Σ) σs P s t' with
      | @term_var _ l s lIn => cases.intro_tuple _ σs P (@term_var Σ l) (@pvar l) s lIn
      | term_val s v        => cases.intro_tuple _ σs P (@term_val Σ) pval s v
      | term_binop op t1 t2 => cases.binop_tuple _ σs P (@term_binop Σ) _ _ _ op t1 t2
      | term_unop op t      => cases.unop_tuple _ σs P (@term_unop Σ) _ _ op t
      | @term_tuple _ τs ts => cases.ctor_tuple _ σs P (@term_tuple Σ) ptuple τs ts
      | _                   => tt
      end eq_refl.

  End Term_tuple_case.

  Section Term_union_case.

    Context {Σ U} (P : Term Σ (ty.union U) → Type).

    Hypothesis (pvar : ∀ (l : LVar) (lIn : l∷ty.union U ∈ Σ), P (term_var l)).
    Hypothesis (pval : ∀ (v : Val (ty.union U)), P (term_val (ty.union U) v)).
    Hypothesis (punion : ∀ K (t : Term Σ (unionk_ty U K)), P (term_union U K t)).

    Definition Term_union_case (t : Term Σ (ty.union U)) : P t :=
      match t as t' in Term _ s return cases.motive_union (Term Σ) U P s t' with
      | @term_var _ l s lIn => cases.intro_union _ U P (@term_var Σ l) (@pvar l) s lIn
      | term_val s v        => cases.intro_union _ U P (@term_val Σ) pval s v
      | term_binop op t1 t2 => cases.binop_union _ U P (@term_binop Σ) _ _ _ op t1 t2
      | term_unop op t      => cases.unop_union _ U P (@term_unop Σ) _ _ op t
      | term_union V K t    => cases.ctor_union _ U P (@term_union Σ) punion V K t
      | _                   => tt
      end eq_refl.

  End Term_union_case.

  Section Term_record_case.

    Context {Σ R} (P : Term Σ (ty.record R) → Type).

    Variable (pvar : ∀ (l : LVar) (lIn : l∷ty.record R ∈ Σ), P (term_var l)).
    Variable (pval : ∀ (v : Val (ty.record R)), P (term_val (ty.record R) v)).
    Variable (precord : ∀ (ts : NamedEnv (Term Σ) (recordf_ty R)), P (term_record R ts)).

    Definition Term_record_case (t : Term Σ (ty.record R)) : P t :=
      match t as t' in Term _ s return cases.motive_record (Term Σ) R P s t' with
      | @term_var _ l s lIn => cases.intro_record _ R P (@term_var Σ l) (@pvar l) s lIn
      | term_val s v        => cases.intro_record _ R P (@term_val Σ) pval s v
      | term_binop op t1 t2 => cases.binop_record _ R P (@term_binop Σ) _ _ _ op t1 t2
      | term_unop op t      => cases.unop_record _ R P (@term_unop Σ) _ _ op t
      | term_record R' ts   => cases.ctor_record _ R P (@term_record Σ) precord R' ts
      | _                   => tt
      end eq_refl.

  End Term_record_case.

  (* We define some specialized view for certain types to make
     recusion over terms easier. *)
  Section TermView.
    Local Set Elimination Schemes.

    (* A view on list terms. *)
    Inductive ListView {Σ σ} : Term Σ (ty.list σ) → Type :=
    | term_list_var {ς} {ςInΣ : (ς∷ty.list σ) ∈ Σ} :
      ListView (term_var ς)
    | term_list_val v :
      ListView (term_val _ v)
    | term_list_cons h {t} (lv : ListView t) :
      ListView (term_binop bop.cons h t)
    | term_list_append {t1 t2} (lv1 : ListView t1) (lv2 : ListView t2) :
      ListView (term_binop bop.append t1 t2)
    | term_list_rev t (lv : ListView t) :
      ListView (term_unop uop.rev t).
    #[global] Arguments term_list_var {Σ σ} ς {ςInΣ}.
    #[global] Arguments term_list_append {Σ σ} [t1 t2] lv1 lv2.

    (* We map each type to a specialized view for that type. *)
    Definition View {Σ} (σ : Ty) : Term Σ σ → Type :=
      match σ with
      | ty.list τ => ListView
      | _         => fun _ => unit
      end.

    Definition view_var {Σ l σ} : ∀ lIn, View (@term_var Σ l σ lIn) :=
      match σ with
       | ty.list σ => @term_list_var _ _ l
       | _         => fun _ => tt
       end.

    Definition view_val {Σ σ} : ∀ v, View (@term_val Σ σ v) :=
      match σ with
      | ty.list σ0 => term_list_val
      | _          => fun _ => tt
      end.

    Definition view_binop {Σ σ1 σ2 σ3} (op : BinOp σ1 σ2 σ3) :
      ∀ {t1 : Term Σ σ1} {t2 : Term Σ σ2},
        View t1 → View t2 → View (term_binop op t1 t2) :=
       match op with
       | bop.cons   => fun t1 t2 _  v2 => term_list_cons t1 v2
       | bop.append => term_list_append
       | _ => fun _ _ _ _ => tt
       end.

    Definition view_unop {Σ σ1 σ2} (op : UnOp σ1 σ2) :
      ∀ {t : Term Σ σ1}, View t → View (term_unop op t) :=
    match op with
      | uop.rev => term_list_rev
      | _ => fun _ _ => tt
      end.

    (* Construct a view for each term. *)
    Fixpoint view {Σ σ} (t : Term Σ σ) {struct t} : View t :=
      match t as t1 in (Term _ t0) return (View t1) with
      | term_var ς          => view_var _
      | term_val _ v        => view_val v
      | term_binop op t1 t2 => view_binop op (view t1) (view t2)
      | term_unop op t      => view_unop op (view t)
      | _                   => tt
      end.

  End TermView.

  Section Equality.

    Open Scope lazy_bool_scope.

    Context {Σ : LCtx}.

    Equations(noeqns) Term_eqb [σ] (t1 t2 : Term Σ σ) : bool :=
      Term_eqb (@term_var _ _ ς1inΣ) (@term_var _ _ ς2inΣ) :=
        ctx.In_eqb ς1inΣ ς2inΣ;
      Term_eqb (term_val _ v1) (term_val _ v2) :=
        if eq_dec v1 v2 then true else false;
      Term_eqb (term_binop op1 x1 y1) (term_binop op2 x2 y2)
        with bop.eqdep_dec op1 op2 => {
        Term_eqb (term_binop op1 x1 y1) (term_binop ?(op1) x2 y2) (left bop.opeq_refl) :=
          Term_eqb x1 x2 &&& Term_eqb y1 y2;
        Term_eqb (term_binop op1 x1 y1) (term_binop op2 x2 y2) (right _) := false
      };
      Term_eqb (term_unop op1 t1) (term_unop op2 t2) with uop.tel_eq_dec op1 op2 => {
        Term_eqb (term_unop op1 t1) (term_unop ?(op1) t2) (left eq_refl) :=
          Term_eqb t1 t2;
        Term_eqb (term_unop op1 t1) (term_unop op2 t2) (right _) := false;
      };
      Term_eqb (@term_tuple ?(σs) xs) (@term_tuple σs ys) :=
        @env.eqb_hom _ (Term Σ) Term_eqb _ xs ys;
      Term_eqb (@term_union ?(u) _ k1 e1) (@term_union u _ k2 e2)
        with eq_dec k1 k2 => {
        Term_eqb (term_union k1 e1) (term_union ?(k1) e2) (left eq_refl) :=
          Term_eqb e1 e2;
        Term_eqb _ _ (right _) := false
      };
      Term_eqb (@term_record ?(r) xs) (@term_record r ys) :=
        @env.eqb_hom _ (fun b => Term Σ (type b)) (fun b => @Term_eqb (type b)) _ xs ys;
      Term_eqb _ _ := false.

    #[local] Set Equations With UIP.

    Lemma Term_eqb_spec (σ : Ty) (t1 t2 : Term Σ σ) :
      reflect (t1 = t2) (Term_eqb t1 t2).
    Proof.
      induction t1 using Term_rect; cbn [Term_eqb]; dependent elimination t2;
        solve_eqb_spec with
        repeat match goal with
            | |- context[eq_dec ?l1 ?l2] => destruct (eq_dec l1 l2)
            | |- context[bop.eqdep_dec ?x ?y] =>
                let e := fresh in
                destruct (bop.eqdep_dec x y) as [e|];
                [dependent elimination e|]
            | |- context[uop.tel_eq_dec ?x ?y] =>
                let e := fresh in
                destruct (uop.tel_eq_dec x y) as [e|];
                [dependent elimination e|]
            | H: ~ bop.OpEq ?o ?o |- False => apply H; constructor
            | |- reflect (term_tuple ?ts1 = term_tuple ?ts2) _ =>
                apply (@ssrbool.iffP (ts1 = ts2))
            | |- reflect (term_record ?R ?ts1 = term_record ?R ?ts2) _ =>
                apply (@ssrbool.iffP (ts1 = ts2))
            | |- reflect (?ts1 = ?ts2) (env.eqb_hom _ ?ts1 ?ts2) =>
                apply env.eqb_hom_spec_point
            end; auto.
    Qed.

  End Equality.

  Section Symbolic.

    Polymorphic Definition List (A : LCtx → Type) (Σ : LCtx) : Type :=
      list (A Σ).
    Polymorphic Definition Const (A : Type) (Σ : LCtx) : Type :=
      A.

  End Symbolic.

  Section SymbolicSubstitutions.

    Definition Sub (Σ1 Σ2 : LCtx) : Set :=
      Env (fun b => Term Σ2 (type b)) Σ1.
    (* Hint Unfold Sub. *)

    Class Subst (T : LCtx → Type) : Type :=
      subst : ∀ {Σ1 : LCtx}, T Σ1 → ∀ {Σ2 : LCtx}, Sub Σ1 Σ2 → T Σ2.
    #[global] Arguments subst {T _ Σ1} t {Σ2} ζ.

    Fixpoint sub_term {σ Σ1} (t : Term Σ1 σ) {Σ2} (ζ : Sub Σ1 Σ2) {struct t} : Term Σ2 σ :=
      match t with
      | term_var ς                 => ζ.[??ς]
      | term_val σ v               => term_val σ v
      | term_binop op t1 t2        => term_binop op (sub_term t1 ζ) (sub_term t2 ζ)
      | term_unop op t             => term_unop op (sub_term t ζ)
      | term_tuple ts              => term_tuple (env.map (fun _ t => sub_term t ζ) ts)
      | term_union U K t           => term_union U K (sub_term t ζ)
      | term_record R ts           => term_record R (env.map (fun _ t => sub_term t ζ) ts)
      end.

    #[export] Instance SubstTerm {σ} : Subst (fun Σ => Term Σ σ) :=
      @sub_term σ.
    #[export,universes(polymorphic=yes)] Instance SubstList {A} `{Subst A} : Subst (List A) :=
      fix substlist {Σ1} xs {Σ2} ζ :=
        match xs with
        | nil => nil
        | cons x xs => cons (subst x ζ) (substlist xs ζ)
        end.

    Lemma substlist_is_map_subst {A} `{Subst A} {Σ1 Σ2} (xs : List A Σ1) (ζ : Sub Σ1 Σ2) :
      subst xs ζ = List.map (fun x => subst x ζ) xs.
    Proof. induction xs; cbn; f_equal; auto. Qed.

    #[export,universes(polymorphic=yes)] Instance SubstConst {A} : Subst (Const A) | 10 :=
       fun _ x _ _ => x.
    #[export] Instance SubstEnv {B : Set} {A : Ctx _ → B → Set} `{∀ b, Subst (fun Σ => A Σ b)} {Δ : Ctx B} :
      Subst (fun Σ => Env (A Σ) Δ) :=
      fun Σ1 xs Σ2 ζ => env.map (fun b a => subst (T := fun Σ => A Σ b) a ζ) xs.

    Definition sub_id Σ : Sub Σ Σ :=
      @env.tabulate _ (fun b => Term _ (type b)) _
                    (fun '(ς∷σ) ςIn => @term_var Σ ς σ ςIn).
    #[global] Arguments sub_id : clear implicits.

    Definition sub_snoc {Σ1 Σ2 : LCtx} (ζ : Sub Σ1 Σ2) b (t : Term Σ2 (type b)) :
      Sub (Σ1 ▻ b) Σ2 := env.snoc ζ b t.
    #[global] Arguments sub_snoc {_ _} _ _ _.

    Definition sub_shift {Σ b} (bIn : b ∈ Σ) : Sub (Σ - b) Σ :=
      env.tabulate
        (D := fun b => Term Σ (type b))
        (fun '(x∷τ) xIn => @term_var Σ x τ (ctx.shift_var bIn xIn)).

    Definition sub_wk1 {Σ b} : Sub Σ (Σ ▻ b) :=
      env.tabulate
        (D := fun b => Term _ (type b))
        (fun '(ς∷σ) ςIn => @term_var _ ς σ (ctx.in_succ ςIn)).

    Definition sub_cat_left {Σ} Δ : Sub Σ (Σ ▻▻ Δ) :=
      env.tabulate
        (D := fun b => Term _ (type b))
        (fun '(ς∷σ) ςIn => @term_var _ ς σ (ctx.in_cat_left Δ ςIn)).

    Definition sub_cat_right {Σ} Δ : Sub Δ (Σ ▻▻ Δ) :=
      env.tabulate
        (D := fun b => Term _ (type b))
        (fun '(ς∷σ) ςIn => @term_var _ ς σ (ctx.in_cat_right ςIn)).

    Definition sub_up1 {Σ1 Σ2} (ζ : Sub Σ1 Σ2) {b} : Sub (Σ1 ▻ b) (Σ2 ▻ b) :=
      sub_snoc (subst ζ sub_wk1) b (let '(ς∷σ) := b in @term_var _ ς σ ctx.in_zero).

    Definition sub_up {Σ1 Σ2} (ζ : Sub Σ1 Σ2) Δ : Sub (Σ1 ▻▻ Δ) (Σ2 ▻▻ Δ) :=
      subst ζ (sub_cat_left Δ) ►► sub_cat_right Δ.

    Definition sub_single {Σ x} (xIn : x ∈ Σ) (t : Term (Σ - x) (type x)) : Sub Σ (Σ - x) :=
       @env.tabulate _
         (fun b => Term (Σ - x) (@type _ _ b)) Σ
         (fun y (yIn : y ∈ Σ) =>
            match ctx.occurs_check_view xIn yIn
            in @ctx.OccursCheckView _ _ _ _ y i
            return Term (Σ - x) (@type _ _ y)
            with
            | ctx.Same _     => t
            | ctx.Diff _ yIn => @term_var _ _ _ yIn
            end).

    Class SubstLaws (T : LCtx → Type) `{Subst T} : Type :=
      { subst_sub_id Σ (t : T Σ) :
          subst t (sub_id _) = t;
        subst_sub_comp Σ0 Σ1 Σ2 (ζ1 : Sub Σ0 Σ1) (ζ2 : Sub Σ1 Σ2) t :
          subst t (subst ζ1 ζ2) = subst (subst t ζ1) ζ2;
      }.

    #[global] Arguments SubstLaws T {_}.

    #[export] Instance SubstLawsTerm {σ} : SubstLaws (fun Σ => Term Σ σ).
    Proof.
      constructor.
      { intros ? t.
        induction t; cbn; f_equal; try assumption.
        - unfold sub_id. now rewrite env.lookup_tabulate.
        - induction IH; cbn; f_equal; auto.
        - induction IH; cbn; f_equal; auto.
      }
      { intros ? ? ? ? ? t.
        induction t; cbn; f_equal; try assumption.
        - unfold subst at 1, SubstEnv. now rewrite env.lookup_map.
        - induction IH; cbn; f_equal; auto.
        - induction IH; cbn; f_equal; auto.
      }
    Qed.

    #[export,universes(polymorphic=yes)] Instance SubstLawsList {A} `{SubstLaws A} : SubstLaws (List A).
    Proof.
      constructor.
      { intros ? t.
        induction t; cbn; f_equal; auto using subst_sub_id.
      }
      { intros ? ? ? ? ? t.
        induction t; cbn; f_equal; auto using subst_sub_comp.
      }
    Qed.

    #[export,universes(polymorphic=yes)] Instance SubstLawsConst {A} : SubstLaws (Const A).
    Proof. constructor; reflexivity. Qed.

    #[export] Instance SubstLawsEnv {B : Set} {A : Ctx _ → B → Set}
      `{∀ b, Subst (fun Σ => A Σ b), ∀ b, SubstLaws (fun Σ => A Σ b)}
      {Δ : Ctx B} :
      SubstLaws (fun Σ => Env (A Σ) Δ).
    Proof.
      constructor.
      { intros ? t.
        induction t; cbn; f_equal; auto using subst_sub_id.
      }
      { intros ? ? ? ? ? t.
        induction t; cbn; f_equal; auto using subst_sub_comp.
      }
    Qed.

    #[export] Instance subst_ctx `{Subst A} : Subst (fun Σ => Ctx (A Σ)) :=
      fix subst_ctx {Σ} xs {Σ'} ζ {struct xs} :=
        match xs with
        | ctx.nil       => ctx.nil
        | ctx.snoc xs x => ctx.snoc (subst_ctx xs ζ) (subst x ζ)
        end.

    #[export] Instance substlaws_ctx `{SubstLaws A} : SubstLaws (fun Σ => Ctx (A Σ)).
    Proof.
      constructor.
      - intros ? xs. induction xs; cbn; f_equal; auto; apply subst_sub_id.
      - intros ? ? ? ? ? xs; induction xs; cbn; f_equal; auto; apply subst_sub_comp.
    Qed.

  End SymbolicSubstitutions.

  Module SubNotations.

    Notation "a ⟨ ζ ⟩" := (subst a ζ).
    Notation "ζ1 ∘ ζ2" := (@subst (Sub _) _ _ ζ1 _ ζ2).

  End SubNotations.

  Section InfrastructureLemmas.

    Lemma lookup_sub_id {Σ x σ} (xIn : x∷σ ∈ Σ) :
      env.lookup (sub_id _) xIn = term_var x.
    Proof. unfold sub_id; now rewrite env.lookup_tabulate. Qed.

    Lemma lookup_sub_comp {Σ0 Σ1 Σ2 x} (xIn : x ∈ Σ0) (ζ1 : Sub Σ0 Σ1) (ζ2 : Sub Σ1 Σ2) :
      env.lookup (subst ζ1 ζ2) xIn = subst (env.lookup ζ1 xIn) ζ2.
    Proof.
      unfold subst at 1, SubstEnv.
      now rewrite env.lookup_map.
    Qed.

    Lemma lookup_sub_wk1 {Σ x σ b} (xIn : x∷σ ∈ Σ) :
      env.lookup (@sub_wk1 Σ b) xIn = @term_var _ _ _ (ctx.in_succ xIn).
    Proof. unfold sub_wk1; now rewrite env.lookup_tabulate. Qed.

    Lemma lookup_sub_shift {Σ x σ b} (bIn : b ∈ Σ) (xIn : x∷σ ∈ (Σ - b)) :
      env.lookup (@sub_shift Σ b bIn) xIn = @term_var Σ x σ (ctx.shift_var bIn xIn).
    Proof. unfold sub_shift; now rewrite env.lookup_tabulate. Qed.

    Lemma lookup_sub_single_eq {Σ x σ} (xIn : x∷σ ∈ Σ) (t : Term (Σ - x∷σ) σ) :
      env.lookup (sub_single xIn t) xIn = t.
    Proof. unfold sub_single. now rewrite env.lookup_tabulate, ctx.occurs_check_view_refl. Qed.

    Lemma lookup_sub_single_neq {Σ x σ y τ} (xIn : x ∷ σ ∈ Σ) (t : Term (Σ - x∷σ) σ) (yIn : y∷τ ∈ Σ - x∷σ) :
      env.lookup (sub_single xIn t) (ctx.shift_var xIn yIn) = term_var y.
    Proof. unfold sub_single. now rewrite env.lookup_tabulate, ctx.occurs_check_view_shift. Qed.

    Lemma sub_comp_id_left {Σ0 Σ1} (ζ : Sub Σ0 Σ1) :
      subst (sub_id Σ0) ζ = ζ.
    Proof.
      apply env.lookup_extensional; intros [x σ] *.
      now rewrite lookup_sub_comp, lookup_sub_id.
    Qed.

    Lemma sub_comp_id_right {Σ0 Σ1} (ζ : Sub Σ0 Σ1) :
      subst ζ (sub_id Σ1) = ζ.
    Proof.
      apply subst_sub_id.
    Qed.

    Lemma sub_comp_assoc {Σ0 Σ1 Σ2 Σ3} (ζ1 : Sub Σ0 Σ1) (ζ2 : Sub Σ1 Σ2) (ζ3 : Sub Σ2 Σ3) :
      subst (subst ζ1 ζ2) ζ3 = subst ζ1 (subst ζ2 ζ3).
    Proof. now rewrite subst_sub_comp. Qed.

    Lemma sub_comp_wk1_tail {Σ0 Σ1 b} (ζ : Sub (Σ0 ▻ b) Σ1) :
      subst sub_wk1 ζ = env.tail ζ.
    Proof.
      apply env.lookup_extensional. intros [x σ] *.
      rewrite lookup_sub_comp, lookup_sub_wk1.
      now destruct (env.view ζ) as [ζ t].
    Qed.

    Lemma sub_comp_shift {Σ0 Σ1 b} (bIn : b ∈ Σ0) (ζ : Sub Σ0 Σ1) :
      subst (sub_shift bIn) ζ = env.remove b ζ bIn.
    Proof.
      rewrite env.remove_remove'. unfold env.remove'.
      apply env.lookup_extensional. intros [x σ] xIn.
      now rewrite lookup_sub_comp, lookup_sub_shift, env.lookup_tabulate.
    Qed.

    Lemma sub_shift_succ {Σ b b'} (bIn : b ∈ Σ) :
      sub_up1 (b := b') (sub_shift bIn) = sub_shift (ctx.in_succ bIn).
    Proof.
      apply env.lookup_extensional; intros.
      destruct (ctx.view bInΓ); first easy.
      cbn -[env.tabulate].
      rewrite lookup_sub_comp, lookup_sub_shift.
      destruct b0 as [x0 τ0].
      change (ctx.snoc (ctx.remove bIn) b') with
        (ctx.remove (ctx.in_succ (b' := b') bIn)).
      rewrite (lookup_sub_shift (ctx.in_succ (b' := b') bIn) (ctx.in_succ (b := x0∷τ0) i)).
      cbn.
      now rewrite lookup_sub_wk1.
    Qed.

    Lemma sub_comp_wk1_comm {Σ0 Σ1 b} (ζ : Sub Σ0 Σ1) :
      subst sub_wk1 (sub_up1 ζ) = subst ζ (sub_wk1 (b:=b)).
    Proof. now rewrite sub_comp_wk1_tail. Qed.

    Lemma sub_snoc_comp {Σ1 Σ2 Σ3 x τ v} (ζ1 : Sub Σ1 Σ2) (ζ2 : Sub Σ2 Σ3) :
      (subst ζ1 ζ2) ► (x∷τ ↦ v) =
      subst (sub_up1 ζ1) (ζ2 ► (x∷τ ↦ v)).
    Proof.
      unfold sub_up1, subst, SubstEnv; cbn.
      rewrite env.map_map. f_equal.
      apply env.map_ext. intros.
      now rewrite <- subst_sub_comp, sub_comp_wk1_tail.
    Qed.

    Lemma sub_up1_comp {Σ0 Σ1 Σ2} (ζ1 : Sub Σ0 Σ1) (ζ2 : Sub Σ1 Σ2) b :
      sub_up1 (b:=b) (subst ζ1 ζ2) = subst (sub_up1 ζ1) (sub_up1 ζ2).
    Proof.
      destruct b as [x σ]. DepElim.hnf_eq. f_equal.
      change (subst (subst ζ1 ζ2) (sub_wk1 (b:=x∷σ)) = subst (subst ζ1 sub_wk1) (sub_up1 ζ2)).
      now rewrite ?sub_comp_assoc, ?sub_comp_wk1_comm.
    Qed.

    Lemma sub_comp_shift_single {Σ x σ} (xIn : x∷σ ∈ Σ) (t : Term (Σ - x∷σ) σ) :
      subst (sub_shift xIn) (sub_single xIn t) = sub_id _.
    Proof.
      apply env.lookup_extensional. intros [y τ] yIn.
      rewrite lookup_sub_id, lookup_sub_comp, lookup_sub_shift. cbn.
      now rewrite lookup_sub_single_neq.
    Qed.

    Lemma sub_up1_id {Σ x} : sub_up1 (sub_id Σ) = sub_id (Σ ▻ x).
    Proof.
      destruct x as [x σ].
      unfold sub_up1.
      rewrite sub_comp_id_left.
      apply env.lookup_extensional. intros y yIn.
      destruct (ctx.view yIn) as [|[y τ] yIn].
      - reflexivity.
      - rewrite lookup_sub_id. cbn.
        now rewrite lookup_sub_wk1.
    Qed.

    Lemma sub_comp_cat_right {Σ1 Σ2 Σ} (ζ1 : Sub Σ1 Σ) (ζ2 : Sub Σ2 Σ) :
      subst (sub_cat_right Σ2) (ζ1 ►► ζ2) = ζ2.
    Proof.
      apply env.lookup_extensional. intros [x σ] xIn.
      unfold sub_cat_right. unfold subst, SubstEnv.
      rewrite env.lookup_map, env.lookup_tabulate. cbn.
      now rewrite env.lookup_cat_right.
    Qed.

    Lemma sub_comp_cat_left {Σ1 Σ2 Σ} (ζ1 : Sub Σ1 Σ) (ζ2 : Sub Σ2 Σ) :
      subst (sub_cat_left Σ2) (ζ1 ►► ζ2) = ζ1.
    Proof.
      apply env.lookup_extensional. intros [x σ] xIn.
      unfold sub_cat_left. unfold subst, SubstEnv.
      rewrite env.lookup_map, env.lookup_tabulate. cbn.
      now rewrite env.lookup_cat_left.
    Qed.

    Lemma subst_shift_single {AT} `{SubstLaws AT} {Σ x σ} (xIn : x∷σ ∈ Σ) (a : AT (Σ - x∷σ)) (t : Term (Σ - x∷σ) σ) :
      subst (subst a (sub_shift xIn)) (sub_single xIn t) = a.
    Proof. now rewrite <- subst_sub_comp, sub_comp_shift_single, subst_sub_id. Qed.

    Lemma subst_wk1_snoc {AT} `{SubstLaws AT} {Σ1 Σ2 b} (a : AT _) (t : Term Σ2 (type b)) (ζ : Sub Σ1 Σ2) :
      subst (subst a sub_wk1) (sub_snoc ζ b t) = subst a ζ.
    Proof. now rewrite <- subst_sub_comp, sub_comp_wk1_tail. Qed.

  End InfrastructureLemmas.

  Section SymbolicPair.

    Definition Pair (A B : LCtx → Type) (Σ : LCtx) : Type :=
      A Σ * B Σ.
    #[export] Instance SubstPair {A B} `{Subst A, Subst B} : Subst (Pair A B) :=
      fun _ '(a,b) _ ζ => (subst a ζ, subst b ζ).

    #[export] Instance SubstLawsPair {A B} `{SubstLaws A, SubstLaws B} : SubstLaws (Pair A B).
    Proof.
      constructor.
      { intros ? [t1 t2]; cbn.
        f_equal; apply subst_sub_id.
      }
      { intros ? ? ? ? ? [t1 t2]; cbn.
        f_equal; apply subst_sub_comp.
      }
    Qed.

  End SymbolicPair.

  Section SymbolicOption.

    Definition Option (A : LCtx → Type) (Σ : LCtx) : Type :=
      option (A Σ).
    #[export] Instance SubstOption {A} `{Subst A} : Subst (Option A) :=
      fun _ ma _ ζ => option_map (fun a => subst a ζ) ma.

    #[export] Instance SubstLawsOption {A} `{SubstLaws A} : SubstLaws (Option A).
    Proof.
      constructor.
      { intros ? [t|]; cbn; f_equal; apply subst_sub_id. }
      { intros ? ? ? ? ? [t|]; cbn; f_equal; apply subst_sub_comp. }
    Qed.


  End SymbolicOption.

  Section SymbolicUnit.

    Definition Unit : LCtx → Type := fun _ => unit.
    #[export] Instance SubstUnit : Subst Unit :=
      fun _ t _ _ => t.
    #[export] Instance SubstLawsUnit : SubstLaws Unit.
    Proof. constructor; reflexivity. Qed.

  End SymbolicUnit.

  Section SymbolicStore.

    Definition SStore (Γ : PCtx) (Σ : LCtx) : Type :=
      NamedEnv (Term Σ) Γ.

    #[export] Instance subst_localstore {Γ} : Subst (SStore Γ) :=
      SubstEnv.
    #[export] Instance substlaws_localstore {Γ} : SubstLaws (SStore Γ) :=
      SubstLawsEnv.

    Lemma subst_lookup {Γ Σ Σ' x σ} (xInΓ : x∷σ ∈ Γ) (ζ : Sub Σ Σ') (δ : SStore Γ Σ) :
      subst δ.[?? x] ζ = (subst δ ζ).[?? x].
    Proof.
      unfold subst at 2, subst_localstore, SubstEnv.
      now rewrite env.lookup_map.
    Qed.

  End SymbolicStore.
  Bind Scope env_scope with SStore.

  Module TermNotations.
    Open Scope term_scope.

    (* BinOp *)
    Notation "e1 + e2" := (term_plus e1 e2) : term_scope.
    Notation "e1 * e2" := (term_times e1 e2) : term_scope.
    Notation "e1 - e2" := (term_minus e1 e2) : term_scope.
    Notation "e1 && e2" := (term_and e1 e2) : term_scope.
    Notation "e1 || e2" := (term_or e1 e2) : term_scope.
    Notation "e1 :: e2" := (term_cons e1 e2) : term_scope.
    Notation "e1 ++ e2" := (term_append e1 e2) : term_scope.
    Notation "e1 +ᵇ e2" := (term_bvadd e1 e2) : term_scope.
    Notation "e1 -ᵇ e2" := (term_bvsub e1 e2) : term_scope.
    Notation "e1 *ᵇ e2" := (term_bvmul e1 e2) : term_scope.

    (* RelOp *)
    Notation "e1 >= e2" := (term_le e2 e1) (only parsing) : term_scope.
    Notation "e1 > e2" := (term_lt e2 e1) (only parsing) : term_scope.
    Notation "e1 <= e2" := (term_le e1 e2) : term_scope.
    Notation "e1 < e2" := (term_lt e1 e2) : term_scope.

    Notation "e1 >=ˢ e2" := (term_bvsle e2 e1) (only parsing) : term_scope.
    Notation "e1 >ˢ e2" := (term_bvslt e2 e1) (only parsing) : term_scope.
    Notation "e1 <ˢ e2" := (term_bvslt e1 e2) : term_scope.
    Notation "e1 <=ˢ e2" := (term_bvsle e1 e2) : term_scope.

    Notation "e1 >=ᵘ e2" := (term_bvule e2 e1) (only parsing) : term_scope.
    Notation "e1 >ᵘ e2" := (term_bvult e2 e1) (only parsing) : term_scope.
    Notation "e1 <=ᵘ e2" := (term_bvule e1 e2) : term_scope.
    Notation "e1 <ᵘ e2" := (term_bvult e1 e2) : term_scope.

    (* Note: this uses ?= rather than = to avoid overlap with the notation for an equality assertion... *)
    Notation "e1 ?= e2" := (term_eq e1 e2) : term_scope.
    Notation "e1 != e2" := (term_neq e1 e2) : term_scope.
    Notation "- e" := (term_neg e) : term_scope.

  End TermNotations.

  Section Erasure.
    Inductive ETerm : Ty -> Set :=
    | eterm_var     (ℓ : LVar) (σ : Ty) (n : nat) : ETerm σ
    | eterm_val     (σ : Ty) (v : Val σ) : ETerm σ
    | eterm_binop   {σ1 σ2 σ3} (op : BinOp σ1 σ2 σ3) (t1 : ETerm σ1) (t2 : ETerm σ2) : ETerm σ3
    | eterm_unop    {σ1 σ2} (op : UnOp σ1 σ2) (t : ETerm σ1) : ETerm σ2
    | eterm_tuple   {σs : Ctx Ty} (ts : Env ETerm σs) : ETerm (ty.tuple σs)
    | eterm_union   {U : unioni} (K : unionk U) (t : ETerm (unionk_ty U K)) : ETerm (ty.union U)
    | eterm_record  (R : recordi) (ts : NamedEnv ETerm (recordf_ty R)) : ETerm (ty.record R).

    Definition erase_term {Σ} : forall {σ} (t : Term Σ σ), ETerm σ :=
      fix erase {σ} t :=
        match t with
        | @term_var _ ℓ σ ℓIn         => eterm_var ℓ σ (ctx.in_at ℓIn)
        | term_val σ v               => eterm_val σ v
        | term_binop op t1 t2        => eterm_binop op (erase t1) (erase t2)
        | term_unop op t             => eterm_unop op (erase t)
        | term_tuple ts              => eterm_tuple (env.map (fun _ => erase) ts)
        | term_union U K t           => eterm_union K (erase t)
        | term_record R ts           => eterm_record R (env.map (fun _ => erase) ts)
        end.

    Fixpoint erase_SStore {Γ Σ} (ts : SStore Γ Σ) : NamedEnv ETerm Γ :=
      match ts with
      | [env] => [env]
      | env.snoc ts b t => env.snoc (erase_SStore ts) b (erase_term t)
      end.
  End Erasure.

End TermsOn.
