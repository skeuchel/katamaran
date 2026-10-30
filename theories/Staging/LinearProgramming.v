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

From stdpp Require Import vector decidable numbers.

From Katamaran Require Import
     Base
     Prelude
     Syntax.Predicates
     Symbolic.Worlds
     VectorUtils.

From Stdlib Require Import Vector.

Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.
Local Set Equations Transparent.

Module Import VecUtils.

  Definition learnFinSucc {P : forall {n}, fin n -> Type} :
    (forall {n} (f : fin (S n)), P f) -> forall {n} (f : fin n), P f :=
    fun H n =>
      match n with
      | 0 => Fin.case0 _
      | S n => H _
      end.

  Lemma learnFinSucc_ind {M : forall {n}, fin n -> Type}
    (H : forall n (f : fin (S n)), M f)
    (P : forall {n} (f : fin n), M f -> Prop) :
    (forall {n} (f : fin (S n)), P f (H n f)) ->
    forall {n} (f : fin n), P f (learnFinSucc H f).
  Proof.
    intros HPf n [|f]; cbn; eapply HPf.
  Qed.

  Section DecideForall2.

    (* reimplemented for compatibility with Rocq 8.20 *)
    Lemma Forall2_cons_iff_copy {A B : Type} {P : A -> B -> Prop} {n h1 h2}
      {v1 : vec A n} {v2 : vec B n} :
      Forall2 P (h1 ::: v1) (h2 ::: v2) <->
      P h1 h2 /\ Forall2 P v1 v2.
    Proof.
      split.
      - intros H.
        inversion H as [| P2 x1 x2 v1p v2p HPx HPv ]; subst.
        split; first assumption.
        pose proof eq_sigT_snd H2.
        pose proof eq_sigT_snd H4.
        rewrite (Eqdep_dec.UIP_refl_nat n (eq_sigT_fst H2)) in H0.
        rewrite (Eqdep_dec.UIP_refl_nat n (eq_sigT_fst H4)) in H1.
        now cbn; subst.
      - now intros; constructor.
    Qed.

    Equations vec_forall2_dec {n A B} {R : A -> B -> Prop} {decR : forall x y, Decision (R x y)} (vs1 : vec A n) (vs2 : vec B n) :
      Decision (Vector.Forall2 R vs1 vs2) :=
    | [#] | [#] := left (Forall2_nil R)
    | v1 ::: vs1 | v2 ::: vs2 := match decR v1 v2 , vec_forall2_dec vs1 vs2 with
                                 | left Rv1v2 , left Rvs1vs2 => left (Forall2_cons R _ _ _ _ Rv1v2 Rvs1vs2)
                                 | right nRv1v2 , _ => right (fun Rvs => _)
                                 | _ , right nRvs1vs2 => right (fun Rvs => _)
                                 end
    .
    Next Obligation.
      now apply Forall2_cons_iff_copy in Rvs.
    Qed.
    Next Obligation.
      now apply Forall2_cons_iff_copy in Rvs.
    Qed.

    #[export] Instance forall2_dec {n A B} {R : A -> B -> Prop} {decR : forall x y, Decision (R x y)} :
      RelDecision (Vector.Forall2 R (n := n)) :=
      vec_forall2_dec.
  End DecideForall2.

  Lemma Forall2_vreplicate_left {n A B} {R : A -> B -> Prop} (a : A) (vs : vec B n) :
    Forall2 R (vreplicate _ a) vs <-> Forall (R a) vs.
  Proof.
    induction vs; first intuition constructor.
    cbn.
    rewrite Forall2_cons_iff_copy, Forall_cons_iff.
    now intuition.
  Qed.
End VecUtils.

Module Import PolyRed.
  (* simple Gauss elimination to upper triangular form *)

  Definition Poly n := vec Z (S n).
  Hint Transparent Poly : typeclass_instances.

  Definition zero {n} : vec Z n :=
    vreplicate _ 0%Z.
  Definition constant {n} (v : Z) : Poly n :=
    cons v zero.
  Definition var {n} (f : fin n) : Poly n :=
    vadd (FS f) 1%Z zero.

  Fixpoint findNonZero {n} (cs : vec Z n) : option (fin n) :=
    match cs with
    | [# ] => None
    | c ::: cs => if Z.eqb 0%Z c
                  then option.map Fin.FS (findNonZero cs)
                  else Some Fin.F1
    end.

  Lemma findNonZero_lookup {n} (cs : vec Z n) :
    option.spec (fun i => 0%Z <> lookup_total i cs)%ctx (cs = zero)
      (findNonZero cs).
  Proof.
    induction cs; first eauto using option.spec.
    cbn -[Z.eqb].
    destruct (Z.eqb_spec 0 h) as [<-|].
    - rewrite option.spec_map.
      revert IHcs.
      apply option.spec_monotonic;
        [easy | intros; now f_equal ].
    - auto using option.spec.
  Qed.

  #[global] Arguments findNonZero {n} cs : simpl never.

  Equations eval_polyp_vremove {n} (i : fin n) (v1 v2 : vec Z n) :
    dot (vremove i v1) (vremove i v2) = (dot v1 v2 - (v1 !!! i * v2 !!! i))%Z :=
  | 0%fin | h1 ::: v1 | h2 ::: v2 := _
  | FS 0%fin | h1 ::: v1 | h2 ::: v2 := _ (eval_polyp_vremove 0%fin v1 v2)
  | FS (FS i) | h1 ::: v1 | h2 ::: v2 := _ (eval_polyp_vremove (FS i) v1 v2)
  .
  Next Obligation. cbn. lia. Qed.
  Next Obligation. cbn. lia. Qed.
  Next Obligation. cbn. lia. Qed.

  Equations eval_polyp_vadd {n} a1 a2 (i : fin (S n)) (v1 v2 : vec Z n) :
    dot (vadd i a1 v1) (vadd i a2 v2) = (a1 * a2 + dot v1 v2)%Z :=
  | a1 | a2 | 0%fin | v1 | v2 := _
  | a1 | a2 | FS i | h1 ::: v1 | h2 ::: v2 := _ (eval_polyp_vadd a1 a2 i v1 v2)
  .
  Next Obligation. cbn; lia. Qed.

  Definition eval_poly {n} (coeffs : Poly n) (vs : vec Z n) : Z :=
    dot coeffs (1%Z ::: vs).
  Arguments eval_poly {n} coeffs vs : simpl never.

  Lemma eval_polyp_app {n1 n2} (coeffs1 : vec Z n1) (coeffs2 : vec Z n2) (vs1 : vec Z n1) (vs2 : vec Z n2) :
    dot (coeffs1 +++ coeffs2) (vs1 +++ vs2) = (dot coeffs1 vs1 + dot coeffs2 vs2)%Z.
  Proof.
    revert vs1; induction coeffs1 as [|c n coeffs1 IH]; intros vs1.
    - inv_vec vs1. cbn. lia.
    - inv_vec vs1; intros x vs1. cbn.
      rewrite IH. lia.
  Qed.

  Lemma eval_poly_app {n1 n2} (coeffs1 : Poly n1) (coeffs2 : vec Z n2) (vs1 : vec Z n1) (vs2 : vec Z n2) :
    eval_poly (coeffs1 +++ coeffs2) (vs1 +++ vs2) = (eval_poly coeffs1 vs1 + dot coeffs2 vs2)%Z.
  Proof.
    now eapply (eval_polyp_app _ _ (1%Z ::: vs1)).
  Qed.

  Lemma eval_polyp_mul {n} (coeffs : vec Z n) (vs : vec Z n) (c : Z) :
    dot (vmap (Z.mul c) coeffs) vs = (c * dot coeffs vs)%Z.
  Proof.
    revert coeffs; induction vs as [|x n vs IH]; intros coeffs.
    - inv_vec coeffs. cbn. lia.
    - inv_vec coeffs; intros c1 coeffs. cbn.
      rewrite IH. lia.
  Qed.

  Lemma eval_poly_mul {n} (coeffs : Poly n) (vs : vec Z n) (c : Z) :
    eval_poly (vmap (Z.mul c) coeffs) vs = (c * eval_poly coeffs vs)%Z.
  Proof.
    unfold eval_poly.
    now eapply eval_polyp_mul.
  Qed.

  Definition add {n} : Poly n -> Poly n -> Poly n := vzip_with Z.add.
  Definition sub {n} : Poly n -> Poly n -> Poly n := vzip_with Z.sub.

  Lemma eval_polyp_sub {n} (p1 p2 : vec Z n) (vs : vec Z n) :
    dot (vzip_with Z.sub p1 p2) vs = (dot p1 vs - dot p2 vs)%Z.
  Proof.
    revert p1 p2; induction vs as [|x n vs IH]; intros p1 p2.
    - inv_vec p1; inv_vec p2. cbn. lia.
    - inv_vec p1; intros c11 p1; inv_vec p2; intros c21 p2. cbn.
      rewrite IH. lia.
  Qed.

  Lemma eval_poly_sub {n} (p1 p2 : Poly n) (vs : vec Z n) :
    eval_poly (sub p1 p2) vs = (eval_poly p1 vs - eval_poly p2 vs)%Z.
  Proof. eapply eval_polyp_sub. Qed.

  Lemma eval_polyp_add {n} (p1 p2 : vec Z n) (vs : vec Z n) :
    dot (vzip_with Z.add p1 p2) vs = (dot p1 vs + dot p2 vs)%Z.
  Proof.
    revert p1 p2; induction vs as [|x n vs IH]; intros p1 p2.
    - inv_vec p1; inv_vec p2. cbn. lia.
    - inv_vec p1; intros c11 p1; inv_vec p2; intros c21 p2. cbn.
      rewrite IH. lia.
  Qed.

  Lemma eval_poly_add {n} (p1 p2 : Poly n) (vs : vec Z n) :
    eval_poly (add p1 p2) vs = (eval_poly p1 vs + eval_poly p2 vs)%Z.
  Proof. eapply eval_polyp_add. Qed.

  Lemma eval_poly_vremove {n} (i : fin (S n)) (p : Poly (S n)) (vs : vec Z (S n)) :
    (eval_poly (vremove (FS i) p) (vremove i vs) = (eval_poly p vs - p !!! FS i * vs !!! i))%Z.
  Proof.
    unfold eval_poly.
    rewrite <-(vremove_FS i).
    refine (eval_polyp_vremove (FS i) p (1%Z ::: vs)).
  Qed.

  Lemma eval_polyp_zero {n} (vs : vec Z n) :
    dot zero vs = 0%Z.
  Proof.
    unfold zero.
    induction vs; cbn; lia.
  Qed.

  Lemma eval_zero {n} (vs : vec Z n): eval_poly zero vs = 0%Z.
  Proof. now apply eval_polyp_zero. Qed.

  Lemma eval_constant {n c} (vs : vec Z n): eval_poly (constant c) vs = c.
  Proof. unfold eval_poly; cbn. rewrite eval_polyp_zero. lia. Qed.

  Lemma eval_var {n i} (vs : vec Z n): eval_poly (var i) vs = vs !!! i.
  Proof. revert n i vs.
         eapply (learnFinSucc (P := fun n i => forall vs, eval_poly (var i) vs = vs !!! i)).
         intros.
         change (dot (vadd f 1%Z zero) vs = vs !!! f).
         rewrite (vadd_lookup_remove f vs) at 1.
         rewrite eval_polyp_vadd, eval_polyp_zero.
         now lia.
  Qed.

  Definition evalPolys {n} (s : list (Poly n)) (vs : vec Z n) : Prop :=
    List.Forall (fun p => eval_poly p vs = 0%Z) s.

  Inductive Upper (n : nat) : Type :=
  | UpperNil : Upper n
  | UpperCons : fin n -> Poly n -> Upper (pred n) -> Upper n.

  Definition reducePoly' {n} (i : fin (S n)) (h : Poly (S n)) (p : Poly (S n)) : Poly n :=
    let a := h !!! FS i in
    let b := p !!! FS i in
    let g := Z.gcd a b in
    let r := (a / g)%Z in
    let q := (b / g)%Z in
    vzip_with Z.sub (map (Z.mul r) (vremove (FS i) p)) (map (Z.mul q) (vremove (FS i) h)).

  Definition reducePoly {n} (i : fin n) (h : Poly n) (p : Poly n) : Poly (pred n) :=
    learnFinSucc (P := fun n _ => Poly n -> Poly n -> Poly (pred n))
      (fun _ => reducePoly') i h p.

  Lemma reducePolyp_sound {n} (f : fin (S n)) (p2 : Poly (S n)) (vs : vec Z (S n)) (p1 : Poly (S n)) :
    p1 !!! FS f <> 0%Z ->
    eval_poly p1 vs = 0%Z →
    eval_poly (reducePoly' f p1 p2) (vremove f vs) = 0%Z <-> eval_poly p2 vs = 0%Z.
  Proof.
    unfold reducePoly'.
    intros Hfp1nz Hp1.
    rewrite !vmap_vremove, !vzip_with_vremove, !eval_poly_vremove.
    rewrite (vlookup_zip_with Z.sub _ _ (FS f)).
    rewrite !vlookup_map.

    destruct (Z.gcd_divide_l (p1 !!! FS f) (p2 !!! FS f)) as [q Hgcdeq].
    assert (Z.gcd (p1 !!! FS f) (p2 !!! FS f) <> 0%Z) as Hgcdnz.
    { intro Hgcdz. rewrite Hgcdz in Hgcdeq. now lia. }

    replace (p1 !!! FS f `div` Z.gcd (p1 !!! FS f) (p2 !!! FS f) * p2 !!! FS f - p2 !!! FS f `div` Z.gcd (p1 !!! FS f) (p2 !!! FS f) * p1 !!! FS f)%Z with 0%Z.
    rewrite Z.mul_0_l, Z.sub_0_r.
    apply (f_equal (Z.mul (p2 !!! FS f `div` Z.gcd (p1 !!! FS f) (p2 !!! FS f)))) in Hp1.
    rewrite <-eval_poly_mul, Z.mul_0_r in Hp1.
    change (vzip_with Z.sub) with (sub (n := S n)).
    rewrite eval_poly_sub, Hp1, Z.sub_0_r, eval_poly_mul.
    enough (p1 !!! FS f `div` Z.gcd (p1 !!! FS f) (p2 !!! FS f) <> 0)%Z by lia.
    rewrite Hgcdeq at 1.
    rewrite Z_div_mult.
    now intros ->; lia.
    pose proof (Z.gcd_nonneg (p1 !!! FS f) (p2 !!! FS f)); now lia.
    rewrite Z.lcm_equiv2; last easy.
    rewrite (Z.mul_comm _ (p1 !!! FS f)), Z.lcm_equiv1; last easy.
    now lia.
  Qed.

  Lemma reducePoly_sound {n} (i : fin n) (p2 : Poly n) (vs : vec Z n) (p1 : Poly n) :
    p1 !!! FS i <> 0%Z ->
    eval_poly p1 vs = 0%Z → eval_poly (reducePoly i p1 p2) (vremove i vs) = 0%Z <-> eval_poly p2 vs = 0%Z.
  Proof.
    unfold reducePoly.
    revert p2 vs p1.
    refine (learnFinSucc_ind (M := fun n (f : fin n) => Poly n → Poly n → Poly (pred n))
              (fun _ => reducePoly')
              (fun n i r => forall (p2 : Poly n) (vs : vec Z n) (p1 : Poly n),
                   p1 !!! FS i <> 0%Z ->
                   eval_poly p1 vs = 0%Z -> eval_poly (r p1 p2) (vremove i vs) = 0%Z <-> eval_poly p2 vs = 0%Z)
              _ _).
    intros n' f p2 vs p1; eapply reducePolyp_sound.
  Qed.

  Definition reducePolys {n} (i : fin n) (p : Poly n) : list (Poly n) -> list (Poly (pred n)) :=
    List.map (reducePoly i p).

  Lemma reducePolys_sound {n} (i : fin n) (l : list (Poly n)) (vs : vec Z n) (p : Poly n) :
    p !!! FS i <> 0%Z ->
    eval_poly p vs = 0%Z → evalPolys (reducePolys i p l) (vremove i vs) <-> evalPolys l vs.
  Proof.
    intros Hpsinz Hpvsz.
    unfold evalPolys, reducePolys.
    rewrite List.Forall_map.
    apply Forall_iff.
    intros p'.
    now eapply reducePoly_sound.
  Qed.

  Lemma reducePolys_sound2 {n} (i : fin n) (l : list (Poly n)) (vs : vec Z n) (p : Poly n) :
    p !!! FS i <> 0%Z ->
    eval_poly p vs = 0%Z ∧ evalPolys (reducePolys i p l) (vremove i vs) ↔ evalPolys (p :: l) vs.
  Proof.
    intros Hpinz.
    split.
    - intros [Hp Hrl].
      rewrite reducePolys_sound in Hrl; try easy.
      now apply list.Forall_cons.
    - intros [Hp Hl]%list.Forall_cons.
      split; first easy.
      now rewrite reducePolys_sound.
  Qed.

  Definition IfSucc (P : nat -> Type) (n : nat) : Type :=
    match n with
    | 0 => True
    | S n => P n
    end.

  Fixpoint nat_rect' (P : nat → Type) (H : ∀ n, IfSucc P n → P n) (n : nat) : P n :=
    H n (match n with
         | 0 => I
         | S n => (nat_rect' P H n)
         end).
  Lemma nat_rectp_unfold {P H n} :
    nat_rect' P H n = H n (match n with
                           | 0 => I
                           | S n => (nat_rect' P H n)
                           end).
  Proof. now destruct n. Qed.

  Lemma nat_rect_ind (M : nat → Type) (H : ∀ n, IfSucc M n → M n)
    (P : forall n, M n -> Prop) (HP : forall n, IfSucc (fun n => P n (nat_rect' M H n)) n -> P n (nat_rect' M H n))
    (n : nat) : P n (nat_rect' M H n).
  Proof.
    induction n; cbn; eapply HP.
    - refine I.
    - eapply IHn.
  Qed.

  Definition toUpper : forall {n} (l : list (Poly n)), option (Upper n) :=
    nat_rect' (fun n => forall (l : list (Poly n)), option (Upper n))
      (fun n IH =>
         list_rect (fun l => option (Upper n)) (Some (UpperNil _))
           (fun p ps IHps =>
              match findNonZero (tl p) with
              | None => if Z.eqb 0%Z (hd p)
                        then
                          (* coeffs are zero and constant is zero, skip the poly *)
                          IHps
                        else
                          (* coeffs are zero but not the constant, system inconsistent *)
                          None
              | Some i =>
                  (* Coeff i is non-zero. Iterate... *)
                  learnFinSucc
                    (P := fun n i => IfSucc (λ n : nat, list (Poly n) → option (Upper n)) n -> Poly n -> list (Poly n) -> option (Upper n))
                    (fun n i IH p ps => option.map (UpperCons i p) (IH (reducePolys i p ps)))
                    i IH p ps
              end)).

  #[global] Arguments toUpper {!n} !l.

  Fixpoint evalUpper {n} (u : Upper n) (vs : vec Z n) : Prop :=
    match u with
    | UpperNil _ => True
    | UpperCons i p u => eval_poly p vs = 0%Z /\ evalUpper u (vremove i vs)
    end.


  Lemma toUpper_sound : forall {n} (l : list (Poly n)),
      option.spec (fun u => forall vs, evalUpper u vs <-> evalPolys l vs) (forall vs, ¬ evalPolys l vs) (toUpper l).
  Proof.
    refine (nat_rect_ind _ _
              (fun n m => forall l, option.spec (λ u : Upper n, ∀ vs : vec Z n, evalUpper u vs <-> evalPolys l vs)
                                      (∀ vs : vec Z n, ¬ evalPolys l vs) (m l)) _).
    unfold toUpper.
    intros n IHn l.
    rewrite nat_rectp_unfold.
    induction l.
    - (* l is empty *)
      eapply option.specSome; intros vs; unfold evalPolys; now rewrite list.Forall_nil.
    - cbn [list_rect].
      destruct (findNonZero_lookup (tl a)) as [i Hneq|H].
      + (* poly a has non-zero coefficient at index i *)
        apply neq_Symmetric in Hneq.
        cbn in Hneq.
        destruct n; first refine (Fin.case0 (fun _ => _) i).
        eapply option.spec_map.
        generalize (IHn (reducePolys i a l)); clear IHn.
        refine (option.spec_monotonic _ _ _ (o := _)).
        * (* consistency of reduced system + validity of a implies consistency of original *)
          intros u Hcpu vs.
          cbn -[vremove eval_poly].
          rewrite (Hcpu (vremove i vs)).
          eapply (reducePolys_sound2 i).
          clear -Hneq.
          revert a Hneq; now refine (vec_S_inv _ _).
        * (* inconsistency of reduced system implies inconsistency of original *)
          intros Hnra vs [Ha Hl]%Forall_cons_1.
          eapply Hnra.
          refine (proj2 (reducePolys_sound _ _ _ _ _ Ha) Hl).
          clear -Hneq. revert a Hneq.
          now refine (vec_S_inv _ _).
      + (* poly a is all-zero: constant too? *)
        destruct (Z.eqb_spec 0 (hd a)).
        * revert IHl.
          apply option.spec_monotonic.
          -- (* poly a is all-zero with zero constant: consistency of remaining equations unaffected by a *)
            intros u Hu vs.
            rewrite (Hu vs).
            split; last now intros [Ha Hl]%Forall_cons_1.
            intros Hlvs.
            eapply List.Forall_cons; last easy.
            revert a H e; refine (vec_S_inv _ _); intros a0 a H e; cbn in *; subst.
            now apply eval_zero.
          -- (* poly a is all-zero with zero constant: inconsistency of remaining equations unaffected by a *)
            intros Hnl vs [Ha Hl]%list.Forall_cons.
            now eapply (Hnl _ Hl).
        * (* poly is all-zero with non-zero constant: unsolvable *)
          eapply option.spec_none.
          clear -H n0.
          revert a H n0. refine (vec_S_inv _ _); intros x v.
          cbn; intros -> Hxnz vs [Ha _]%Forall_cons_1.
          unfold eval_poly in Ha; cbn in Ha.
          rewrite eval_polyp_zero in Ha.
          now lia.
  Qed.
End PolyRed.

Module LinearProgramming.
  (* This module defines an extremely minimal notion of linear programming problems
   * and a sound but far-from-complete solver for it.
   * It's even dubious whether we do enough to call it linear programming.
   * The only goal is to efficiently and soundly discharge very common
   * inconsistent systems of inequalities, with absolutely no ambition of completeness.
   *)

  Record Problem (n : nat) : Set :=
    MkProblem {
        probPoly : list (Poly n)
      ; probSlackvars : vec bool n
      }.

  Definition SlacksPos {n} (slack : vec bool n) (vs : vec Z n) : Prop :=
    Forall2 (fun (isSlack : bool) v => if isSlack then v >=? 0 else true)%Z slack vs.

  Definition FeasibleSolutionUpper {n} (u : Upper n) (slacks : vec bool n) (vs : vec Z n) : Prop :=
    evalUpper u vs /\ SlacksPos slacks vs.

  Definition FeasibleSolution {n} (prob : Problem n) (vs : vec Z n) : Prop :=
    evalPolys (probPoly prob) vs /\ SlacksPos (probSlackvars prob) vs.

  Definition LPSat {n} (prob : Problem n) : Prop :=
    exists vs, FeasibleSolution prob vs.

  Definition checkInfeasiblePoly {n} (slackvars : vec bool n) (poly : Poly n) : bool :=
    match uncons poly with
    | (constant , coeffs) => (match Z.sgn constant with
                              | -1 => bool_decide (Forall2 (fun isSlack coeff => (coeff = 0) \/ (Is_true isSlack /\ (coeff <= 0))) slackvars coeffs)
                              | 1 => bool_decide (Forall2 (fun isSlack coeff => (coeff = 0) \/ (Is_true isSlack /\ (coeff >= 0))) slackvars coeffs)
                              | _ => false
                              end)%Z
    end.

  Lemma SlacksPos_eval_pos {n} {slackvars : vec bool n} {coeffs : vec Z n} {vs : vec Z n} :
    Forall2 (λ (isSlack : bool) coeff, coeff = 0%Z ∨ isSlack ∧ (coeff >= 0)%Z) slackvars coeffs →
    SlacksPos slackvars vs → (dot coeffs vs >= 0)%Z.
  Proof.
    induction 1 as [|n s1 c1 ss cs H1 Hs]; first (inv_vec vs; now cbn).
    revert vs. refine (vec_S_inv _ _).
    intros v vs [Hsv1 Hsvs]%Forall2_cons_iff_copy; cbn.
    specialize (IHHs vs Hsvs).
    enough (c1 * v >= 0)%Z by now lia.
    clear IHHs Hsvs Hs vs ss cs.
    destruct H1 as [|[Hs1 Hc1]]; first now lia.
    rewrite (Is_true_eq_true _ Hs1) in Hsv1.
    destruct (Z.geb_spec v 0); last easy.
    now lia.
  Qed.

  Lemma SlacksPos_eval_neg {n} {slackvars : vec bool n} {coeffs : vec Z n} {vs : vec Z n} :
    Forall2 (λ (isSlack : bool) coeff, coeff = 0%Z ∨ isSlack ∧ (coeff <= 0)%Z) slackvars coeffs →
    SlacksPos slackvars vs → (dot coeffs vs <= 0)%Z.
  Proof.
    induction 1 as [|n s1 c1 ss cs H1 Hs]; first (inv_vec vs; now cbn).
    revert vs. refine (vec_S_inv _ _).
    intros v vs [Hsv1 Hsvs]%Forall2_cons_iff_copy; cbn.
    specialize (IHHs vs Hsvs).
    enough (c1 * v <= 0)%Z by now lia.
    clear IHHs Hsvs Hs vs ss cs.
    destruct H1 as [|[Hs1 Hc1]]; first now lia.
    rewrite (Is_true_eq_true _ Hs1) in Hsv1.
    destruct (Z.geb_spec v 0); last easy.
    now lia.
  Qed.

  Lemma checkInfeasiblePoly_sound {n} {slackvars : vec bool n} {poly : Poly n} :
    checkInfeasiblePoly slackvars poly ->
    forall vs, ~(eval_poly poly vs = 0%Z /\ SlacksPos slackvars vs).
  Proof.
    revert poly.
    refine (vec_S_inv _ _).
    intros const coeffs; cbn.
    destruct (Z.sgn_spec const) as [[Hpos ->]|[[Hzero ->]|[Hneg ->]]]; try easy.
    - destruct (bool_decide_reflect (Forall2 (λ (isSlack : bool) (coeff : Z), coeff = 0%Z ∨ isSlack ∧ (coeff >= 0)%Z) slackvars coeffs)) as [Hscs|?]; last easy.
      intros _ vs [Heq Hsp].
      unfold eval_poly in Heq; cbn in Heq.
      enough (dot coeffs vs >= 0)%Z by lia.
      now eapply (SlacksPos_eval_pos Hscs).
    - destruct (bool_decide_reflect (Forall2 (λ (isSlack : bool) (coeff : Z), coeff = 0%Z ∨ isSlack ∧ (coeff <= 0)%Z) slackvars coeffs)) as [Hscs|?]; last easy.
      intros _ vs [Heq Hsp].
      unfold eval_poly in Heq; cbn in Heq.
      enough (dot coeffs vs <= 0)%Z by lia.
      now eapply (SlacksPos_eval_neg Hscs).
  Qed.

  Fixpoint checkInfeasibleUpper {n} (slackvars : vec bool n) (u : Upper n) : bool :=
    match u with
      UpperNil _ => false
    | UpperCons p poly u' => checkInfeasiblePoly slackvars poly ||
                               checkInfeasibleUpper (vremove p slackvars) u'
    end.

  Lemma SlacksPos_vremove {n : nat} {t : fin n} {slacks : vec bool n} {vs : vec Z n} :
    SlacksPos slacks vs → SlacksPos (vremove t slacks) (vremove t vs).
  Proof.
    revert slacks vs.
    induction t;
      refine (vec_S_inv _ _); intros slack slacks;
      refine (vec_S_inv _ _); intros v vs [Hv Hslacks]%Forall2_cons_iff_copy;
      cbn -[vremove]; first easy.
    destruct n as [|n]; first inversion t.
    rewrite ?vremove_FS.
    apply Forall2_cons; first easy.
    now apply IHt.
  Qed.

  Lemma checkInfeasibleUpper_sound {n} {slackvars : vec bool n} {u : Upper n} :
    checkInfeasibleUpper slackvars u ->
    forall vs, ~ (FeasibleSolutionUpper u slackvars vs).
  Proof.
    revert slackvars.
    induction u; first easy.
    intros slacks [H|Hfeas]%orb_True.
    - intros v [[Hfirst Hrest] Hslacks].
      clear Hrest IHu.
      eapply (checkInfeasiblePoly_sound H (conj Hfirst Hslacks)).
    - intros vs [[Hfirst Hrest] Hslacks].
      eapply (IHu _ Hfeas).
      split; first eassumption.
      now apply SlacksPos_vremove.
  Qed.

  Definition checkInfeasible {n} (prob : Problem n) : bool :=
    match toUpper (probPoly prob) with
    | Some u => checkInfeasibleUpper (probSlackvars prob) u
    | None => false
    end.

  Lemma checkInfeasible_sound {n} {prob : Problem n} :
    checkInfeasible prob -> ~(LPSat prob).
  Proof.
    destruct prob as [poly slacks]; unfold checkInfeasible; cbn.
    intros Hinfeas [vs [Heval Hslacks]]; cbn in *.
    destruct (toUpper_sound poly); last easy.
    eapply (checkInfeasibleUpper_sound Hinfeas).
    split; last eassumption.
    now rewrite H.
  Qed.

  (* test problem 1: x >= 0, x <= -1
   * desugars to: x - s_1 = 0, 1 + x + s_2 = 0
   *)
  Definition testProblem1 : Problem 3 :=
    (MkProblem [
         [# 0; 1; -1; 0];
         [# 1; 1; 0; 1]
       ]
       [# false; true; true])%Z
  .
  Eval compute in checkInfeasible testProblem1.

  (* test problem 2: x >= 0, x <= 2000, x + 10 <= 20 and x + 5 >= 16
   * desugars to: x - s_1 = 0, x + s_2 - 2000 = 0, x + s_3 - 10 = 0, x -11 - s_4 = 0
   *)
  Definition testProblem2 : Problem 5 :=
    (MkProblem [
         [# 0; 1; -1; 0; 0; 0];
         [# -2000; 1; 0; 1; 0; 0];
         [# -10; 1; 0; 0; 1; 0];
         [# -11; 1; 0; 0; 0; -1]
       ]
       [# false; true; true; true; true])%Z
  .
  Eval compute in checkInfeasible testProblem2.

  Section Slackify.
    Import PolyRed.
    Inductive Ineq := | Geq0 | Eq0 | Leq0.
    Record IneqPoly (n : nat) : Set :=
      MkIneqPoly {
          ineqPolyPoly : Poly n
        ; ineqPolyIneq : Ineq
        }.
    Definition IneqProblem (n : nat) : Set := list (IneqPoly n).
    Definition evalIneq (ineq : Ineq) : Z -> Prop :=
      match ineq with
      | Geq0 => Z.le 0%Z
      | Leq0 => Z.ge 0%Z
      | Eq0 => eq 0%Z
      end.
    Definition IneqSolves {n} (vs : vec Z n) (p : IneqPoly n) : Prop :=
      match p with
        MkIneqPoly coeffs ineq => evalIneq ineq (eval_poly coeffs vs)
      end.

    Definition IneqSat {n} (prob : IneqProblem n) : Prop :=
      exists vs, List.Forall (IneqSolves vs) prob.

    Definition nrSlackIneq {n} (ineq : IneqPoly n) : nat :=
      match ineqPolyIneq ineq with
      | Geq0 | Leq0 => 1
      | Eq0 => 0
      end.
    Fixpoint nrSlackIneqs {n} (ineqs : list (IneqPoly n)) : nat :=
      match ineqs with
        []%list => 0
      | (ineq :: ineqs)%list => nrSlackIneq ineq + nrSlackIneqs ineqs
      end.

    Fixpoint slackCoeffs {n} (ineqs : IneqProblem n) : list (vec Z (nrSlackIneqs ineqs)) :=
      match ineqs return list (vec Z (nrSlackIneqs ineqs)) with
      | []%list => []%list
      | (ineq :: ineqs)%list =>
          let coeffs0 : vec Z (nrSlackIneq ineq + nrSlackIneqs ineqs) :=
            match ineq with
            | MkIneqPoly _ Geq0 => cons (-1)%Z (vreplicate _ 0%Z)
            | MkIneqPoly _ Leq0 => cons 1%Z (vreplicate _ 0%Z)
            | MkIneqPoly _ Eq0 => vreplicate _ 0%Z
            end
          in let extend : vec Z (nrSlackIneqs ineqs) -> vec Z (nrSlackIneq ineq + nrSlackIneqs ineqs) :=
               match ineq with
               | MkIneqPoly _ Geq0 => cons 0%Z
               | MkIneqPoly _ Leq0 => cons 0%Z
               | MkIneqPoly _ Eq0 => id
               end
          in coeffs0 :: (List.map extend (slackCoeffs ineqs))
      end.

    Definition slackify {n} (ineqs : IneqProblem n) : Problem (n + nrSlackIneqs ineqs) :=
      MkProblem
        (zip_with append (List.map (@ineqPolyPoly _) ineqs) (slackCoeffs ineqs))
        (vreplicate n false +++ vreplicate (nrSlackIneqs ineqs) true).

    Fixpoint evalSlacks {n} (ineqs : IneqProblem n) (vs : vec Z n) : vec Z (nrSlackIneqs ineqs) :=
      match ineqs return vec Z (nrSlackIneqs ineqs) with
      | []%list => [# ]
      | (ineq :: ineqs)%list =>
          let slacks : vec Z (nrSlackIneqs ineqs) := evalSlacks ineqs vs in
          match ineq with
          | MkIneqPoly coeffs pred =>
              match pred with
              | Geq0 => eval_poly coeffs vs ::: slacks
              | Leq0 => (- eval_poly coeffs vs)%Z ::: slacks
              | Eq0 => slacks
              end
          end
      end.

    Lemma Forall_zip_with_ext {A B C1 C2 : Type} {P1 : C1 → Prop} {P2 : C2 → Prop}
      {f1 : A → B → C1} {f2 : A → B → C2} {l1 : list A} {l2 : list B} :
      (forall a b, P1 (f1 a b) -> P2 (f2 a b)) ->
        List.Forall P1 (zip_with f1 l1 l2) → List.Forall P2 (zip_with f2 l1 l2).
    Proof.
      intros HPf. revert l2.
      induction l1; intros l2; destruct l2; cbn; try easy.
      rewrite ?List.Forall_cons_iff.
      intuition.
    Qed.


    Lemma slackify_sol {n} {ineqs : IneqProblem n} {vs : vec Z n} :
      List.Forall (IneqSolves vs) ineqs →
      FeasibleSolution (slackify ineqs) (vs +++ evalSlacks ineqs vs).
    Proof.
      (* TODO: cleanup proof. *)
      unfold slackify, FeasibleSolution, evalPolys; cbn -[eval_poly].
      split.
      - induction ineqs as [|[poly [ | |]] ineqs]; first easy;
          rewrite List.Forall_cons_iff in H;
          destruct H as [Hpoly Hineqs].
        + cbn. constructor.
          * rewrite eval_poly_app; cbn.
            change (vreplicate ?n 0%Z) with (@zero n).
            rewrite eval_polyp_zero.
            lia.
          * specialize (IHineqs Hineqs).
            rewrite zip_with_fmap_r.
            revert IHineqs.
            eapply Forall_zip_with_ext.
            intros coeffs slackCoeffs Heval.
            rewrite eval_poly_app; cbn.
            rewrite eval_poly_app in Heval.
            now lia.
        + cbn. constructor.
          * rewrite eval_poly_app; cbn.
            change (vreplicate ?n 0%Z) with (@zero n).
            rewrite eval_polyp_zero.
            cbn in Hpoly.
            lia.
          * rewrite list_fmap_id.
            intuition.
        + cbn. constructor.
          * rewrite eval_poly_app; cbn.
            change (vreplicate ?n 0%Z) with (@zero n).
            rewrite eval_polyp_zero.
            lia.
          * specialize (IHineqs Hineqs).
            rewrite zip_with_fmap_r.
            revert IHineqs.
            eapply Forall_zip_with_ext.
            intros coeffs slackCoeffs Heval.
            rewrite eval_poly_app; cbn.
            rewrite eval_poly_app in Heval.
            now lia.
      - apply Forall2_append.
        + rewrite Forall2_vreplicate_left.
          eapply Forall_forall; intuition.
        + rewrite Forall2_vreplicate_left.
          induction ineqs; first constructor; cbn.
          rewrite List.Forall_cons_iff in H.
          destruct H as [Hvs Hineqs].
          destruct a as [poly pred].
          specialize (IHineqs Hineqs).
          destruct pred; rewrite ?Forall_cons_iff; intuition;
            cbn in Hvs.
          destruct (Z.geb_spec (eval_poly poly vs) 0); now try lia.
          destruct (Z.geb_spec (- (eval_poly poly vs)) 0); now try lia.
    Qed.

    Lemma slackify_sound_help {n} {ineqs : IneqProblem n} :
      IneqSat ineqs -> LPSat (slackify ineqs).
    Proof.
      intros [vs Hsat].
      exists (vs +++ evalSlacks ineqs vs).
      now eapply slackify_sol.
    Qed.

    Lemma slackify_sound {n} {ineqs : IneqProblem n} :
      ~LPSat (slackify ineqs) -> ~IneqSat ineqs.
    Proof.
      intros Hunsat Hsat.
      now eapply Hunsat, slackify_sound_help.
    Qed.
  End Slackify.

  (* test problem 1: x >= 0, x <= -1
   * desugars to: x - s_1 = 0, 1 + x + s_2 = 0
   *)
  Definition testProblem3 : IneqProblem 1 :=
    [ {| ineqPolyPoly := [# 0; 1 ]; ineqPolyIneq := Geq0 |};
      {| ineqPolyPoly := [# 1; 1 ]; ineqPolyIneq := Leq0 |}
    ]%list%Z.
  Eval compute in checkInfeasible (slackify testProblem3).

  (* test problem 2: x >= 0, x <= 2000, x + 10 <= 20 and x + 5 >= 16
   * desugars to: x - s_1 = 0, x + s_2 - 2000 = 0, x + s_3 - 10 = 0, x -11 - s_4 = 0
   *)
  Definition testProblem4 : IneqProblem 1 :=
    [ {| ineqPolyPoly := [# 0; 1 ]; ineqPolyIneq := Geq0 |};
      {| ineqPolyPoly := [# -2000; 1 ]; ineqPolyIneq := Leq0 |};
      {| ineqPolyPoly := [# -10; 1 ]; ineqPolyIneq := Leq0 |};
      {| ineqPolyPoly := [# -11; 1 ]; ineqPolyIneq := Geq0 |}
    ]%list%Z.
  Eval compute in checkInfeasible (slackify testProblem4).

End LinearProgramming.

(* Module Type LPKatamaran *)
(*   (Import GLOBAL : GlobalState) *)
(*   (Import P : PredicateKit GLOBAL) *)
(*   (Import W : WorldsMixin GLOBAL P). *)

(*   Import Vector. *)
(*   Import PolyRed. *)

(*   Definition AllInts : LCtx -> Type := ctx.All (fun b => type b = ty.int). *)

(*   Record SPoly (Γ : LCtx) : Type := *)
(*     MkPoly { *)
(*         poly_int_vars : AllInts Γ *)
(*       ; polyCoeffs : Poly (ctx.length Γ) *)
(*       }. *)

(*   (* Note that the vector is cons-based while valuations are snoc-based, so for efficient conversion, we keep the coefficients in the vector in reverse order than in the Valuation. *) *)
(*   Fixpoint val_to_vec {Γ} (iΓ : AllInts Γ) : Valuation Γ -> vec Z (ctx.length Γ) := *)
(*     match iΓ with *)
(*       ctx.all_nil _ => fun _ => [# ] : vec Z (ctx.length [ctx]) *)
(*     | ctx.all_snoc iΓ' eqint => *)
(*         fun ι => match env.view ι with *)
(*                    env.isSnoc ι' v => *)
(*                      eq_rect _ Val v _ eqint ::: val_to_vec iΓ' ι' *)
(*                  end *)
(*     end. *)

(*   (* Note that the vector is cons-based while valuations are snoc-based, so for efficient conversion, we keep the coefficients in the vector in reverse order than in the Valuation. *) *)
(*   Fixpoint vec_to_val {Γ} (iΓ : AllInts Γ) : vec Z (ctx.length Γ) -> Valuation Γ := *)
(*     match iΓ with *)
(*       ctx.all_nil _ => fun _ => [env] *)
(*     | ctx.all_snoc iΓ' eqint => *)
(*         fun vs => *)
(*           (vec_to_val iΓ' (tl (vs : vec Z (ctx.length (_ ▻ _))))) *)
(*           .[ _ ↦ eq_rect _ Val (hd vs : Val ty.int) _ (eq_sym eqint)] *)
(*     end. *)

(*   Lemma val_to_vec_to_val {Γ} (iΓ : AllInts Γ) : forall ι, *)
(*       vec_to_val iΓ (val_to_vec iΓ ι) = ι. *)
(*   Proof. *)
(*     induction iΓ; intros; destruct (env.view ι). *)
(*     { now cbn. } *)
(*     cbn. *)
(*     now rewrite IHiΓ, eq_rect_sym1. *)
(*   Qed. *)

(*   Definition inst_poly {Γ} (p : SPoly Γ) (ι : Valuation Γ) : Z := *)
(*     (eval_poly (polyCoeffs p) (val_to_vec (poly_int_vars p) ι))%Z. *)

(*   #[export] Instance Inst_poly : Inst SPoly Z := fun _ => inst_poly. *)

(*   Section Zify. *)
(*   End Zify. *)
(* End LPKatamaran. *)
