(* Tests for the oracle of Staging/LiaSimplex.v. *)

From Stdlib Require Import List ZArith QArith Lia.
From Stdlib Require PrimInt63.
Import (notations) PrimInt63.
From Stdlib.micromega Require Import EnvRing RingMicromega Tauto ZMicromega.
From Katamaran Require Staging.LiaOracle.
From Katamaran Require Import Staging.LiaSimplex.

Import ListNotations.
#[local] Open Scope Z_scope.

(* The arithmetic of [Num] agrees with [Z], and its results are in the
   right tier. *)

Definition canon (a : Num.t) : bool := Num.eqb a (Num.of_Z (Num.to_Z a)).

Definition edges : list Z :=
  let p := [0; 1; 2; 3; 7; 2^31; 2^62 - 1; 2^62; 2^62 + 1; 2^63 - 1; 2^63;
            2^63 + 1; 3 * 2^62 + 5; 2^100 + 12345; 2^126 - 1; 2^126; 2^126 + 1;
            2^130 + 7; 123456789012345678901234567] in
  p ++ map Z.opp p.

Definition agree1 (x y : Z) : bool :=
  let a := Num.of_Z x in
  let b := Num.of_Z y in
  let ok r z := Z.eqb (Num.to_Z r) z && canon r in
  ok a x && ok (Num.add a b) (x + y) && ok (Num.sub a b) (x - y)
  && ok (Num.mul a b) (x * y) && ok (Num.opp a) (- x) && ok (Num.abs a) (Z.abs x)
  && ok (Num.gcd a b) (Z.gcd x y)
  && Bool.eqb (Num.ltb a b) (x <? y) && Bool.eqb (Num.eqb a b) (x =? y)
  && Bool.eqb (Num.is_zero a) (x =? 0) && Bool.eqb (Num.is_pos a) (0 <? x)
  && Bool.eqb (Num.is_neg a) (x <? 0)
  && (if y =? 0 then true
      else ok (Num.divexact (Num.mul a b) b) x
           && Bool.eqb (Num.divides b a) (Z.rem x y =? 0)
           && (if 0 <? y then ok (Num.fdiv a b) (x / y)
                              && ok (Num.cdiv a b) (- (- x / y)) else true)).

Goal forallb (fun x => forallb (agree1 x) edges) edges = true.
Proof. vm_compute. reflexivity. Qed.

(* Infeasible over the rationals. *)

Goal forall x y : Z, x <= y -> y <= x + 1 -> 2 * x <= 2 * y.
Proof. intros. lia_simplex. Qed.

Goal forall x y z : Z,
    x + y <= 3 -> y - z >= 2 -> x = 4 * z -> z > 5 -> x + 3 * y < 40 -> False.
Proof. intros. lia_simplex. Qed.

Goal forall a b : Z, 0 <= a < 8 -> 0 <= b < 8 -> a + 8 * b < 64.
Proof. intros. lia_simplex. Qed.

Goal forall x y z : Z,
    3 * x + 2 * y <= 7 -> x - y = 1 -> z = x + y ->
    5 * x <= 10 /\ (z < 4 \/ y > 100).
Proof. intros. lia_simplex. Qed.

Goal forall x y : Z,
    3 * x <= 2 * y -> 2 * y <= 3 * x + 1 -> 3 * x <> 2 * y ->
    3 * x + 1 <> 2 * y -> False.
Proof. intros. lia_simplex. Qed.

Goal forall x y z : nat,
    (x + y <= z -> z - y >= x /\ Nat.max x y <= z /\ (x = z -> y = 0))%nat.
Proof. intros. lia_simplex. Qed.

Goal forall x y : Z, x * y >= 1 -> 2 * (x * y) + 3 > 4.
Proof. intros. lia_simplex. Qed.

Goal forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Z,
    x0 <= x1 -> x1 <= x2 -> x2 <= x3 -> x3 <= x4 -> x4 <= x5 -> x5 <= x6 ->
    x6 <= x7 -> x7 <= x8 -> x8 <= x9 -> x0 <= x9.
Proof. intros. lia_simplex. Qed.

Goal forall x y z : Z,
    3 * x + 2 * y <= 7 -> x - y = 1 -> z = x + y ->
    5 * x <= 10 /\ (z < 4 \/ y > 100).
Proof. intros. lia_simplex_auto. Qed.

(* Infeasible over the integers only: cutting planes of the hypotheses ... *)

Goal forall x y : Z, 2 * x + 2 * y = 1 -> False.
Proof. intros. lia_simplex. Qed.

Goal forall x y : Z, 2 * x + 2 * y >= 1 -> x + y <= 0 -> False.
Proof. intros. lia_simplex. Qed.

(* ... and branch and bound. *)

Goal forall x y : Z, 0 <= x <= 3 -> 2 * y = 2 * x + 1 -> False.
Proof. intros. lia_simplex. Qed.

Goal forall x y : Z, 3 * x - 3 * y = 1 \/ 6 * x + 4 * y = 3 -> False.
Proof. intros. lia_simplex. Qed.

Goal forall x y : Z,
    1 <= 3 * x - 2 * y <= 1 -> 2 <= 4 * x + 6 * y <= 3 -> 0 <= x <= 10 -> False.
Proof. intros. lia_simplex. Qed.

Goal forall x y : Z, 1 <= 2 * x + 3 * y <= 1 -> 0 <= x -> 0 <= y -> False.
Proof. intros. lia_simplex_auto. Qed.

(* Not supported: the non-linear preprocessing of [lia]. *)

Goal forall x y : Z, x = 2 -> x * y >= 2 * y.
Proof. intros. Fail lia_simplex. lia. Qed.

Goal forall x y : Z, 0 <= x -> 0 <= y -> 0 <= x * y.
Proof. intros. Fail lia_simplex. lia. Qed.

(* Random clauses. Every answer is checked: a certificate by [ZChecker], and a
   solution by evaluating the hypotheses. *)

Definition lcg (s : Z) : Z := (s * 1103515245 + 12345) mod 2147483648.
Definition rnd (s k : Z) : Z := (s / 65536) mod (2 * k + 1) - k.

(* A linear expression over [n] variables, each with probability [d] in 8. *)
Fixpoint rnd_expr (n : nat) (d c : Z) (x : positive) (s : Z) : PExpr Z * Z :=
  match n with
  | O => let s := lcg s in (PEc (rnd s 10), s)
  | S n =>
      let s := lcg s in
      let s' := lcg s in
      let (e, s'') := rnd_expr n d c (Pos.succ x) s' in
      (if rnd s' 4 + 4 <? d then PEadd (PEmul (PEc (rnd s c)) (PEX x)) e else e, s'')
  end.

(* [m] hypotheses over [n] variables. *)
Fixpoint rnd_clause (m n : nat) (d c : Z) (s : Z) : list (NFormula Z) * Z :=
  match m with
  | O => ([], s)
  | S m =>
      let (e, s) := rnd_expr n d c 1 s in
      let s := lcg s in
      let (l, s') := rnd_clause m n d c s in
      ((normZ e, if rnd s 3 =? 0 then Equal else NonStrict) :: l, s')
  end.

Definition qzero (a : Q) : bool := match Qnum a with Z0 => true | _ => false end.
Definition qneg (a : Q) : bool := match Qnum a with Zneg _ => true | _ => false end.

Definition holds (env : positive -> Q) (f : NFormula Z) : bool :=
  let v := Pphi Qplus Qmult inject_Z env (fst f) in
  match snd f with Equal => qzero v | _ => negb (qneg v) end.

Fixpoint mon_index (m : list positive) (l : list (list positive)) (i : PrimInt63.int) : option PrimInt63.int :=
  match l with
  | [] => None
  | m' :: l =>
      if list_eq_dec Pos.eq_dec m m' then Some i else mon_index m l (PrimInt63.add i 1%uint63)
  end.

(* The verdicts: refuted, satisfied (by an integer solution if [int]), unknown,
   wrong (a certificate rejected or a solution violating a hypothesis). *)
Variant verdict : Set := VUnsat | VSat | VUnknown | VBad.

Definition check (ps : params) (integers : bool) (l : list (NFormula Z)) : verdict :=
  match solve ps l with
  | Proof pf => if ZChecker l pf then VUnsat else VBad
  | Sat _ st mons =>
      let env x :=
        match mon_index [x; 1%positive] mons 0%uint63 with
        | Some i => let (a, b) := value st i in Qmake (Num.to_Z a) (Z.to_pos (Num.to_Z b))
        | None => 0%Q
        end in
      let integral x := Z.eqb (Zpos (Qden (Qred (env x)))) 1 in
      if forallb (holds env) l && (negb integers || forallb integral (map Pos.of_nat (seq 1 30)))
      then VSat else VBad
  | Unknown => VUnknown
  end.

(* The old oracle refutes exactly the clauses infeasible over the rationals. *)
Definition rational_unsat (l : list (NFormula Z)) : bool :=
  ZChecker l (LiaOracle.ZOracle LiaOracle.default_fuel l).

(* Counts: rationally infeasible (old oracle); refuted, satisfied, unknown
   without branching; the same with branch and bound; wrong answers, and
   rationally infeasible clauses not refuted. *)
Record counts : Set := Counts {
  c_rat : nat; c_unsat : nat; c_sat : nat; c_unknown : nat;
  c_bb_unsat : nat; c_bb_sat : nat; c_bb_unknown : nat; c_bad : nat }.

Definition tally (c : counts) (rat : bool) (v1 v2 : verdict) : counts :=
  let '(Counts r u s k bu bs bk b) := c in
  let inc (x : nat) (yes : bool) := if yes then S x else x in
  let is v w := match v, w with
                | VUnsat, VUnsat | VSat, VSat | VUnknown, VUnknown | VBad, VBad => true
                | _, _ => false end in
  Counts (inc r rat) (inc u (is v1 VUnsat)) (inc s (is v1 VSat)) (inc k (is v1 VUnknown))
    (inc bu (is v2 VUnsat)) (inc bs (is v2 VSat)) (inc bk (is v2 VUnknown))
    (inc b (is v1 VBad || is v2 VBad || (rat && negb (is v1 VUnsat))
            || (is v1 VUnsat && negb (is v2 VUnsat)) || (is v2 VSat && rat))).

Fixpoint run (k m n : nat) (d c : Z) (s : Z) (acc : counts) : counts :=
  match k with
  | O => acc
  | S k =>
      let (l, s) := rnd_clause m n d c s in
      run k m n d c s
        (tally acc (rational_unsat l) (check (Params 0 0) false l)
           (check default_params true l))
  end.

Definition zero : counts := Counts 0 0 0 0 0 0 0 0.

Compute run 200 4 3 8 3 2 zero.
Compute run 200 6 4 8 3 1 zero.
Compute run 100 10 4 8 3 5 zero.
Compute run 40 12 8 8 3 3 zero.
Compute run 40 12 8 3 3 7 zero.
Compute run 20 20 15 8 3 3 zero.
