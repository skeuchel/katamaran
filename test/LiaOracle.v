(* Tests for the oracle of Symbolic/LiaOracle.v. *)

From Stdlib Require Import List ZArith QArith FMapPositive Lia.
From Stdlib.micromega Require Import EnvRing RingMicromega Tauto ZMicromega.
From Katamaran Require Import Symbolic.LiaOracle.

Import ListNotations.
#[local] Open Scope Z_scope.

(* Goals whose negation is infeasible over the rationals. *)

Goal forall x y : Z, x <= y -> y <= x + 1 -> 2 * x <= 2 * y.
Proof. intros. lia_oracle. Qed.

Goal forall x y z : Z,
    x + y <= 3 -> y - z >= 2 -> x = 4 * z -> z > 5 -> x + 3 * y < 40 -> False.
Proof. intros. lia_oracle. Qed.

Goal forall a b : Z, 0 <= a < 8 -> 0 <= b < 8 -> a + 8 * b < 64.
Proof. intros. lia_oracle. Qed.

(* Several clauses. *)
Goal forall x y z : Z,
    3 * x + 2 * y <= 7 -> x - y = 1 -> z = x + y ->
    5 * x <= 10 /\ (z < 4 \/ y > 100).
Proof. intros. lia_oracle. Qed.

Goal forall x y : Z,
    3 * x <= 2 * y -> 2 * y <= 3 * x + 1 -> 3 * x <> 2 * y ->
    3 * x + 1 <> 2 * y -> False.
Proof. intros. lia_oracle. Qed.

Goal forall x y z : nat,
    (x + y <= z -> z - y >= x /\ Nat.max x y <= z /\ (x = z -> y = 0))%nat.
Proof. intros. lia_oracle. Qed.

(* Non-linear monomials are variables of the linear problem. *)
Goal forall x y : Z, x * y >= 1 -> 2 * (x * y) + 3 > 4.
Proof. intros. lia_oracle. Qed.

Goal forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Z,
    x0 <= x1 -> x1 <= x2 -> x2 <= x3 -> x3 <= x4 -> x4 <= x5 -> x5 <= x6 ->
    x6 <= x7 -> x7 <= x8 -> x8 <= x9 -> x0 <= x9.
Proof. intros. lia_oracle. Qed.

(* The oracle running in the kernel. *)
Goal forall x y z : Z,
    3 * x + 2 * y <= 7 -> x - y = 1 -> z = x + y ->
    5 * x <= 10 /\ (z < 4 \/ y > 100).
Proof. intros. lia_auto. Qed.

(* Not ported yet: reasoning over the integers ... *)
Goal forall x y : Z, 2 * x + 2 * y = 1 -> False.
Proof. intros. Fail lia_oracle. lia. Qed.

(* ... and the non-linear preprocessing of [lia]. *)
Goal forall x y : Z, x = 2 -> x * y >= 2 * y.
Proof. intros. Fail lia_oracle. lia. Qed.

Goal forall x y : Z, 0 <= x -> 0 <= y -> 0 <= x * y.
Proof. intros. Fail lia_oracle. lia. Qed.

(* Random clauses. Whatever the Simplex answers is checked: a certificate by
   [ZChecker], and a solution by evaluating the hypotheses. *)

Definition lcg (s : Z) : Z := (s * 1103515245 + 12345) mod 2147483648.
Definition rnd (s k : Z) : Z := (s / 65536) mod (2 * k + 1) - k.

Fixpoint rnd_expr (n : nat) (x : positive) (s : Z) : PExpr Z * Z :=
  match n with
  | O => let s := lcg s in (PEc (rnd s 10), s)
  | S n =>
      let s := lcg s in
      let (e, s') := rnd_expr n (Pos.succ x) s in
      (PEadd (PEmul (PEc (rnd s 3)) (PEX x)) e, s')
  end.

(* [m] hypotheses over [n] variables. *)
Fixpoint rnd_clause (m n : nat) (s : Z) : list (NFormula Z) * Z :=
  match m with
  | O => ([], s)
  | S m =>
      let (e, s) := rnd_expr n 1 s in
      let s := lcg s in
      let (l, s') := rnd_clause m n s in
      ((normZ e, if rnd s 3 =? 0 then Equal else NonStrict) :: l, s')
  end.

Variant verdict : Set := VUnsat | VSat | VBad.

Definition check (l : list (NFormula Z)) : verdict :=
  let '(cs, (tr, base)) := linearise_hyps 0 l (mempty, 1%positive) in
  let (cs, hs) := slacks base cs in
  match solve base default_fuel (length cs) cs (PositiveMap.empty _) with
  | Unsat _ _ => if ZChecker l (ZOracle default_fuel l) then VUnsat else VBad
  | Sat t =>
      let env x :=
        match mfind [x; 1%positive] tr with
        | Some i =>
            match PositiveMap.find i t with
            | Some row => lcst row
            | None => 0%Q
            end
        | None => 0%Q
        end in
      let holds '(p, o) :=
        let v := Qred (Pphi Qplus Qmult inject_Z env p) in
        match o with Equal => qzero v | _ => negb (qneg v) end in
      if forallb holds l then VSat else VBad
  | OutOfFuel => VBad
  end.

(* The numbers of infeasible, feasible and wrongly answered clauses among [k]. *)
Fixpoint run (k m n : nat) (s : Z) (acc : nat * nat * nat) : nat * nat * nat :=
  match k with
  | O => acc
  | S k =>
      let (l, s) := rnd_clause m n s in
      let '(u, sa, b) := acc in
      run k m n s
        match check l with
        | VUnsat => (S u, sa, b)
        | VSat => (u, S sa, b)
        | VBad => (u, sa, S b)
        end
  end.

Goal run 200 4 3 2 (0, 0, 0)%nat = (25, 175, 0)%nat.
Proof. vm_compute. reflexivity. Qed.

Goal run 200 6 4 1 (0, 0, 0)%nat = (46, 154, 0)%nat.
Proof. vm_compute. reflexivity. Qed.

Goal run 100 10 4 5 (0, 0, 0)%nat = (77, 23, 0)%nat.
Proof. vm_compute. reflexivity. Qed.

Goal run 40 12 8 3 (0, 0, 0)%nat = (10, 30, 0)%nat.
Proof. vm_compute. reflexivity. Qed.
