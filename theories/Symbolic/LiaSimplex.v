(******************************************************************************)
(* A certificate oracle for linear integer arithmetic, built on the Simplex   *)
(* of Dutertre and de Moura, "A Fast Linear-Arithmetic Solver for DPLL(T)",   *)
(* CAV 2006, with branch and bound and a test for integer solutions of the    *)
(* equalities.                                                                *)
(******************************************************************************)

From Stdlib Require Import Bool List ZArith FMapPositive Lia.
From Stdlib Require PrimInt63 PArray.
Import (notations) PrimInt63.
From Stdlib.micromega Require Import EnvRing RingMicromega Tauto ZMicromega VarMap.

Import ListNotations.

(** The oracle refutes a clause, a list of hypotheses [p = 0] and [p >= 0]
    over [Z], with a [ZArithProof]: a tree of case splits [x <= k \/ x >= k+1]
    whose leaves are Farkas combinations. Nothing here is proved: [ZChecker]
    checks the certificates.

    The Simplex is the one of Dutertre and de Moura. Every distinct linear form
    of the hypotheses gets a slack variable, a hypothesis becomes a bound on its
    variable, and the tableau is fixed up front. A conflict is a row whose basic
    variable violates a bound that no non-basic variable can repair; the row's
    coefficients are the Farkas multipliers. Before the Simplex, integer
    elimination checks that the equalities have an integer solution.

    For speed under [vm_compute]:
    - Numbers are primitive integers, and lists of them past 62 bits ([Num]).
    - Rows are kept fraction free, as in SMTInterpol: [h * x = sum a_j x_j]
      with integers [h > 0] and [a_j] without common divisor.
    - Bounds are integers: a hypothesis [g * q + c >= 0], with [q] primitive,
      bounds [q] by [ceil (-c / g)], justified by a cutting plane if [g] does
      not divide [c]. Non-basic variables sit at a bound or at 0, so they are
      integers too, and a basic variable is [num / h] for an integer [num]
      stored with its row. There are no rationals.
    - Bounds and values are primitive arrays, indexed by variable. Branch and
      bound goes back to older versions of them. *)

(** * Integers *)

Module Num.

  (** Two tiers:
      - [Sm i]: [|i| < 2^62], so [i <> min_int] and negation cannot overflow.
      - [Bg neg m]: [(-1)^neg * m] for [m >= 2^62], [m] a list of 63-bit limbs,
        least significant first, without leading zeros.
      Fraction-free rows need the second tier to be fast: their entries are
      determinants, and their updates multiply two of them. [Z] is only used
      to convert, and for divisions by a number of several limbs. *)
  Variant t : Set :=
  | Sm (i : PrimInt63.int)
  | Bg (neg : bool) (m : list PrimInt63.int).

  #[local] Abbreviation int := PrimInt63.int.
  #[local] Abbreviation ieqb := PrimInt63.eqb.
  #[local] Abbreviation iltb := PrimInt63.ltb.
  #[local] Abbreviation iltsb := PrimInt63.ltsb.
  #[local] Abbreviation iadd := PrimInt63.add.
  #[local] Abbreviation isub := PrimInt63.sub.
  #[local] Open Scope uint63_scope.

  Definition min_int : int := Eval vm_compute in PrimInt63.lsl 1 62.

  (** ** Magnitudes: lists of limbs *)

  Fixpoint trim (m : list int) : list int :=
    match m with
    | [] => []
    | x :: m => match trim m with [] => if ieqb x 0 then [] else [x] | m => x :: m end
    end.

  Fixpoint minc (a : list int) : list int :=
    match a with
    | [] => [1]
    | x :: a =>
        match PrimInt63.addc x 1 with
        | CarryType.C0 r => r :: a
        | CarryType.C1 r => r :: minc a
        end
    end.

  (** [a + b + c]. *)
  Fixpoint madd (c : bool) (a b : list int) : list int :=
    match a, b with
    | [], _ => if c then minc b else b
    | _, [] => if c then minc a else a
    | x :: a, y :: b =>
        match (if c then PrimInt63.addcarryc x y else PrimInt63.addc x y) with
        | CarryType.C0 r => r :: madd false a b
        | CarryType.C1 r => r :: madd true a b
        end
    end.

  (** [a - b - c], for [a >= b + c]; not trimmed. *)
  Fixpoint msub (c : bool) (a b : list int) : list int :=
    match a, b with
    | [], _ => []
    | x :: a, [] =>
        if c then
          match PrimInt63.subc x 1 with
          | CarryType.C0 r => r :: a
          | CarryType.C1 r => r :: msub true a []
          end
        else x :: a
    | x :: a, y :: b =>
        match (if c then PrimInt63.subcarryc x y else PrimInt63.subc x y) with
        | CarryType.C0 r => r :: msub false a b
        | CarryType.C1 r => r :: msub true a b
        end
    end.

  (** For trimmed [a] and [b]. *)
  Fixpoint mcmp (a b : list int) : comparison :=
    match a, b with
    | [], [] => Eq
    | [], _ => Lt
    | _, [] => Gt
    | x :: a, y :: b => match mcmp a b with Eq => PrimInt63.compare x y | c => c end
    end.

  (** [a * y + c]. *)
  Fixpoint mmul1 (c : int) (a : list int) (y : int) : list int :=
    match a with
    | [] => if ieqb c 0 then [] else [c]
    | x :: a =>
        let '(h, l) := PrimInt63.mulc x y in
        match PrimInt63.addc l c with
        | CarryType.C0 r => r :: mmul1 h a y
        | CarryType.C1 r => r :: mmul1 (iadd h 1) a y
        end
    end.

  (** Not trimmed. *)
  Fixpoint mmul (a b : list int) : list int :=
    match b with
    | [] => []
    | y :: b => madd false (mmul1 0 a y) (0 :: mmul a b)
    end.

  (** Quotient and remainder of the number with limbs [ra], most significant
      first, plus [r * 2^(63 * length ra)], by [y > r]. *)
  Fixpoint mdiv1 (r : int) (ra : list int) (y : int) (acc : list int) : list int * int :=
    match ra with
    | [] => (acc, r)
    | x :: ra =>
        let '(q, r) := PrimInt63.diveucl_21 r x y in mdiv1 r ra y (q :: acc)
    end.

  Definition mdivmod1 (a : list int) (y : int) : list int * int :=
    let '(q, r) := mdiv1 0 (rev a) y [] in (trim q, r).

  (** Shifts by [0 < k < 63] bits. *)
  Fixpoint mshr (k : int) (a : list int) : list int :=
    match a with
    | [] => []
    | x :: a' =>
        match a' with
        | [] => [PrimInt63.lsr x k]
        | y :: _ => PrimInt63.lor (PrimInt63.lsr x k) (PrimInt63.lsl y (isub 63 k)) :: mshr k a'
        end
    end.

  Fixpoint mshl (c k : int) (a : list int) : list int :=
    match a with
    | [] => if ieqb c 0 then [] else [c]
    | x :: a => PrimInt63.lor (PrimInt63.lsl x k) c :: mshl (PrimInt63.lsr x (isub 63 k)) k a
    end.

  (** Drop the factors 2 of [a <> 0]; also return how many limbs and bits. *)
  Fixpoint mstrip (a : list int) (limbs : nat) : list int * nat * int :=
    match a with
    | [] => ([], limbs, 0)
    | x :: a' =>
        if ieqb x 0 then mstrip a' (S limbs)
        else
          let k := PrimInt63.tail0 x in
          (if ieqb k 0 then a else trim (mshr k a), limbs, k)
    end.

  Definition mstrip' (a : list int) : list int :=
    let '(a, _, _) := mstrip a O in a.

  (** Binary gcd of odd [a] and [b]; each step removes a bit. *)
  Fixpoint mgcd_odd (fuel : nat) (a b : list int) : list int :=
    match fuel with
    | O => a
    | S fuel =>
        match mcmp a b with
        | Eq => a
        | Gt => mgcd_odd fuel (mstrip' (trim (msub false a b))) b
        | Lt => mgcd_odd fuel a (mstrip' (trim (msub false b a)))
        end
    end.

  Definition mgcd (a b : list int) : list int :=
    match a, b with
    | [], _ => b
    | _, [] => a
    | _, _ =>
        let '(a, la, ka) := mstrip a O in
        let '(b, lb, kb) := mstrip b O in
        let g := mgcd_odd (64 * (length a + length b)) a b in
        let '(l, k) :=
          if Nat.ltb la lb then (la, ka)
          else if Nat.ltb lb la then (lb, kb)
          else (la, if iltb ka kb then ka else kb) in
        repeat 0 l ++ (if ieqb k 0 then g else mshl 0 k g)
    end.

  (** [b^-1 mod 2^63] for odd [b]: Newton's iteration doubles the correct
      bits, from 3. *)
  Fixpoint minv (n : nat) (b x : int) : int :=
    match n with
    | O => x
    | S n => minv n b (PrimInt63.mul x (isub 2 (PrimInt63.mul b x)))
    end.

  (** [k] limbs of [a / b] for odd [b] dividing [a], from the least
      significant one (Jebelean): each is the low limb of the remainder times
      [inv = b^-1], which clears that limb. *)
  Fixpoint mdivexact_odd (k : nat) (inv : int) (a b : list int) (acc : list int) :
    list int :=
    match k, a with
    | S k, x :: _ =>
        let q := PrimInt63.mul x inv in
        match msub false a (mmul1 0 b q) with
        | _ :: a => mdivexact_odd k inv a b (q :: acc)
        | [] => rev (q :: acc)
        end
    | _, _ => rev acc
    end.

  (** [a / b] for [b <> 0] dividing [a]. *)
  Definition mdivexact (a b : list int) : list int :=
    let '(b, l, k) := mstrip b O in
    let a := skipn l a in
    let a := if ieqb k 0 then a else trim (mshr k a) in
    match b with
    | [] => []
    | b0 :: _ =>
        trim (mdivexact_odd (S (length a - length b)) (minv 5%nat b0 b0) a b [])
    end.

  (** ** Conversions *)

  (** For [i <> 0], unsigned. *)
  Fixpoint pos_of_int (fuel : nat) (i : int) : positive :=
    match fuel with
    | O => xH
    | S fuel =>
        if ieqb i 1 then xH
        else if ieqb (PrimInt63.land i 1) 0
        then xO (pos_of_int fuel (PrimInt63.lsr i 1))
        else xI (pos_of_int fuel (PrimInt63.lsr i 1))
    end.

  Definition z_of_uint (i : int) : Z :=
    if ieqb i 0 then Z0 else Zpos (pos_of_int 63%nat i).

  Definition z_of_int (i : int) : Z :=
    if iltsb i 0 then Z.opp (z_of_uint (isub 0 i)) else z_of_uint i.

  Fixpoint int_of_pos (p : positive) : int :=
    match p with
    | xH => 1
    | xO p => PrimInt63.lsl (int_of_pos p) 1
    | xI p => PrimInt63.lor (PrimInt63.lsl (int_of_pos p) 1) 1
    end.

  Definition z_of_mag (m : list int) : Z :=
    fold_right (fun x z => Z.add (Z.mul z 9223372036854775808%Z) (z_of_uint x)) Z0 m.

  Definition to_Z (a : t) : Z :=
    match a with
    | Sm i => z_of_int i
    | Bg neg m => if neg then Z.opp (z_of_mag m) else z_of_mag m
    end.

  (** The limbs of [z > 0], with fuel for [2^(63 * fuel)]. *)
  Fixpoint mag_of_Z (fuel : nat) (z : Z) : list int :=
    match fuel with
    | O => []
    | S fuel =>
        let '(q, r) := Z.div_eucl z 9223372036854775808%Z in
        (match r with Zpos p => int_of_pos p | _ => 0 end)
          :: match q with Z0 => [] | _ => mag_of_Z fuel q end
    end.

  Definition of_mag (neg : bool) (p : positive) : t :=
    if Pos.ltb p 4611686018427387904%positive then
      if neg then Sm (isub 0 (int_of_pos p)) else Sm (int_of_pos p)
    else Bg neg (mag_of_Z (Pos.size_nat p) (Zpos p)).

  Definition of_Z (z : Z) : t :=
    match z with
    | Z0 => Sm 0
    | Zpos p => of_mag false p
    | Zneg p => of_mag true p
    end.

  Definition zero : t := Sm 0.
  Definition one : t := Sm 1.

  (** The number of sign [neg] and magnitude [m], trimmed. *)
  Definition mk (neg : bool) (m : list int) : t :=
    match m with
    | [] => Sm 0
    | [l] => if iltb l min_int then Sm (if neg then isub 0 l else l) else Bg neg m
    | _ => Bg neg m
    end.

  Definition sign_mag (a : t) : bool * list int :=
    match a with
    | Sm x =>
        if iltsb x 0 then (true, [isub 0 x])
        else if ieqb x 0 then (false, []) else (false, [x])
    | Bg n m => (n, m)
    end.

  (** ** Arithmetic *)

  Definition add_slow (a b : t) : t :=
    let '(n1, m1) := sign_mag a in
    let '(n2, m2) := sign_mag b in
    if Bool.eqb n1 n2 then mk n1 (madd false m1 m2)
    else match mcmp m1 m2 with
         | Eq => Sm 0
         | Gt => mk n1 (trim (msub false m1 m2))
         | Lt => mk n2 (trim (msub false m2 m1))
         end.

  Definition add (a b : t) : t :=
    match a, b with
    | Sm x, Sm y =>
        let r := iadd x y in
        if iltsb (PrimInt63.land (PrimInt63.lxor x r) (PrimInt63.lxor y r)) 0
        then add_slow a b
        else if ieqb r min_int then add_slow a b
        else Sm r
    | _, _ => add_slow a b
    end.

  Definition opp (a : t) : t :=
    match a with
    | Sm x => Sm (isub 0 x)
    | Bg n m => Bg (negb n) m
    end.

  Definition sub (a b : t) : t :=
    match a, b with
    | Sm x, Sm y =>
        let r := isub x y in
        if iltsb (PrimInt63.land (PrimInt63.lxor x y) (PrimInt63.lxor x r)) 0
        then add_slow a (opp b)
        else if ieqb r min_int then add_slow a (opp b)
        else Sm r
    | _, _ => add_slow a (opp b)
    end.

  Definition mul_slow (a b : t) : t :=
    let '(n1, m1) := sign_mag a in
    let '(n2, m2) := sign_mag b in
    match m1, m2 with
    | [], _ | _, [] => Sm 0
    | _, [y] => mk (xorb n1 n2) (mmul1 0 m1 y)
    | [x], _ => mk (xorb n1 n2) (mmul1 0 m2 x)
    | _, _ => mk (xorb n1 n2) (trim (mmul m1 m2))
    end.

  (** If [r <> min_int] and [r / y = x], then [r] is the exact product. *)
  Definition mul (a b : t) : t :=
    match a, b with
    | Sm x, Sm y =>
        if ieqb y 0 then b
        else
          let r := PrimInt63.mul x y in
          if ieqb r min_int then mul_slow a b
          else if ieqb (PrimInt63.divs r y) x then Sm r
          else mul_slow a b
    | _, _ => mul_slow a b
    end.

  Definition abs (a : t) : t :=
    match a with
    | Sm x => if iltsb x 0 then Sm (isub 0 x) else a
    | Bg _ m => Bg false m
    end.

  Definition compare (a b : t) : comparison :=
    match a, b with
    | Sm x, Sm y => PrimInt63.compares x y
    | Sm _, Bg n _ => if n then Gt else Lt
    | Bg n _, Sm _ => if n then Lt else Gt
    | Bg n1 m1, Bg n2 m2 =>
        match n1, n2 with
        | false, true => Gt
        | true, false => Lt
        | false, false => mcmp m1 m2
        | true, true => mcmp m2 m1
        end
    end.

  Definition ltb (a b : t) : bool :=
    match a, b with
    | Sm x, Sm y => iltsb x y
    | _, _ => match compare a b with Lt => true | _ => false end
    end.

  Definition eqb (a b : t) : bool :=
    match a, b with
    | Sm x, Sm y => ieqb x y
    | Bg _ _, Bg _ _ => match compare a b with Eq => true | _ => false end
    | _, _ => false
    end.

  Definition is_zero (a : t) : bool :=
    match a with Sm x => ieqb x 0 | _ => false end.
  Definition is_one (a : t) : bool :=
    match a with Sm x => ieqb x 1 | _ => false end.
  Definition is_pos (a : t) : bool :=
    match a with Sm x => iltsb 0 x | Bg n _ => negb n end.
  Definition is_neg (a : t) : bool :=
    match a with Sm x => iltsb x 0 | Bg n _ => n end.

  (** Euclid needs fewer than 92 steps below [2^63]. *)
  Fixpoint igcd (fuel : nat) (a b : int) : int :=
    match fuel with
    | O => a
    | S fuel => if ieqb b 0 then a else igcd fuel b (PrimInt63.mod a b)
    end.

  (** Non-negative. *)
  Definition gcd (a b : t) : t :=
    match abs a, abs b with
    | Sm x, Sm y => Sm (igcd 100%nat x y)
    | Bg _ m, Sm y | Sm y, Bg _ m =>
        if ieqb y 0 then Bg false m else Sm (igcd 100%nat y (snd (mdivmod1 m y)))
    | Bg _ m1, Bg _ m2 => mk false (mgcd m1 m2)
    end.

  (** Rounded towards 0. *)
  Definition quot (a b : t) : t :=
    match a, b with
    | Sm x, Sm y => Sm (PrimInt63.divs x y)
    | Bg n m, Sm y =>
        let ny := iltsb y 0 in
        mk (xorb n ny) (fst (mdivmod1 m (if ny then isub 0 y else y)))
    | Sm _, Bg _ _ => Sm 0
    | _, _ => of_Z (Z.quot (to_Z a) (to_Z b))
    end.

  (** Division of [a] by a divisor [b]. *)
  Definition divexact (a b : t) : t :=
    match a, b with
    | Bg n1 m1, Bg n2 m2 => mk (xorb n1 n2) (mdivexact m1 m2)
    | _, _ => quot a b
    end.

  (** Rounded down, for [b > 0]. *)
  Definition fdiv (a b : t) : t :=
    match a, b with
    | Sm x, Sm y =>
        let q := PrimInt63.divs x y in
        if iltsb x 0 then
          if ieqb (PrimInt63.mods x y) 0 then Sm q else Sm (isub q 1)
        else Sm q
    | Bg n m, Sm y =>
        let '(q, r) := mdivmod1 m y in
        if n then if ieqb r 0 then mk true q else mk true (minc q) else mk false q
    | Sm x, Bg _ _ => if iltsb x 0 then Sm (isub 0 1) else Sm 0
    | _, _ => of_Z (Z.div (to_Z a) (to_Z b))
    end.

  (** Rounded up, for [b > 0]. *)
  Definition cdiv (a b : t) : t := opp (fdiv (opp a) b).

  Definition divides (b a : t) : bool :=
    match a, b with
    | Sm x, Sm y => ieqb (PrimInt63.mods x y) 0
    | Bg _ m, Sm y => ieqb (snd (mdivmod1 m (if iltsb y 0 then isub 0 y else y))) 0
    | Sm x, Bg _ _ => ieqb x 0
    | _, _ => Z.eqb (Z.rem (to_Z a) (to_Z b)) 0
    end.

  (** For [a, b > 0]. *)
  Definition lcm (a b : t) : t := mul (divexact a (gcd a b)) b.

End Num.

#[local] Abbreviation int := PrimInt63.int.
#[local] Abbreviation num := Num.t.
#[local] Abbreviation array := PArray.array.
#[local] Notation "t .[ i ]" := (PArray.get t i)
  (at level 1, left associativity, format "t .[ i ]").
#[local] Notation "t .[ i <- a ]" := (PArray.set t i a)
  (at level 1, left associativity, format "t .[ i <- a ]").

(** * Sparse vectors

    Sorted by variable, without zero coefficients. Variables are below [2^62],
    so the unsigned order is the signed one. *)

Definition vec : Set := list (int * num).

Fixpoint vget (x : int) (v : vec) : num :=
  match v with
  | [] => Num.zero
  | (y, a) :: v =>
      if PrimInt63.ltb y x then vget x v
      else if PrimInt63.eqb y x then a else Num.zero
  end.

Definition vscale (c : num) (v : vec) : vec :=
  map (fun '(x, a) => (x, Num.mul c a)) v.

(** [c2 * v2] without the variable [skip]. *)
Fixpoint vscale_skip (skip : int) (c2 : num) (v2 : vec) : vec :=
  match v2 with
  | [] => []
  | (x, a) :: v2 =>
      if PrimInt63.eqb x skip then vscale c2 v2
      else (x, Num.mul c2 a) :: vscale_skip skip c2 v2
  end.

(** [c1 * v1 + c2 * v2] without the variable [skip] of [v2], which is not in
    [v1]. *)
Fixpoint vcomb (skip : int) (c1 c2 : num) (v1 : vec) : vec -> vec :=
  match v1 with
  | [] => vscale_skip skip c2
  | (x1, a1) :: v1' =>
      fix go (v2 : vec) : vec :=
        match v2 with
        | [] => vscale c1 v1
        | (x2, a2) :: v2' =>
            if PrimInt63.eqb x2 skip then go v2'
            else if PrimInt63.ltb x1 x2 then
              (x1, Num.mul c1 a1) :: vcomb skip c1 c2 v1' v2
            else if PrimInt63.eqb x1 x2 then
              let a := Num.add (Num.mul c1 a1) (Num.mul c2 a2) in
              if Num.is_zero a then vcomb skip c1 c2 v1' v2'
              else (x1, a) :: vcomb skip c1 c2 v1' v2'
            else (x2, Num.mul c2 a2) :: go v2'
        end
  end.

(** The gcd of [g] and the coefficients of [v]. *)
Fixpoint vgcd (g : num) (v : vec) : num :=
  if Num.is_one g then g
  else match v with
       | [] => g
       | (_, a) :: v => vgcd (Num.gcd g a) v
       end.

Definition vdiv (g : num) (v : vec) : vec :=
  map (fun '(x, a) => (x, Num.divexact a g)) v.

Definition veval (vals : array num) (v : vec) : num :=
  fold_left (fun acc '(x, a) => Num.add acc (Num.mul a vals.[x])) v Num.zero.

Fixpoint veqb (v w : vec) : bool :=
  match v, w with
  | [], [] => true
  | (x, a) :: v, (y, b) :: w =>
      if PrimInt63.eqb x y then if Num.eqb a b then veqb v w else false
      else false
  | _, _ => false
  end.

(** * Bounds and their justification *)

(** The formulas certificates refer to: a hypothesis of the clause, the
    cutting plane of one, and the case of the [d]-th split on the current
    branch. *)
Variant fact : Set :=
| FHyp (i : nat)
| FCut (i : nat)
| FSplit (d : nat).

(** A bound [x >= val] or [x <= val]. The inequality [x - val >= 0], or
    [val - x >= 0], is the formula [bfact] divided by [bdiv], negated if
    [bneg]. [beq]: that formula is an equality (only those are negated). *)
Record bnd : Set := Bnd {
  bval : num;
  bfact : fact;
  bdiv : num;
  bneg : bool;
  beq : bool;
}.

(** A Farkas combination: bounds with positive multipliers. *)
Definition conflict : Set := list (bnd * num).

(** * The Simplex *)

(** [rhead * rvar = sum rents] with [rhead > 0] and no common divisor; the
    value of [rvar] is [rnum / rhead], [rnum] the value of [rents]. *)
Record row : Set := Row {
  rvar : int;
  rhead : num;
  rnum : num;
  rents : vec;
}.

(** [vals] holds the values of the non-basic variables. *)
Record state : Type := St {
  rows : list row;
  vals : array num;
  lo : array (option bnd);
  hi : array (option bnd);
}.

Definition below (b : option bnd) (v : num) : bool :=
  match b with Some b => Num.ltb v (bval b) | None => false end.
Definition above (b : option bnd) (v : num) : bool :=
  match b with Some b => Num.ltb (bval b) v | None => false end.

Definition below_row (b : option bnd) (r : row) : option bnd :=
  match b with
  | Some b' => if Num.ltb (rnum r) (Num.mul (bval b') (rhead r)) then b else None
  | None => None
  end.
Definition above_row (b : option bnd) (r : row) : option bnd :=
  match b with
  | Some b' => if Num.ltb (Num.mul (bval b') (rhead r)) (rnum r) then b else None
  | None => None
  end.

(** The basic variable out of its bounds with the least index: its row, whether
    it is too small, and the bound it violates. *)
Fixpoint violated (lo hi : array (option bnd)) (rs : list row)
  (best : option (row * bool * bnd)) : option (row * bool * bnd) :=
  match rs with
  | [] => best
  | r :: rs =>
      let x := rvar r in
      if match best with
         | Some (r', _, _) => PrimInt63.ltb (rvar r') x
         | None => false
         end
      then violated lo hi rs best
      else match below_row lo.[x] r with
           | Some b => violated lo hi rs (Some (r, true, b))
           | None =>
               match above_row hi.[x] r with
               | Some b => violated lo hi rs (Some (r, false, b))
               | None => violated lo hi rs best
               end
           end
  end.

(** The first non-basic variable of a row that can move its basic variable up
    ([inc]) or down. *)
Fixpoint entering (st : state) (inc : bool) (v : vec) : option (int * num) :=
  match v with
  | [] => None
  | (k, a) :: v =>
      if (if Bool.eqb (Num.is_pos a) inc
          then match (hi st).[k] with
               | Some b => Num.ltb (vals st).[k] (bval b)
               | None => true
               end
          else match (lo st).[k] with
               | Some b => Num.ltb (bval b) (vals st).[k]
               | None => true
               end)
      then Some (k, a) else entering st inc v
  end.

(** The row of [x], and the bound [b] that [x] violates and nothing can
    repair, give the Farkas combination: [rhead] times [b], and [|a|] times the
    bound that blocks each non-basic variable. *)
Definition explain (st : state) (r : row) (inc : bool) (b : bnd) : conflict :=
  (b, rhead r) ::
  fold_right
    (fun '(k, a) c =>
       match (if Bool.eqb (Num.is_pos a) inc then (hi st).[k] else (lo st).[k]) with
       | Some b => (b, Num.abs a) :: c
       | None => c
       end)
    [] (rents r).

(** Replace [j] in [r] by [e / h], where [numE] is the value of [e] and [vj]
    the old value of [j]. *)
Definition substitute (j : int) (h : num) (e : vec) (numE vj : num) (r : row) : row :=
  let b := vget j (rents r) in
  if Num.is_zero b then r
  else
    (* h * h_r * x_r = b * e + h * (rest of the row), divided by gcd b h *)
    let rest := Num.sub (rnum r) (Num.mul b vj) in
    let g0 := Num.gcd b h in
    let b := Num.divexact b g0 in
    let h := Num.divexact h g0 in
    let ents := vcomb j b h e (rents r) in
    let head := Num.mul h (rhead r) in
    let n := Num.add (Num.mul b numE) (Num.mul h rest) in
    let g := vgcd head ents in
    if Num.is_one g then Row (rvar r) head n ents
    else Row (rvar r) (Num.divexact head g) (Num.divexact n g) (vdiv g ents).

(** Make [j], with coefficient [aj] in [r], basic, and set the variable of
    [r] to [v]. *)
Definition pivot (st : state) (r : row) (j : int) (aj : num) (v : num) : state :=
  let x := rvar r in
  let vj := (vals st).[j] in
  let vals := (vals st).[x <- v] in
  (* |aj| * j = s * (h * x - rest), s the sign of aj *)
  let neg := Num.is_neg aj in
  let h := Num.abs aj in
  let e := vcomb j (if neg then Num.opp (rhead r) else rhead r)
             (if neg then Num.one else Num.opp Num.one)
             [(x, Num.one)] (rents r) in
  let numE := veval vals e in
  St (map (fun r' =>
             if PrimInt63.eqb (rvar r') x then Row j h numE e
             else substitute j h e numE vj r')
          (rows st))
     vals (lo st) (hi st).

Variant sresult : Type :=
| Feasible (st : state)
| Infeasible (c : conflict)
| Stuck.

Variant step : Type := Done (r : sresult) | More (st : state).

(** One iteration of [check]: Bland's rule, the least variables first. *)
Definition step1 (st : state) : step :=
  match violated (lo st) (hi st) (rows st) None with
  | None => Done (Feasible st)
  | Some (r, inc, b) =>
      match entering st inc (rents r) with
      | None => Done (Infeasible (explain st r inc b))
      | Some (j, aj) => More (pivot st r j aj (bval b))
      end
  end.

(** At most [p] iterations. *)
Fixpoint loop (p : positive) (st : state) : step :=
  match p with
  | xH => step1 st
  | xO p => match loop p st with More st => loop p st | d => d end
  | xI p =>
      match loop p st with
      | More st => match loop p st with More st => step1 st | d => d end
      | d => d
      end
  end.

Definition check (p : positive) (st : state) : sresult :=
  match loop p st with Done r => r | More _ => Stuck end.

(** Add a bound to a basic variable; [lower] tells which. *)
Definition assert (st : state) (x : int) (lower : bool) (b : bnd) : state + conflict :=
  if lower then
    match (hi st).[x] with
    | Some u => if Num.ltb (bval u) (bval b) then inr [(b, Num.one); (u, Num.one)]
               else inl (St (rows st) (vals st) (lo st).[x <- Some b] (hi st))
    | None => inl (St (rows st) (vals st) (lo st).[x <- Some b] (hi st))
    end
  else
    match (lo st).[x] with
    | Some l => if Num.ltb (bval b) (bval l) then inr [(l, Num.one); (b, Num.one)]
               else inl (St (rows st) (vals st) (lo st) (hi st).[x <- Some b])
    | None => inl (St (rows st) (vals st) (lo st) (hi st).[x <- Some b])
    end.

(** * Branch and bound *)

(** The basic variable below [n] with the least index whose value is not an
    integer, and its value rounded down. *)
Fixpoint fractional (n : int) (rs : list row) (best : option (int * num)) :
  option (int * num) :=
  match rs with
  | [] => best
  | r :: rs =>
      let x := rvar r in
      if PrimInt63.ltb x n &&
         match best with Some (y, _) => PrimInt63.ltb x y | None => true end &&
         negb (Num.divides (rhead r) (rnum r))
      then fractional n rs (Some (x, Num.fdiv (rnum r) (rhead r)))
      else fractional n rs best
  end.

(** A refutation: a Farkas combination, or a split [x >= k + 1 \/ x <= k]. *)
Inductive tree : Set :=
| Leaf (c : conflict)
| Node (x : int) (k : num) (t1 t2 : tree).

Variant bbresult : Type :=
| Refuted (t : tree)
| Model (st : state)
| GaveUp.

Definition pivot_fuel : positive := 100000.

(** Depth first, with at most [depth] nested and [budget] splits in all. *)
Fixpoint bb (depth : nat) (n : int) (d : nat) (st : state) (budget : nat) :
  bbresult * nat :=
  match check pivot_fuel st with
  | Infeasible c => (Refuted (Leaf c), budget)
  | Stuck => (GaveUp, budget)
  | Feasible st =>
      match fractional n (rows st) None with
      | None => (Model st, budget)
      | Some (x, k) =>
          match depth, budget with
          | S depth, S budget =>
              let k1 := Num.add k Num.one in
              let (r1, budget) :=
                match assert st x true (Bnd k1 (FSplit d) Num.one false false) with
                | inl st => bb depth n (S d) st budget
                | inr c => (Refuted (Leaf c), budget)
                end in
              match r1 with
              | Refuted t1 =>
                  let (r2, budget) :=
                    match assert st x false (Bnd k (FSplit d) Num.one false false) with
                    | inl st => bb depth n (S d) st budget
                    | inr c => (Refuted (Leaf c), budget)
                    end in
                  match r2 with
                  | Refuted t2 => (Refuted (Node x k t1 t2), budget)
                  | r2 => (r2, budget)
                  end
              | r1 => (r1, budget)
              end
          | _, _ => (GaveUp, budget)
          end
      end
  end.

(** * Linearisation

    The monomials of the hypotheses are the variables [0 .. n-1] of the linear
    problem, numbered in order of appearance. *)

(** A monomial is the list [xn; en; ...; x1; e1] of its variables, in
    decreasing order, and their exponents. A trie numbers them. *)
#[local] Unset Elimination Schemes.
Inductive mtrie : Type :=
| MNode (v : option int) (ch : PositiveMap.t mtrie).
#[local] Set Elimination Schemes.

Definition mempty : mtrie := MNode None (PositiveMap.empty _).

Fixpoint mfind (m : list positive) (t : mtrie) : option int :=
  match m, t with
  | [], MNode v _ => v
  | x :: m, MNode _ ch =>
      match PositiveMap.find x ch with
      | Some t => mfind m t
      | None => None
      end
  end.

Fixpoint madd (m : list positive) (i : int) (t : mtrie) : mtrie :=
  let (v, ch) := t in
  match m with
  | [] => MNode (Some i) ch
  | x :: m =>
      let t := match PositiveMap.find x ch with Some t => t | None => mempty end in
      MNode v (PositiveMap.add x (madd m i t) ch)
  end.

(** The trie, the number of monomials, and the monomials in reverse order. *)
Record mons : Type := Mons { mtr : mtrie; mcount : int; mlist : list (list positive) }.

Definition intern (m : list positive) (st : mons) : int * mons :=
  match mfind m (mtr st) with
  | Some x => (x, st)
  | None =>
      let n := mcount st in
      (n, Mons (madd m n (mtr st)) (PrimInt63.add n 1%uint63) (m :: mlist st))
  end.

Definition mon_mul (x i : positive) (m : list positive) : list positive :=
  match m with
  | y :: e :: m' => if Pos.eqb x y then y :: Pos.add e i :: m' else x :: i :: m
  | _ => x :: i :: m
  end.

(** Add [m * p] to the unsorted vector and the constant, where the first
    variable of [p] is [jmp]. *)
Fixpoint linearise (jmp : positive) (m : list positive) (p : Pol Z)
  (acc : vec * Z * mons) : vec * Z * mons :=
  match p with
  | Pc c =>
      match c, m with
      | Z0, _ => acc
      | _, [] => let '(v, k, st) := acc in (v, Z.add k c, st)
      | _, _ =>
          let '(v, k, st) := acc in
          let (x, st) := intern m st in
          ((x, Num.of_Z c) :: v, k, st)
      end
  | Pinj j p => linearise (Pos.add jmp j) m p acc
  | PX p i q =>
      linearise (Pos.succ jmp) m q (linearise jmp (mon_mul jmp i m) p acc)
  end.

Fixpoint vinsert (x : int) (a : num) (v : vec) : vec :=
  match v with
  | [] => [(x, a)]
  | (y, b) :: v' => if PrimInt63.ltb x y then (x, a) :: v else (y, b) :: vinsert x a v'
  end.

Definition vsort (v : vec) : vec := fold_left (fun w '(x, a) => vinsert x a w) v [].

(** A hypothesis [i] as [v + c op 0]. *)
Record lhyp : Type := LHyp { hidx : nat; hop : Op1; hvec : vec; hcst : num }.

Fixpoint linearise_hyps (i : nat) (l : list (NFormula Z)) (st : mons) :
  list lhyp * mons :=
  match l with
  | [] => ([], st)
  | (p, o) :: l =>
      let '(v, c, st) := linearise 1 [] p ([], Z0, st) in
      let (hs, st) := linearise_hyps (S i) l st in
      (LHyp i o (vsort v) (Num.of_Z c) :: hs, st)
  end.

(** * The problem

    Hypothesis [i], [v + c >= 0] with [v = s * g * q], [g > 0], [s] the sign
    of the first coefficient of [v], and [q] primitive, is a bound on the
    variable of [q]:
    - [q >= ceil (-c / g)] if [s = 1], and [q <= floor (c / g)] if [s = -1].
      If [g] does not divide [c], the bound is the cutting plane of [i].
    An equality is both bounds, with [g] dividing [c] (else it has no integer
    solution). Every [q] of two or more variables gets a slack variable, from
    [n] on, defined by a row [1 * slack = q]. *)

Variant prep : Type :=
| Bounds (bs : list (int * bool * bnd)) (slacks : list (vec * int)) (next : int)
| Trivial (pf : ZArithProof).

Definition slack (q : vec) (slacks : list (vec * int)) (next : int) :
  int * list (vec * int) * int :=
  match q with
  | [(x, a)] => if Num.is_one a then (x, slacks, next) else (next, (q, next) :: slacks, PrimInt63.add next 1%uint63)
  | _ =>
      match List.find (fun '(q', _) => veqb q q') slacks with
      | Some (_, s) => (s, slacks, next)
      | None => (next, (q, next) :: slacks, PrimInt63.add next 1%uint63)
      end
  end.

Definition prep_hyp (h : lhyp) (acc : prep) : prep :=
  match acc with
  | Trivial _ => acc
  | Bounds bs sl next =>
      let i := hidx h in
      let c := hcst h in
      match hop h, hvec h with
      | (NonEqual | Strict), _ => acc
      | Equal, [] =>
          if Num.is_zero c then acc else Trivial (RatProof (PsatzIn Z i) DoneProof)
      | NonStrict, [] =>
          if Num.is_neg c then Trivial (RatProof (PsatzIn Z i) DoneProof) else acc
      | o, ((_, a0) :: _) as v =>
          let neg := Num.is_neg a0 in
          let g := vgcd (Num.abs a0) v in
          let q := vdiv (if neg then Num.opp g else g) v in
          let '(x, sl, next) := slack q sl next in
          match o with
          | Equal =>
              if Num.divides g c then
                let b := Num.divexact (if neg then c else Num.opp c) g in
                Bounds ((x, true, Bnd b (FHyp i) g neg true)
                          :: (x, false, Bnd b (FHyp i) g (negb neg) true) :: bs)
                  sl next
              else Trivial (CutProof (PsatzIn Z i) DoneProof)
          | _ =>
              let b := if neg then Num.fdiv c g else Num.cdiv (Num.opp c) g in
              let bd :=
                if Num.divides g c then Bnd b (FHyp i) g false false
                else Bnd b (FCut i) Num.one false false in
              Bounds ((x, negb neg, bd) :: bs) sl next
          end
      end
  end.

(** The initial state: the slack variables are basic, the others are at the
    bound closest to 0. *)
Definition initial (n next : int) (bs : list (int * bool * bnd))
  (slacks : list (vec * int)) : state + conflict :=
  let lohi :=
    fold_left
      (fun (acc : array (option bnd) * array (option bnd) + conflict)
           (xb : int * bool * bnd) =>
         let '(x, lower, b) := xb in
         match acc with
         | inr _ => acc
         | inl (lo, hi) =>
             if lower then
               if above lo.[x] (bval b) || match lo.[x] with None => true | _ => false end
               then match hi.[x] with
                    | Some u => if Num.ltb (bval u) (bval b) then inr [(b, Num.one); (u, Num.one)]
                               else inl (lo.[x <- Some b], hi)
                    | None => inl (lo.[x <- Some b], hi)
                    end
               else acc
             else
               if below hi.[x] (bval b) || match hi.[x] with None => true | _ => false end
               then match lo.[x] with
                    | Some l => if Num.ltb (bval b) (bval l) then inr [(l, Num.one); (b, Num.one)]
                               else inl (lo, hi.[x <- Some b])
                    | None => inl (lo, hi.[x <- Some b])
                    end
               else acc
         end)
      bs (inl (PArray.make next None, PArray.make next None)) in
  
  match lohi with
  | inr c => inr c
  | inl (lo, hi) =>
      let fix init (k : nat) (x : int) (vals : array num) :=
        match k with
        | O => vals
        | S k =>
            let v :=
              match lo.[x], hi.[x] with
              | Some l, _ => if Num.is_pos (bval l) then bval l else
                               match hi.[x] with
                               | Some u => if Num.is_neg (bval u) then bval u else Num.zero
                               | None => Num.zero
                               end
              | None, Some u => if Num.is_neg (bval u) then bval u else Num.zero
              | None, None => Num.zero
              end in
            init k (PrimInt63.add x 1%uint63) vals.[x <- v]
        end in
      let vals := init (Z.to_nat (Num.z_of_int n)) 0%uint63 (PArray.make next Num.zero) in
      inl (St (map (fun '(q, s) => Row s Num.one (veval vals q) q) slacks) vals lo hi)
  end.

(** * Certificates *)

Definition mon_pexpr : list positive -> PExpr Z :=
  fix go m :=
    match m with
    | x :: e :: m => PEmul (PEpow (PEX x) (Npos e)) (go m)
    | _ => PEc 1%Z
    end.

(** [2 * x - 2 * k - 1]: [SplitProof] cuts it into [x >= k + 1] and [x <= k]. *)
Definition split_pol (mons : array (list positive)) (x : int) (k : num) : PolC Z :=
  normZ (PEsub (PEmul (PEc 2%Z) (mon_pexpr mons.[x]))
           (PEc (Z.add (Z.mul 2 (Num.to_Z k)) 1))).

Fixpoint index_of (i : nat) (l : list nat) : nat :=
  match l with
  | [] => O
  | j :: l => if Nat.eqb i j then O else S (index_of i l)
  end.

(** The position of a fact in the list of formulas of [ZChecker], after the
    cuts [cuts] (in the order they are added) and [d] splits. *)
Definition fact_index (cuts : list nat) (ncuts d : nat) (f : fact) : nat :=
  match f with
  | FHyp i => ncuts + d + i
  | FCut i => ncuts + d - 1 - index_of i cuts
  | FSplit s => d - 1 - s
  end.

(** The combination [c] with integer coefficients, as a [Psatz]. *)
Definition farkas (idx : fact -> nat) (c : conflict) : Psatz Z :=
  let l := fold_left
             (fun l '(b, m) => Num.lcm l (Num.divexact (bdiv b) (Num.gcd m (bdiv b))))
             c Num.one in
  let ns := map (fun '(b, m) =>
                   let gm := Num.gcd m (bdiv b) in
                   (b, Num.mul (Num.divexact m gm) (Num.divexact l (Num.divexact (bdiv b) gm))))
             c in
  let g := fold_left (fun g '(_, n) => Num.gcd g n) ns Num.zero in
  fold_left
    (fun w '(b, n) =>
       let n := Num.to_Z (Num.divexact n g) in
       let i := PsatzIn Z (idx (bfact b)) in
       let t :=
         if beq b then PsatzMulC (Pc (if bneg b then Z.opp n else n)) i
         else if Z.eqb n 1 then i
         else PsatzMulE (PsatzC n) i in
       match w with PsatzZ _ => t | _ => PsatzAdd t w end)
    ns (PsatzZ Z).

Fixpoint tree_cuts (t : tree) (acc : list nat) : list nat :=
  match t with
  | Leaf c =>
      fold_left
        (fun acc '(b, _) =>
           match bfact b with
           | FCut i => if existsb (Nat.eqb i) acc then acc else i :: acc
           | _ => acc
           end)
        c acc
  | Node _ _ t1 t2 => tree_cuts t2 (tree_cuts t1 acc)
  end.

Fixpoint tree_proof (mons : array (list positive)) (cuts : list nat) (ncuts d : nat)
  (t : tree) : ZArithProof :=
  match t with
  | Leaf c => RatProof (farkas (fact_index cuts ncuts d) c) DoneProof
  | Node x k t1 t2 =>
      SplitProof (split_pol mons x k)
        (tree_proof mons cuts ncuts (S d) t1) (tree_proof mons cuts ncuts (S d) t2)
  end.

Definition proof (mons : array (list positive)) (t : tree) : ZArithProof :=
  let cuts := rev (tree_cuts t []) in
  let ncuts := length cuts in
  snd (fold_left
         (fun '(k, pf) i => (S k, fun p => pf (CutProof (PsatzIn Z (k + i)) p)))
         cuts (O, fun p => p))
    (tree_proof mons cuts ncuts O t).

(** * Integer solutions of the equalities

    The equalities alone may have no integer solution, which branching cannot
    show. Integer elimination, as in the omega test, finds an integer
    combination of them whose coefficients have a gcd that does not divide its
    constant. Every row [co * x = b] is the combination [comb] of hypotheses.
    Column operations, [x_k -= q * x_j] in every row, change the variables but
    not that gcd: they reduce a row to a single variable [a * x_k = b], which
    has a solution only if [a] divides [b], and then [x_k] is eliminated. *)

Record drow : Type := DRow { dco : vec; db : num; dcomb : vec }.

(** Add [d] to the coefficient of [x] in [v]. *)
Fixpoint vadd1 (x : int) (d : num) (v : vec) : vec :=
  match v with
  | [] => [(x, d)]
  | (y, a) :: v' =>
      if PrimInt63.ltb x y then (x, d) :: v
      else if PrimInt63.eqb x y then
        let a := Num.add a d in if Num.is_zero a then v' else (x, a) :: v'
      else (y, a) :: vadd1 x d v'
  end.

(** Column [k] minus [q] times column [j], in every row. *)
Definition colop (j k : int) (q : num) (rs : list drow) : list drow :=
  map (fun r =>
         let a := vget j (dco r) in
         if Num.is_zero a then r
         else DRow (vadd1 k (Num.opp (Num.mul q a)) (dco r)) (db r) (dcomb r))
    rs.

(** A coefficient of [v] of least absolute value. *)
Definition min_abs (v : vec) : int * num :=
  match v with
  | [] => (0%uint63, Num.zero)
  | ja :: v =>
      fold_left (fun '(j, a) '(k, b) => if Num.ltb (Num.abs b) (Num.abs a) then (k, b) else (j, a))
        v ja
  end.

(** Reduce the first row to a single variable. *)
Fixpoint reduce (fuel : nat) (rs : list drow) : list drow :=
  match fuel, rs with
  | S fuel, p :: _ =>
      match dco p with
      | _ :: _ :: _ =>
          let '(j, aj) := min_abs (dco p) in
          reduce fuel
            (fold_left
               (fun rs '(k, ak) =>
                  if PrimInt63.eqb k j then rs else colop j k (Num.quot ak aj) rs)
               (dco p) rs)
      | _ => rs
      end
  | _, _ => rs
  end.

Definition dnorm (r : drow) : drow :=
  let g := vgcd (vgcd (Num.gcd (db r) Num.zero) (dco r)) (dcomb r) in
  if Num.is_one g || Num.is_zero g then r
  else DRow (vdiv g (dco r)) (Num.divexact (db r) g) (vdiv g (dcomb r)).

(** Eliminate [x_k] from [r] with [p], which is [a * x_k = b]. *)
Definition elim (k : int) (a : num) (p r : drow) : drow :=
  let rk := vget k (dco r) in
  if Num.is_zero rk then r
  else
    let g := Num.gcd a rk in
    let s := Num.divexact a g in
    let t := Num.opp (Num.divexact rk g) in
    dnorm (DRow (vcomb 9223372036854775807%uint63 t s (dco p) (dco r))
             (Num.add (Num.mul s (db r)) (Num.mul t (db p)))
             (vcomb 9223372036854775807%uint63 t s (dcomb p) (dcomb r))).

(** The combination of the equalities [comb]. *)
Definition dcert (comb : vec) : Psatz Z :=
  fold_left
    (fun w '(i, a) =>
       let t := PsatzMulC (Pc (Num.to_Z a)) (PsatzIn Z (Z.to_nat (Num.z_of_int i))) in
       match w with PsatzZ _ => t | _ => PsatzAdd t w end)
    comb (PsatzZ Z).

(** A refutation, if the equalities [rs] have no integer solution. *)
Fixpoint dioph (fuel : nat) (rs : list drow) : option ZArithProof :=
  match fuel, rs with
  | S fuel, p :: rs =>
      match dco p with
      | [] =>
          if Num.is_zero (db p) then dioph fuel rs
          else Some (RatProof (dcert (dcomb p)) DoneProof)
      | _ =>
          match reduce 1000 (p :: rs) with
          | p :: rs =>
              match dco p with
              | [(k, a)] =>
                  if Num.divides a (db p) then dioph fuel (map (elim k a p) rs)
                  else Some (CutProof (dcert (dcomb p)) DoneProof)
              | _ => None
              end
          | [] => None
          end
      end
  | _, _ => None
  end.

Fixpoint int_of_nat (n : nat) : int :=
  match n with O => 0%uint63 | S n => PrimInt63.add (int_of_nat n) 1%uint63 end.

Definition equalities (hs : list lhyp) : list drow :=
  fold_right
    (fun h rs =>
       match hop h, hvec h with
       | Equal, _ :: _ =>
           DRow (hvec h) (Num.opp (hcst h)) [(int_of_nat (hidx h), Num.one)] :: rs
       | _, _ => rs
       end)
    [] hs.

(** * The oracle *)

Record params : Set := Params { depth : nat; budget : nat }.

Definition default_params : params := Params 16 64.

Variant answer : Type :=
| Proof (pf : ZArithProof)
(** A solution, [value st k] for the [k]-th monomial of [mons]. *)
| Sat (n : int) (st : state) (mons : list (list positive))
| Unknown.

Fixpoint array_of_list {A} (a : array A) (i : int) (l : list A) : array A :=
  match l with
  | [] => a
  | x :: l => array_of_list a.[i <- x] (PrimInt63.add i 1%uint63) l
  end.

Definition solve (ps : params) (l : list (NFormula Z)) : answer :=
  let (hs, ms) := linearise_hyps 0 l (Mons mempty 0%uint63 []) in
  let n := mcount ms in
  match fold_left (fun acc h => prep_hyp h acc) hs (Bounds [] [] n) with
  | Trivial pf => Proof pf
  | Bounds bs sl next =>
      let eqs := equalities hs in
      match dioph (S (length eqs)) eqs with
      | Some pf => Proof pf
      | None =>
      let monos := array_of_list (PArray.make n []) 0%uint63 (rev (mlist ms)) in
      match initial n next bs (rev sl) with
      | inr c => Proof (proof monos (Leaf c))
      | inl st =>
          match fst (bb (depth ps) n O st (budget ps)) with
          | Refuted t => Proof (proof monos t)
          | Model st => Sat n st (rev (mlist ms))
          | GaveUp => Unknown
          end
      end
      end
  end.

(** The value of [x] in [st], as a numerator and a positive denominator. *)
Definition value (st : state) (x : int) : num * num :=
  match List.find (fun r => PrimInt63.eqb (rvar r) x) (rows st) with
  | Some r => (rnum r, rhead r)
  | None => ((vals st).[x], Num.one)
  end.

Definition ZOracle (ps : params) (l : list (NFormula Z)) : ZArithProof :=
  match solve ps l with Proof pf => pf | _ => DoneProof end.

(** The witnesses [ZTautoChecker] expects for [f]: one per clause of its
    conjunctive normal form. *)
Definition ZTautoOracle (f : BFormula (Formula Z) isProp) : list ZArithProof :=
  map (fun cl => ZOracle default_params (map fst cl))
    (xcnf (Annot := unit) Zunsat Zdeduce normalise negate true f).

(** A decision procedure that needs no witness. *)
Definition ZTautoAuto (f : BFormula (Formula Z) isProp) : bool :=
  ZTautoChecker f (ZTautoOracle f).

Lemma ZTautoAuto_sound f :
  ZTautoAuto f = true -> forall env, eval_bf (Zeval_formula env) f.
Proof. apply ZTautoChecker_sound. Qed.

(** * Clauses

    For procedures that keep their hypotheses in normal form, as a
    conjunction of [NFormula]s. *)

(** [l] is contradictory. *)
Definition ZRefutes (l : list (NFormula Z)) : bool :=
  ZChecker l (ZOracle default_params l).

Lemma ZRefutes_sound l :
  ZRefutes l = true -> forall env, Forall (eval_nformula env) l -> False.
Proof.
  intros H env. generalize (ZChecker_sound _ _ H env). clear H.
  induction l; cbn; [easy|]. intros H Hl. inversion Hl; subst.
  now apply IHl; [apply H|].
Qed.

(** [f] as a disjunction, of two cases for a disequality. *)
Definition ZCases (f : Formula Z) : list (NFormula Z) :=
  xnegate (xnnormalise f).

Lemma ZCases_sound f env :
  Zeval_formula env isProp f -> Exists (eval_nformula env) (ZCases f).
Proof.
  intros H%xnnormalise_correct. unfold ZCases.
  destruct (xnnormalise f) as [p o].
  change (Zeval_op1 o (eval_pol env p)) in H.
  assert (Hge : forall q, eval_nformula env (q, NonStrict) <-> 0 <= eval_pol env q)
    by reflexivity.
  destruct o; cbn [xnegate Zeval_op1] in *.
  - now constructor.
  - destruct (Z.lt_trichotomy (eval_pol env p) 0) as [|[|]]; [|easy|].
    + apply Exists_cons_tl, Exists_cons_hd, Hge.
      rewrite eval_pol_sub, eval_pol_Pc. lia.
    + apply Exists_cons_hd, Hge. rewrite eval_pol_sub, eval_pol_Pc. lia.
  - apply Exists_cons_hd, Hge. rewrite eval_pol_sub, eval_pol_Pc. lia.
  - now constructor.
Qed.

(** [f] contradicts [hyps]. *)
Definition ZContradicts (hyps : list (NFormula Z)) (f : Formula Z) : bool :=
  forallb (fun c => ZRefutes (c :: hyps)) (ZCases f).

Lemma ZContradicts_sound hyps f :
  ZContradicts hyps f = true ->
  forall env, Forall (eval_nformula env) hyps ->
              Zeval_formula env isProp f -> False.
Proof.
  unfold ZContradicts. rewrite forallb_forall. intros H env Hh Hf.
  apply (ZCases_sound f env), Exists_exists in Hf. destruct Hf as (c & Hin & Hc).
  now apply (ZRefutes_sound _ (H c Hin) env); constructor.
Qed.

(** The negation of [f]. *)
Definition ZNeg (f : Formula Z) : Formula Z :=
  {| Flhs := Flhs f;
     Fop := match Fop f with
            | OpEq => OpNEq
            | OpNEq => OpEq
            | OpLe => OpGt
            | OpGe => OpLt
            | OpLt => OpGe
            | OpGt => OpLe
            end;
     Frhs := Frhs f |}.

Lemma ZNeg_sound f env :
  Zeval_formula env isProp (ZNeg f) -> ~ Zeval_formula env isProp f.
Proof. destruct f as [l [] r]; cbn; lia. Qed.

Lemma ZNeg_complete f env :
  ~ Zeval_formula env isProp (ZNeg f) -> Zeval_formula env isProp f.
Proof. destruct f as [l [] r]; cbn; lia. Qed.

(** [f] as a hypothesis. A disequality is dropped. *)
Definition ZHyp (f : Formula Z) : list (NFormula Z) :=
  match ZCases f with
  | [c] => [c]
  | _ => []
  end.

Lemma ZHyp_sound f env :
  Zeval_formula env isProp f -> Forall (eval_nformula env) (ZHyp f).
Proof.
  intros H%ZCases_sound. unfold ZHyp.
  destruct (ZCases f) as [|c [|]]; [easy| |easy].
  inversion H; subst; [now constructor|]. now inversion H1.
Qed.

(** * Tactics

    [xlia] is used for its reification. It also runs the oracle of [lia],
    fails if that one finds no witness, and drops the hypotheses its witness
    does not use. *)

Ltac zchecker_simplex :=
  let __wit := fresh "__wit" in
  let __varmap := fresh "__varmap" in
  let __ff := fresh "__ff" in
  intros __wit __varmap __ff;
  let w := eval vm_compute in (ZTautoOracle __ff) in
  exact (ZTautoChecker_sound __ff w
           (@eq_refl bool true <: @eq bool (ZTautoChecker __ff w) true)
           (@find Z Z0 __varmap)).

Ltac zchecker_simplex_auto :=
  let __wit := fresh "__wit" in
  let __varmap := fresh "__varmap" in
  let __ff := fresh "__ff" in
  intros __wit __varmap __ff;
  exact (ZTautoAuto_sound __ff
           (@eq_refl bool true <: @eq bool (ZTautoAuto __ff) true)
           (@find Z Z0 __varmap)).

(** Like [lia], with the witness of the oracle above. *)
Ltac lia_simplex := Zify.zify; xlia zchecker_simplex.

(** Like [lia_simplex], with the oracle running in the kernel. *)
Ltac lia_simplex_auto := Zify.zify; xlia zchecker_simplex_auto.
