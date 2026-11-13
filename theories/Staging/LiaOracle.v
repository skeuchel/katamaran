(******************************************************************************)
(* A Gallina port of the rational part of the certificate oracle of [lia].    *)
(*                                                                            *)
(* Derived from plugins/micromega/{simplex,vect,certificate,polynomial}.ml of *)
(* the Rocq Prover, Copyright INRIA, CNRS and contributors, distributed under *)
(* the terms of the GNU Lesser General Public License Version 2.1.            *)
(******************************************************************************)

From Stdlib Require Import Bool List ZArith QArith Qabs FMapPositive Lia.
From Stdlib.micromega Require Import EnvRing RingMicromega Tauto ZMicromega VarMap.

Import ListNotations.

(** The oracle searches for a Farkas certificate: a non-negative combination
    of the hypotheses of a clause that is a negative constant. It is the
    Simplex of [simplex.ml] without the integer part (cutting planes, case
    splits), so it refutes exactly the clauses that are infeasible over the
    rationals.

    Nothing here is proved correct, nor has to be: certificates are checked by
    [ZChecker]. The Simplex uses Bland's rule, as the original, and takes fuel
    only to be structurally recursive. *)

(** * Rationals in lowest terms *)

Definition qadd (a b : Q) : Q :=
  match a, b with
  | Qmake n xH, Qmake m xH => Qmake (n + m) 1
  | _, _ => Qred (Qplus a b)
  end.

Definition qmul (a b : Q) : Q :=
  match a, b with
  | Qmake n xH, Qmake m xH => Qmake (n * m) 1
  | _, _ => Qred (Qmult a b)
  end.

Definition qdiv (a b : Q) : Q := qmul a (Qinv b).

Definition qzero (a : Q) : bool :=
  match Qnum a with Z0 => true | _ => false end.
Definition qpos (a : Q) : bool :=
  match Qnum a with Zpos _ => true | _ => false end.
Definition qneg (a : Q) : bool :=
  match Qnum a with Zneg _ => true | _ => false end.

(** * Sparse vectors

    Sorted by variable, without zero coefficients. *)

Definition vec : Set := list (positive * Q).

Definition vcons (x : positive) (a : Q) (v : vec) : vec :=
  if qzero a then v else (x, a) :: v.

Fixpoint vget (x : positive) (v : vec) : Q :=
  match v with
  | [] => 0%Q
  | (y, a) :: v =>
      match Pos.compare x y with
      | Eq => a
      | Lt => 0%Q
      | Gt => vget x v
      end
  end.

Fixpoint vdel (x : positive) (v : vec) : vec :=
  match v with
  | [] => []
  | (y, a) :: v' =>
      match Pos.compare x y with
      | Eq => v'
      | Lt => v
      | Gt => (y, a) :: vdel x v'
      end
  end.

Definition vmap (f : Q -> Q) (v : vec) : vec :=
  map (fun '(x, a) => (x, f a)) v.

(** [vaddmul c v1 v2] is [c * v1 + v2], for [c <> 0]. *)
Fixpoint vaddmul (c : Q) (v1 : vec) : vec -> vec :=
  match v1 with
  | [] => fun v2 => v2
  | (x1, a1) :: v1' =>
      fix go (v2 : vec) : vec :=
        match v2 with
        | [] => vmap (qmul c) v1
        | (x2, a2) :: v2' =>
            match Pos.compare x1 x2 with
            | Eq => vcons x1 (qadd (qmul c a1) a2) (vaddmul c v1' v2')
            | Lt => (x1, qmul c a1) :: vaddmul c v1' v2
            | Gt => (x2, a2) :: go v2'
            end
        end
  end.

(** * Linear expressions *)

Record lin : Set := Lin { lcst : Q; lvec : vec }.

Definition lopp (e : lin) : lin :=
  Lin (Qopp (lcst e)) (vmap Qopp (lvec e)).

(** [laddmul c e1 e2] is [c * e1 + e2], for [c <> 0]. *)
Definition laddmul (c : Q) (e1 e2 : lin) : lin :=
  Lin (qadd (qmul c (lcst e1)) (lcst e2)) (vaddmul c (lvec e1) (lvec e2)).

(** * Simplex *)

(** A tableau maps every basic variable to its definition in terms of the
    non-basic ones. In the solution it denotes, the non-basic variables are 0. *)
Definition tableau : Type := PositiveMap.t lin.

Variant result : Type :=
| Sat (t : tableau)
(** The slack variable [s] is defined by [e], whose constant is negative and
    whose other coefficients are negative ones of slack variables. *)
| Unsat (s : positive) (e : lin)
| OutOfFuel.

Section Simplex.

  (** The variables from [base] on are slack variables: each stands for a
      constraint, and has to be non-negative. *)
  Variable base : positive.

  (** [obj] is the slack variable being made non-negative. *)
  Definition restricted (obj x : positive) : bool :=
    Pos.leb base x && negb (Pos.eqb x obj).

  (** The first variable of the row [v] that can increase its value, and
      whether it has to be increased (or decreased) for that. *)
  Fixpoint pivot_column (obj : positive) (v : vec) : option (positive * bool) :=
    match v with
    | [] => None
    | (x, a) :: v =>
        if qneg a
        then if restricted obj x then pivot_column obj v else Some (x, false)
        else Some (x, true)
    end.

  (** The basic slack variable that first becomes negative when the non-basic
      [j] is increased ([up]) or decreased, with ties going to the smallest. *)
  Definition pivot_row (obj j : positive) (up : bool) (t : tableau) :
    option positive :=
    option_map fst
      (PositiveMap.fold
         (fun i row best =>
            let a := vget j (lvec row) in
            if restricted obj i && (if up then qneg a else qpos a) then
              let sc := Qabs (qdiv (lcst row) a) in
              match best with
              | None => Some (i, sc)
              | Some (i0, sc0) =>
                  match Qcompare sc0 sc with
                  | Lt => best
                  | Gt => Some (i, sc)
                  | Eq => if Pos.ltb i0 i then best else Some (i, sc)
                  end
              end
            else best)
         t None).

  (** Replace [c] in [row] by its definition [piv]. *)
  Definition subst (c : positive) (piv row : lin) : lin :=
    let g := vget c (lvec row) in
    if qzero g then row
    else laddmul g piv (Lin (lcst row) (vdel c (lvec row))).

  (** Make [c] basic instead of [r]. *)
  Definition pivot (r c : positive) (t : tableau) : tableau :=
    match PositiveMap.find r t with
    | None => t
    | Some row =>
        (* r = a * c + e  becomes  c = (1/a) * r - (1/a) * e *)
        let k := Qopp (Qinv (vget c (lvec row))) in
        let piv :=
          Lin (qmul k (lcst row))
            (vaddmul k (vdel c (lvec row)) [(r, Qopp k)]) in
        PositiveMap.add c piv
          (PositiveMap.map (subst c piv) (PositiveMap.remove r t))
    end.

  (** Pivot until the basic variable [obj] is non-negative. *)
  Fixpoint simplex (fuel : nat) (obj : positive) (t : tableau) : result :=
    match PositiveMap.find obj t with
    | None => OutOfFuel
    | Some row =>
        if qneg (lcst row) then
          match pivot_column obj (lvec row) with
          | None => Unsat obj row
          | Some (j, up) =>
              match pivot_row obj j up t with
              | None => Sat (pivot obj j t)
              | Some i =>
                  match fuel with
                  | O => OutOfFuel
                  | S fuel => simplex fuel obj (pivot i j t)
                  end
              end
          end
        else Sat t
    end.

  (** The value of [e], over the non-slack variables, in the solution of [t]. *)
  Definition value (t : tableau) (e : lin) : Q :=
    fold_left
      (fun acc '(x, a) =>
         match PositiveMap.find x t with
         | Some row => qadd acc (qmul a (lcst row))
         | None => acc
         end)
      (lvec e) (lcst e).

  (** Express [e] in terms of the non-basic variables of [t]. *)
  Definition reduce (t : tableau) (e : lin) : lin :=
    fold_left
      (fun acc '(x, a) =>
         match PositiveMap.find x t with
         | Some row => laddmul a row acc
         | None => Lin (lcst acc) (vaddmul a [(x, 1%Q)] (lvec acc))
         end)
      (lvec e) (Lin (lcst e) []).

  Definition cstr : Set := positive * lin.

  (** Split off the constraint with the least value: [c], with value [e], or
      a later one of [l]. *)
  Fixpoint most_violated (t : tableau) (l : list cstr) (e : Q) (c : cstr)
    (rest : list cstr) : cstr * list cstr :=
    match l with
    | [] => (c, rest)
    | c' :: l =>
        let e' := value t (snd c') in
        if Qle_bool e' e
        then most_violated t l e' c' (c :: rest)
        else most_violated t l e c (c' :: rest)
    end.

  (** Add the constraints [s = e /\ s >= 0] of [l], which has length [n], to
      [t]. Every Simplex run gets [fuel] pivots. *)
  Fixpoint solve (fuel n : nat) (l : list cstr) (t : tableau) : result :=
    match n, l with
    | S n, c :: l =>
        let '((s, e), l) := most_violated t l (value t (snd c)) c [] in
        match simplex fuel s (PositiveMap.add s (reduce t e) t) with
        | Sat t => solve fuel n l t
        | r => r
        end
    | _, _ => Sat t
    end.

End Simplex.

(** * Linearisation

    The monomials of the hypotheses become the variables of the linear
    problem, numbered in order of appearance. *)

(** A monomial is the list [xn; en; ...; x1; e1] of its variables, in
    decreasing order, and their exponents. A trie numbers them. *)
#[local] Unset Elimination Schemes.
Inductive mtrie : Type :=
| MNode (v : option positive) (ch : PositiveMap.t mtrie).
#[local] Set Elimination Schemes.

Definition mempty : mtrie := MNode None (PositiveMap.empty _).

Fixpoint mfind (m : list positive) (t : mtrie) : option positive :=
  match m, t with
  | [], MNode v _ => v
  | x :: m, MNode _ ch =>
      match PositiveMap.find x ch with
      | Some t => mfind m t
      | None => None
      end
  end.

Fixpoint madd (m : list positive) (i : positive) (t : mtrie) : mtrie :=
  let (v, ch) := t in
  match m with
  | [] => MNode (Some i) ch
  | x :: m =>
      let t := match PositiveMap.find x ch with Some t => t | None => mempty end in
      MNode v (PositiveMap.add x (madd m i t) ch)
  end.

(** The numbered monomials, and the next free number. *)
Definition mons : Type := mtrie * positive.

Definition intern (m : list positive) (st : mons) : positive * mons :=
  let (t, n) := st in
  match mfind m t with
  | Some x => (x, st)
  | None => (n, (madd m n t, Pos.succ n))
  end.

Definition mon_mul (x i : positive) (m : list positive) : list positive :=
  match m with
  | y :: e :: m' => if Pos.eqb x y then y :: Pos.add e i :: m' else x :: i :: m
  | _ => x :: i :: m
  end.

(** Add [m * p] to [acc], where the first variable of [p] is [jmp]. *)
Fixpoint linearise (jmp : positive) (m : list positive) (p : Pol Z)
  (acc : lin * mons) : lin * mons :=
  match p with
  | Pc c =>
      match c, m with
      | Z0, _ => acc
      | _, [] => let (e, st) := acc in (Lin (qadd (lcst e) (inject_Z c)) (lvec e), st)
      | _, _ =>
          let (e, st) := acc in
          let (x, st) := intern m st in
          (Lin (lcst e) (vaddmul (inject_Z c) [(x, 1%Q)] (lvec e)), st)
      end
  | Pinj j p => linearise (Pos.add jmp j) m p acc
  | PX p i q =>
      linearise (Pos.succ jmp) m q (linearise jmp (mon_mul jmp i m) p acc)
  end.

(** What a slack variable stands for: the hypothesis [i], which is an
    inequality [p >= 0], or an equality read as [p >= 0] or as [- p >= 0]. *)
Variant hyp : Set :=
| HypGe (i : nat)
| HypEq (i : nat) (neg : bool).

Fixpoint linearise_hyps (i : nat) (l : list (NFormula Z)) (st : mons) :
  list (hyp * lin) * positive :=
  match l with
  | [] => ([], snd st)
  | (p, o) :: l =>
      let (e, st) := linearise 1 [] p (Lin 0 [], st) in
      let (cs, n) := linearise_hyps (S i) l st in
      (match o with
       | Equal => (HypEq i false, e) :: (HypEq i true, lopp e) :: cs
       | NonStrict | Strict => (HypGe i, e) :: cs
       | NonEqual => cs
       end, n)
  end.

(** Number the constraints from [s] on. *)
Fixpoint slacks (s : positive) (l : list (hyp * lin)) :
  list cstr * PositiveMap.t hyp :=
  match l with
  | [] => ([], PositiveMap.empty _)
  | (h, e) :: l =>
      let (cs, hs) := slacks (Pos.succ s) l in
      ((s, e) :: cs, PositiveMap.add s h hs)
  end.

(** * Certificates *)

Definition psatz_mul (n : Z) (h : hyp) : Psatz Z :=
  match h with
  | HypGe i =>
      match n with
      | 1%Z => PsatzIn Z i
      | _ => PsatzMulE (PsatzC n) (PsatzIn Z i)
      end
  | HypEq i neg => PsatzMulC (Pc (if neg then Z.opp n else n)) (PsatzIn Z i)
  end.

Definition psatz_add (w1 w2 : Psatz Z) : Psatz Z :=
  match w2 with
  | PsatzZ _ => w1
  | _ => PsatzAdd w1 w2
  end.

(** The combination [c] of slack variables, with positive coefficients, as a
    combination of the hypotheses with integer coefficients. *)
Definition farkas (hs : PositiveMap.t hyp) (c : vec) : option (Psatz Z) :=
  let d := fold_left (fun d xa => Z.lcm d (Zpos (Qden (snd xa)))) c 1%Z in
  let ns := map (fun '(x, a) => (x, Qnum a * (d / Zpos (Qden a)))%Z) c in
  let g := fold_left (fun g xn => Z.gcd g (snd xn)) ns 0%Z in
  fold_right
    (fun '(x, n) w =>
       match PositiveMap.find x hs, w with
       | Some h, Some w => Some (psatz_add (psatz_mul (n / g) h) w)
       | _, _ => None
       end)
    (Some (PsatzZ Z)) ns.

(** * The oracle *)

(** The linear problem of the clause [l]: its first slack variable, its
    constraints, and what they stand for. *)
Definition problem (l : list (NFormula Z)) :
  positive * (list cstr * PositiveMap.t hyp) :=
  let (cs, base) := linearise_hyps 0 l (mempty, 1%positive) in
  (base, slacks base cs).

Definition default_fuel : nat := 1000.

Definition ZOracle (fuel : nat) (l : list (NFormula Z)) : ZArithProof :=
  let '(base, (cs, hs)) := problem l in
  match solve base fuel (length cs) cs (PositiveMap.empty _) with
  | Unsat s e =>
      match farkas hs ((s, 1%Q) :: vmap Qopp (lvec e)) with
      | Some w => RatProof w DoneProof
      | None => DoneProof
      end
  | _ => DoneProof
  end.

(** The witnesses [ZTautoChecker] expects for [f]: one per clause of its
    conjunctive normal form. *)
Definition ZTautoOracle (f : BFormula (Formula Z) isProp) : list ZArithProof :=
  map (fun cl => ZOracle default_fuel (map fst cl))
    (xcnf (Annot := unit) Zunsat Zdeduce normalise negate true f).

(** A decision procedure that needs no witness. *)
Definition ZTautoAuto (f : BFormula (Formula Z) isProp) : bool :=
  ZTautoChecker f (ZTautoOracle f).

Lemma ZTautoAuto_sound f :
  ZTautoAuto f = true -> forall env, eval_bf (Zeval_formula env) f.
Proof. apply ZTautoChecker_sound. Qed.

(** * Tactics

    [xlia] is used for its reification, and also runs the oracle of [lia]: it
    fails if that one finds no witness, and drops the hypotheses its witness
    does not use. So these tactics are for testing the oracle above, and prove
    nothing that [lia] cannot. *)

Ltac zchecker_oracle :=
  let __wit := fresh "__wit" in
  let __varmap := fresh "__varmap" in
  let __ff := fresh "__ff" in
  intros __wit __varmap __ff;
  let w := eval vm_compute in (ZTautoOracle __ff) in
  exact (ZTautoChecker_sound __ff w
           (@eq_refl bool true <: @eq bool (ZTautoChecker __ff w) true)
           (@find Z Z0 __varmap)).

Ltac zchecker_auto :=
  let __wit := fresh "__wit" in
  let __varmap := fresh "__varmap" in
  let __ff := fresh "__ff" in
  intros __wit __varmap __ff;
  exact (ZTautoAuto_sound __ff
           (@eq_refl bool true <: @eq bool (ZTautoAuto __ff) true)
           (@find Z Z0 __varmap)).

(** Like [lia], with the witness of the oracle above. *)
Ltac lia_oracle := Zify.zify; xlia zchecker_oracle.

(** Like [lia_oracle], with the oracle running in the kernel. *)
Ltac lia_auto := Zify.zify; xlia zchecker_auto.
