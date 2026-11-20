From Stdlib Require Import Bool List PArray Uint63 PeanoNat ZArith.
From Katamaran Require Import RiscvPmp.Lifting.Dominators.
Import ListNotations.

(* Compare [dominator_tree] with a naive reference on random graphs. *)

Definition of_nat (n : nat) : int := of_Z (Z.of_nat n).
Definition to_nat (i : int) : nat := Z.to_nat (to_Z i).

(** Reference: [a] dominates [b] iff [b] is reachable, and unreachable once
    [a] is removed. *)

Definition reach_step (g : list (list nat)) (avoid : nat) (seen : list bool) :
  list bool :=
  let vs := seq 0 (List.length g) in
  let next := concat (map (fun '((v, b) : nat * bool) => if b then nth v g [] else [])
                        (combine vs seen)) in
  map (fun '((v, b) : nat * bool) => b || (negb (v =? avoid) && existsb (Nat.eqb v) next))
    (combine vs seen).

Definition reach (g : list (list nat)) (avoid r : nat) : list bool :=
  Nat.iter (List.length g) (reach_step g avoid)
    (map (fun v => (v =? r) && negb (v =? avoid)) (seq 0 (List.length g))).

(* Row [a] says which vertices [a] dominates. *)
Definition ref_dominators (g : list (list nat)) (r : nat) : list (list bool) :=
  let all := reach g (List.length g) r in
  map (fun a =>
         let without := reach g a r in
         map (fun b => nth a all false && nth b all false &&
                         ((a =? b) || negb (nth b without false)))
           (seq 0 (List.length g)))
    (seq 0 (List.length g)).

Definition to_graph (g : list (list nat)) : graph :=
  snd (fold_left (fun '((i, a) : int * graph) ws => (i + 1, a.[i <- map of_nat ws])%uint63)
         g (0%uint63, make (of_nat (List.length g)) [])).

Definition agrees (g : list (list nat)) : bool :=
  let g' := to_graph g in
  let t := dominator_tree g' 0 in
  let vs := seq 0 (List.length g) in
  check_parent_property g' t &&
  forallb (fun '((a, row) : nat * list bool) => forallb (fun '((b, d) : nat * bool) =>
    Bool.eqb d (dominates t (of_nat a) (of_nat b))) (combine vs row))
    (combine vs (ref_dominators g 0)).

(** Random graphs from a linear congruential generator. *)

Definition next (x : int) : int :=
  (x * 6364136223846793005 + 1442695040888963407)%uint63.

Definition rand (x : int) (k : nat) : nat :=
  to_nat (PrimInt63.mod (x >> 20)%uint63 (of_nat k)).

(* [n] vertices with up to [d] successors each. *)
Fixpoint random_succs (x : int) (n d : nat) (vs : nat) :
  int * list (list nat) :=
  match vs with
  | O => (x, [])
  | S vs =>
      let x := next x in
      let fix succs x k :=
        match k with
        | O => (x, [])
        | S k => let x := next x in
                 let w := rand x n in
                 let '(x, ws) := succs x k in (x, w :: ws)
        end in
      let '(x, ws) := succs x (rand x (S d)) in
      let '(x, g) := random_succs x n d vs in
      (x, ws :: g)
  end.

Fixpoint random_tests (x : int) (count maxn d : nat) : bool :=
  match count with
  | O => true
  | S count =>
      let x := next x in
      let n := S (rand x maxn) in
      let '(x, g) := random_succs x n d n in
      agrees g && random_tests x count maxn d
  end.

Goal random_tests 1 500 12 2 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Goal random_tests 2 300 20 3 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Goal random_tests 3 30 40 5 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Local Open Scope uint63_scope.

(* Classification on the graph 0 -> 1 -> {2, 3} -> 4 -> {1, 5}. *)
Definition g0 : graph :=
  (make 6 []).[0 <- [1]].[1 <- [2;3]].[2 <- [4]].[3 <- [4]].[4 <- [1;5]].

Definition to_list {A} (a : array A) : list A :=
  for_down (length a) 0 (fun i l => a.[i] :: l) [].

Goal let t := dominator_tree g0 0 in
     (to_list (dt_idom t), to_list (dt_children t), reducible g0 t,
      to_list (loop_headers g0 t), to_list (forward_in_degrees g0 t)) =
     ([0; 0; 1; 1; 1; 4], [[1]; [3; 2; 4]; []; []; [5]; []], true,
      [false; true; false; false; false; false], [0; 1; 1; 1; 2; 1]).
Proof. vm_compute. reflexivity. Qed.

(* Irreducible: 0 -> {1, 2}, 1 <-> 2. *)
Goal let g := (make 3 []).[0 <- [1;2]].[1 <- [2]].[2 <- [1]] in
     reducible g (dominator_tree g 0) = false.
Proof. vm_compute. reflexivity. Qed.

(** Large graphs: a path with skip edges and edges back to [i/2], which makes
    the DFS and the compressed paths deep, and a random graph. *)

Definition chain (n : int) : graph :=
  for_up 0 n
    (fun i a =>
       let ws := List.filter (fun w => w <? n) [i + 1; i + 2] in
       a.[i <- (i >> 1) :: ws])%uint63
    (make n []).

Definition random_graph (n d : int) : graph :=
  snd (for_up 0 n
         (fun i '((x, a) : int * graph) =>
            let '(x, ws) :=
              for_up 0 d (fun _ '((x, ws) : int * list int) => let x := next x in
                                            (x, PrimInt63.mod (x >> 20) n :: ws))%uint63
                (x, []) in
            (x, a.[i <- ws]))
         (7%uint63, make n [])).

Time Eval vm_compute in
  let g := chain 100000 in check_parent_property g (dominator_tree g 0).
Time Eval vm_compute in
  let g := random_graph 100000 3 in check_parent_property g (dominator_tree g 0).
