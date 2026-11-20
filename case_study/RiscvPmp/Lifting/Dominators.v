(******************************************************************************)
(* Copyright (c) 2026 Steven Keuchel                                          *)
(* All rights reserved.                                                       *)
(*                                                                            *)
(* Redistribution and use in source and binary forms, with or without         *)
(* modification, are permitted provided that the following conditions are    *)
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
(* CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,       *)
(* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,        *)
(* PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR         *)
(* PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF     *)
(* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING       *)
(* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS         *)
(* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.               *)
(******************************************************************************)

From Stdlib Require Import Bool List PArray Uint63.
Import ListNotations.

Local Open Scope uint63_scope.

(** * Dominator trees of control-flow graphs

    Lengauer–Tarjan with path compression (O(m log n)) on primitive arrays and
    integers, so that it runs fast under [vm_compute]. A graph is an array of
    successor lists; its vertices are [0 .. length g - 1]. Successors outside
    that range are ignored. *)

Definition graph : Type := array (list int).

(* Marks unreachable vertices and absent links. *)
Definition undef : int := max_int.

(** ** Loops *)

(* Run [step] until it returns [inr], at most 2^k times. *)
Fixpoint iterate {St} (k : nat) (step : St -> St + St) (s : St) : St + St :=
  match k with
  | O   => step s
  | S k => match iterate k step s with
           | inl s => iterate k step s
           | inr s => inr s
           end
  end.

Definition loop {St} (step : St -> St + St) (s : St) : St :=
  match iterate 62 step s with inl s | inr s => s end.

(* [f i] for i = lo .. hi-1. *)
Definition for_up {A} (lo hi : int) (f : int -> A -> A) (a : A) : A :=
  snd (loop (fun '(i, a) => if i <? hi then inl (i + 1, f i a) else inr (i, a))
          (lo, a)).

(* [f i] for i = hi-1 downto lo. *)
Definition for_down {A} (hi lo : int) (f : int -> A -> A) (a : A) : A :=
  snd (loop (fun '(i, a) => if lo <? i then inl (i - 1, f (i - 1) a) else inr (i, a))
          (hi, a)).

(** ** Depth-first search *)

Record dfs : Type :=
  { dfs_pre    : array int; (* vertex -> preorder number, or [undef] *)
    dfs_post   : array int; (* vertex -> postorder number, or [undef] *)
    dfs_vertex : array int; (* preorder number -> vertex *)
    dfs_parent : array int; (* preorder number -> preorder number of parent *)
    dfs_count  : int;       (* number of reachable vertices *)
    dfs_rpo    : list int;  (* reachable vertices in reverse postorder *)
  }.

Record dfs_state : Type :=
  { ds_stack : list (int * list int); (* vertex and its unexplored successors *)
    ds_dfs   : dfs;
    ds_npost : int;
  }.

Definition dfs_visit (g : graph) (w p : int) (stack : list (int * list int)) (d : dfs)
  (npost : int) : dfs_state :=
  let i := dfs_count d in
  {| ds_stack := (w, g.[w]) :: stack;
     ds_dfs   := {| dfs_pre    := (dfs_pre d).[w <- i];
                    dfs_post   := dfs_post d;
                    dfs_vertex := (dfs_vertex d).[i <- w];
                    dfs_parent := (dfs_parent d).[i <- p];
                    dfs_count  := i + 1;
                    dfs_rpo    := dfs_rpo d |};
     ds_npost := npost |}.

Definition dfs_step (g : graph) (s : dfs_state) : dfs_state + dfs_state :=
  let '{| ds_stack := stack; ds_dfs := d; ds_npost := npost |} := s in
  match stack with
  | [] => inr s
  | (v, []) :: stack =>
      inl {| ds_stack := stack;
             ds_dfs   := {| dfs_pre    := dfs_pre d;
                            dfs_post   := (dfs_post d).[v <- npost];
                            dfs_vertex := dfs_vertex d;
                            dfs_parent := dfs_parent d;
                            dfs_count  := dfs_count d;
                            dfs_rpo    := v :: dfs_rpo d |};
             ds_npost := npost + 1 |}
  | (v, w :: ws) :: stack =>
      let stack := (v, ws) :: stack in
      if (w <? length g) && ((dfs_pre d).[w] =? undef)
      then inl (dfs_visit g w (dfs_pre d).[v] stack d npost)
      else inl {| ds_stack := stack; ds_dfs := d; ds_npost := npost |}
  end.

Definition run_dfs (g : graph) (r : int) : dfs :=
  let n := length g in
  let d := {| dfs_pre    := make n undef;
              dfs_post   := make n undef;
              dfs_vertex := make n undef;
              dfs_parent := make n undef;
              dfs_count  := 0;
              dfs_rpo    := [] |} in
  if r <? n
  then ds_dfs (loop (dfs_step g) (dfs_visit g r 0 [] d 0))
  else d.

(* [a] is an ancestor of [b] (or equal), for reachable [b]. *)
Definition dfs_ancestor (d : dfs) (a b : int) : bool :=
  ((dfs_pre d).[a] <=? (dfs_pre d).[b]) && ((dfs_pre d).[b] <? undef) &&
  ((dfs_post d).[b] <=? (dfs_post d).[a]).

(** ** Lengauer–Tarjan

    Works on preorder numbers: semidominators are compared directly and
    unreachable vertices drop out. *)

(* Predecessors as preorder numbers, indexed by preorder number. *)
Definition dfs_preds (g : graph) (d : dfs) : array (list int) :=
  for_up 0 (dfs_count d)
    (fun i acc =>
       List.fold_left
         (fun acc w =>
            let j := (dfs_pre d).[w] in
            if j =? undef then acc else acc.[j <- i :: acc.[j]])
         g.[(dfs_vertex d).[i]] acc)
    (make (dfs_count d) []).

(* The vertices on the forest path from [v] whose ancestor link gets
   compressed, nearest to the root first. *)
Definition compress_path (anc : array int) (v : int) : list int :=
  snd (loop (fun '(u, acc) =>
               let a := anc.[u] in
               if anc.[a] =? undef then inr (u, acc) else inl (a, u :: acc))
          (v, [])).

(* The vertex with minimal semidominator on the forest path to [v], excluding
   its root, with path compression. *)
Definition eval (semi : array int) (anc best : array int) (v : int) :
  array int * array int * int :=
  let '(anc, best) :=
    List.fold_left
      (fun '(anc, best) u =>
         let a := anc.[u] in
         let b := best.[a] in
         let best := if semi.[b] <? semi.[best.[u]] then best.[u <- b] else best in
         (anc.[u <- anc.[a]], best))
      (compress_path anc v) (anc, best) in
  (anc, best, best.[v]).

Record lt_state : Type :=
  { lt_semi    : array int;
    lt_anc     : array int;
    lt_best    : array int;
    lt_bucket  : array (list int);
    lt_idom    : array int;
    lt_samedom : array int;
  }.

Definition lt_step (d : dfs) (preds : array (list int)) (i : int) (s : lt_state) :
  lt_state :=
  let '{| lt_semi := semi; lt_anc := anc; lt_best := best; lt_bucket := bucket;
          lt_idom := idom; lt_samedom := samedom |} := s in
  let p := (dfs_parent d).[i] in
  let '(anc, best, sd) :=
    List.fold_left
      (fun '(anc, best, sd) v =>
         if v <=? i then (anc, best, if v <? sd then v else sd)
         else let '(anc, best, u) := eval semi anc best v in
              let s' := semi.[u] in
              (anc, best, if s' <? sd then s' else sd))
      preds.[i] (anc, best, p) in
  let semi := semi.[i <- sd] in
  let bucket := bucket.[sd <- i :: bucket.[sd]] in
  let anc := anc.[i <- p] in
  let '(anc, best, idom, samedom) :=
    List.fold_left
      (fun '(anc, best, idom, samedom) v =>
         let '(anc, best, y) := eval semi anc best v in
         if semi.[y] =? semi.[v]
         then (anc, best, idom.[v <- p], samedom)
         else (anc, best, idom, samedom.[v <- y]))
      bucket.[p] (anc, best, idom, samedom) in
  {| lt_semi := semi; lt_anc := anc; lt_best := best; lt_bucket := bucket.[p <- []];
     lt_idom := idom; lt_samedom := samedom |}.

(* Immediate dominators as preorder numbers, indexed by preorder number. *)
Definition lt_idoms (g : graph) (d : dfs) : array int :=
  let k := dfs_count d in
  let ids := for_up 0 k (fun i a => a.[i <- i]) (make k 0) in
  (* Separate copies: reading an old version of a persistent array is slow. *)
  let s := {| lt_semi := ids; lt_anc := make k undef; lt_best := copy ids;
              lt_bucket := make k []; lt_idom := (make k undef).[0 <- 0];
              lt_samedom := make k undef |} in
  let s := for_down k 1 (lt_step d (dfs_preds g d)) s in
  let samedom := lt_samedom s in
  for_up 1 k
    (fun i idom =>
       let j := samedom.[i] in
       if j =? undef then idom else idom.[i <- idom.[j]])
    (lt_idom s).

(** ** Dominator trees *)

Record domtree : Type :=
  { dt_root     : int;
    dt_cfg      : dfs;              (* DFS of the graph *)
    dt_idom     : array int;        (* vertex -> immediate dominator, root -> root *)
    dt_children : array (list int); (* children in reverse postorder of the graph *)
    dt_tree     : dfs;              (* DFS of the tree, for dominance queries *)
  }.

Definition dominator_tree (g : graph) (r : int) : domtree :=
  let n := length g in
  let d := run_dfs g r in
  let vertex := dfs_vertex d in
  let idom := lt_idoms g d in
  let idom := for_up 0 (dfs_count d)
                (fun i a => a.[vertex.[i] <- vertex.[idom.[i]]]) (make n undef) in
  let children :=
    List.fold_left
      (fun ch v => if v =? r then ch else ch.[idom.[v] <- v :: ch.[idom.[v]]])
      (List.rev_append (dfs_rpo d) []) (make n []) in
  {| dt_root := r; dt_cfg := d; dt_idom := idom; dt_children := children;
     dt_tree := run_dfs children r |}.

(* [a] dominates [b] (or equals it), for reachable [a] and [b]. O(1). *)
Definition dominates (t : domtree) (a b : int) : bool :=
  dfs_ancestor (dt_tree t) a b.

Definition reachable (t : domtree) (v : int) : bool :=
  (dfs_pre (dt_cfg t)).[v] <? undef.

Definition forall_edges (g : graph) (t : domtree) (f : int -> int -> bool) : bool :=
  List.forallb
    (fun u => List.forallb (fun w => negb (w <? length g) || f u w) g.[u])
    (dfs_rpo (dt_cfg t)).

(* Every edge [u -> w] stays within the subtree of [idom w]. This implies that
   tree ancestors dominate, and is what scoping a join point for [w] at
   [idom w] needs. *)
Definition check_parent_property (g : graph) (t : domtree) : bool :=
  (dfs_count (dt_tree t) =? dfs_count (dt_cfg t)) &&
  forall_edges g t
    (fun u w => (w =? dt_root t) || dominates t (dt_idom t).[w] u).

(** ** Classifying join points

    A back edge targets a vertex that dominates its source; that vertex is a
    loop header and becomes a recursive join point. A merge node has at least
    two incoming forward edges. The graph is reducible iff every retreating
    edge of the DFS is a back edge. *)

Definition back_edge (t : domtree) (u w : int) : bool := dominates t w u.

Definition reducible (g : graph) (t : domtree) : bool :=
  forall_edges g t
    (fun u w => negb (dfs_ancestor (dt_cfg t) w u) || back_edge t u w).

Definition loop_headers (g : graph) (t : domtree) : array bool :=
  List.fold_left
    (fun a u =>
       List.fold_left
         (fun a w => if (w <? length g) && back_edge t u w then a.[w <- true] else a)
         g.[u] a)
    (dfs_rpo (dt_cfg t)) (make (length g) false).

(* Number of incoming forward edges from reachable vertices. *)
Definition forward_in_degrees (g : graph) (t : domtree) : array int :=
  List.fold_left
    (fun a u =>
       List.fold_left
         (fun a w => if (w <? length g) && negb (back_edge t u w)
                     then a.[w <- a.[w] + 1] else a)
         g.[u] a)
    (dfs_rpo (dt_cfg t)) (make (length g) 0).

Definition merge_node (fwd : array int) (v : int) : bool := 2 <=? fwd.[v].
