import Mathlib
open Nat

--additionals
inductive bin_tree : Type
| root
| succ : bin_tree -> bin_tree
| join : (T1 T2 : bin_tree) -> bin_tree

def bin_tree.height : bin_tree -> Nat
| .root => 0
| .succ T => height T + 1
| .join T1 T2 => max (height T1) (height T2) + 1

def bin_tree.num_leaves : bin_tree -> Nat
| .root => 1
| .succ T => T.num_leaves
| .join T1 T2 => (num_leaves T1) + (num_leaves T2) + 1

inductive general_tree : Type
| leaf
| join : (T : List general_tree) -> general_tree

--small exercise 1
def cat: Nat → Nat
| 0 => 1
| n + 1 => Finset.univ.sum (λ (i : Fin n.succ)=> catalan ↑i * catalan (n - ↑i))

--small exercise 2 
inductive plane_tree : Type 
| trees : List plane_tree -> plane_tree

def plane_tree.leaf : plane_tree := trees []

def plane_tree.join : plane_tree → plane_tree → plane_tree
| left, trees right =>
  trees (List.cons left right)

def plane_tree.leaf_num : plane_tree -> Nat
| plane_tree.trees [] => 1
| plane_tree.trees (T :: L) => T.leaf_num + (plane_tree.trees L).leaf_num

def plane_tree.size : plane_tree -> Nat
| plane_tree.trees [] => 2
| plane_tree.trees (T :: L) => T.size + (plane_tree.trees L).size

--small exercise 3
inductive full_bin_tree : Type
| leaf
| join : (T1 T2 : full_bin_tree) -> full_bin_tree

def full_bin_tree.size : full_bin_tree -> Nat
| .leaf => 1
| .join T1 T2 => size T1 + size T2 + 1

def full_bin_tree.size_no_leaf : full_bin_tree → Nat
| .leaf => 0
| .join T1 T2 => size_no_leaf T1 + size_no_leaf T2 + 1

--small exercise 4
def full_bin_tree_n (n : Nat) : Type :=
  { T : full_bin_tree // full_bin_tree.size_no_leaf T = n}

--small exercise 5
def ballot := {pq : Nat × Nat // pq.1 - pq.2 >= 0}

def ballot.p : ballot → Nat
| ballot => ballot.val.1

def ballot.q: ballot → Nat
| ballot => ballot.val.2

def ballot_s (n:Nat) := {s : ballot // s.p + s.q = n}

--big exercise 4
def plane_equiv : List plane_tree ≃ plane_tree := 
  Equiv.mk plane_tree.trees
  (λ (plane_tree.trees lst) => lst)
  (λ (_) => rfl)
  (λ (plane_tree.trees _) => rfl)

