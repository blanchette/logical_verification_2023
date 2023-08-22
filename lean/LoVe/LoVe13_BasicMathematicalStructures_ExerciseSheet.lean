/- Copyright © 2018–2023 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe13_BasicMathematicalStructures_Demo


/- # LoVe Exercise 13: Basic Mathematical Structures

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Type Classes

Recall the inductive type `BTree` we introduced in lecture 5: -/

#check BTree

/- The following function takes two trees and attaches copies of the second
tree to each leaf of the first tree. -/

def BTree.graft {α : Type} : BTree α → BTree α → BTree α
  | BTree.empty,      u => u
  | BTree.node a l r, u => BTree.node a (BTree.graft l u) (BTree.graft r u)

#reduce BTree.graft (BTree.node 1 BTree.empty BTree.empty)
  (BTree.node 2 BTree.empty BTree.empty)

/- 1.1. Prove the following two theorems by structural induction on `t`. -/

theorem BTree.graft_assoc {α : Type} (t u v : BTree α) :
  BTree.graft (BTree.graft t u) v = BTree.graft t (BTree.graft u v) :=
  sorry

theorem BTree.graft_empty {α : Type} (t : BTree α) :
  BTree.graft t BTree.empty = t :=
  sorry

/- 1.2. Declare `BTree` an instance of `AddMonoid` using `graft` as the
addition operator. -/

#print AddMonoid

@[instance] def BTree.AddMonoid {α : Type} : AddMonoid (BTree α) :=
  { add       :=
      sorry
    add_assoc :=
      sorry
    zero      :=
      sorry
    add_zero  :=
      sorry
    zero_add  :=
      sorry
  }

/- 1.3 (**optional**). Explain why `BTree` with `graft` as addition cannot
be declared an instance of `AddGroup`. -/

#print AddGroup

-- enter your explanation here

/- 1.4 (**optional**). Prove the following theorem illustrating why `BTree`
with `graft` as addition does not constitute an `AddGroup`. -/

theorem BTree.add_left_neg_counterexample :
  ∃x : BTree ℕ, ∀y : BTree ℕ, BTree.graft y x ≠ BTree.empty :=
  sorry


/- ## Question 2: Multisets and Finsets

Recall the following definitions from the lecture: -/

#check Finset.elems
#check List.elems

/- 2.1. Prove that the finite set of nodes does not change when mirroring a
tree. -/

theorem Finset.elems_mirror (t : BTree ℕ) :
  Finset.elems (mirror t) = Finset.elems t :=
  sorry

/- 2.2. Show that this does not hold for the list of nodes by providing a
tree `t` for which `List.elems t ≠ List.elems (mirror t)`.

If you define a suitable counterexample, the proof below will succeed. -/

def rottenTree : BTree ℕ :=
  sorry

#eval List.elems rottenTree
#eval List.elems (mirror rottenTree)

theorem List.elems_mirror_counterexample :
  ∃t : BTree ℕ, List.elems t ≠ List.elems (mirror t) :=
  by
    apply Exists.intro rottenTree
    simp [List.elems]

end LoVe
