/- Copyright © 2018–2023 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe Demo 3: Backward Proofs

A __tactic__ operates on a proof goal and either proves it or creates new
subgoals. Tactics are a __backward__ proof mechanism: They start from the goal
and work towards the available hypotheses and theorems. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

namespace BackwardProofs


/- ## Tactic Mode

Syntax of tactical proofs:

    by
      _tactic₁_
      …
      _tacticN

The keyword `by` indicates to Lean the proof is tactical. -/

theorem fst_of_two_props :
  ∀a b : Prop, a → b → a :=
  by
    intro a b
    intro ha hb
    apply ha

/- Note that `a → b → a` is parsed as `a → (b → a)`.

Propositions in Lean are terms of type `Prop`. `Prop` is a type, just like `Nat`
and `List Bool`. In fact there is a close correspondence between propositions and
types, which will be explained in lecture 4.


## Basic Tactics

`intro` moves `∀`-quantified variables, or the assumptions of implications `→`,
from the goal's conclusion (after `⊢`) into the goal's hypotheses (before `⊢`).

`apply` matches the goal's conclusion with the conclusion of the specified
theorem and adds the theorem's hypotheses as new goals. -/

theorem fst_of_two_props_params (a b : Prop) (ha : a) (hb : b) :
  a :=
  by apply ha

theorem prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
  a → c :=
  by
    intro ha
    apply hbc
    apply hab
    apply ha

/- The above proof step by step:

* Assume we have a proof of `a`.
* The goal is `c`, which we can show if we prove `b` (from `hbc`).
* The goal is `b`, which we can show if we prove `a` (from `hab`).
* We already know `a` (from `ha`).

Next, `exact` matches the goal's conclusion with the specified theorem, closing
the goal. We can often use `apply` in such situations, but `exact` communicates
our intentions better. -/

theorem fst_of_two_props_exact (a b : Prop) (ha : a) (hb : b) :
  a :=
  by exact ha

/- `assumption` finds a hypothesis from the local context that matches the
goal's conclusion and applies it to prove the goal. -/

theorem fst_of_two_props_assumption (a b : Prop)
    (ha : a) (hb : b) :
  a :=
  by assumption

/- `rfl` proves `l = r`, where the two sides are syntactically equal up to
computation. Computation means unfolding of definitions, β-reduction
(application of `fun` to an argument), `let`, and more. -/

theorem α_example {α β : Type} (f : α → β) :
  (fun x ↦ f x) = (fun y ↦ f y) :=
  by rfl

theorem β_example {α β : Type} (f : α → β) (a : α) :
  (fun x ↦ f x) a = f a :=
  by rfl

def double (n : ℕ) : ℕ :=
  n + n

theorem δ_example :
  double 5 = 5 + 5 :=
  by rfl

/- `let` introduces a definition that is locally scoped. Below, `n := 2` is only
in scope in the expression `n + n`. -/

theorem ζ_example :
  (let n : ℕ := 2
   n + n) = 4 :=
  by rfl

theorem η_example {α β : Type} (f : α → β) :
  (fun x ↦ f x) = f :=
  by rfl

/- `(a, b)` is the pair whose first component is `a` and whose second component
is `b`. `Prod.fst` is a so-called projection that extracts the first component
of a pair. -/

theorem ι_example {α β : Type} (a : α) (b : β) :
  Prod.fst (a, b) = a :=
  by rfl


/- ## Reasoning about Logical Connectives and Quantifiers

Introduction rules: -/

#check True.intro
#check And.intro
#check Or.inl
#check Or.inr
#check Iff.intro
#check Exists.intro

/- Elimination rules: -/

#check False.elim
#check And.left
#check And.right
#check Or.elim
#check Iff.mp
#check Iff.mpr
#check Exists.elim

/- Definition of `¬` and related theorems: -/

#print Not
#check Classical.em
#check Classical.byContradiction

/- There are no explicit rules for `Not` (`¬`) since `¬ p` is defined as
`p → False`. -/

theorem And_swap (a b : Prop) :
  a ∧ b → b ∧ a :=
  by
    intro hab
    apply And.intro
    apply And.right
    exact hab
    apply And.left
    exact hab

/- The above proof step by step:

* Assume we know `a ∧ b`.
* The goal is `b ∧ a`.
* Show `b`, which we can if we can show a conjunction with `b` on the right.
* We can, we already have `a ∧ b`.
* Show `a`, which we can if we can show a conjunction with `a` on the left.
* We can, we already have `a ∧ b`.

The `{ … }` combinator focuses on a specific subgoal. The tactic inside must
fully prove it. In the proof below, `{ … }` is used for each of the two subgoals
to give more structure to the proof. -/

theorem And_swap_braces :
  ∀a b : Prop, a ∧ b → b ∧ a :=
  by
    intro a b hab
    apply And.intro
    { exact And.right hab }
    { exact And.left hab }

/- Notice above how we pass the hypothesis `hab` directly to the theorems
`And.right` and `And.left`, instead of waiting for the theorems' assumptions to
appear as new subgoals. This is a small forward step in an otherwise backward
proof. -/

opaque f : ℕ → ℕ

theorem f5_if (h : ∀n : ℕ, f n = n) :
  f 5 = 5 :=
  by exact h 5

theorem Or_swap (a b : Prop) :
  a ∨ b → b ∨ a :=
  by
    intro hab
    apply Or.elim hab
    { intro ha
      exact Or.inr ha }
    { intro hb
      exact Or.inl hb }

theorem modus_ponens (a b : Prop) :
  (a → b) → a → b :=
  by
    intro hab ha
    apply hab
    exact ha

theorem Not_Not_intro (a : Prop) :
  a → ¬¬ a :=
  by
    intro ha hna
    apply hna
    exact ha

theorem Exists_double_iden :
  ∃n : ℕ, double n = n :=
  by
    apply Exists.intro 0
    rfl


/- ## Reasoning about Equality -/

#check Eq.refl
#check Eq.symm
#check Eq.trans
#check Eq.subst

/- The above rules can be used directly: -/

theorem Eq_trans_symm {α : Type} (a b c : α)
    (hab : a = b) (hcb : c = b) :
  a = c :=
  by
    apply Eq.trans
    { exact hab }
    { apply Eq.symm
      exact hcb }

/- `rw` applies a single equation as a left-to-right rewrite rule, once. To
apply an equation right-to-left, prefix its name with `←`. -/

theorem Eq_trans_symm_rw {α : Type} (a b c : α)
    (hab : a = b) (hcb : c = b) :
  a = c :=
  by
    rw [hab]
    rw [hcb]

/- `rw` can expand a definition. Below, `¬¬ a` becomes `¬ a → False`, and `¬ a`
becomes `a → False`. -/

theorem a_proof_of_negation (a : Prop) :
  a → ¬¬ a :=
  by
    rw [Not]
    rw [Not]
    intro ha
    intro hna
    apply hna
    exact ha

/- `simp` applies a standard set of rewrite rules (the __simp set__)
exhaustively. The set can be extended using the `@[simp]` attribute. Theorems
can be temporarily added to the simp set with the syntax
`simp [_theorem₁_, …, _theoremN_]`. -/

theorem cong_two_args_1p1 {α : Type} (a b c d : α)
    (g : α → α → ℕ → α) (hab : a = b) (hcd : c = d) :
  g a c (1 + 1) = g b d 2 :=
  by simp [hab, hcd]

/- `ac_rfl` is similar to `rfl`, but it can reason up to associativity and
commutativity of `+`, `*`, and other binary operators. -/

theorem abc_Eq_cba (a b c : ℕ) :
  a + b + c = c + b + a :=
  by ac_rfl


/- ## Proofs by Mathematical Induction

`induction` performs induction on the specified variable. It gives rise to one
named subgoal per constructor. -/

theorem add_zero (n : ℕ) :
  add 0 n = n :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih => simp [add, ih]

theorem add_succ (m n : ℕ) :
  add (Nat.succ m) n = Nat.succ (add m n) :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih => simp [add, ih]

theorem add_comm (m n : ℕ) :
  add m n = add n m :=
  by
    induction n with
    | zero       => simp [add, add_zero]
    | succ n' ih => simp [add, add_succ, ih]

theorem add_assoc (l m n : ℕ) :
  add (add l m) n = add l (add m n) :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih => simp [add, ih]

/- `ac_rfl` is extensible. We can register `add` as a commutative and
associative operator using the type class instance mechanism (explained in
lecture 5). This is useful for the `ac_rfl` invocation below. -/

instance IsAssociative_add : IsAssociative ℕ add :=
  { assoc := add_assoc }

instance IsCommutative_add : IsCommutative ℕ add :=
  { comm := add_comm }

theorem mul_add (l m n : ℕ) :
  mul l (add m n) = add (mul l m) (mul l n) :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih =>
      simp [add, mul, ih]
      ac_rfl


/- ## Cleanup Tactics

`clear` removes unused variables or hypotheses.

`rename` changes the name of a variable or hypothesis. -/

theorem cleanup_example (a b c : Prop) (ha : a) (hb : b)
    (hab : a → b) (hbc : b → c) :
  c :=
  by
    clear ha hab a
    apply hbc
    clear hbc c
    rename b => h
    exact h

end BackwardProofs

end LoVe
