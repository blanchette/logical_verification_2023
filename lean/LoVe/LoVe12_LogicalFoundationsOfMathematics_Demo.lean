/- Copyright © 2018–2023 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo


/- # LoVe Demo 12: Logical Foundations of Mathematics

We dive deeper into the logical foundations of Lean. Most of the features
described here are especially relevant for defining mathematical objects and
proving theorems about them. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Universes

Not only terms have a type, but also types have a type. For example,

    `@And.intro : ∀a b, a → b → a ∧ b`

and

    `∀a b, a → b → a ∧ b : Prop`

Now, what is the type of `Prop`? `Prop` has the same type as virtually all other
types we have constructed so far:

    `Prop : Type`

What is the type of `Type`? The typing `Type : Type` would lead to a
contradiction, called **Girard's paradox**, resembling Russel's paradox.
Instead:

    `Type   : Type 1`
    `Type 1 : Type 2`
    `Type 2 : Type 3`
    ⋮

Aliases:

    `Type`   := `Type 0`
    `Prop`   := `Sort 0`
    `Type u` := `Sort (u + 1)`

The types of types (`Sort u`, `Type u`, and `Prop`) are called __universes__.
The `u` in `Sort u` is a __universe level__.

The hierarchy is captured by the following typing judgment:

    ————————————————————————— Sort
    C ⊢ Sort u : Sort (u + 1) -/

#check @And.intro
#check ∀a b : Prop, a → b → a ∧ b
#check Prop
#check ℕ
#check Type
#check Type 1
#check Type 2

universe u v

#check Type u

#check Sort 0
#check Sort 1
#check Sort 2
#check Sort u

#check Type _


/- ## The Peculiarities of Prop

`Prop` is different from the other universes in many respects.


### Impredicativity

The function type `σ → τ` is put into the larger one of the universes that
`σ` and `τ` live in:

    C ⊢ σ : Type u    C ⊢ τ : Type v
    ————————————————————————————————— SimpleArrow-Type
    C ⊢ σ → τ : Type (max u v)

For dependent types, this generalizes to

    C ⊢ σ : Type u    C, x : σ ⊢ τ[x] : Type v
    ——————————————————————————————————————————— Arrow-Type
    C ⊢ (x : σ) → τ[x] : Type (max u v)

This behavior of the universes `Type v` is called __predicativity__.

To force expressions such as `∀a : Prop, a → a` to be of type `Prop` anyway, we
need a special typing rule for `Prop`:

    C ⊢ σ : Sort u    x : σ ⊢ τ[x] : Prop
    —————————————————————————————————————— Arrow-Prop
    C ⊢ (∀x : σ, τ[x]) : Prop

This behavior of `Prop` is called __impredicativity__.

The rules `Arrow-Type` and `Arrow-Prop` can be generalized into a single rule:

    C ⊢ σ : Sort u    C, x : σ ⊢ τ[x] : Sort v
    ——————————————————————————————————————————— Arrow
    C ⊢ (x : σ) → τ[x] : Sort (imax u v)

where

    `imax u 0       = 0`
    `imax u (v + 1) = max u (v + 1)` -/

#check fun (α : Type u) (β : Type v) ↦ α → β
#check ∀a : Prop, a → a


/- ### Proof Irrelevance

A second difference between `Prop` and `Type u` is __proof irrelevance__:

    `∀(a : Prop) (h₁ h₂ : a), h₁ = h₂`

This makes reasoning about dependent types easier.

When viewing a proposition as a type and a proof as an element of that type,
proof irrelevance means that a proposition is either an empty type or has
exactly one inhabitant.

Proof irrelevance can be proved by `rfl`.

An unfortunate consequence of proof irrelevance is that it prevents us from
performing rule induction by pattern matching and recursion. -/

#check proof_irrel

theorem proof_irrel {a : Prop} (h₁ h₂ : a) :
  h₁ = h₂ :=
  by rfl


/- ### No Large Elimination

A further difference between `Prop` and `Type u` is that `Prop` does not allow
__large elimination__, meaning that it impossible to extract data from a proof
of a proposition.

This is necessary to allow proof irrelevance. -/

/-
-- fails
def unsquare (i : ℤ) (hsq : ∃j, i = j * j) : ℤ :=
  match hsq with
  | Exists.intro j _ => j
-/

/- If the above were accepted, we could derive `False` as follows.

Let

    `hsq₁` := `Exists.intro 3 (by linarith)`
    `hsq₂` := `Exists.intro (-3) (by linarith)`

be two proofs of `∃j, (9 : ℤ) = j * j`. Then

    `unsquare 9 hsq₁ = 3`
    `unsquare 9 hsq₂ = -3`

However, by proof irrelevance, `hsq₁ = hsq₂`. Hence

    `unsquare 9 hsq₂ = 3`

Thus

    `3 = -3`

a contradiction.

As a compromise, Lean allows __small elimination__. It is called small
elimination because it eliminates only into `Prop`, whereas large elimination can
eliminate into an arbitrary large universe `Sort u`. This means we can use
`match` to analyze the structure of a proof, extract existential witnesses, and
so on, as long as the `match` expression is itself a proof. We have seen several
examples of this in lecture 5.

As a further compromise, Lean allows large elimination for
__syntactic subsingletons__: types in `Prop` for which it can be established
syntactically that they have cardinality 0 or 1. These are propositions such as
`False` and `a ∧ b` that can be proved in at most one way.


## The Axiom of Choice

Lean's logic includes the axiom of choice, which makes it possible to obtain an
arbitrary element from any nonempty type.

Consider Lean's `Nonempty` inductive predicate: -/

#print Nonempty

/- The predicate states that `α` has at least one element.

To prove `Nonempty α`, we must provide an `α` value to `Nonempty.intro`: -/

theorem Nat.Nonempty :
  Nonempty ℕ :=
  Nonempty.intro 0

/- Since `Nonempty` lives in `Prop`, large elimination is not available, and
thus we cannot extract the element that was used from a proof of `Nonempty α`.

The axiom of choice allows us to obtain some element of type `α` if we can show
`Nonempty α`: -/

#print Classical.choice

/- It will just give us an arbitrary element of `α`; we have no way of knowing
whether this is the element that was used to prove `Nonempty α`.

The constant `Classical.choice` is noncomputable, which is why some logicians
prefer to work without this axiom. -/

/-
#eval Classical.choice Nat.Nonempty     -- fails
-/
#reduce Classical.choice Nat.Nonempty

/- The axiom of choice is only an axiom in Lean's core library, giving users
the freedom to work with or without it.

Definitions using it must be marked as `noncomputable`: -/

noncomputable def arbitraryNat : ℕ :=
  Classical.choice Nat.Nonempty

/- The following tools rely on choice.


### Law of Excluded Middle -/

#check Classical.em
#check Classical.byContradiction


/- ### Hilbert Choice -/

#print Classical.choose
#print Classical.choose_spec

#check fun (p : ℕ → Prop) (h : ∃n : ℕ, p n) ↦
  Classical.choose h
#check fun (p : ℕ → Prop) (h : ∃n : ℕ, p n) ↦
  Classical.choose_spec h


/- ### Set-Theoretic Axiom of Choice -/

#print Classical.axiomOfChoice


/- ## Subtypes

Subtyping is a mechanism to create new types from existing ones.

Given a predicate on the elements of the base type, the __subtype__ contains
only those elements of the base type that fulfill this property. More precisely,
the subtype contains element–proof pairs that combine an element of the base
type and a proof that it fulfills the property.

Subtyping is useful for those types that cannot be defined as an inductive
type. For example, any attempt at defining the type of finite sets along the
following lines is doomed to fail: -/

-- wrong
inductive Finset (α : Type) : Type
  | empty  : Finset α
  | insert : α → Finset α → Finset α

/- Why does this not model finite sets?

Given a base type and a property, the subtype has the syntax

    `{` _variable_ `:` _base-type_ `//` _property-applied-to-variable_ `}`

Alias:

    `{x : τ // P[x]}` := `@Subtype τ (fun x ↦ P[x])`

Examples:

    `{i : ℕ // i ≤ n}`            := `@Subtype ℕ (fun i ↦ i ≤ n)`
    `{A : Set α // Set.Finite A}` := `@Subtype (Set α) Set.Finite`


### First Example: Full Binary Trees -/

#check BTree
#check IsFull
#check mirror
#check IsFull_mirror
#check mirror_mirror

def FullBTree (α : Type) : Type :=
  {t : BTree α // IsFull t}

#print Subtype
#check Subtype.mk

/- To define elements of `FullBTree`, we must provide a `BTree` and a proof
that it is full: -/

def emptyFullBTree : FullBTree ℕ :=
  Subtype.mk BTree.empty IsFull.empty

def fullBTree6 : FullBTree ℕ :=
  Subtype.mk (BTree.node 6 BTree.empty BTree.empty)
    (by
       apply IsFull.node
       apply IsFull.empty
       apply IsFull.empty
       rfl)

#reduce Subtype.val fullBTree6
#check Subtype.property fullBTree6

/- We can lift existing operations on `BTree` to `FullBTree`: -/

def FullBTree.mirror {α : Type} (t : FullBTree α) :
  FullBTree α :=
  Subtype.mk (LoVe.mirror (Subtype.val t))
    (by
       apply IsFull_mirror
       apply Subtype.property t)

#reduce Subtype.val (FullBTree.mirror fullBTree6)

/- And of course we can prove theorems about the lifted operations: -/

theorem FullBTree.mirror_mirror {α : Type} (t : FullBTree α) :
  (FullBTree.mirror (FullBTree.mirror t)) = t :=
  by
    apply Subtype.eq
    simp [FullBTree.mirror, LoVe.mirror_mirror]

#check Subtype.eq


/- ### Second Example: Vectors -/

def Vector (α : Type) (n : ℕ) : Type :=
  {xs : List α // List.length xs = n}

def vector123 : Vector ℤ 3 :=
  Subtype.mk [1, 2, 3] (by rfl)

def Vector.neg {n : ℕ} (v : Vector ℤ n) : Vector ℤ n :=
  Subtype.mk (List.map Int.neg (Subtype.val v))
    (by
       rw [List.length_map]
       exact Subtype.property v)

theorem Vector.neg_neg (n : ℕ) (v : Vector ℤ n) :
  Vector.neg (Vector.neg v) = v :=
  by
    apply Subtype.eq
    simp [Vector.neg]


/- ## Quotient Types

Quotients are a powerful construction in mathematics used to construct `ℤ`, `ℚ`,
`ℝ`, and many other types.

Like subtyping, quotienting constructs a new type from an existing type. Unlike
a subtype, a quotient type contains all of the elements of the base type, but
some elements that were different in the base type are considered equal in the
quotient type. In mathematical terms, the quotient type is isomorphic to a
partition of the base type.

To define a quotient type, we need to provide a type that it is derived from and
an equivalence relation on the type that determines which elements are
considered equal. -/

#check Quotient
#print Setoid

#check Quotient.mk
#check Quotient.sound
#check Quotient.exact

#check Quotient.lift
#check Quotient.lift₂
#check @Quotient.inductionOn


/- ## First Example: Integers

Let us build the integers `ℤ` as a quotient over pairs of natural numbers
`ℕ × ℕ`.

A pair `(p, n)` of natural numbers represents the integer `p - n`. Nonnegative
integers `p` can be represented by `(p, 0)`. Negative integers `-n` can be
represented by `(0, n)`. However, many representations of the same integer are
possible; e.g., `(7, 0)`, `(8, 1)`, `(9, 2)`, and `(10, 3)` all represent the
integer `7`.

Which equivalence relation can we use?

We want two pairs `(p₁, n₁)` and `(p₂, n₂)` to be equal if `p₁ - n₁ = p₂ - n₂`.
However, this does not work because subtraction on `ℕ` is ill-behaved (e.g.,
`0 - 1 = 0`). Instead, we use `p₁ + n₂ = p₂ + n₁`. -/

instance Int.Setoid : Setoid (ℕ × ℕ) :=
  { r :=
      fun pn₁ pn₂ : ℕ × ℕ ↦
        Prod.fst pn₁ + Prod.snd pn₂ =
        Prod.fst pn₂ + Prod.snd pn₁
    iseqv :=
      { refl :=
          by
            intro pn
            rfl
        symm :=
          by
            intro pn₁ pn₂ h
            rw [h]
        trans :=
          by
            intro pn₁ pn₂ pn₃ h₁₂ h₂₃
            linarith } }

theorem Int.Setoid_Iff (pn₁ pn₂ : ℕ × ℕ) :
  pn₁ ≈ pn₂ ↔
  Prod.fst pn₁ + Prod.snd pn₂ = Prod.fst pn₂ + Prod.snd pn₁ :=
  by rfl

def Int : Type :=
  Quotient Int.Setoid

def Int.zero : Int :=
  ⟦(0, 0)⟧

theorem Int.zero_Eq (m : ℕ) :
  Int.zero = ⟦(m, m)⟧ :=
  by
    rw [Int.zero]
    apply Quotient.sound
    rw [Int.Setoid_Iff]
    simp

def Int.add : Int → Int → Int :=
  Quotient.lift₂
    (fun pn₁ pn₂ : ℕ × ℕ ↦
       ⟦(Prod.fst pn₁ + Prod.fst pn₂,
         Prod.snd pn₁ + Prod.snd pn₂)⟧)
    (by
       intro pn₁ pn₂ pn₁' pn₂' h₁ h₂
       apply Quotient.sound
       rw [Int.Setoid_Iff] at *
       linarith)

theorem Int.add_Eq (p₁ n₁ p₂ n₂ : ℕ) :
  Int.add ⟦(p₁, n₁)⟧ ⟦(p₂, n₂)⟧ = ⟦(p₁ + p₂, n₁ + n₂)⟧ :=
  by rfl

theorem Int.add_zero (i : Int) :
  Int.add Int.zero i = i :=
  by
    induction i using Quotient.inductionOn with
    | h pn =>
      cases pn with
      | mk p n => simp [Int.zero, Int.add_Eq]

/- This definitional syntax would be nice: -/

/-
-- fails
def Int.add : Int → Int → Int
  | ⟦(p₁, n₁)⟧, ⟦(p₂, n₂)⟧ => ⟦(p₁ + p₂, n₁ + n₂)⟧
-/

/- But it would be dangerous: -/

/-
-- fails
def Int.fst : Int → ℕ
  | ⟦(p, n)⟧ => p
-/

/- Using `Int.fst`, we could derive `False`. First, we have

    `Int.fst ⟦(0, 0)⟧ = 0`
    `Int.fst ⟦(1, 1)⟧ = 1`

But since `⟦(0, 0)⟧ = ⟦(1, 1)⟧`, we get

    `0 = 1` -/


/- ### Second Example: Unordered Pairs

__Unordered pairs__ are pairs for which no distinction is made between the first
and second components. They are usually written `{a, b}`.

We will introduce the type `UPair` of unordered pairs as the quotient of pairs
`(a, b)` with respect to the relation "contains the same elements as". -/

instance UPair.Setoid (α : Type) : Setoid (α × α) :=
{ r :=
    fun ab₁ ab₂ : α × α ↦
      ({Prod.fst ab₁, Prod.snd ab₁} : Set α) =
      ({Prod.fst ab₂, Prod.snd ab₂} : Set α)
  iseqv :=
    { refl  := by simp
      symm  := by aesop
      trans := by aesop } }

theorem UPair.Setoid_Iff {α : Type} (ab₁ ab₂ : α × α) :
  ab₁ ≈ ab₂ ↔
  ({Prod.fst ab₁, Prod.snd ab₁} : Set α) =
  ({Prod.fst ab₂, Prod.snd ab₂} : Set α) :=
  by rfl

def UPair (α : Type) : Type :=
  Quotient (UPair.Setoid α)

#check UPair.Setoid

/- It is easy to prove that our pairs are really unordered: -/

theorem UPair.mk_symm {α : Type} (a b : α) :
  (⟦(a, b)⟧ : UPair α) = ⟦(b, a)⟧ :=
  by
    apply Quotient.sound
    rw [UPair.Setoid_Iff]
    simp [Set.unordered_pair_comm]

/- Another representation of unordered pairs is as sets of cardinality 1 or 2.
The following operation converts `UPair` to that representation: -/

def Set_of_UPair {α : Type} : UPair α → Set α :=
  Quotient.lift (fun ab : α × α ↦ {Prod.fst ab, Prod.snd ab})
    (by
       intro ab₁ ab₂ h
       rw [UPair.Setoid_Iff] at *
       exact h)


/- ### Alternative Definitions via Normalization and Subtyping

Each element of a quotient type corresponds to an `≈`-equivalence class.
If there exists a systematic way to obtain a **canonical representative** for
each class, we can use a subtype instead of a quotient, keeping only the
canonical representatives.

Consider the quotient type `Int` above. We could say that a pair `(p, n)` is
__canonical__ if `p` or `n` is `0`. -/

namespace Alternative

inductive Int.IsCanonical : ℕ × ℕ → Prop
  | nonpos {n : ℕ} : Int.IsCanonical (0, n)
  | nonneg {p : ℕ} : Int.IsCanonical (p, 0)

def Int : Type :=
  {pn : ℕ × ℕ // Int.IsCanonical pn}

/- **Normalizing** pairs of natural numbers is easy: -/

def Int.normalize : ℕ × ℕ → ℕ × ℕ
  | (p, n) => if p ≥ n then (p - n, 0) else (0, n - p)

theorem Int.IsCanonical_normalize (pn : ℕ × ℕ) :
  Int.IsCanonical (Int.normalize pn) :=
  by
    cases pn with
    | mk p n =>
      simp [Int.normalize]
      cases Classical.em (p ≥ n) with
      | inl hpn =>
        simp [*]
        exact Int.IsCanonical.nonneg
      | inr hpn =>
        simp [*]
        exact Int.IsCanonical.nonpos

/- For unordered pairs, there is no obvious normal form, except to always put
the smaller element first (or last). This requires a linear order `≤` on `α`. -/

def UPair.IsCanonical {α : Type} [LinearOrder α] :
  α × α → Prop
  | (a, b) => a ≤ b

def UPair (α : Type) [LinearOrder α] : Type :=
  {ab : α × α // UPair.IsCanonical ab}

end Alternative

end LoVe
