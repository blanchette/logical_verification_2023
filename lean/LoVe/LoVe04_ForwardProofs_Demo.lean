/- Copyright © 2018–2023 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe Demo 4: Forward Proofs

When developing a proof, often it makes sense to work __forward__: to start with
what we already know and proceed step by step towards our goal. Lean's
structured proofs and raw proof terms are two styles that support forward
reasoning. -/

set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

namespace ForwardProofs


/- ## Structured Constructs

Structured proofs are syntactic sugar sprinkled on top of Lean's
__proof terms__.

The simplest kind of structured proof is the name of a theorem, possibly with
arguments. -/

theorem add_comm (m n : ℕ) :
  add m n = add n m :=
  sorry

theorem add_comm_zero_left (n : ℕ) :
  add 0 n = add n 0 :=
  add_comm 0 n

/- The equivalent backward proof: -/

theorem add_comm_zero_left_by_exact (n : ℕ) :
  add 0 n = add n 0 :=
  by exact add_comm 0 n

/- `fix` and `assume` move `∀`-quantified variables and assumptions from the
goal into the local context. They can be seen as structured versions of the
`intro` tactic.

`show` repeats the goal to prove. It is useful as documentation or to rephrase
the goal (up to computation). -/

theorem fst_of_two_props :
  ∀a b : Prop, a → b → a :=
  fix a b : Prop
  assume ha : a
  assume hb : b
  show a from
    ha

theorem fst_of_two_props_show (a b : Prop) (ha : a) (hb : b) :
  a :=
  show a from
    ha

theorem fst_of_two_props_no_show (a b : Prop) (ha : a) (hb : b) :
  a :=
  ha

/- `have` proves an intermediate theorem, which can refer to the local
context. -/

theorem prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
  a → c :=
  assume ha : a
  have hb : b :=
    hab ha
  have hc : c :=
    hbc hb
  show c from
    hc

theorem prop_comp_inline (a b c : Prop) (hab : a → b)
  (hbc : b → c) :
  a → c :=
  assume ha : a
  show c from
    hbc (hab ha)


/- ## Forward Reasoning about Connectives and Quantifiers -/

theorem And_swap (a b : Prop) :
  a ∧ b → b ∧ a :=
  assume hab : a ∧ b
  have ha : a :=
    And.left hab
  have hb : b :=
    And.right hab
  show b ∧ a from
    And.intro hb ha

theorem or_swap (a b : Prop) :
  a ∨ b → b ∨ a :=
  assume hab : a ∨ b
  show b ∨ a from
    Or.elim hab
      (assume ha : a
       show b ∨ a from
         Or.inr ha)
      (assume hb : b
       show b ∨ a from
         Or.inl hb)

def double (n : ℕ) : ℕ :=
  n + n

theorem nat_exists_double_iden :
  ∃n : ℕ, double n = n :=
  Exists.intro 0
    (show double 0 = 0 from
     by rfl)

theorem nat_exists_double_iden_no_show :
  ∃n : ℕ, double n = n :=
  Exists.intro 0 (by rfl)

theorem modus_ponens (a b : Prop) :
  (a → b) → a → b :=
  assume hab : a → b
  assume ha : a
  show b from
    hab ha

theorem not_not_intro (a : Prop) :
  a → ¬¬ a :=
  assume ha : a
  assume hna : ¬ a
  show False from
    hna ha

/- Just as you can apply forward reasoning inside a backward proof, you can
apply backward reasoning inside a forward proof (indicated with `by`): -/

theorem Forall.one_point {α : Type} (t : α) (P : α → Prop) :
  (∀x, x = t → P x) ↔ P t :=
  Iff.intro
    (assume hall : ∀x, x = t → P x
     show P t from
       by
         apply hall t
         rfl)
    (assume hp : P t
     fix x : α
     assume heq : x = t
     show P x from
       by
         rw [heq]
         exact hp)

theorem beast_666 (beast : ℕ) :
  (∀n, n = 666 → beast ≥ n) ↔ beast ≥ 666 :=
  Forall.one_point _ _

#print beast_666

theorem Exists.one_point {α : Type} (t : α) (P : α → Prop) :
  (∃x : α, x = t ∧ P x) ↔ P t :=
  Iff.intro
    (assume hex : ∃x, x = t ∧ P x
     show P t from
       Exists.elim hex
         (fix x : α
          assume hand : x = t ∧ P x
          have hxt : x = t :=
            And.left hand
          have hpx : P x :=
            And.right hand
          show P t from
            by
              rw [←hxt]
              exact hpx))
    (assume hp : P t
     show ∃x : α, x = t ∧ P x from
       Exists.intro t
         (have tt : t = t :=
            by rfl
          show t = t ∧ P t from
            And.intro tt hp))


/- ## Calculational Proofs

In informal mathematics, we often use transitive chains of equalities,
inequalities, or equivalences (e.g., `a ≥ b ≥ c`). In Lean, such calculational
proofs are supported by `calc`.

Syntax:

    calc
      _term₀_ _op₁_ _term₁_ :=
        _proof₁_
      _ _op₂_ _term₂_ :=
        _proof₂_
     ⋮
      _ _opN_ _termN_ :=
        _proofN_ -/

theorem two_mul_example (m n : ℕ) :
  2 * m + n = m + n + m :=
calc 
  2 * m + n = m + m + n :=
    by rw [Nat.two_mul]
  _ = m + n + m :=
    by ac_rfl

/- `calc` saves some repetition, some `have` labels, and some transitive
reasoning: -/

theorem two_mul_example_have (m n : ℕ) :
  2 * m + n = m + n + m :=
  have hmul : 2 * m + n = m + m + n :=
    by rw [Nat.two_mul]
  have hcomm : m + m + n = m + n + m :=
    by ac_rfl
  show _ from
    Eq.trans hmul hcomm


/- ## Forward Reasoning with Tactics

The `have`, `let`, and `calc` structured proof commands are also available as a
tactic. Even in tactic mode, it can be useful to state intermediate results and
definitions in a forward fashion. -/

theorem prop_comp_tactical (a b c : Prop) (hab : a → b)
  (hbc : b → c) :
  a → c :=
  by
    intro ha
    have hb : b :=
      hab ha
    let c' := c
    have hc : c' :=
      hbc hb
    exact hc


/- ## Dependent Types

Dependent types are the defining feature of the dependent type theory family of
logics.

Consider a function `pick` that take a number `n : ℕ` and that returns a number
between 0 and `n`. Conceptually, `pick` has a dependent type, namely

    `(n : ℕ) → {i : ℕ // i ≤ n}`

We can think of this type as a `ℕ`-indexed family, where each member's type may
depend on the index:

    `pick n : {i : ℕ // i ≤ n}`

But a type may also depend on another type, e.g., `List` (or `fun α ↦ List α`)
and `fun α ↦ α → α`.

A term may depend on a type, e.g., `fun α ↦ fun (x : α) ↦ x` (a polymorphic
identity function).

Of course, a term may also depend on a term.

Unless otherwise specified, a __dependent type__ means a type depending on a
term. This is what we mean when we say that simple type theory does not support
dependent types.

In summary, there are four cases for `fun x ↦ t` in the calculus of inductive
constructions (cf. Barendregt's `λ`-cube):

Body (`t`) |              | Argument (`x`) | Description
---------- | ------------ | -------------- | ----------------------------------
A term     | depending on | a term         | Simply typed anonymous function
A type     | depending on | a term         | Dependent type (strictly speaking)
A term     | depending on | a type         | Polymorphic term
A type     | depending on | a type         | Type constructor

Revised typing rules:

    C ⊢ t : (x : σ) → τ[x]    C ⊢ u : σ
    ———————————————————————————————————— App'
    C ⊢ t u : τ[u]

    C, x : σ ⊢ t : τ[x]
    ———————————————————————————————————— Fun'
    C ⊢ (fun x : σ ↦ t) : (x : σ) → τ[x]

These two rules degenerate to `App` and `Fun` if `x` does not occur in `τ[x]`

Example of `App'`:

    ⊢ pick : (n : ℕ) → {i : ℕ // i ≤ n}    ⊢ 5 : ℕ
    ——————————————————————————————————————————————— App'
    ⊢ pick 5 : {i : ℕ // i ≤ 5}

Example of `Fun'`:

    α : Type, x : α ⊢ x : α
    —————————————————————————————————— Fun or Fun'
    α : Type ⊢ (fun x : α ↦ x) : α → α
    ————————————————————————————————————————————————————— Fun'
    ⊢ (fun α : Type ↦ fun x : α ↦ x) : (α : Type) → α → α

Remarkably, universal quantification is simply an alias for a dependent type:

    `∀x : σ, τ` := `(x : σ) → τ`

This will become clearer below.


## The PAT Principle

`→` is used both as the implication symbol and as the type constructor of
functions. The two pairs of concepts not only look the same, they are the same,
by the PAT principle:

* PAT = propositions as types;
* PAT = proofs as terms.

Types:

* `σ → τ` is the type of total functions from `σ` to `τ`.
* `(x : σ) → τ[x]` is the dependent function type from `x : σ` to `τ[x]`.

Propositions:

* `P → Q` can be read as "`P` implies `Q`", or as the type of functions mapping
  proofs of `P` to proofs of `Q`.
* `∀x : σ, Q[x]` can be read as "for all `x`, `Q[x]`", or as the type of
  functions of type `(x : σ) → Q[x]`, mapping values `x` of type `σ` to proofs
  of `Q[x]`.

Terms:

* A constant is a term.
* A variable is a term.
* `t u` is the application of function `t` to value `u`.
* `fun x ↦ t[x]` is a function mapping `x` to `t[x]`.

Proofs:

* A theorem or hypothesis name is a proof.
* `H t`, which instantiates the leading parameter or quantifier of proof `H`'
  statement with term `t`, is a proof.
* `H G`, which discharges the leading assumption of `H`'s statement with
  proof `G`, is a proof.
* `fun h : P ↦ H[h]` is a proof of `P → Q`, assuming `H[h]` is a proof of `Q`
  for `h : P`.
* `fun x : σ ↦ H[x]` is a proof of `∀x : σ, Q[x]`, assuming `H[x]` is a proof
  of `Q[x]` for `x : σ`. -/

theorem And_swap_raw (a b : Prop) :
  a ∧ b → b ∧ a :=
  fun hab : a ∧ b ↦ And.intro (And.right hab) (And.left hab)

theorem And_swap_tactical (a b : Prop) :
  a ∧ b → b ∧ a :=
  by
    intro hab
    apply And.intro
    apply And.right
    exact hab
    apply And.left
    exact hab

/- Tactical proofs are reduced to proof terms. -/

#print And_swap
#print And_swap_raw
#print And_swap_tactical

end ForwardProofs


/- ## Induction by Pattern Matching and Recursion

By the PAT principle, a proof by induction is the same as a recursively
specified proof term. Thus, as alternative to the `induction` tactic, induction
can also be done by pattern matching and recursion:

* the induction hypothesis is then available under the name of the theorem we
  are proving;

* well-foundedness of the argument is often proved automatically. -/

#check reverse

theorem reverse_append {α : Type} :
  ∀xs ys : List α,
    reverse (xs ++ ys) = reverse ys ++ reverse xs
  | [],      ys => by simp [reverse]
  | x :: xs, ys => by simp [reverse, reverse_append xs]

theorem reverse_append_tactical {α : Type} (xs ys : List α) :
  reverse (xs ++ ys) = reverse ys ++ reverse xs :=
  by
    induction xs with
    | nil           => simp [reverse]
    | cons x xs' ih => simp [reverse, ih]

theorem reverse_reverse {α : Type} :
  ∀xs : List α, reverse (reverse xs) = xs
  | []      => by rfl
  | x :: xs =>
    by simp [reverse, reverse_append, reverse_reverse xs]

end LoVe
