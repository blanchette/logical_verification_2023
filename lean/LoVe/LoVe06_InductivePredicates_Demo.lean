/- Copyright © 2018–2023 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe04_ForwardProofs_Demo
import LoVe.LoVe05_FunctionalProgramming_Demo


/- # LoVe Demo 6: Inductive Predicates

__Inductive predicates__, or inductively defined propositions, are a convenient
way to specify functions of type `⋯ → Prop`. They are reminiscent of formal
systems and of the Horn clauses of Prolog, the logic programming language par
excellence.

A possible view of Lean:

    Lean = functional programming + logic programming + more logic -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Introductory Examples

### Even Numbers

Mathematicians often define sets as the smallest that meets some criteria. For
example:

    The set `E` of even natural numbers is defined as the smallest set closed
    under the following rules: (1) `0 ∈ E` and (2) for every `k ∈ ℕ`, if
    `k ∈ E`, then `k + 2 ∈ E`.

In Lean, we can define the corresponding "is even" predicate as follows: -/

inductive Even : ℕ → Prop where
  | zero    : Even 0
  | add_two : ∀k : ℕ, Even k → Even (k + 2)

/- This should look familiar. We have used the same syntax, except with `Type`
instead of `Prop`, for inductive types.

The above command introduces a new unary predicate `Even` as well as two
constructors, `Even.zero` and `Even.add_two`, which can be used to build proof
terms. Thanks to the "no junk" guarantee of inductive definitions, `Even.zero`
and `Even.add_two` are the only two ways to construct proofs of `Even`.

By the PAT principle, `Even` can be seen as an inductive type, the values being
the proof terms. -/

theorem Even_4 :
  Even 4 :=
  have Even_0 : Even 0 :=
    Even.zero
  have Even_2 : Even 2 :=
    Even.add_two _ Even_0
  show Even 4 from
    Even.add_two _ Even_2

/- Why cannot we simply define `Even` recursively? Indeed, why not? -/

def evenRec : ℕ → Bool
  | 0     => true
  | 1     => false
  | k + 2 => evenRec k

/- There are advantages and disadvantages to both styles.

The recursive version requires us to specify a false case (1), and it requires
us to worry about termination. On the other hand, because it is computational,
it works well with `rfl`, `simp`, `#reduce`, and `#eval`.

The inductive version is often considered more abstract and elegant. Each rule
is stated independently of the others.

Yet another way to define `Even` is as a nonrecursive definition: -/

def evenNonrec (k : ℕ) : Prop :=
  k % 2 = 0

/- Mathematicians would probably find this the most satisfactory definition.
But the inductive version is a convenient, intuitive example that is typical of
many realistic inductive definitions.


### Tennis Games

Transition systems consists of transition rules, which together specify a
binary predicate connecting a "before" and an "after" state. As a simple
specimen of a transition system, we consider the possible transitions, in a game
of tennis, starting from 0–0. -/

inductive Score : Type where
  | vs       : ℕ → ℕ → Score
  | advServ  : Score
  | advRecv  : Score
  | gameServ : Score
  | gameRecv : Score

infixr:50 " – " => Score.vs

inductive Step : Score → Score → Prop where
  | serv_0_15     : ∀n, Step (0–n) (15–n)
  | serv_15_30    : ∀n, Step (15–n) (30–n)
  | serv_30_40    : ∀n, Step (30–n) (40–n)
  | serv_40_game  : ∀n, n < 40 → Step (40–n) Score.gameServ
  | serv_40_adv   : Step (40–40) Score.advServ
  | serv_adv_40   : Step Score.advServ (40–40)
  | serv_adv_game : Step Score.advServ Score.gameServ
  | recv_0_15     : ∀n, Step (n–0) (n–15)
  | recv_15_30    : ∀n, Step (n–15) (n–30)
  | recv_30_40    : ∀n, Step (n–30) (n–40)
  | recv_40_game  : ∀n, n < 40 → Step (n–40) Score.gameRecv
  | recv_40_adv   : Step (40–40) Score.advRecv
  | recv_adv_40   : Step Score.advRecv (40–40)
  | recv_adv_game : Step Score.advRecv Score.gameRecv

infixr:45 " ↝ " => Step

/- Note that while `Score.vs` allows arbitrary numbers as arguments, the
formulation of the constructors for `Step` ensures only valid tennis scores can
be reached from `0–0`.

We can ask, and formally answer, questions such as: Can the score ever return to
`0–0`? -/

theorem no_Step_to_0_0 (s : Score) :
  ¬ s ↝ 0–0 :=
  by
    intro h
    cases h


/- ### Reflexive Transitive Closure

Our last introductory example is the reflexive transitive closure of a
relation `R`, modeled as a binary predicate `Star R`. -/

inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop
where
  | base (a b : α)    : R a b → Star R a b
  | refl (a : α)      : Star R a a
  | trans (a b c : α) : Star R a b → Star R b c → Star R a c

/- The first rule embeds `R` into `Star R`. The second rule achieves the
reflexive closure. The third rule achieves the transitive closure.

The definition is truly elegant. If you doubt this, try implementing `Star` as a
recursive function: -/

def starRec {α : Type} (R : α → α → Bool) :
  α → α → Bool :=
  sorry


/- ### A Nonexample

Not all inductive definitions are legal. -/

/-
-- fails
inductive Illegal : Prop where
  | intro : ¬ Illegal → Illegal
-/


/- ## Logical Symbols

The truth values `False` and `True`, the connectives `∧`, `∨` and `↔`, the
`∃` quantifier, and the equality predicate `=` are all defined as inductive
propositions or predicates. In contrast, `∀` and `→` are built into the logic.

Syntactic sugar:

    `∃x : α, P` := `Exists (λx : α, P)`
    `x = y`     := `Eq x y` -/

namespace logical_symbols

inductive And (a b : Prop) : Prop where
  | intro : a → b → And a b

inductive Or (a b : Prop) : Prop where
  | inl : a → Or a b
  | inr : b → Or a b

inductive Iff (a b : Prop) : Prop where
  | intro : (a → b) → (b → a) → Iff a b

inductive Exists {α : Type} (P : α → Prop) : Prop where
  | intro : ∀a : α, P a → Exists P

inductive True : Prop where
  | intro : True

inductive False : Prop where

inductive Eq {α : Type} : α → α → Prop where
  | refl : ∀a : α, Eq a a

end logical_symbols

#print And
#print Or
#print Iff
#print Exists
#print True
#print False
#print Eq


/- ## Rule Induction

Just as we can perform induction on a term, we can perform induction on a proof
term.

This is called __rule induction__, because the induction is on the introduction
rules (i.e., the constructors of the proof term). Thanks to the PAT principle,
this works as expected. -/

theorem mod_two_Eq_zero_of_Even (n : ℕ) (h : Even n) :
  n % 2 = 0 :=
  by
    induction h with
    | zero            => rfl
    | add_two k hk ih => simp [ih]

theorem Not_Even_two_mul_add_one (m n : ℕ)
    (hm : m = 2 * n + 1) :
  ¬ Even m :=
  by
    intro h
    induction h generalizing n with
    | zero            => linarith
    | add_two k hk ih =>
      apply ih (n - 1)
      cases n with
      | zero    => simp [Nat.ctor_eq_zero] at *
      | succ n' =>
        simp [Nat.succ_eq_add_one] at *
        linarith

/- `linarith` proves goals involving linear arithmetic equalities or
inequalities. "Linear" means it works only with `+` and `-`, not `*` and `/`
(but multiplication by a constant is supported). -/

theorem linarith_example (i : Int) (hi : i > 5) :
  2 * i + 3 > 11 :=
  by linarith

theorem Star_Star_Iff_Star {α : Type} (R : α → α → Prop)
    (a b : α) :
  Star (Star R) a b ↔ Star R a b :=
  by
    apply Iff.intro
    { intro h
      induction h with
      | base a b hab                  => exact hab
      | refl a                        => apply Star.refl
      | trans a b c hab hbc ihab ihbc =>
        apply Star.trans a b
        { exact ihab }
        { exact ihbc } }
    { intro h
      apply Star.base
      exact h }

@[simp] theorem Star_Star_Eq_Star {α : Type}
    (R : α → α → Prop) :
  Star (Star R) = Star R :=
  by
    apply funext
    intro a
    apply funext
    intro b
    apply propext
    apply Star_Star_Iff_Star

#check funext
#check propext


/- ## Elimination

Given an inductive predicate `P`, its introduction rules typically have the form
`∀…, ⋯ → P …` and can be used to prove goals of the form `⊢ P …`.

Elimination works the other way around: It extracts information from a theorem
or hypothesis of the form `P …`. Elimination takes various forms: pattern
matching, the `cases` and `induction` tactics, and custom elimination rules
(e.g., `And.left`).

* `cases` works like `induction` but without induction hypothesis.

* `match` is available as well.

Now we can finally understand how `cases h` where `h : l = r` and how
`cases Classical.em h` work. -/

#print Eq

theorem cases_Eq_example {α : Type} (l r : α) (h : l = r)
    (P : α → α → Prop) :
  P l r :=
  by
    cases h
    sorry

#check Classical.em
#print Or

theorem cases_Classical_em_example {α : Type} (a : α)
    (P Q : α → Prop) :
  Q a :=
  by
    have hor : P a ∨ ¬ P a :=
      Classical.em (P a)
    cases hor with
    | inl hl => sorry
    | inr hr => sorry

/- Often it is convenient to rewrite concrete terms of the form `P (c …)`,
where `c` is typically a constructor. We can state and prove an
__inversion rule__ to support such eliminative reasoning.

Typical inversion rule:

    `∀x y, P (c x y) → (∃…, ⋯ ∧ ⋯) ∨ ⋯ ∨ (∃…, ⋯ ∧ ⋯)`

It can be useful to combine introduction and elimination into a single theorem,
which can be used for rewriting both the hypotheses and conclusions of goals:

    `∀x y, P (c x y) ↔ (∃…, ⋯ ∧ ⋯) ∨ ⋯ ∨ (∃…, ⋯ ∧ ⋯)` -/

theorem Even_Iff (n : ℕ) :
  Even n ↔ n = 0 ∨ (∃m : ℕ, n = m + 2 ∧ Even m) :=
  by
    apply Iff.intro
    { intro hn
      cases hn with
      | zero         => simp
      | add_two k hk =>
        apply Or.inr
        apply Exists.intro k
        simp [hk] }
    { intro hor
      cases hor with
      | inl heq => simp [heq, Even.zero]
      | inr hex =>
        cases hex with
        | intro k hand =>
          cases hand with
          | intro heq hk =>
            simp [heq, Even.add_two _ hk] }

theorem Even_Iff_struct (n : ℕ) :
  Even n ↔ n = 0 ∨ (∃m : ℕ, n = m + 2 ∧ Even m) :=
  Iff.intro
    (assume hn : Even n
     match n, hn with
     | _, Even.zero         =>
       show 0 = 0 ∨ _ from
         by simp
     | _, Even.add_two k hk =>
       show _ ∨ (∃m, k + 2 = m + 2 ∧ Even m) from
         Or.inr (Exists.intro k (by simp [*])))
    (assume hor : n = 0 ∨ (∃m, n = m + 2 ∧ Even m)
     match hor with
     | Or.inl heq =>
       show Even n from
         by simp [heq, Even.zero]
     | Or.inr hex =>
       match hex with
       | Exists.intro m hand =>
         match hand with
         | And.intro heq hm =>
           show Even n from
             by simp [heq, Even.add_two _ hm])


/- ## Further Examples

### Sorted Lists -/

inductive Sorted : List ℕ → Prop where
  | nil : Sorted []
  | single (x : ℕ) : Sorted [x]
  | two_or_more (x y : ℕ) {zs : List ℕ} (hle : x ≤ y)
      (hsorted : Sorted (y :: zs)) :
    Sorted (x :: y :: zs)

theorem Sorted_nil :
  Sorted [] :=
  Sorted.nil

theorem Sorted_2 :
  Sorted [2] :=
  Sorted.single _

theorem Sorted_3_5 :
  Sorted [3, 5] :=
  by
    apply Sorted.two_or_more
    { simp }
    { exact Sorted.single _ }

theorem Sorted_3_5_raw :
  Sorted [3, 5] :=
  Sorted.two_or_more _ _ (by simp) (Sorted.single _)

theorem sorted_7_9_9_11 :
  Sorted [7, 9, 9, 11] :=
  Sorted.two_or_more _ _ (by simp)
    (Sorted.two_or_more _ _ (by simp)
       (Sorted.two_or_more _ _ (by simp)
          (Sorted.single _)))

theorem Not_Sorted_17_13 :
  ¬ Sorted [17, 13] :=
  by
    intro h
    cases h with
    | two_or_more _ _ hlet hsorted => simp at hlet


/- ### Palindromes -/

inductive Palindrome {α : Type} : List α → Prop where
  | nil : Palindrome []
  | single (x : α) : Palindrome [x]
  | sandwich (x : α) (xs : List α) (hxs : Palindrome xs) :
    Palindrome ([x] ++ xs ++ [x])

/-
-- fails
def palindromeRec {α : Type} : List α → Bool
  | []                 => true
  | [_]                => true
  | ([x] ++ xs ++ [x]) => palindromeRec xs
  | _                  => false
-/

theorem Palindrome_aa {α : Type} (a : α) :
  Palindrome [a, a] :=
  Palindrome.sandwich a _ Palindrome.nil

theorem Palindrome_aba {α : Type} (a b : α) :
  Palindrome [a, b, a] :=
  Palindrome.sandwich a _ (Palindrome.single b)

theorem Palindrome_reverse {α : Type} (xs : List α)
    (hxs : Palindrome xs) :
  Palindrome (reverse xs) :=
  by
    induction hxs with
    | nil                  => exact Palindrome.nil
    | single x             => exact Palindrome.single x
    | sandwich x xs hxs ih =>
      { simp [reverse, reverse_append]
        exact Palindrome.sandwich _ _ ih }


/- ### Full Binary Trees -/

#check BTree

inductive IsFull {α : Type} : BTree α → Prop where
  | empty : IsFull BTree.empty
  | node (a : α) (l r : BTree α)
      (hl : IsFull l) (hr : IsFull r)
      (hiff : l = BTree.empty ↔ r = BTree.empty) :
    IsFull (BTree.node a l r)

theorem IsFull_singleton {α : Type} (a : α) :
  IsFull (BTree.node a BTree.empty BTree.empty) :=
  by
    apply IsFull.node
    { exact IsFull.empty }
    { exact IsFull.empty }
    { rfl }

theorem IsFull_mirror {α : Type} (t : BTree α)
    (ht : IsFull t) :
  IsFull (mirror t) :=
  by
    induction ht with
    | empty                           => exact IsFull.empty
    | node a l r hl hr hiff ih_l ih_r =>
      { rw [mirror]
        apply IsFull.node
        { exact ih_r }
        { exact ih_l }
        { simp [mirror_Eq_empty_Iff, *] } }

theorem IsFull_mirror_struct_induct {α : Type} (t : BTree α) :
  IsFull t → IsFull (mirror t) :=
  by
    induction t with
    | empty                =>
      { intro ht
        exact ht }
    | node a l r ih_l ih_r =>
      { intro ht
        cases ht with
        | node _ _ _ hl hr hiff =>
          { rw [mirror]
            apply IsFull.node
            { exact ih_r hr }
            { apply ih_l hl }
            { simp [mirror_Eq_empty_Iff, *] } } }


/- ### First-Order Terms -/

inductive Term (α β : Type) : Type where
  | var : β → Term α β
  | fn  : α → List (Term α β) → Term α β

inductive WellFormed {α β : Type} (arity : α → ℕ) :
  Term α β → Prop where
  | var (x : β) : WellFormed arity (Term.var x)
  | fn (f : α) (ts : List (Term α β))
      (hargs : ∀t ∈ ts, WellFormed arity t)
      (hlen : length ts = arity f) :
    WellFormed arity (Term.fn f ts)

inductive VariableFree {α β : Type} : Term α β → Prop where
  | fn (f : α) (ts : List (Term α β))
      (hargs : ∀t ∈ ts, VariableFree t) :
    VariableFree (Term.fn f ts)

end LoVe
