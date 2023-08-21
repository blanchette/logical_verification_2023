/- Copyright © 2018–2023 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Demo 7: Effectful Programming

Monads are an important functional programming abstraction. They generalize
computation with side effects, offering effectful programming in a pure
functional programming language. Haskell has shown that they can be used very
successfully to write imperative programs. For us, they are interesting in their
own right and for two more reasons:

* They provide a nice example of axiomatic reasoning.

* They are needed for programming Lean itself (metaprogramming, lecture 8). -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Introductory Example

Consider the following programming task:

    Implement a function `sum257 ns` that sums up the second, fifth, and
    seventh items of a list `ns` of natural numbers. Use `Option ℕ` for the
    result so that if the list has fewer than seven elements, you can return
    `Option.none`.

A straightforward solution follows: -/

def nth {α : Type} : List α → Nat → Option α
  | [],      _     => Option.none
  | x :: _,  0     => Option.some x
  | _ :: xs, n + 1 => nth xs n

def sum257 (ns : List ℕ) : Option ℕ :=
  match nth ns 1 with
  | Option.none    => Option.none
  | Option.some n₂ =>
    match nth ns 4 with
    | Option.none    => Option.none
    | Option.some n₅ =>
      match nth ns 6 with
      | Option.none    => Option.none
      | Option.some n₇ => Option.some (n₂ + n₅ + n₇)

/- The code is ugly, because of all the pattern matching on options.

We can put all the ugliness in one function, which we call `connect`: -/

def connect {α : Type} {β : Type} :
  Option α → (α → Option β) → Option β
  | Option.none,   _ => Option.none
  | Option.some a, f => f a

def sum257Connect (ns : List ℕ) : Option ℕ :=
  connect (nth ns 1)
    (fun n₂ ↦ connect (nth ns 4)
       (fun n₅ ↦ connect (nth ns 6)
          (fun n₇ ↦ Option.some (n₂ + n₅ + n₇))))

/- Instead of defining `connect` ourselves, we can use Lean's predefined
general `bind` operation. We can also use `pure` instead of `Option.some`: -/

#check bind

def sum257Bind (ns : List ℕ) : Option ℕ :=
  bind (nth ns 1)
    (fun n₂ ↦ bind (nth ns 4)
       (fun n₅ ↦ bind (nth ns 6)
          (fun n₇ ↦ pure (n₂ + n₅ + n₇))))

/- By using `bind` and `pure`, `sum257Bind` makes no reference to the
constructors `Option.none` and `Option.some`.

Syntactic sugar:

    `ma >>= f` := `bind ma f` -/

def sum257Op (ns : List ℕ) : Option ℕ :=
  nth ns 1 >>=
    fun n₂ ↦ nth ns 4 >>=
      fun n₅ ↦ nth ns 6 >>=
        fun n₇ ↦ pure (n₂ + n₅ + n₇)

/- Syntactic sugar:

    do
      let a ← ma
      t
    :=
    ma >>= (fun a ↦ t)

    do
      ma
      t
    :=
    ma >>= (fun _ ↦ t) -/

def sum257Dos (ns : List ℕ) : Option ℕ :=
  do
    let n₂ ← nth ns 1
    do
      let n₅ ← nth ns 4
      do
        let n₇ ← nth ns 6
        pure (n₂ + n₅ + n₇)

/- The `do`s can be combined: -/

def sum257Do (ns : List ℕ) : Option ℕ :=
  do
    let n₂ ← nth ns 1
    let n₅ ← nth ns 4
    let n₇ ← nth ns 6
    pure (n₂ + n₅ + n₇)

/- Although the notation has an imperative flavor, the function is a pure
functional program.


## Two Operations and Three Laws

The `Option` type constructor is an example of a monad.

In general, a __monad__ is a type constructor `m` that depends on some type
parameter `α` (i.e., `m α`) equipped with two distinguished operations:

    `pure {α : Type} : α → m α`
    `bind {α β : Type} : m α → (α → m β) → m β`

For `Option`:

    `pure` := `Option.some`
    `bind` := `connect`

Intuitively, we can think of a monad as a "box":

* `pure` puts the data into the box.

* `bind` allows us to access the data in the box and modify it (possibly even
  changing its type, since the result is an `m β` monad, not a `m α` monad).

There is no general way to extract the data from the monad, i.e., to obtain an
`α` from an `m α`.

To summarize, `pure a` provides no side effect and simply provides a box
containing the the value `a`, whereas `bind ma f` (also written `ma >>= f`)
executes `ma`, then executes `f` with the boxed result `a` of `ma`.

The option monad is only one instance among many.

Type                 | Effect
-------------------- | -------------------------------------------------------
`id`                 | no effects
`Option`             | simple exceptions
`fun α ↦ σ → α × σ`  | threading through a state of type `σ`
`fun α ↦ Set α`      | nondeterministic computation returning `α` values
`fun α ↦ t → α`      | reading elements of type `t` (e.g., a configuration)
`fun α ↦ ℕ × α`      | adjoining running time (e.g., to model time complexity)
`fun α ↦ String × α` | adjoining text output (e.g., for logging)
`IO`                 | interaction with the operating system
`TacticM`            | interaction with the proof assistant

All of the above are unary type constructors `m : Type → Type`.

Some effects can be combined (e.g., `Option (t → α)`).

Some effects are not executable (e.g., `Set α`). They are nonetheless useful for
modeling programs abstractly in the logic.

Specific monads may provide a way to extract the boxed value stored in the monad
without `bind`'s requirement of putting it back in a monad.

Monads have several benefits, including:

* They provide the convenient and highly readable `do` notation.

* They support generic operations, such as
  `mmap {α β : Type} : (α → m β) → List α → m (List β)`, which work uniformly
  across all monads.

The `bind` and `pure` operations are normally required to obey three laws. Pure
data as the first program can be simplified away:

    do
      let a' ← pure a,
      f a'
  =
    f a

Pure data as the second program can be simplified away:

    do
      let a ← ma
      pure a
  =
    ma

Nested programs `ma`, `f`, `g` can be flattened using this associativity rule:

    do
      let b ←
        do
          let a ← ma
          f a
      g b
  =
    do
      let a ← ma
      let b ← f a
      g b


## A Type Class of Monads

Monads are a mathematical structure, so we use class to add them as a type
class. We can think of a type class as a structure that is parameterized by a
type, or here, by a type constructor `m : Type → Type`. -/

class LawfulMonad (m : Type → Type)
  extends Pure m, Bind m where
  pure_bind {α β : Type} (a : α) (f : α → m β) :
    (pure a >>= f) = f a
  bind_pure {α : Type} (ma : m α) :
    (ma >>= pure) = ma
  bind_assoc {α β γ : Type} (f : α → m β) (g : β → m γ)
      (ma : m α) :
    ((ma >>= f) >>= g) = (ma >>= (fun a ↦ f a >>= g))

/- Step by step:

* We are creating a structure parameterized by a unary type constructor `m`.

* The structure inherits the fields, and any syntactic sugar, from structures
  called `Bind` and `Pure`, which provide the `bind` and `pure` operations on
  `m` and some syntactic sugar.

* The definition adds three fields to those already provided by `Bind` and
  `Pure`, to store the proofs of the laws.

To instantiate this definition with a concrete monad, we must supply the type
constructor `m` (e.g., `Option`), `bind` and `pure` operators, and proofs of the
laws.


## No Effects

Our first monad is the trivial monad `m := id` (i.e., `m := (fun α ↦ α)`). -/

def id.pure {α : Type} : α → id α
  | a => a

def id.bind {α β : Type} : id α → (α → id β) → id β
  | a, f => f a

instance id.LawfulMonad : LawfulMonad id :=
  { pure       := id.pure
    bind       := id.bind
    pure_bind  :=
      by
        intro α β a f
        rfl
    bind_pure  :=
      by
        intro α ma
        rfl
    bind_assoc :=
      by
        intro α β γ f g ma
        rfl }


/- ## Basic Exceptions

As we saw above, the option type provides a basic exception mechanism. -/

def Option.pure {α : Type} : α → Option α :=
  Option.some

def Option.bind {α β : Type} :
  Option α → (α → Option β) → Option β
  | Option.none,   _ => Option.none
  | Option.some a, f => f a

instance Option.LawfulMonad : LawfulMonad Option :=
  { pure       := Option.pure
    bind       := Option.bind
    pure_bind  :=
      by
        intro α β a f
        rfl
    bind_pure  :=
      by
        intro α ma
        cases ma with
        | none   => rfl
        | some _ => rfl
    bind_assoc :=
      by
        intro α β γ f g ma
        cases ma with
        | none   => rfl
        | some _ => rfl }

def Option.throw {α : Type} : Option α :=
  Option.none

def Option.catch {α : Type} : Option α → Option α → Option α
  | Option.none,   ma' => ma'
  | Option.some a, _   => Option.some a


/- ## Mutable State

The state monad provides an abstraction corresponding to a mutable state. Some
compilers recognize the state monad to produce efficient imperative code. -/

def Action (σ α : Type) : Type :=
  σ → α × σ

def Action.read {σ : Type} : Action σ σ
  | s => (s, s)

def Action.write {σ : Type} (s : σ) : Action σ Unit
  | _ => ((), s)

def Action.pure {σ α : Type} (a : α) : Action σ α
  | s => (a, s)

def Action.bind {σ : Type} {α β : Type} (ma : Action σ α)
    (f : α → Action σ β) :
  Action σ β
  | s =>
    match ma s with
    | (a, s') => f a s'

/- `Action.pure` is like a `return` statement; it does not change the state.

`Action.bind` is like the sequential composition of two statements with
respect to a state. -/

instance Action.LawfulMonad {σ : Type} :
  LawfulMonad (Action σ) :=
  { pure       := Action.pure
    bind       := Action.bind
    pure_bind  :=
      by
        intro α β a f
        simp [Pure.pure, Bind.bind, Action.pure, Action.bind]
    bind_pure  :=
      by
        intro α ma
        simp [Pure.pure, Bind.bind, Action.pure, Action.bind]
    bind_assoc :=
      by
        intro α β γ f g ma
        simp [Pure.pure, Bind.bind, Action.pure, Action.bind] }

def increasingly : List ℕ → Action ℕ (List ℕ)
  | []        => pure []
  | (n :: ns) =>
    do
      let prev ← Action.read
      if n < prev then
        increasingly ns
      else
        do
          Action.write n
          let ns' ← increasingly ns
          pure (n :: ns')

#eval increasingly [1, 2, 3, 2] 0
#eval increasingly [1, 2, 3, 2, 4, 5, 2] 0


/- ## Nondeterminism

The set monad stores an arbitrary, possibly infinite number of `α` values. -/

#check Set

def Set.pure {α : Type} : α → Set α
  | a => {a}

def Set.bind {α β : Type} : Set α → (α → Set β) → Set β
  | A, f => {b | ∃a, a ∈ A ∧ b ∈ f a}

/- `Set.bind` is like a `map` function over sets in which each element of the
source set maps to a set of elements (all of which are combined). -/

instance Set.LawfulMonad : LawfulMonad Set :=
  { pure       := Set.pure
    bind       := Set.bind
    pure_bind  :=
      by
        intro α β a f
        simp [Pure.pure, Bind.bind, Set.pure, Set.bind]
    bind_pure  :=
      by
        intro α ma
        simp [Pure.pure, Bind.bind, Set.pure, Set.bind]
    bind_assoc :=
      by
        intro α β γ f g ma
        simp [Pure.pure, Bind.bind, Set.pure, Set.bind]
        apply Set.ext
        aesop }

/- `aesop` is a general-purpose proof search tactic. Among others, it performs
elimination of the logical symbols `∧`, `∨`, `↔`, and `∃` in hypotheses and
introduction of `∧`, `↔`, and `∃` in the target, and it regularly invokes the
simplifier. It can succeed at proving a goal, fail, or succeed partially,
leaving some unfinished subgoals to the user.


## A Generic Algorithm: Iteration over a List

We consider a generic effectful program `mmap` that iterates over a list and
applies a function `f` to each element. -/

def nthsFine {α : Type} (xss : List (List α)) (n : ℕ) :
  List (Option α) :=
  List.map (fun xs ↦ nth xs n) xss

#eval nthsFine [[11, 12, 13, 14], [21, 22, 23]] 2
#eval nthsFine [[11, 12, 13, 14], [21, 22, 23]] 3

def mmap {m : Type → Type} [LawfulMonad m] {α β : Type}
    (f : α → m β) :
  List α → m (List β)
  | []      => pure []
  | a :: as =>
    do
      let b ← f a
      let bs ← mmap f as
      pure (b :: bs)

def nthsCoarse {α : Type} (xss : List (List α)) (n : ℕ) :
  Option (List α) :=
  mmap (fun xs ↦ nth xs n) xss

#eval nthsCoarse [[11, 12, 13, 14], [21, 22, 23]] 2
#eval nthsCoarse [[11, 12, 13, 14], [21, 22, 23]] 3

theorem mmap_append {m : Type → Type} [LawfulMonad m]
    {α β : Type} (f : α → m β) :
  ∀as as' : List α, mmap f (as ++ as') =
    do
      let bs ← mmap f as
      let bs' ← mmap f as'
      pure (bs ++ bs')
  | [],      _   =>
    by simp [mmap, LawfulMonad.bind_pure, LawfulMonad.pure_bind]
  | a :: as, as' =>
    by simp [mmap, mmap_append _ as as', LawfulMonad.pure_bind,
      LawfulMonad.bind_assoc]

end LoVe
