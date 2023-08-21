/- Copyright © 2018–2023 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Preface

## Proof Assistants

Proof assistants (also called interactive theorem provers)

* check and help develop formal proofs;
* can be used to prove big theorems, not only logic puzzles;
* can be tedious to use;
* are highly addictive (think video games).

A selection of proof assistants, classified by logical foundations:

* set theory: Isabelle/ZF, Metamath, Mizar;
* simple type theory: HOL4, HOL Light, Isabelle/HOL;
* **dependent type theory**: Agda, Coq, **Lean**, Matita, PVS.


## Success Stories

Mathematics:

* the four-color theorem (in Coq);
* the Kepler conjecture (in HOL Light and Isabelle/HOL);
* the definition of perfectoid spaces (in Lean).

Computer science:

* hardware;
* operating systems;
* programming language theory;
* compilers;
* security.


## Lean

Lean is a proof assistant developed primarily by Leonardo de Moura (Microsoft
Research) since 2012.

Its mathematical library, `mathlib`, is developed under the leadership of
Jeremy Avigad (Carnegie Mellon University).

We use the community version of Lean 4. We use its basic libraries, `mathlib4`,
and `LoVelib`, among others. Lean is a research project.

Strengths:

* highly expressive logic based on a dependent type theory called the
  **calculus of inductive constructions**;
* extended with classical axioms and quotient types;
* metaprogramming framework;
* modern user interface;
* documentation;
* open source;
* endless source of puns (Lean Forward, Lean Together, Boolean, …).


## This Course

### Web Site

    https://lean-forward.github.io/logical-verification/2023/index.html


### Installation Instructions

    https://github.com/blanchette/logical_verification_2023/blob/main/README.md#logical-verification-2023---installation-instructions


### Repository (Demos, Exercises, Homework)

    https://github.com/blanchette/logical_verification_2023

The file you are currently looking at is a demo. There are

* 14 demo files;
* 14 exercise sheets;
* 12 homework sheets (10 points each);
* 1 project (20 points).

You may submit at most 10 homework, or at most 8 homework and the project.
Homework, including the project, must be done individually. The homework builds
on the exercises, which build on the demos.


### The Hitchhiker's Guide to Logical Verification

    https://github.com/blanchette/logical_verification_2023/blob/main/hitchhikers_guide.pdf
    https://github.com/blanchette/logical_verification_2023/blob/main/hitchhikers_guide_tablet.pdf

The lecture notes consist of a preface and 14 chapters. They cover the same
material as the corresponding lectures but with more details. Sometimes there
will not be enough time to cover everything in class, so reading the lecture
notes will be necessary.


### Final Exam

The course aims at teaching concepts, not syntax. Therefore, the final exam is
on paper. It is also closed book.


## Our Goal

We want you to

* master fundamental theory and techniques in interactive theorem proving;
* familiarize yourselves with some application areas;
* develop some practical skills you can apply on a larger project (as a hobby,
  for an MSc or PhD, or in industry);
* feel ready to move to another proof assistant and apply what you have learned;
* understand the domain well enough to start reading scientific papers.

This course is neither a pure logical foundations course nor a Lean tutorial.
Lean is our vehicle, not an end in itself.


# LoVe Demo 1: Types and Terms

We start our journey by studying the basics of Lean, starting with terms
(expressions) and their types. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## A View of Lean

In a first approximation:

    Lean = functional programming + logic

In today's lecture, we cover the syntax of types and terms, which are similar to
those of the simply typed λ-calculus or typed functional programming languages
(ML, OCaml, Haskell).


## Types

Types `σ`, `τ`, `υ`:

* type variables `α`;
* basic types `T`;
* complex types `T σ1 … σN`.

Some type constructors `T` are written infix, e.g., `→` (function type).

The function arrow is right-associative:
`σ₁ → σ₂ → σ₃ → τ` = `σ₁ → (σ₂ → (σ₃ → τ))`.

Polymorphic types are also possible. In Lean, the type variables must be bound
using `∀`, e.g., `∀α, α → α`.


## Terms

Terms `t`, `u`:

* constants `c`;
* variables `x`;
* applications `t u`;
* anonymous functions `fun x ↦ t` (also called λ-expressions).

__Currying__: functions can be

* fully applied (e.g., `f x y z` if `f` can take at most 3 arguments);
* partially applied (e.g., `f x y`, `f x`);
* left unapplied (e.g., `f`).

Application is left-associative: `f x y z` = `((f x) y) z`.

`#check` reports the type of its argument. -/

#check ℕ
#check ℤ

#check Empty
#check Unit
#check Bool

#check ℕ → ℤ
#check ℤ → ℕ
#check Bool → ℕ → ℤ
#check (Bool → ℕ) → ℤ
#check ℕ → (Bool → ℕ) → ℤ

#check fun x : ℕ ↦ x
#check fun f : ℕ → ℕ ↦ fun g : ℕ → ℕ ↦ fun h : ℕ → ℕ ↦
  fun x : ℕ ↦ h (g (f x))
#check fun (f g h : ℕ → ℕ) (x : ℕ) ↦ h (g (f x))

/- `opaque` defines an arbitrary constant of the specified type. -/

opaque a : ℤ
opaque b : ℤ
opaque f : ℤ → ℤ
opaque g : ℤ → ℤ → ℤ

#check fun x : ℤ ↦ g (f (g a x)) (g x b)
#check fun x ↦ g (f (g a x)) (g x b)

#check fun x ↦ x


/- ## Type Checking and Type Inference

Type checking and type inference are decidable problems (although this property is
quickly lost if features such as overloading or subtyping are added).

Type judgment: `C ⊢ t : σ`, meaning `t` has type `σ` in local context `C`.

Typing rules:

    —————————— Cst   if c is globally declared with type σ
    C ⊢ c : σ

    —————————— Var   if x : σ is the rightmost occurrence of x in C
    C ⊢ x : σ

    C ⊢ t : σ → τ    C ⊢ u : σ
    ——————————————————————————— App
    C ⊢ t u : τ

    C, x : σ ⊢ t : τ
    ——————————————————————————— Fun
    C ⊢ (fun x : σ ↦ t) : σ → τ

If the same variable `x` occurs multiple times in the context C, the rightmost
occurrence shadows the other ones.


## Type Inhabitation

Given a type `σ`, the __type inhabitation__ problem consists of finding a term
of that type. Type inhabitation is undecidable.

Recursive procedure:

1. If `σ` is of the form `τ → υ`, a candidate inhabitant is an anonymous
   function of the form `fun x ↦ _`.

2. Alternatively, you can use any constant or variable `x : τ₁ → ⋯ → τN → σ` to
   build the term `x _ … _`. -/

opaque α : Type
opaque β : Type
opaque γ : Type

def someFunOfType : (α → β → γ) → ((β → α) → β) → α → γ :=
  fun f g a ↦ f a (g (fun b ↦ a))

end LoVe
