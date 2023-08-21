/- Copyright © 2018–2023 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Demo 9: Operational Semantics

In this and the next two lectures, we will see how to use Lean to specify the
syntax and semantics of programming languages and to reason about the
semantics. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## First Things First: Formalization Projects

Instead of two of the homework sheets, you can do a verification project, worth
20 points. If you choose to do so, please send your lecturer a message by email
by the end of the week. For a fully successful project, we expect about 200 (or
more) lines of Lean, including definitions and proofs.

Some ideas for projects follow.

Computer science:

* extended WHILE language with static arrays or other features;
* functional data structures (e.g., balanced trees);
* functional algorithms (e.g., bubble sort, merge sort, Tarjan's algorithm);
* compiler from expressions or imperative programs to, e.g., stack machine;
* type systems (e.g., Benjamin Pierce's __Types and Programming Languages__);
* security properties (e.g., Volpano–Smith-style noninterference analysis);
* theory of first-order terms, including matching, term rewriting;
* automata theory;
* normalization of context-free grammars or regular expressions;
* process algebras and bisimilarity;
* soundness and possibly completeness of proof systems (e.g., Genzen's sequent
  calculus, natural deduction, tableaux);
* separation logic;
* verified program using Hoare logic.

Mathematics:

* graphs;
* combinatorics;
* number theory.

Metaprogramming:

* custom tactic;
* custom diagnosis tool.

Past evaluation:

Q: How did you find the project?

A: Enjoyable.

A: Fun and hard.

A: Good, I think the format was excellent in a way that it gave people the
   chance to do challenging exercises and hand them in incomplete.

A: I really really liked it. I think it's a great way of learning—find
   something you like, dig in it a little, get stuck, ask for help. I wish I
   could do more of that!

A: It was great to have some time to try to work out some stuff you find
   interesting yourself.

A: lots of fun actually!!!

A: Very helpful. It gave the opportunity to spend some more time on a
   particular aspect of the course.


## Formal Semantics

A formal semantics helps specify and reason about the programming language
itself, and about individual programs.

It can form the basis of verified compilers, interpreters, verifiers, static
analyzers, type checkers, etc. Without formal proofs, these tools are
**almost always wrong**.

In this area, proof assistants are widely used. Every year, about 10-20% of POPL
papers are partially or totally formalized. Reasons for this success:

* Little machinery (background libraries, tactics) is needed to get started,
  beyond inductive types and predicates and recursive functions.

* The proofs tend to have lots of cases, which is a good match for computers.

* Proof assistants keep track of what needs to be changed when we extend the
  programming language with more features.

Case in point: WebAssembly. To quote Conrad Watt (with some abbreviations):

    We have produced a full Isabelle mechanisation of the core execution
    semantics and type system of the WebAssembly language. To complete this
    proof, **several deficiencies** in the official WebAssembly specification,
    uncovered by our proof and modelling work, needed to be corrected. In some
    cases, these meant that the type system was **originally unsound**.

    We have maintained a constructive dialogue with the working group,
    verifying new features as they are added. In particular, the mechanism by
    which a WebAssembly implementation interfaces with its host environment was
    not formally specified in the working group's original paper. Extending our
    mechanisation to model this feature revealed a deficiency in the WebAssembly
    specification that **sabotaged the soundness** of the type system.


## A Minimalistic Imperative Language

A state `s` is a function from variable names to values (`String → ℕ`).

__WHILE__ is a minimalistic imperative language with the following grammar:

    S  ::=  skip                 -- no-op
         |  x := a               -- assignment
         |  S; S                 -- sequential composition
         |  if B then S else S   -- conditional statement
         |  while B do S         -- while loop

where `S` stands for a statement (also called command or program), `x` for a
variable, `a` for an arithmetic expression, and `B` for a Boolean expression. -/

#print State

inductive Stmt : Type where
  | skip       : Stmt
  | assign     : String → (State → ℕ) → Stmt
  | seq        : Stmt → Stmt → Stmt
  | ifThenElse : (State → Prop) → Stmt → Stmt → Stmt
  | whileDo    : (State → Prop) → Stmt → Stmt

infixr:90 "; " => Stmt.seq

/- In our grammar, we deliberately leave the syntax of arithmetic and Boolean
expressions unspecified. In Lean, we have the choice:

* We could use a type such as `AExp` from lecture 2 and similarly for Boolean
  expressions.

* We could decide that an arithmetic expression is simply a function from
  states to natural numbers (`State → ℕ`) and a Boolean expression is a
  predicate (`State → Prop` or `State → Bool`).

This corresponds to the difference between deep and shallow embeddings:

* A __deep embedding__ of some syntax (expression, formula, program, etc.)
  consists of an abstract syntax tree specified in the proof assistant
  (e.g., `AExp`) with a semantics (e.g., `eval`).

* In contrast, a __shallow embedding__ simply reuses the corresponding
  mechanisms from the logic (e.g., terms, functions, predicate types).

A deep embedding allows us to reason about the syntax (and its semantics). A
shallow embedding is more lightweight, because we can use it directly, without
having to define a semantics.

We will use a deep embedding of programs (which we find interesting), and
shallow embeddings of assignments and Boolean expressions (which we find
boring).

The program

  while x > y do
    skip;
    x := x - 1

is modeled as -/

def sillyLoop : Stmt :=
  Stmt.whileDo (fun s ↦ s "x" > s "y")
    (Stmt.skip;
     Stmt.assign "x" (fun s ↦ s "x" - 1))


/- ## Big-Step Semantics

An __operational semantics__ corresponds to an idealized interpreter (specified
in a Prolog-like language). Two main variants:

* big-step semantics;

* small-step semantics.

In a __big-step semantics__ (also called __natural semantics__), judgments have
the form `(S, s) ⟹ t`:

    Starting in a state `s`, executing `S` terminates in the state `t`.

Example:

    `(x := x + y; y := 0, [x ↦ 3, y ↦ 5]) ⟹ [x ↦ 8, y ↦ 0]`

Derivation rules:

    ——————————————— Skip
    (skip, s) ⟹ s

    ——————————————————————————— Assign
    (x := a, s) ⟹ s[x ↦ s(a)]

    (S, s) ⟹ t   (T, t) ⟹ u
    ——————————————————————————— Seq
    (S; T, s) ⟹ u

    (S, s) ⟹ t
    ————————————————————————————— If-True   if s(B) is true
    (if B then S else T, s) ⟹ t

    (T, s) ⟹ t
    ————————————————————————————— If-False   if s(B) is false
    (if B then S else T, s) ⟹ t

    (S, s) ⟹ t   (while B do S, t) ⟹ u
    —————————————————————————————————————— While-True   if s(B) is true
    (while B do S, s) ⟹ u

    ————————————————————————— While-False   if s(B) is false
    (while B do S, s) ⟹ s

Above, `s(e)` denotes the value of expression `e` in state `s` and `s[x ↦ s(e)]`
denotes the state that is identical to `s` except that the variable `x` is bound
to the value `s(e)`.

In Lean, the judgment corresponds to an inductive predicate, and the derivation
rules correspond to the predicate's introduction rules. Using an inductive
predicate as opposed to a recursive function allows us to cope with
nontermination (e.g., a diverging `while`) and nondeterminism (e.g.,
multithreading). -/

inductive BigStep : Stmt × State → State → Prop where
  | skip (s) :
    BigStep (Stmt.skip, s) s
  | assign (x a s) :
    BigStep (Stmt.assign x a, s) (s[x ↦ a s])
  | seq (S T s t u) (hS : BigStep (S, s) t)
      (hT : BigStep (T, t) u) :
    BigStep (S; T, s) u
  | if_true (B S T s t) (hcond : B s)
      (hbody : BigStep (S, s) t) :
    BigStep (Stmt.ifThenElse B S T, s) t
  | if_false (B S T s t) (hcond : ¬ B s)
      (hbody : BigStep (T, s) t) :
    BigStep (Stmt.ifThenElse B S T, s) t
  | while_true (B S s t u) (hcond : B s)
      (hbody : BigStep (S, s) t)
      (hrest : BigStep (Stmt.whileDo B S, t) u) :
    BigStep (Stmt.whileDo B S, s) u
  | while_false (B S s) (hcond : ¬ B s) :
    BigStep (Stmt.whileDo B S, s) s

infix:110 " ⟹ " => BigStep

theorem sillyLoop_from_1_BigStep :
  (sillyLoop, (fun _ ↦ 0)["x" ↦ 1]) ⟹ (fun _ ↦ 0) :=
  by
    rw [sillyLoop]
    apply BigStep.while_true
    { simp }
    { apply BigStep.seq
      { apply BigStep.skip }
      { apply BigStep.assign } }
    { simp
      apply BigStep.while_false
      simp }


/- ## Properties of the Big-Step Semantics

Equipped with a big-step semantics, we can

* prove properties of the programming language, such as **equivalence proofs**
  between programs and **determinism**;

* reason about **concrete programs**, proving theorems relating final states `t`
  with initial states `s`. -/

theorem BigStep_deterministic {Ss l r} (hl : Ss ⟹ l)
    (hr : Ss ⟹ r) :
  l = r :=
  by
    induction hl generalizing r with
    | skip s =>
      cases hr with
      | skip => rfl
    | assign x a s =>
      cases hr with
      | assign => rfl
    | seq S T s l₀ l hS hT ihS ihT =>
      cases hr with
      | seq _ _ _ r₀ _ hS' hT' =>
        cases ihS hS' with
        | refl =>
          cases ihT hT' with
          | refl => rfl
    | if_true B S T s l hB hS ih =>
      cases hr with
      | if_true _ _ _ _ _ hB' hS'  => apply ih hS'
      | if_false _ _ _ _ _ hB' hS' => aesop
    | if_false B S T s l hB hT ih =>
      cases hr with
      | if_true _ _ _ _ _ hB' hS'  => aesop
      | if_false _ _ _ _ _ hB' hS' => apply ih hS'
    | while_true B S s l₀ l hB hS hw ihS ihw =>
      cases hr with
      | while_true _ _ _ r₀ hB' hB' hS' hw' =>
        cases ihS hS' with
        | refl =>
          cases ihw hw' with
          | refl => rfl
      | while_false _ _ _ hB' => aesop
    | while_false B S s hB =>
      cases hr with
      | while_true _ _ _ s' _ hB' hS hw => aesop
      | while_false _ _ _ hB'           => rfl


theorem BigStep_terminates {S s} :
  ∃t, (S, s) ⟹ t :=
  sorry   -- unprovable

/- We can define inversion rules about the big-step semantics: -/

@[simp] theorem BigStep_skip_Iff {s t} :
  (Stmt.skip, s) ⟹ t ↔ t = s :=
  by
    apply Iff.intro
    { intro h
      cases h with
      | skip => rfl }
    { intro h
      rw [h]
      apply BigStep.skip }

@[simp] theorem BigStep_assign_Iff {x a s t} :
  (Stmt.assign x a, s) ⟹ t ↔ t = s[x ↦ a s] :=
  by
    apply Iff.intro
    { intro h
      cases h with
      | assign => rfl }
    { intro h
      rw [h]
      apply BigStep.assign }

@[simp] theorem BigStep_seq_Iff {S T s u} :
  (S; T, s) ⟹ u ↔ (∃t, (S, s) ⟹ t ∧ (T, t) ⟹ u) :=
  by
    apply Iff.intro
    { intro h
      cases h with
      | seq =>
        apply Exists.intro
        apply And.intro <;>
          assumption }
    { intro h
      cases h with
      | intro s' h' =>
        cases h' with
        | intro hS hT =>
          apply BigStep.seq <;>
            assumption }

@[simp] theorem BigStep_if_Iff {B S T s t} :
  (Stmt.ifThenElse B S T, s) ⟹ t ↔
  (B s ∧ (S, s) ⟹ t) ∨ (¬ B s ∧ (T, s) ⟹ t) :=
  by
    apply Iff.intro
    { intro h
      cases h with
      | if_true _ _ _ _ _ hB hS =>
        apply Or.intro_left
        aesop
      | if_false _ _ _ _ _ hB hT =>
        apply Or.intro_right
        aesop }
    { intro h
      cases h with
      | inl h =>
        cases h with
        | intro hB hS =>
          apply BigStep.if_true <;>
            assumption
      | inr h =>
        cases h with
        | intro hB hT =>
          apply BigStep.if_false <;>
            assumption }

theorem BigStep_while_Iff {B S s u} :
  (Stmt.whileDo B S, s) ⟹ u ↔
  (∃t, B s ∧ (S, s) ⟹ t ∧ (Stmt.whileDo B S, t) ⟹ u)
  ∨ (¬ B s ∧ u = s) :=
  by
    apply Iff.intro
    { intro h
      cases h with
      | while_true _ _ _ t _ hB hS hw =>
        apply Or.intro_left
        apply Exists.intro t
        aesop
      | while_false _ _ _ hB =>
        apply Or.intro_right
        aesop }
    { intro h
      cases h with
      | inl hex =>
        cases hex with
        | intro t h =>
          cases h with
          | intro hB h =>
            cases h with
            | intro hS hwhile =>
              apply BigStep.while_true <;>
                assumption
      | inr h =>
        cases h with
        | intro hB hus =>
          rw [hus]
          apply BigStep.while_false
          assumption}

@[simp] theorem BigStep_while_true_Iff {B S s u}
    (hcond : B s) :
  (Stmt.whileDo B S, s) ⟹ u ↔
  (∃t, (S, s) ⟹ t ∧ (Stmt.whileDo B S, t) ⟹ u) :=
  by
    rw [BigStep_while_Iff]
    simp [hcond]

@[simp] theorem BigStep_while_false_Iff {B S s t}
    (hcond : ¬ B s) :
  (Stmt.whileDo B S, s) ⟹ t ↔ t = s :=
  by
    rw [BigStep_while_Iff]
    simp [hcond]


/- ## Small-Step Semantics

A big-step semantics

* does not let us reason about intermediate states;

* does not let us express nontermination or interleaving (for multithreading).

__Small-step semantics__ (also called __structural operational semantics__)
solve the above issues.

A judgment has the form `(S, s) ⇒ (T, t)`:

    Starting in a state `s`, executing one step of `S` leaves us in the
    state `t`, with the program `T` remaining to be executed.

An execution is a finite or infinite chain `(S₀, s₀) ⇒ (S₁, s₁) ⇒ …`.

A pair `(S, s)` is called a __configuration__. It is __final__ if no transition
of the form `(S, s) ⇒ _` is possible.

Example:

      `(x := x + y; y := 0, [x ↦ 3, y ↦ 5])`
    `⇒ (skip; y := 0,       [x ↦ 8, y ↦ 5])`
    `⇒ (y := 0,             [x ↦ 8, y ↦ 5])`
    `⇒ (skip,               [x ↦ 8, y ↦ 0])`

Derivation rules:

    ————————————————————————————————— Assign
    (x := a, s) ⇒ (skip, s[x ↦ s(a)])

    (S, s) ⇒ (S', s')
    ———-——————————————————— Seq-Step
    (S; T, s) ⇒ (S'; T, s')

    ————————————————————— Seq-Skip
    (skip; S, s) ⇒ (S, s)

    ———————————————————————————————— If-True   if s(B) is true
    (if B then S else T, s) ⇒ (S, s)

    ———————————————————————————————— If-False   if s(B) is false
    (if B then S else T, s) ⇒ (T, s)

    ——————————————————————————————————————————————————————————————— While
    (while B do S, s) ⇒ (if B then (S; while B do S) else skip, s)

There is no rule for `skip` (why?). -/

inductive SmallStep : Stmt × State → Stmt × State → Prop where
  | assign (x a s) :
    SmallStep (Stmt.assign x a, s) (Stmt.skip, s[x ↦ a s])
  | seq_step (S S' T s s') (hS : SmallStep (S, s) (S', s')) :
    SmallStep (S; T, s) (S'; T, s')
  | seq_skip (T s) :
    SmallStep (Stmt.skip; T, s) (T, s)
  | if_true (B S T s) (hcond : B s) :
    SmallStep (Stmt.ifThenElse B S T, s) (S, s)
  | if_false (B S T s) (hcond : ¬ B s) :
    SmallStep (Stmt.ifThenElse B S T, s) (T, s)
  | whileDo (B S s) :
    SmallStep (Stmt.whileDo B S, s)
      (Stmt.ifThenElse B (S; Stmt.whileDo B S) Stmt.skip, s)

infixr:100 " ⇒ " => SmallStep
infixr:100 " ⇒* " => RTC SmallStep

theorem sillyLoop_from_1_SmallStep :
  (sillyLoop, (fun _ ↦ 0)["x" ↦ 1]) ⇒*
  (Stmt.skip, (fun _ ↦ 0)) :=
  by
    rw [sillyLoop]
    apply RTC.head
    { apply SmallStep.whileDo }
    { apply RTC.head
      { apply SmallStep.if_true
        simp }
      { apply RTC.head
        { apply SmallStep.seq_step
          apply SmallStep.seq_skip }
        { apply RTC.head
          { apply SmallStep.seq_step
            apply SmallStep.assign }
          { apply RTC.head
            { apply SmallStep.seq_skip }
            { apply RTC.head
              { apply SmallStep.whileDo }
              { apply RTC.head
                { apply SmallStep.if_false
                  simp }
                { simp
                  apply RTC.refl } } } } } } }

/- Equipped with a small-step semantics, we can **define** a big-step
semantics:

    `(S, s) ⟹ t` if and only if `(S, s) ⇒* (skip, t)`

where `r*` denotes the reflexive transitive closure of a relation `r`.

Alternatively, if we have already defined a big-step semantics, we can **prove**
the above equivalence theorem to validate our definitions.

The main disadvantage of small-step semantics is that we now have two relations,
`⇒` and `⇒*`, and reasoning tends to be more complicated.


## Properties of the Small-Step Semantics

We can prove that a configuration `(S, s)` is final if and only if `S = skip`.
This ensures that we have not forgotten a derivation rule. -/

theorem SmallStep_final (S s) :
  (¬ ∃T t, (S, s) ⇒ (T, t)) ↔ S = Stmt.skip :=
  by
    induction S with
    | skip =>
      simp
      intros T t hstep
      cases hstep
    | assign x a =>
      simp
      apply Exists.intro Stmt.skip
      apply Exists.intro (s[x ↦ a s])
      apply SmallStep.assign
    | seq S T ihS ihT =>
      simp
      cases Classical.em (S = Stmt.skip) with
      | inl h =>
        rw [h]
        apply Exists.intro T
        apply Exists.intro s
        apply SmallStep.seq_skip
      | inr h =>
        simp [h] at ihS
        cases ihS with
        | intro S' hS₀ =>
          cases hS₀ with
          | intro s' hS =>
            apply Exists.intro (S'; T)
            apply Exists.intro s'
            apply SmallStep.seq_step
            assumption
    | ifThenElse B S T ihS ihT =>
      simp
      cases Classical.em (B s) with
      | inl h =>
        apply Exists.intro S
        apply Exists.intro s
        apply SmallStep.if_true
        assumption
      | inr h =>
        apply Exists.intro T
        apply Exists.intro s
        apply SmallStep.if_false
        assumption
    | whileDo B S ih =>
      simp
      apply Exists.intro
        (Stmt.ifThenElse B (S; Stmt.whileDo B S)
           Stmt.skip)
      apply Exists.intro s
      apply SmallStep.whileDo

theorem SmallStep_deterministic {Ss Ll Rr}
    (hl : Ss ⇒ Ll) (hr : Ss ⇒ Rr) :
  Ll = Rr :=
  by
    induction hl generalizing Rr with
    | assign x a s =>
      cases hr with
      | assign _ _ _ => rfl
    | seq_step S S₁ T s s₁ hS₁ ih =>
      cases hr with
      | seq_step S S₂ _ _ s₂ hS₂ =>
        have hSs₁₂ :=
          ih hS₂
        aesop
      | seq_skip => cases hS₁
    | seq_skip T s =>
      cases hr with
      | seq_step _ S _ _ s' hskip => cases hskip
      | seq_skip                  => rfl
    | if_true B S T s hB =>
      cases hr with
      | if_true  => rfl
      | if_false => aesop
    | if_false B S T s hB =>
      cases hr with
      | if_true  => aesop
      | if_false => rfl
    | whileDo B S s =>
      cases hr with
      | whileDo => rfl

/- We can define inversion rules also about the small-step semantics. Here are
three examples: -/

theorem SmallStep_skip {S s t} :
  ¬ ((Stmt.skip, s) ⇒ (S, t)) :=
  by
    intro h
    cases h

@[simp] theorem SmallStep_seq_Iff {S T s Ut} :
  (S; T, s) ⇒ Ut ↔
  (∃S' t, (S, s) ⇒ (S', t) ∧ Ut = (S'; T, t))
  ∨ (S = Stmt.skip ∧ Ut = (T, s)) :=
  by
    apply Iff.intro
    { intro hST
      cases hST with
      | seq_step _ S' _ _ s' hS =>
        apply Or.intro_left
        apply Exists.intro S'
        apply Exists.intro s'
        aesop
      | seq_skip =>
        apply Or.intro_right
        aesop }
    {
      intro hor
      cases hor with
      | inl hex =>
        cases hex with
        | intro S' hex' =>
          cases hex' with
          | intro s' hand =>
            cases hand with
            | intro hS hUt =>
              rw [hUt]
              apply SmallStep.seq_step
              assumption
      | inr hand =>
        cases hand with
        | intro hS hUt =>
          rw [hS, hUt]
          apply SmallStep.seq_skip }

@[simp] theorem SmallStep_if_Iff {B S T s Us} :
  (Stmt.ifThenElse B S T, s) ⇒ Us ↔
  (B s ∧ Us = (S, s)) ∨ (¬ B s ∧ Us = (T, s)) :=
  by
    apply Iff.intro
    { intro h
      cases h with
      | if_true _ _ _ _ hB  => aesop
      | if_false _ _ _ _ hB => aesop }
    { intro hor
      cases hor with
      | inl hand =>
        cases hand with
        | intro hB hUs =>
          rw [hUs]
          apply SmallStep.if_true
          assumption
      | inr hand =>
        cases hand with
        | intro hB hUs =>
          rw [hUs]
          apply SmallStep.if_false
          assumption }


/- ### Equivalence of the Big-Step and the Small-Step Semantics (**optional**)

A more important result is the connection between the big-step and the
small-step semantics:

    `(S, s) ⟹ t ↔ (S, s) ⇒* (Stmt.skip, t)`

Its proof, given below, is beyond the scope of this course. -/

theorem RTC_SmallStep_seq {S T s u}
    (h : (S, s) ⇒* (Stmt.skip, u)) :
  (S; T, s) ⇒* (Stmt.skip; T, u) :=
  by
    apply RTC.lift (fun Ss ↦ (Prod.fst Ss; T, Prod.snd Ss)) _ h
    intro Ss Ss' hrtc
    cases Ss with
    | mk S s =>
      cases Ss' with
      | mk S' s' =>
        apply SmallStep.seq_step
        assumption

theorem RTC_SmallStep_of_BigStep {Ss t} (hS : Ss ⟹ t) :
  Ss ⇒* (Stmt.skip, t) :=
  by
    induction hS with
    | skip => exact RTC.refl
    | assign =>
      apply RTC.single
      apply SmallStep.assign
    | seq S T s t u hS hT ihS ihT =>
      apply RTC.trans
      { exact RTC_SmallStep_seq ihS }
      { apply RTC.head
        apply SmallStep.seq_skip
        assumption }
    | if_true B S T s t hB hst ih =>
      apply RTC.head
      { apply SmallStep.if_true
        assumption }
      { assumption }
    | if_false B S T s t hB hst ih =>
      apply RTC.head
      { apply SmallStep.if_false
        assumption }
      { assumption }
    | while_true B S s t u hB hS hw ihS ihw =>
      apply RTC.head
      { apply SmallStep.whileDo }
      { apply RTC.head
        { apply SmallStep.if_true
          assumption }
        { apply RTC.trans
          { exact RTC_SmallStep_seq ihS }
          { apply RTC.head
            apply SmallStep.seq_skip
            assumption } } }
    | while_false B S s hB =>
      apply RTC.tail
      apply RTC.single
      apply SmallStep.whileDo
      apply SmallStep.if_false
      assumption

theorem BigStep_of_SmallStep_of_BigStep {Ss₀ Ss₁ s₂}
    (h₁ : Ss₀ ⇒ Ss₁) :
  Ss₁ ⟹ s₂ → Ss₀ ⟹ s₂ :=
  by
    induction h₁ generalizing s₂ with
    | assign x a s               => simp
    | seq_step S S' T s s' hS ih => aesop
    | seq_skip T s               => simp
    | if_true B S T s hB         => aesop
    | if_false B S T s hB        => aesop
    | whileDo B S s              => aesop

theorem BigStep_of_RTC_SmallStep {Ss t} :
  Ss ⇒* (Stmt.skip, t) → Ss ⟹ t :=
  by
    intro hS
    induction hS using RTC.head_induction_on with
    | refl =>
      apply BigStep.skip
    | head Ss Ss' hST hsmallT ih =>
      cases Ss' with
      | mk S' s' =>
        apply BigStep_of_SmallStep_of_BigStep hST
        apply ih

theorem BigStep_Iff_RTC_SmallStep {Ss t} :
  Ss ⟹ t ↔ Ss ⇒* (Stmt.skip, t) :=
  Iff.intro RTC_SmallStep_of_BigStep BigStep_of_RTC_SmallStep

end LoVe
