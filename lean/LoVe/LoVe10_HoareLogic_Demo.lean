/- Copyright © 2018–2023 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe08_Metaprogramming_Demo
import LoVe.LoVe09_OperationalSemantics_Demo


/- # LoVe Demo 10: Hoare Logic

We review a second way to specify the semantics of a programming language: Hoare
logic. If operational semantics corresponds to an idealized interpreter,
__Hoare logic__ (also called __axiomatic semantics__) corresponds to a verifier.
Hoare logic is particularly convenient to reason about concrete programs. -/


set_option autoImplicit false
set_option tactic.hygienic false

open Lean
open Lean.Meta
open Lean.Elab.Tactic

namespace LoVe


/- ## Hoare Triples

The basic judgments of Hoare logic are often called __Hoare triples__. They have
the form

    `{P} S {Q}`

where `S` is a statement, and `P` and `Q` (called __precondition__ and
__postcondition__) are logical formulas over the state variables.

Intended meaning:

    If `P` holds before `S` is executed and the execution terminates normally,
    `Q` holds at termination.

This is a __partial correctness__ statement: The program is correct if it
terminates normally (i.e., no run-time error, no infinite loop or divergence).

All of these Hoare triples are valid (with respect to the intended meaning):

    `{True} b := 4 {b = 4}`
    `{a = 2} b := 2 * a {a = 2 ∧ b = 4}`
    `{b ≥ 5} b := b + 1 {b ≥ 6}`
    `{False} skip {b = 100}`
    `{True} while i ≠ 100 do i := i + 1 {i = 100}`


## Hoare Rules

The following is a complete set of rules for reasoning about WHILE programs:

    ———————————— Skip
    {P} skip {P}

    ——————————————————— Assign
    {Q[a/x]} x := a {Q}

    {P} S {R}   {R} S' {Q}
    —————————————————————— Seq
    {P} S; S' {Q}

    {P ∧ B} S {Q}   {P ∧ ¬B} S' {Q}
    ——————————————————————————————— If
    {P} if B then S else S' {Q}

    {I ∧ B} S {I}
    ————————————————————————— While
    {I} while B do S {I ∧ ¬B}

    P' → P   {P} S {Q}   Q → Q'
    ——————————————————————————— Conseq
    {P'} S {Q'}

`Q[a/x]` denotes `Q` with `x` replaced by `a`.

In the `While` rule, `I` is called an __invariant__.

Except for `Conseq`, the rules are syntax-driven: by looking at a program, we
see immediately which rule to apply.

Example derivations:

    —————————————————————— Assign   —————————————————————— Assign
    {a = 2} b := a {b = 2}          {b = 2} c := b {c = 2}
    —————————————————————————————————————————————————————— Seq
    {a = 2} b := a; c := b {c = 2}


                     —————————————————————— Assign
    x > 10 → x > 5   {x > 5} y := x {y > 5}   y > 5 → y > 0
    ——————————————————————————————————————————————————————— Conseq
    {x > 10} y := x {y > 0}

Various __derived rules__ can be proved to be correct in terms of the standard
rules. For example, we can derive bidirectional rules for `skip`, `:=`, and
`while`:

    P → Q
    ———————————— Skip'
    {P} skip {Q}

    P → Q[a/x]
    —————————————— Assign'
    {P} x := a {Q}

    {P ∧ B} S {P}   P ∧ ¬B → Q
    —————————————————————————— While'
    {P} while B do S {Q}


## A Semantic Approach to Hoare Logic

We can, and will, define Hoare triples **semantically** in Lean.

We will use predicates on states (`State → Prop`) to represent pre- and
postconditions, following the shallow embedding style. -/

def PartialHoare (P : State → Prop) (S : Stmt)
    (Q : State → Prop) : Prop :=
  ∀s t, P s → (S, s) ⟹ t → Q t

macro "{*" P:term " *} " "(" S:term ")" " {* " Q:term " *}" : term =>
  `(PartialHoare $P $S $Q)

namespace PartialHoare

theorem skip_intro {P} :
  {* P *} (Stmt.skip) {* P *} :=
  by
    intro s t hs hst
    cases hst
    assumption

theorem assign_intro (P) {x a} :
  {* fun s ↦ P (s[x ↦ a s]) *} (Stmt.assign x a) {* P *} :=
  by
    intro s t P' hst
    cases hst with
    | assign => assumption

theorem seq_intro {P Q R S T} (hS : {* P *} (S) {* Q *})
    (hT : {* Q *} (T) {* R *}) :
  {* P *} (S; T) {* R *} :=
  by
    intro s t hs hst
    cases hst with
    | seq _ _ _ u d hS' hT' =>
      apply hT
      { apply hS
        { exact hs }
        { assumption } }
      { assumption }

theorem if_intro {B P Q S T}
    (hS : {* fun s ↦ P s ∧ B s *} (S) {* Q *})
    (hT : {* fun s ↦ P s ∧ ¬ B s *} (T) {* Q *}) :
  {* P *} (Stmt.ifThenElse B S T) {* Q *} :=
  by
    intro s t hs hst
    cases hst with
    | if_true _ _ _ _ _ hB hS' =>
      apply hS
      exact And.intro hs hB
      assumption
    | if_false _ _ _ _ _ hB hT' =>
      apply hT
      exact And.intro hs hB
      assumption

theorem while_intro (P) {B S}
    (h : {* fun s ↦ P s ∧ B s *} (S) {* P *}) :
  {* P *} (Stmt.whileDo B S) {* fun s ↦ P s ∧ ¬ B s *} :=
  by
    intro s t hs hst
    generalize ws_eq : (Stmt.whileDo B S, s) = Ss
    rw [ws_eq] at hst
    induction hst generalizing s with
    | skip s'                       => cases ws_eq
    | assign x a s'                 => cases ws_eq
    | seq S T s' t' u hS hT ih      => cases ws_eq
    | if_true B S T s' t' hB hS ih  => cases ws_eq
    | if_false B S T s' t' hB hT ih => cases ws_eq
    | while_true B' S' s' t' u hB' hS hw ih_hS ih_hw =>
      cases ws_eq
      apply ih_hw
      { apply h
        { apply And.intro <;>
            assumption }
        { exact hS } }
      { rfl }
    | while_false B' S' s' hB'      =>
      cases ws_eq
      aesop

theorem consequence {P P' Q Q' S}
    (h : {* P *} (S) {* Q *}) (hp : ∀s, P' s → P s)
    (hq : ∀s, Q s → Q' s) :
  {* P' *} (S) {* Q' *} :=
  fix s t : State
  assume hs : P' s
  assume hst : (S, s) ⟹ t
  show Q' t from
    hq _ (h s t (hp s hs) hst)

theorem consequence_left (P') {P Q S}
    (h : {* P *} (S) {* Q *}) (hp : ∀s, P' s → P s) :
  {* P' *} (S) {* Q *} :=
  consequence h hp (by aesop)

theorem consequence_right (Q) {Q' P S}
    (h : {* P *} (S) {* Q *}) (hq : ∀s, Q s → Q' s) :
  {* P *} (S) {* Q' *} :=
  consequence h (by aesop) hq

theorem skip_intro' {P Q} (h : ∀s, P s → Q s) :
  {* P *} (Stmt.skip) {* Q *} :=
  consequence skip_intro h (by aesop)

theorem assign_intro' {P Q x a}
    (h : ∀s, P s → Q (s[x ↦ a s])):
  {* P *} (Stmt.assign x a) {* Q *} :=
  consequence (assign_intro Q) h (by aesop)

theorem seq_intro' {P Q R S T} (hT : {* Q *} (T) {* R *})
    (hS : {* P *} (S) {* Q *}) :
  {* P *} (S; T) {* R *} :=
  seq_intro hS hT

theorem while_intro' {B P Q S} (I)
    (hS : {* fun s ↦ I s ∧ B s *} (S) {* I *})
    (hP : ∀s, P s → I s)
    (hQ : ∀s, ¬ B s → I s → Q s) :
  {* P *} (Stmt.whileDo B S) {* Q *} :=
  consequence (while_intro I hS) hP (by aesop)

theorem assign_intro_forward (P) {x a} :
  {* P *}
  (Stmt.assign x a)
  {* fun s ↦ ∃n₀, P (s[x ↦ n₀]) ∧ s x = a (s[x ↦ n₀]) *} :=
  by
    apply assign_intro'
    intro s hP
    apply Exists.intro (s x)
    simp [*]

theorem assign_intro_backward (Q) {x a} :
  {* fun s ↦ ∃n', Q (s[x ↦ n']) ∧ n' = a s *}
  (Stmt.assign x a)
  {* Q *} :=
  by
    apply assign_intro'
    intro s hP
    cases hP with
    | intro n' hQ => aesop

end PartialHoare


/- ## First Program: Exchanging Two Variables -/

def SWAP : Stmt :=
  Stmt.assign "t" (fun s ↦ s "a");
  Stmt.assign "a" (fun s ↦ s "b");
  Stmt.assign "b" (fun s ↦ s "t")

theorem SWAP_correct (a₀ b₀ : ℕ) :
  {* fun s ↦ s "a" = a₀ ∧ s "b" = b₀ *}
  (SWAP)
  {* fun s ↦ s "a" = b₀ ∧ s "b" = a₀ *} :=
  by
    apply PartialHoare.seq_intro'
    apply PartialHoare.seq_intro'
    apply PartialHoare.assign_intro
    apply PartialHoare.assign_intro
    apply PartialHoare.assign_intro'
    aesop


/- ## Second Program: Adding Two Numbers -/

def ADD : Stmt :=
  Stmt.whileDo (fun s ↦ s "n" ≠ 0)
    (Stmt.assign "n" (fun s ↦ s "n" - 1);
     Stmt.assign "m" (fun s ↦ s "m" + 1))

theorem ADD_correct (n₀ m₀ : ℕ) :
  {* fun s ↦ s "n" = n₀ ∧ s "m" = m₀ *}
  (ADD)
  {* fun s ↦ s "n" = 0 ∧ s "m" = n₀ + m₀ *} :=
  PartialHoare.while_intro' (fun s ↦ s "n" + s "m" = n₀ + m₀)
    (by
      apply PartialHoare.seq_intro'
      { apply PartialHoare.assign_intro }
      { apply PartialHoare.assign_intro'
        aesop })
    (by aesop)
    (by aesop)

/- How did we come up with this invariant? The invariant must

1. be true before we enter the loop;

2. remain true after each iteration of the loop if it was true before the
   iteration;

3. be strong enough to imply the desired loop postcondition.

The invariant `True` meets 1 and 2 but usually not 3. Similarly, `False` meets
2 and 3 but usually not 1. Suitable invariants are often of the form

__work done__ + __work remaining__ = __desired result__

where `+` is some suitable operator. When we enter the loop, __work done__ will
often be `0`. And when we exit the loop, __work remaining__ should be `0`.

For the `ADD` loop:

* __work done__ is `m`;
* __work remaining__ is `n`;
* __desired result__ is `n₀ + m₀`.


## A Verification Condition Generator

__Verification condition generators__ (VCGs) are programs that apply Hoare rules
automatically, producing __verification conditions__ that must be proved by the
user. The user must usually also provide strong enough loop invariants, as an
annotation in their programs.

We can use Lean's metaprogramming framework to define a simple VCG.

Hundreds of program verification tools are based on these principles.

VCGs typically work backwards from the postcondition, using backward rules
(rules stated to have an arbitrary `Q` as their postcondition). This works well
because `Assign` is backward. -/

def Stmt.invWhileDo (I B : State → Prop) (S : Stmt) : Stmt :=
  Stmt.whileDo B S

namespace PartialHoare

theorem invWhile_intro {B I Q S}
    (hS : {* fun s ↦ I s ∧ B s *} (S) {* I *})
    (hQ : ∀s, ¬ B s → I s → Q s) :
  {* I *} (Stmt.invWhileDo I B S) {* Q *} :=
  while_intro' I hS (by aesop) hQ

theorem invWhile_intro' {B I P Q S}
    (hS : {* fun s ↦ I s ∧ B s *} (S) {* I *})
    (hP : ∀s, P s → I s) (hQ : ∀s, ¬ B s → I s → Q s) :
  {* P *} (Stmt.invWhileDo I B S) {* Q *} :=
  while_intro' I hS hP hQ

end PartialHoare

def matchPartialHoare : Expr → Option (Expr × Expr × Expr)
  | (Expr.app (Expr.app (Expr.app
       (Expr.const ``PartialHoare _) P) S) Q) =>
    Option.some (P, S, Q)
  | _ =>
    Option.none

partial def vcg : TacticM Unit :=
  do
    let goals ← getUnsolvedGoals
    if goals.length != 0 then
      let target ← getMainTarget
      match matchPartialHoare target with
      | Option.none           => return
      | Option.some (P, S, Q) =>
        if Expr.isAppOfArity S ``Stmt.skip 0 then
          if Expr.isMVar P then
            applyConstant ``PartialHoare.skip_intro
          else
            applyConstant ``PartialHoare.skip_intro'
        else if Expr.isAppOfArity S ``Stmt.assign 2 then
          if Expr.isMVar P then
            applyConstant ``PartialHoare.assign_intro
          else
            applyConstant ``PartialHoare.assign_intro'
        else if Expr.isAppOfArity S ``Stmt.seq 2 then
          andThenOnSubgoals
            (applyConstant ``PartialHoare.seq_intro') vcg
        else if Expr.isAppOfArity S ``Stmt.ifThenElse 3 then
          andThenOnSubgoals
            (applyConstant ``PartialHoare.if_intro) vcg
        else if Expr.isAppOfArity S ``Stmt.invWhileDo 3 then
          if Expr.isMVar P then
            andThenOnSubgoals
              (applyConstant ``PartialHoare.invWhile_intro) vcg
          else
            andThenOnSubgoals
              (applyConstant ``PartialHoare.invWhile_intro')
              vcg
        else
          failure

elab "vcg" : tactic =>
  vcg


/- ## Second Program Revisited: Adding Two Numbers -/

theorem ADD_correct_vcg (n₀ m₀ : ℕ) :
  {* fun s ↦ s "n" = n₀ ∧ s "m" = m₀ *}
  (ADD)
  {* fun s ↦ s "n" = 0 ∧ s "m" = n₀ + m₀ *} :=
show {* fun s ↦ s "n" = n₀ ∧ s "m" = m₀ *}
     (Stmt.invWhileDo (fun s ↦ s "n" + s "m" = n₀ + m₀)
        (fun s ↦ s "n" ≠ 0)
        (Stmt.assign "n" (fun s ↦ s "n" - 1);
         Stmt.assign "m" (fun s ↦ s "m" + 1)))
     {* fun s ↦ s "n" = 0 ∧ s "m" = n₀ + m₀ *} from
  by
    vcg <;>
      aesop


/- ## Hoare Triples for Total Correctness

__Total correctness__ asserts that the program not only is partially correct but
also that it always terminates normally. Hoare triples for total correctness
have the form

    [P] S [Q]

Intended meaning:

    If `P` holds before `S` is executed, the execution terminates normally and
    `Q` holds in the final state.

For deterministic programs, an equivalent formulation is as follows:

    If `P` holds before `S` is executed, there exists a state in which execution
    terminates normally and `Q` holds in that state.

Example:

    `[i ≤ 100] while i ≠ 100 do i := i + 1 [i = 100]`

In our WHILE language, this only affects while loops, which must now be
annotated by a __variant__ `V` (a natural number that decreases with each
iteration):

    [I ∧ B ∧ V = v₀] S [I ∧ V < v₀]
    ——————————————————————————————— While-Var
    [I] while B do S [I ∧ ¬B]

What is a suitable variant for the example above? -/

end LoVe
