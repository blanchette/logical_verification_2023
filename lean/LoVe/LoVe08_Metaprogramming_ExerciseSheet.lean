/- Copyright © 2018–2023 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe08_Metaprogramming_Demo


/- # LoVe Exercise 8: Metaprogramming

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

namespace LoVe


/- ## Question 1: `destruct_and` on Steroids

Recall from the lecture that `destruct_and` fails on easy goals such as -/

theorem abc_ac (a b c : Prop) (h : a ∧ b ∧ c) :
  a ∧ c :=
  sorry

/- We will now address this by developing a new tactic called `destro_and`,
which applies both **des**truction and in**tro**duction rules for conjunction.
It will also go automatically through the hypotheses instead of taking an
argument. We will develop it in three steps.

1.1. Develop a tactic `intro_and` that replaces all goals of the form
`a ∧ b` with two new goals `a` and `b` systematically, until all top-level
conjunctions are gone. Define your tactic as a macro. -/

#check repeat'

-- enter your definition here

theorem abcd_bd (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) :
  b ∧ d :=
  by
    intro_and
    /- The proof state should be as follows:

        case left
        a b c d: Prop
        h : a ∧ (b ∧ c) ∧ d
        ⊢ b

        case right
        a b c d : Prop
        h : a ∧ (b ∧ c) ∧ d
        ⊢ d -/
    repeat' sorry

theorem abcd_bacb (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) :
  b ∧ (a ∧ (c ∧ b)) :=
  by
    intro_and
    /- The proof state should be as follows:

        case left
        a b c d : Prop
        h : a ∧ (b ∧ c) ∧ d
        ⊢ b

        case right.left
        a b c d : Prop
        h : a ∧ (b ∧ c) ∧ d
        ⊢ a

        case right.right.left
        a b c d : Prop
        h : a ∧ (b ∧ c) ∧ d
        ⊢ c

        case right.right.right
        a b c d : Prop
        h : a ∧ (b ∧ c) ∧ d
        ⊢ b -/
    repeat' sorry

/- 1.2. Develop a tactic `cases_and` that replaces hypotheses of the form
`h : a ∧ b` by two new hypotheses `h_left : a` and `h_right : b` systematically,
until all top-level conjunctions are gone.

Here is some pseudocode that you can follow:

1. Wrap the entire `do` block in a call to `withMainContext` to ensure you work
   with the right context.

2. Retrieve the list of hypotheses from the context. This is provided by
   `getLCtx`.

3. Find the first hypothesis (= term) with a type (= proposition) of the form
   `_ ∧ _`. To iterate, you can use the `for … in … do` syntax. To obtain the
   type of a term, you can use `inferType`. To check if a type `ty` has the form
   `_ ∧ _`, you can use `Expr.isAppOfArity ty ``And 2` (with two backticks before
   `And`).

4. Perform a case split on the first found hypothesis. This can be achieved
   using the metaprogram `cases` provided in `LoVelib`. To extract the free
   variable associated with a hypothesis, use `LocalDecl.fvarId`.

5. Repeat (via a recursive call).

6. Return. -/

partial def casesAnd : TacticM Unit :=
  sorry

elab "cases_and" : tactic =>
  casesAnd

theorem abcd_bd_again (a b c d : Prop) :
  a ∧ (b ∧ c) ∧ d → b ∧ d :=
  by
    intro h
    cases_and
    /- The proof state should be as follows:

        case intro.intro.intro
        a b c d : Prop
        left : a
        right : d
        left_1 : b
        right_1 : c
        ⊢ b ∧ d -/
    sorry

/- 1.3. Implement a `destro_and` tactic that first invokes `cases_and`, then
`intro_and`, before it tries to prove all the subgoals that can be discharged
directly by `assumption`. -/

macro "destro_and" : tactic =>
  sorry

theorem abcd_bd_over_again (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) :
  b ∧ d :=
  by destro_and

theorem abcd_bacb_again (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) :
  b ∧ (a ∧ (c ∧ b)) :=
  by destro_and

theorem abd_bacb_again (a b c d : Prop) (h : a ∧ b ∧ d) :
  b ∧ (a ∧ (c ∧ b)) :=
  by
    destro_and
    /- The proof state should be roughly as follows:

        case intro.intro.right.right.left
        a b c d : Prop
        left : a
        left_1 : b
        right : d
        ⊢ c -/
    sorry   -- unprovable

/- 1.4. Provide some more examples for `destro_and` to convince yourself that
it works as expected also on more complicated examples. -/

-- enter your examples here


/- ## Question 2 (**optional**): A Theorem Finder

We will implement a function that allows us to find theorems by constants
appearing in their statements. So given a list of constant names, the function
will list all theorems in which all these constants appear.

2.1 (**optional**). Write a function that checks whether an expression contains
a specific constant.

Hints:

* You can pattern-match on `e` and proceed recursively.

* The "or" connective on `Bool` is called `||`, and equality is called `==`. -/

def constInExpr (name : Name) (e : Expr) : Bool :=
  sorry

/- 2.2 (**optional**). Write a function that checks whether an expression
contains **all** constants in a list.

Hint: You can either proceed recursively or use `List.and` and `List.map`. -/

def constsInExpr (names : List Name) (e : Expr) : Bool :=
  sorry

/- 2.3 (**optional**). Develop a tactic that uses `constsInExpr` to print the
name of all theorems that contain all constants `names` in their statement.

This code should be similar to that of `proveDirect` in the demo file. With
`ConstantInfo.type`, you can extract the proposition associated with a theorem. -/

def findConsts (names : List Name) : TacticM Unit :=
  sorry

elab "find_consts" "(" names:ident+ ")" : tactic =>
  findConsts (Array.toList (Array.map getId names))

/- Test the solution. -/

theorem List.a_property_of_reverse {α : Type} (xs : List α) (a : α) :
  List.reverse (List.concat xs a) = a :: List.reverse xs :=
  by
    find_consts (List.reverse)
    find_consts (List.reverse List.concat)
    apply List.reverse_concat

end LoVe
