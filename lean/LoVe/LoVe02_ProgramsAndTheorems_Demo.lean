/- Copyright © 2018–2023 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Demo 2: Programs and Theorems

We continue our study of the basics of Lean, focusing on programs and theorems,
without carrying out any proofs yet. We review how to define new types and
functions and how to state their intended properties as theorems. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Type Definitions

An __inductive type__ (also called __inductive datatype__,
__algebraic datatype__, or just __datatype__) is a type that consists all the
values that can be built using a finite number of applications of its
__constructors__, and only those.


### Natural Numbers -/

namespace MyNat

/- Definition of type `Nat` (= `ℕ`) of natural numbers, using unary notation: -/

inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat

#check Nat
#check Nat.zero
#check Nat.succ

/- `#print` outputs the definition of its argument. -/

#print Nat

end MyNat

/- Outside namespace `MyNat`, `Nat` refers to the type defined in the Lean core
library unless it is qualified by the `MyNat` namespace. -/

#print Nat
#print MyNat.Nat

/- ### Arithmetic Expressions -/

inductive AExp : Type where
  | num : ℤ → AExp
  | var : String → AExp
  | add : AExp → AExp → AExp
  | sub : AExp → AExp → AExp
  | mul : AExp → AExp → AExp
  | div : AExp → AExp → AExp


/- ### Lists -/

namespace MyList

inductive List (α : Type) where
  | nil  : List α
  | cons : α → List α → List α

#check List
#check List.nil
#check List.cons
#print List

end MyList

#print List
#print MyList.List


/- ## Function Definitions

The syntax for defining a function operating on an inductive type is very
compact: We define a single function and use __pattern matching__ to extract the
arguments to the constructors. -/

def fib : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | n + 2 => fib (n + 1) + fib n

/- When there are multiple arguments, separate the patterns by `,`: -/

def add : ℕ → ℕ → ℕ
  | m, Nat.zero   => m
  | m, Nat.succ n => Nat.succ (add m n)

/- `#eval` and `#reduce` evaluate and output the value of a term. -/

#eval add 2 7
#reduce add 2 7

def mul : ℕ → ℕ → ℕ
  | _, Nat.zero   => Nat.zero
  | m, Nat.succ n => add m (mul m n)

#eval mul 2 7

#print mul

def power : ℕ → ℕ → ℕ
  | _, Nat.zero   => 1
  | m, Nat.succ n => mul m (power m n)

#eval power 2 5

/- `add`, `mul`, and `power` are artificial examples. These operations are
already available in Lean as `+`, `*`, and `^`.

If it is not necessary to pattern-match on an argument, it can be moved to
the left of the `:` and made a named argument: -/

def powerParam (m : ℕ) : ℕ → ℕ
  | Nat.zero   => 1
  | Nat.succ n => mul m (powerParam m n)

#eval powerParam 2 5

def iter (α : Type) (z : α) (f : α → α) : ℕ → α
  | Nat.zero   => z
  | Nat.succ n => f (iter α z f n)

#check iter

def powerIter (m n : ℕ) : ℕ :=
  iter ℕ 1 (mul m) n

#eval powerIter 2 5

def append (α : Type) : List α → List α → List α
  | List.nil,       ys => ys
  | List.cons x xs, ys => List.cons x (append α xs ys)

/- Because `append` must work for any type of list, the type of its elements is
provided as an argument. As a result, the type must be provided in every call
(or use `_` if Lean can infer the type). -/

#check append
#eval append ℕ [3, 1] [4, 1, 5]
#eval append _ [3, 1] [4, 1, 5]

/- If the type argument is enclosed in `{ }` rather than `( )`, it is implicit
and need not be provided in every call (provided Lean can infer it). -/

def appendImplicit {α : Type} : List α → List α → List α
  | List.nil,       ys => ys
  | List.cons x xs, ys => List.cons x (appendImplicit xs ys)

#eval appendImplicit [3, 1] [4, 1, 5]

/- Prefixing a definition name with `@` gives the corresponding defintion in
which all implicit arguments have been made explicit. This is useful in
situations where Lean cannot work out how to instantiate the implicit
argument. -/

#check @appendImplicit
#eval @appendImplicit ℕ [3, 1] [4, 1, 5]
#eval @appendImplicit _ [3, 1] [4, 1, 5]

/- Aliases:

    `[]`          := `List.nil`
    `x :: xs`     := `List.cons x xs`
    `[x₁, …, xN]` := `x₁ :: … :: xN :: []` -/

def appendPretty {α : Type} : List α → List α → List α
  | [],      ys => ys
  | x :: xs, ys => x :: appendPretty xs ys

def reverse {α : Type} : List α → List α
  | []      => []
  | x :: xs => reverse xs ++ [x]

def eval (env : String → ℤ) : AExp → ℤ
  | AExp.num i     => i
  | AExp.var x     => env x
  | AExp.add e₁ e₂ => eval env e₁ + eval env e₂
  | AExp.sub e₁ e₂ => eval env e₁ - eval env e₂
  | AExp.mul e₁ e₂ => eval env e₁ * eval env e₂
  | AExp.div e₁ e₂ => eval env e₁ / eval env e₂

#eval eval (fun x ↦ 7) (AExp.div (AExp.var "y") (AExp.num 0))

/- Lean only accepts the function definitions for which it can prove
termination. In particular, it accepts __structurally recursive__ functions,
which peel off exactly one constructor at a time.


## Theorem Statements

Notice the similarity with `def` commands. `theorem` is like `def` except that
the result is a proposition rather than data or a function. -/

namespace SorryTheorems

theorem add_comm (m n : ℕ) :
  add m n = add n m :=
  sorry

theorem add_assoc (l m n : ℕ) :
  add (add l m) n = add l (add m n) :=
  sorry

theorem mul_comm (m n : ℕ) :
  mul m n = mul n m :=
  sorry

theorem mul_assoc (l m n : ℕ) :
  mul (mul l m) n = mul l (mul m n) :=
  sorry

theorem mul_add (l m n : ℕ) :
  mul l (add m n) = add (mul l m) (mul l n) :=
  sorry

theorem reverse_reverse {α : Type} (xs : List α) :
  reverse (reverse xs) = xs :=
  sorry

/- Axioms are like theorems but without proofs. Opaque declarations are like
definitions but without bodies. -/

opaque a : ℤ
opaque b : ℤ

axiom a_less_b :
  a < b

end SorryTheorems

end LoVe
