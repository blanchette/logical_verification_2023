/- Copyright © 2018–2023 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe07_EffectfulProgramming_Demo


/- # LoVe Exercise 7: Effectful Programming

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: A State Monad with Failure

We introduce a richer notion of lawful monad that provides an `orelse`
operator satisfying some laws, given below. `emp` denotes failure. `orelse x y`
tries `x` first, falling back on `y` on failure. -/

class LawfulMonadWithOrelse (m : Type → Type)
  extends LawfulMonad m where
  emp {α : Type} : m α
  orelse {α : Type} : m α → m α → m α
  emp_orelse {α : Type} (a : m α) :
    orelse emp a = a
  orelse_emp {α : Type} (a : m α) :
    orelse a emp = a
  orelse_assoc {α : Type} (a b c : m α) :
    orelse (orelse a b) c = orelse a (orelse b c)
  emp_bind {α β : Type} (f : α → m β) :
    (emp >>= f) = emp
  bind_emp {α β : Type} (f : m α) :
    (f >>= (fun a ↦ (emp : m β))) = emp

/- 1.1. We set up the `Option` type constructor to be a
`LawfulMonad_with_orelse`. Complete the proofs.

Hint: Use `simp [Bind.bind]` to unfold the definition of the bind operator and
`simp [Option.orelse]` to unfold the definition of the `orelse` operator. -/

def Option.orelse {α : Type} : Option α → Option α → Option α
  | Option.none,   ma' => ma'
  | Option.some a, _   => Option.some a

@[instance] def Option.LawfulMonadWithOrelse :
  LawfulMonadWithOrelse Option :=
  { Option.LawfulMonad with
    emp          := Option.none
    orelse       := Option.orelse
    emp_orelse   :=
      sorry
    orelse_emp   :=
      by
        intro α ma
        simp [Option.orelse]
        cases ma
        { rfl }
        { rfl }
    orelse_assoc :=
      sorry
    emp_bind     :=
      by
        intro α β f
        simp [Bind.bind]
        rfl
    bind_emp     :=
      sorry
  }

@[simp] theorem Option.some_bind {α β : Type} (a : α) (g : α → Option β) :
  (Option.some a >>= g) = g a :=
  sorry

/- 1.2. Now we are ready to define `FAction σ`: a monad with an internal state
of type `σ` that can fail (unlike `Action σ`).

We start with defining `FAction σ α`, where `σ` is the type of the internal
state, and `α` is the type of the value stored in the monad. We use `Option` to
model failure. This means we can also use the monad operations of `Option` when
defining the monad operations on `FAction`.

Hints:

* Remember that `FAction σ α` is an alias for a function type, so you can use
  pattern matching and `fun s ↦ …` to define values of type `FAction σ α`.

* `FAction` is very similar to `Action` from the lecture's demo. You can look
  there for inspiration. -/

def FAction (σ : Type) (α : Type) : Type :=
  sorry

/- 1.3. Define the `get` and `set` function for `FAction`, where `get` returns
the state passed along the state monad and `set s` changes the state to `s`. -/

def get {σ : Type} : FAction σ σ :=
  sorry

def set {σ : Type} (s : σ) : FAction σ Unit :=
  sorry

/- We set up the `>>=` syntax on `FAction`: -/

def FAction.bind {σ α β : Type} (f : FAction σ α) (g : α → FAction σ β) :
  FAction σ β
  | s => f s >>= (fun (a, s) ↦ g a s)

instance FAction.Bind {σ : Type} : Bind (FAction σ) :=
  { bind := FAction.bind }

theorem FAction.bind_apply {σ α β : Type} (f : FAction σ α)
    (g : α → FAction σ β) (s : σ) :
  (f >>= g) s = (f s >>= (fun (a, s) ↦ g a s)) :=
  by rfl

/- 1.4. Define the operator `pure` for `FAction`, in such a way that it will
satisfy the three laws. -/

def FAction.pure {σ α : Type} (a : α) : FAction σ α :=
  sorry

/- We set up the syntax for `pure` on `FAction`: -/

instance FAction.Pure {σ : Type} : Pure (FAction σ) :=
  { pure := FAction.pure }

theorem FAction.pure_apply {σ α : Type} (a : α) (s : σ) :
  (pure a : FAction σ α) s = Option.some (a, s) :=
  by rfl

/- 1.5. Register `FAction` as a monad.

Hints:

* The `funext` theorem is useful when you need to prove equality between two
  functions.

* The theorem `FAction.pure_apply` or `FAction.bind_apply` might prove useful. -/

@[instance] def FAction.LawfulMonad {σ : Type} : LawfulMonad (FAction σ) :=
  { FAction.Bind, FAction.Pure with
    pure_bind :=
      by
      sorry
    bind_pure :=
      by
        intro α ma
        apply funext
        intro s
        simp [FAction.bind_apply, FAction.pure_apply]
        apply LawfulMonad.bind_pure
    bind_assoc :=
      sorry
  }


/- ## Question 2 (**optional**): Kleisli Operator

The Kleisli operator `>=>` (not to be confused with `>>=`) is useful for
pipelining effectful functions. Note that `fun a ↦ f a >>= g` is to be parsed as
`fun a ↦ (f a >>= g)`, not as `(fun a ↦ f a) >>= g`. -/

def kleisli {m : Type → Type} [LawfulMonad m] {α β γ : Type} (f : α → m β)
    (g : β → m γ) : α → m γ :=
  fun a ↦ f a >>= g

infixr:90 (priority := high) " >=> " => kleisli

/- 2.1 (**optional**). Prove that `pure` is a left and right unit for the
Kleisli operator. -/

theorem pure_kleisli {m : Type → Type} [LawfulMonad m] {α β : Type}
    (f : α → m β) :
  (pure >=> f) = f :=
  sorry

theorem kleisli_pure {m : Type → Type} [LawfulMonad m] {α β : Type}
    (f : α → m β) :
  (f >=> pure) = f :=
  sorry

/- 2.2 (**optional**). Prove that the Kleisli operator is associative. -/

theorem kleisli_assoc {m : Type → Type} [LawfulMonad m] {α β γ δ : Type}
    (f : α → m β) (g : β → m γ) (h : γ → m δ) :
  ((f >=> g) >=> h) = (f >=> (g >=> h)) :=
  sorry

end LoVe
