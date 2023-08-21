/- Copyright © 2018–2023 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe09_OperationalSemantics_Demo


/- # LoVe Demo 11: Denotational Semantics

We review a third way to specify the semantics of a programming language:
denotational semantics. Denotational semantics attempts to directly specify the
meaning of programs.

If operational semantics is an idealized interpreter and Hoare logic is an
idealized verifier, then denotational semantics is an idealized compiler. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Compositionality

A __denotational semantics__ defines the meaning of each program as a
mathematical object:

    `⟦ ⟧ : syntax → semantics`

A key property of denotational semantics is __compositionality__: The meaning of
a compound statement should be defined in terms of the meaning of its
components. This disqualifies

    `⟦S⟧ = {st | (S, Prod.fst st) ⟹ Prod.snd st}`

(i.e.

    `⟦S⟧ = {(s, t) | (S, s) ⟹ t}`)

because operational semantics is not compositional.

In short, we want

    `⟦S; T⟧               = … ⟦S⟧ … ⟦T⟧ …`
    `⟦if b then S else T⟧ = … ⟦S⟧ … ⟦T⟧ …`
    `⟦while b do S⟧       = … ⟦S⟧ …`

An evaluation function on arithmetic expressions

    `eval : AExp → ((String → ℤ) → ℤ)`

is a denotational semantics. We want the same for imperative programs.


## A Relational Denotational Semantics

We can represent the semantics of an imperative program as a function from
initial state to final state or more generally as a relation between initial
state and final state: `Set (State × State)`.

For `skip`, `:=`, `;`, and `if then else`, the denotational semantics is
easy: -/

namespace SorryDefs

def denote : Stmt → Set (State × State)
  | Stmt.skip             => Id
  | Stmt.assign x a       =>
    {st | Prod.snd st = (Prod.fst st)[x ↦ a (Prod.fst st)]}
  | Stmt.seq S T          => denote S ◯ denote T
  | Stmt.ifThenElse B S T =>
    (denote S ⇃ B) ∪ (denote T ⇃ (fun s ↦ ¬ B s))
  | Stmt.whileDo b S      => sorry

end SorryDefs

/- We write `⟦S⟧` for `denote S`. For `while`, we would like to write

    `((denote S ◯ denote (Stmt.whileDo b S)) ⇃ b)`
    `∪ (Id ⇃ (fun s ↦ ¬ b s))`

but this is ill-founded due to the recursive call on `Stmt.whileDo b S`.

What we are looking for is an `X` such that

    `X = ((denote S ◯ X) ⇃ b) ∪ (Id ⇃ (fun s ↦ ¬ b s))`

In other words, we are looking for a fixpoint.

Most of this lecture is concerned with building a least fixpoint operator
`lfp` that will allow us to define the `while` case as well:

    `lfp (fun X ↦ ((denote S ◯ X) ⇃ b) ∪ (Id ⇃ (fun s ↦ ¬ b s)))`


## Fixpoints

A __fixpoint__ (or fixed point) of `f` is a solution for `X` in the equation

    `X = f X`

In general, fixpoints may not exist at all (e.g., `f := Nat.succ`), or there may
be several fixpoints (e.g., `f := id`). But under some conditions on `f`, a
unique __least fixpoint__ and a unique __greatest fixpoint__ are guaranteed to
exist.

Consider this __fixpoint equation__:

    `X = (fun (P : ℕ → Prop) (n : ℕ) ↦ n = 0 ∨ ∃m : ℕ, n = m + 2 ∧ P m) X`
      `= (fun n : ℕ ↦ n = 0 ∨ ∃m : ℕ, n = m + 2 ∧ X m)`

where `X : ℕ → Prop` and
`f := (fun (P : ℕ → Prop) (n : ℕ) ↦ n = 0 ∨ ∃m : ℕ, n = m + 2 ∧ P m)`.

The above example admits only one fixpoint. The fixpoint equation uniquely
specifies `X` as the set of even numbers.

In general, the least and greatest fixpoint may be different:

    `X = X`

Here, the least fixpoint is `fun _ ↦ False` and the greatest fixpoint is
`fun _ ↦ True`. Conventionally, `False < True`, and thus
`(fun _ ↦ False) < (fun _ ↦ True)`. Similarly, `∅ < @Set.univ ℕ`.

For the semantics of programming languages:

* `X` will have type `Set (State × State)` (which is isomorphic to
  `State → State → Prop`), representing relations between states;

* `f` will correspond to either taking one extra iteration of the loop (if the
  condition `B` is true) or the identity (if `B` is false).

The least fixpoint corresponds to finite executions of a program, which is all
we care about.

**Key observation**:

    Inductive predicates correspond to least fixpoints, but they are built into
    Lean's logic (the calculus of inductive constructions).


## Monotone Functions

Let `α` and `β` be types with partial order `≤`. A function `f : α → β` is
__monotone__ if

    `a₁ ≤ a₂ → f a₁ ≤ f a₂`   for all `a₁`, `a₂`

Many operations on sets (e.g., `∪`), relations (e.g., `◯`), and functions
(e.g., `fun x ↦ x`, `fun _ ↦ k`, `∘`) are monotone or preserve monotonicity.

All monotone functions `f : Set α → Set α` admit least and greatest fixpoints.

**Example of a nonmonotone function**:

    `f A = (if A = ∅ then Set.univ else ∅)`

Assuming `α` is inhabited, we have `∅ ⊆ Set.univ`, but
`f ∅ = Set.univ ⊈ ∅ = f Set.univ`. -/

def Monotone {α β : Type} [PartialOrder α] [PartialOrder β]
  (f : α → β) : Prop :=
  ∀a₁ a₂, a₁ ≤ a₂ → f a₁ ≤ f a₂

theorem Monotone_id {α : Type} [PartialOrder α] :
  Monotone (fun a : α ↦ a) :=
  by
    intro a₁ a₂ ha
    exact ha

theorem Monotone_const {α β : Type} [PartialOrder α]
    [PartialOrder β] (b : β) :
  Monotone (fun _ : α ↦ b) :=
  by
    intro a₁ a₂ ha
    exact le_refl b

theorem Monotone_union {α β : Type} [PartialOrder α]
    (f g : α → Set β) (hf : Monotone f) (hg : Monotone g) :
  Monotone (fun a ↦ f a ∪ g a) :=
  by
    intro a₁ a₂ ha b hb
    cases hb with
    | inl h => exact Or.inl (hf a₁ a₂ ha h)
    | inr h => exact Or.inr (hg a₁ a₂ ha h)

/- We will prove the following two theorems in the exercise. -/

namespace SorryTheorems

theorem Monotone_comp {α β : Type} [PartialOrder α]
    (f g : α → Set (β × β)) (hf : Monotone f)
    (hg : Monotone g) :
  Monotone (fun a ↦ f a ◯ g a) :=
  sorry

theorem Monotone_restrict {α β : Type} [PartialOrder α]
    (f : α → Set (β × β)) (P : β → Prop) (hf : Monotone f) :
  Monotone (fun a ↦ f a ⇃ P) :=
  sorry

end SorryTheorems


/- ## Complete Lattices

To define the least fixpoint on sets, we need `⊆` and `⋂`. Complete lattices
capture this concept abstractly. A __complete lattice__ is an ordered type `α`
for which each set of type `Set α` has an infimum.

More precisely, A complete lattice consists of

* a partial order `≤ : α → α → Prop` (i.e., a reflexive, antisymmetric, and
  transitive, and binary predicate);

* an operator `Inf : Set α → α`, called __infimum__.

Moreover, `Inf A` must satisfy these two properties:

* `Inf A` is a lower bound of `A`: `Inf A ≤ b` for all `b ∈ A`;

* `Inf A` is a greatest lower bound: `b ≤ Inf A` for all `b` such that
  `∀a, a ∈ A → b ≤ a`.

**Warning:** `Inf A` is not necessarily an element of `A`.

Examples:

* `Set α` is an instance w.r.t. `⊆` and `⋂` for all `α`;
* `Prop` is an instance w.r.t. `→` and `∀` (`Inf A := ∀a ∈ A, a`);
* `ENat := ℕ ∪ {∞}`;
* `EReal := ℝ ∪ {- ∞, ∞}`;
* `β → α` if `α` is a complete lattice;
* `α × β` if `α`, `β` are complete lattices.

Finite example (with apologies for the ASCII art):

                Z            Inf {}           = ?
              /   \          Inf {Z}          = ?
             A     B         Inf {A, B}       = ?
              \   /          Inf {Z, A}       = ?
                Y            Inf {Z, A, B, Y} = ?

Nonexamples:

* `ℕ`, `ℤ`, `ℚ`, `ℝ`: no infimum for `∅`, `Inf ℕ`, etc.
* `ERat := ℚ ∪ {- ∞, ∞}`: `Inf {q | 2 < q * q} = sqrt 2` is not in `ERat`. -/

class CompleteLattice (α : Type)
  extends PartialOrder α : Type where
  Inf    : Set α → α
  Inf_le : ∀A b, b ∈ A → Inf A ≤ b
  le_Inf : ∀A b, (∀a, a ∈ A → b ≤ a) → b ≤ Inf A

/- For sets: -/

instance Set.CompleteLattice {α : Type} :
  CompleteLattice (Set α) :=
  { @Set.PartialOrder α with
    Inf         := fun X ↦ {a | ∀A, A ∈ X → a ∈ A}
    Inf_le      := by aesop
    le_Inf      := by aesop }


/- ## Least Fixpoint -/

def lfp {α : Type} [CompleteLattice α] (f : α → α) : α :=
  CompleteLattice.Inf {a | f a ≤ a}

theorem lfp_le {α : Type} [CompleteLattice α] (f : α → α)
    (a : α) (h : f a ≤ a) :
  lfp f ≤ a :=
  CompleteLattice.Inf_le _ _ h

theorem le_lfp {α : Type} [CompleteLattice α] (f : α → α)
    (a : α) (h : ∀a', f a' ≤ a' → a ≤ a') :
  a ≤ lfp f :=
  CompleteLattice.le_Inf _ _ h

/- **Knaster-Tarski theorem:** For any monotone function `f`:

* `lfp f` is a fixpoint: `lfp f = f (lfp f)` (theorem `lfp_eq`);
* `lfp f` is smaller than any other fixpoint: `X = f X → lfp f ≤ X`. -/

theorem lfp_eq {α : Type} [CompleteLattice α] (f : α → α)
    (hf : Monotone f) :
  lfp f = f (lfp f) :=
  by
    have h : f (lfp f) ≤ lfp f :=
      by
        apply le_lfp
        intro a' ha'
        apply le_trans
        { apply hf
          apply lfp_le
          assumption }
        { assumption }
    apply le_antisymm
    { apply lfp_le
      apply hf
      assumption }
    { assumption }


/- ## A Relational Denotational Semantics, Continued -/

def denote : Stmt → Set (State × State)
  | Stmt.skip             => Id
  | Stmt.assign x a       =>
    {st | Prod.snd st = (Prod.fst st)[x ↦ a (Prod.fst st)]}
  | Stmt.seq S T          => denote S ◯ denote T
  | Stmt.ifThenElse B S T =>
    (denote S ⇃ B) ∪ (denote T ⇃ (fun s ↦ ¬ B s))
  | Stmt.whileDo B S      =>
    lfp (fun X ↦ ((denote S ◯ X) ⇃ B)
      ∪ (Id ⇃ (fun s ↦ ¬ B s)))

notation (priority := high) "⟦" S "⟧" => denote S

theorem Monotone_while_lfp_arg (S B) :
  Monotone (fun X ↦ ⟦S⟧ ◯ X ⇃ B ∪ Id ⇃ (fun s ↦ ¬ B s)) :=
  by
    apply Monotone_union
    { apply SorryTheorems.Monotone_restrict
      apply SorryTheorems.Monotone_comp
      { exact Monotone_const _ }
      { exact Monotone_id } }
    { apply SorryTheorems.Monotone_restrict
      exact Monotone_const _ }


/- ## Application to Program Equivalence

Based on the denotational semantics, we introduce the notion of program
equivalence: `S₁ ~ S₂`. (Compare with exercise 8.) -/

def DenoteEquiv (S₁ S₂ : Stmt) : Prop :=
  ⟦S₁⟧ = ⟦S₂⟧

infix:50 (priority := high) " ~ " => DenoteEquiv

/- It is obvious from the definition that `~` is an equivalence relation.

Program equivalence can be used to replace subprograms by other subprograms with
the same semantics. This is achieved by the following congruence rules: -/

theorem DenoteEquiv.seq_congr {S₁ S₂ T₁ T₂ : Stmt}
    (hS : S₁ ~ S₂) (hT : T₁ ~ T₂) :
  S₁; T₁ ~ S₂; T₂ :=
  by
    simp [DenoteEquiv, denote] at *
    simp [*]

theorem DenoteEquiv.if_congr {B} {S₁ S₂ T₁ T₂ : Stmt}
    (hS : S₁ ~ S₂) (hT : T₁ ~ T₂) :
  Stmt.ifThenElse B S₁ T₁ ~ Stmt.ifThenElse B S₂ T₂ :=
  by
    simp [DenoteEquiv, denote] at *
    simp [*]

theorem DenoteEquiv.while_congr {B} {S₁ S₂ : Stmt}
    (hS : S₁ ~ S₂) :
  Stmt.whileDo B S₁ ~ Stmt.whileDo B S₂ :=
  by
    simp [DenoteEquiv, denote] at *
    simp [*]

/- Compare the simplicity of these proofs with the corresponding proofs for a
big-step semantics (exercise 8).

Let us prove some program equivalences. -/

theorem DenoteEquiv.skip_assign_id {x} :
  Stmt.assign x (fun s ↦ s x) ~ Stmt.skip :=
  by simp [DenoteEquiv, denote, Id]

theorem DenoteEquiv.seq_skip_left {S} :
  Stmt.skip; S ~ S :=
  by simp [DenoteEquiv, denote, Id, comp]

theorem DenoteEquiv.seq_skip_right {S} :
  S; Stmt.skip ~ S :=
  by simp [DenoteEquiv, denote, Id, comp]

theorem DenoteEquiv.if_seq_while {B S} :
  Stmt.ifThenElse B (S; Stmt.whileDo B S) Stmt.skip
  ~ Stmt.whileDo B S :=
  by
    simp [DenoteEquiv, denote]
    apply Eq.symm
    apply lfp_eq
    apply Monotone_while_lfp_arg


/- ## Equivalence of the Denotational and the Big-Step Semantics
## (**optional**) -/

theorem denote_of_BigStep (Ss : Stmt × State) (t : State)
    (h : Ss ⟹ t) :
  (Prod.snd Ss, t) ∈ ⟦Prod.fst Ss⟧ :=
  by
    induction h with
    | skip s => simp [denote]
    | assign x a s => simp [denote]
    | seq S T s t u hS hT ihS ihT =>
      simp [denote]
      aesop
    | if_true B S T s t hB hS ih =>
      simp at *
      simp [denote, *]
    | if_false B S T s t hB hT ih =>
      simp at *
      simp [denote, *]
    | while_true B S s t u hB hS hw ihS ihw =>
      rw [Eq.symm DenoteEquiv.if_seq_while]
      simp at *
      simp [denote, *]
      aesop
    | while_false B S s hB =>
      rw [Eq.symm DenoteEquiv.if_seq_while]
      simp at *
      simp [denote, *]

theorem BigStep_of_denote :
  ∀(S : Stmt) (s t : State), (s, t) ∈ ⟦S⟧ → (S, s) ⟹ t
  | Stmt.skip,             s, t => by simp [denote]
  | Stmt.assign x a,       s, t => by simp [denote]
  | Stmt.seq S T,          s, t =>
    by
      intro hst
      simp [denote] at hst
      cases hst with
      | intro u hu =>
        cases hu with
        | intro hsu hut =>
          apply BigStep.seq
          { exact BigStep_of_denote _ _ _ hsu }
          { exact BigStep_of_denote _ _ _ hut }
  | Stmt.ifThenElse B S T, s, t =>
    by
      intro hst
      simp [denote] at hst
      cases hst with
      | inl htrue =>
        cases htrue with
        | intro hst hB =>
          apply BigStep.if_true
          { exact hB }
          { exact BigStep_of_denote _ _ _ hst }
      | inr hfalse =>
        cases hfalse with
        | intro hst hB =>
          apply BigStep.if_false
          { exact hB }
          { exact BigStep_of_denote _ _ _ hst }
  | Stmt.whileDo B S,      s, t =>
    by
      have hw : ⟦Stmt.whileDo B S⟧
        ≤ {st | (Stmt.whileDo B S, Prod.fst st) ⟹
             Prod.snd st} :=
        by
          apply lfp_le _ _ _
          intro uv huv
          cases uv with
          | mk u v =>
            simp at huv
            cases huv with
            | inl hand =>
              cases hand with
              | intro hst hB =>
                cases hst with
                | intro w hw =>
                  cases hw with
                  | intro huw hw =>
                    apply BigStep.while_true
                    { exact hB }
                    { exact BigStep_of_denote _ _ _ huw }
                    { exact hw }
            | inr hand =>
              cases hand with
              | intro hvu hB =>
                cases hvu
                apply BigStep.while_false
                exact hB
      apply hw

theorem denote_Iff_BigStep (S : Stmt) (s t : State) :
  (s, t) ∈ ⟦S⟧ ↔ (S, s) ⟹ t :=
  Iff.intro (BigStep_of_denote S s t) (denote_of_BigStep (S, s) t)


/- ## A Simpler Approach Based on an Inductive Predicate (**optional**) -/

inductive Awhile (B : State → Prop)
    (r : Set (State × State)) :
  State → State → Prop
  | true {s t u} (hcond : B s) (hbody : (s, t) ∈ r)
      (hrest : Awhile B r t u) :
    Awhile B r s u
  | false {s} (hcond : ¬ B s) :
    Awhile B r s s

def denoteAwhile : Stmt → Set (State × State)
  | Stmt.skip             => Id
  | Stmt.assign x a       =>
    {st | Prod.snd st = (Prod.fst st)[x ↦ a (Prod.fst st)]}
  | Stmt.seq S T          => denoteAwhile S ◯ denoteAwhile T
  | Stmt.ifThenElse B S T =>
    (denoteAwhile S ⇃ B)
    ∪ (denoteAwhile T ⇃ (fun s ↦ ¬ B s))
  | Stmt.whileDo b S      =>
    {st | Awhile b (denoteAwhile S) (Prod.fst st)
       (Prod.snd st)}

end LoVe
