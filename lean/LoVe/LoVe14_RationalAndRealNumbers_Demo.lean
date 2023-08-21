/- Copyright © 2018–2023 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Demo 14: Rational and Real Numbers

We review the construction of `ℚ` and `ℝ` as quotient types.

Our procedure to construct types with specific properties:

1. Create a new type that can represent all elements, but not necessarily in a
   unique manner.

2. Quotient this representation, equating elements that should be equal.

3. Define operators on the quotient type by lifting functions from the base
   type and prove that they are compatible with the quotient relation.

We used this approach in lecture 12 to construct `ℤ`. It can be used for `ℚ` and
`ℝ` as well. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Rational Numbers

**Step 1:** A rational number is a number that can be expressed as a fraction
`n / d` of integers `n` and `d ≠ 0`: -/

structure Fraction where
  num            : ℤ
  denom          : ℤ
  denom_Neq_zero : denom ≠ 0

/- The number `n` is called the numerator, and the number `d` is called the
denominator.

The representation of a rational number as a fraction is not unique—e.g.,
`1 / 2 = 2 / 4 = -1 / -2`.

**Step 2:** Two fractions `n₁ / d₁` and `n₂ / d₂` represent the same rational
number if the ratio between numerator and denominator are the same—i.e.,
`n₁ * d₂ = n₂ * d₁`. This will be our equivalence relation `≈` on fractions. -/

namespace Fraction

instance Setoid : Setoid Fraction :=
  { r :=
      fun a b : Fraction ↦ num a * denom b = num b * denom a
    iseqv :=
      { refl  := by aesop
        symm  := by aesop
        trans :=
          by
            intro a b c heq_ab heq_bc
            apply Int.eq_of_mul_eq_mul_right (denom_Neq_zero b)
            calc
              num a * denom c * denom b
              = num a * denom b * denom c :=
                by ac_rfl
              _ = num b * denom a * denom c :=
                by rw [heq_ab]
              _ = num b * denom c * denom a :=
                by ac_rfl
              _ = num c * denom b * denom a :=
                by rw [heq_bc]
              _ = num c * denom a * denom b :=
                by ac_rfl
            } }

theorem Setoid_Iff (a b : Fraction) :
  a ≈ b ↔ num a * denom b = num b * denom a :=
  by rfl

/- **Step 3:** Define `0 := 0 / 1`, `1 := 1 / 1`, addition, multiplication, etc.

    `n₁ / d₁ + n₂ / d₂`     := `(n₁ * d₂ + n₂ * d₁) / (d₁ * d₂)`
    `(n₁ / d₁) * (n₂ / d₂)` := `(n₁ * n₂) / (d₁ * d₂)`

Then show that they are compatible with `≈`. -/

def of_int (i : ℤ) : Fraction :=
  { num            := i
    denom          := 1
    denom_Neq_zero := by simp }

instance Zero : Zero Fraction :=
  { zero := of_int 0 }

instance One : One Fraction :=
  { one := of_int 1 }

instance Add : Add Fraction :=
  { add := fun a b : Fraction ↦
      { num            := num a * denom b + num b * denom a
        denom          := denom a * denom b
        denom_Neq_zero := by simp [denom_Neq_zero] } }

@[simp] theorem add_num (a b : Fraction) :
  num (a + b) = num a * denom b + num b * denom a :=
  by rfl

@[simp] theorem add_denom (a b : Fraction) :
  denom (a + b) = denom a * denom b :=
  by rfl

theorem Setoid_add {a a' b b' : Fraction} (ha : a ≈ a')
    (hb : b ≈ b') :
  a + b ≈ a' + b' :=
  by
    simp [Setoid_Iff, add_denom, add_num] at *
    calc
      (num a * denom b + num b * denom a)
          * (denom a' * denom b')
      = num a * denom a' * denom b * denom b'
        + num b * denom b' * denom a * denom a' :=
        by
          simp [add_mul, mul_add]
          ac_rfl
      _ = num a' * denom a * denom b * denom b'
            + num b' * denom b * denom a * denom a' :=
        by simp [*]
      _ = (num a' * denom b' + num b' * denom a')
            * (denom a * denom b) :=
        by
          simp [add_mul, mul_add]
          ac_rfl

instance Neg : Neg Fraction :=
  { neg := fun a : Fraction ↦
      { a with
        num := - num a } }

@[simp] theorem neg_num (a : Fraction) :
  num (- a) = - num a :=
  by rfl

@[simp] theorem neg_denom (a : Fraction) :
  denom (- a) = denom a :=
  by rfl

theorem Setoid_neg {a a' : Fraction} (hab : a ≈ a') :
  - a ≈ - a' :=
  by
    simp [Setoid_Iff] at *
    exact hab

instance Mul : Mul Fraction :=
  { mul := fun a b : Fraction ↦
      { num            := num a * num b
        denom          := denom a * denom b
        denom_Neq_zero :=
          by simp [Int.mul_eq_zero, denom_Neq_zero] } }

@[simp] theorem mul_num (a b : Fraction) :
  num (a * b) = num a * num b :=
  by rfl

@[simp] theorem mul_denom (a b : Fraction) :
  denom (a * b) = denom a * denom b :=
  by rfl

theorem Setoid_mul {a a' b b' : Fraction} (ha : a ≈ a')
    (hb : b ≈ b') :
  a * b ≈ a' * b' :=
  by
    simp [Setoid_Iff] at *
    calc
      num a * num b * (denom a' * denom b')
      = (num a * denom a') * (num b * denom b') :=
        by ac_rfl
      _ = (num a' * denom a) * (num b' * denom b) :=
        by simp [*]
      _ = num a' * num b' * (denom a * denom b) :=
        by ac_rfl

instance Inv : Inv Fraction :=
  { inv := fun a : Fraction ↦
      if ha : num a = 0 then
        0
      else
        { num            := denom a
          denom          := num a
          denom_Neq_zero := ha } }

theorem inv_def (a : Fraction) (ha : num a ≠ 0) :
  a⁻¹ =
  { num            := denom a
    denom          := num a
    denom_Neq_zero := ha } :=
  dif_neg ha

theorem inv_zero (a : Fraction) (ha : num a = 0) :
  a⁻¹ = 0 :=
  dif_pos ha

@[simp] theorem inv_num (a : Fraction) (ha : num a ≠ 0) :
  num (a⁻¹) = denom a :=
  by rw [inv_def a ha]

@[simp] theorem inv_denom (a : Fraction) (ha : num a ≠ 0) :
  denom (a⁻¹) = num a :=
  by rw [inv_def a ha]

theorem Setoid_inv {a a' : Fraction} (ha : a ≈ a') :
  a⁻¹ ≈ a'⁻¹ :=
  by
    cases Classical.em (num a = 0) with
    | inl ha0 =>
      cases Classical.em (num a' = 0) with
      | inl ha'0 =>
        simp [ha0, ha'0, inv_zero]
      | inr ha'0 =>
        simp [ha0, ha'0, Setoid_Iff, denom_Neq_zero] at ha
    | inr ha0 =>
      cases Classical.em (num a' = 0) with
      | inl ha'0 =>
        simp [ha0, ha'0, Setoid_Iff, denom_Neq_zero] at ha
      | inr ha'0 =>
        simp [Setoid_Iff, ha0, ha'0] at *
        linarith

end Fraction

def Rat : Type :=
  Quotient Fraction.Setoid

namespace Rat

def mk : Fraction → Rat :=
  Quotient.mk Fraction.Setoid

instance Zero : Zero Rat :=
  { zero := mk 0 }

instance One : One Rat :=
  { one := mk 1 }

instance Add : Add Rat :=
  { add := Quotient.lift₂ (fun a b : Fraction ↦ mk (a + b))
      (by
         intro a b a' b' ha hb
         apply Quotient.sound
         exact Fraction.Setoid_add ha hb) }

instance Neg : Neg Rat :=
  { neg := Quotient.lift (fun a : Fraction ↦ mk (- a))
      (by
         intro a a' ha
         apply Quotient.sound
         exact Fraction.Setoid_neg ha) }

instance Mul : Mul Rat :=
  { mul := Quotient.lift₂ (fun a b : Fraction ↦ mk (a * b))
      (by
         intro a b a' b' ha hb
         apply Quotient.sound
         exact Fraction.Setoid_mul ha hb) }

instance Inv : Inv Rat :=
  { inv := Quotient.lift (fun a : Fraction ↦ mk (a⁻¹))
      (by
         intro a a' ha
         apply Quotient.sound
         exact Fraction.Setoid_inv ha) }

end Rat


/- ### Alternative Definition of `ℚ`

Define `ℚ` as a subtype of `fraction`, with the requirement that the denominator
is positive and that the numerator and the denominator have no common divisors
except `1` and `-1`: -/

namespace Alternative

def Rat.IsCanonical (a : Fraction) : Prop :=
  Fraction.denom a > 0
  ∧ Nat.coprime (Int.natAbs (Fraction.num a))
      (Int.natAbs (Fraction.denom a))

def Rat : Type :=
  {a : Fraction // Rat.IsCanonical a}

end Alternative

/- This is more or less the `mathlib` definition.

Advantages:

* no quotient required;
* more efficient computation;
* more properties are syntactic equalities up to computation.

Disadvantage:

* more complicated function definitions.


### Real Numbers

Some sequences of rational numbers seem to converge because the numbers in the
sequence get closer and closer to each other, and yet do not converge to a
rational number.

Example:

    `a₀ = 1`
    `a₁ = 1.4`
    `a₂ = 1.41`
    `a₃ = 1.414`
    `a₄ = 1.4142`
    `a₅ = 1.41421`
    `a₆ = 1.414213`
    `a₇ = 1.4142135`
       ⋮

This sequence seems to converge because each `a_n` is at most `10^-n` away from
any of the following numbers. But the limit is `√2`, which is not a rational
number.

The rational numbers are incomplete, and the reals are their  __completion__.

To construct the reals, we need to fill in the gaps that are revealed by these
sequences that seem to converge, but do not.

Mathematically, a sequence `a₀, a₁, …` of rational numbers is __Cauchy__ if for
any `ε > 0`, there exists an `N ∈ ℕ` such that for all `m ≥ N`, we have
`|a_N - a_m| < ε`.

In other words, no matter how small we choose `ε`, we can always find a point in
the sequence from which all following numbers deviate less than by `ε`. -/

def IsCauchySeq (f : ℕ → ℚ) : Prop :=
  ∀ε > 0, ∃N, ∀m ≥ N, abs (f N - f m) < ε

/- Not every sequence is a Cauchy sequence: -/

theorem id_Not_CauchySeq :
  ¬ IsCauchySeq (fun n : ℕ ↦ (n : ℚ)) :=
  by
    rw [IsCauchySeq]
    intro h
    cases h 1 zero_lt_one with
    | intro i hi =>
      have hi_succi :=
        hi (i + 1) (by simp)
      simp [←sub_sub] at hi_succi

/- We define a type of Cauchy sequences as a subtype: -/

def CauchySeq : Type :=
  {f : ℕ → ℚ // IsCauchySeq f}

def seqOf (f : CauchySeq) : ℕ → ℚ :=
  Subtype.val f

/- Cauchy sequences represent real numbers:

* `a_n = 1 / n` represents the real number `0`;
* `1, 1.4, 1.41, …` represents the real number `√2`;
* `a_n = 0` also represents the real number `0`.

Since different Cauchy sequences can represent the same real number, we need to
take the quotient. Formally, two sequences represent the same real number when
their difference converges to zero: -/

namespace CauchySeq

instance Setoid : Setoid CauchySeq :=
{ r :=
    fun f g : CauchySeq ↦
      ∀ε > 0, ∃N, ∀m ≥ N, abs (seqOf f m - seqOf g m) < ε
  iseqv :=
    { refl :=
        by
          intro f ε hε
          apply Exists.intro 0
          aesop
      symm :=
        by
          intro f g hfg ε hε
          cases hfg ε hε with
          | intro N hN =>
            apply Exists.intro N
            intro m hm
            rw [abs_sub_comm]
            apply hN m hm
      trans :=
        by
          intro f g h hfg hgh ε hε
          cases hfg (ε / 2) (half_pos hε) with
          | intro N₁ hN₁ =>
            cases hgh (ε / 2) (half_pos hε) with
            | intro N₂ hN₂ =>
              apply Exists.intro (max N₁ N₂)
              intro m hm
              calc
                abs (seqOf f m - seqOf h m)
                ≤ abs (seqOf f m - seqOf g m)
                  + abs (seqOf g m - seqOf h m) :=
                  by apply abs_sub_le
              _ < ε / 2 + ε / 2 :=
                add_lt_add (hN₁ m (le_of_max_le_left hm))
                  (hN₂ m (le_of_max_le_right hm))
              _ = ε :=
                by simp } }

theorem Setoid_iff (f g : CauchySeq) :
  f ≈ g ↔
  ∀ε > 0, ∃N, ∀m ≥ N, abs (seqOf f m - seqOf g m) < ε :=
  by rfl

/- We can define constants such as `0` and `1` as a constant sequence. Any
constant sequence is a Cauchy sequence: -/

def const (q : ℚ) : CauchySeq :=
  Subtype.mk (fun _ : ℕ ↦ q)
    (by
       rw [IsCauchySeq]
       intro ε hε
       aesop)

/- Defining addition of real numbers requires a little more effort. We define
addition on Cauchy sequences as pairwise addition: -/

instance Add : Add CauchySeq :=
  { add := fun f g : CauchySeq ↦
      Subtype.mk (fun n : ℕ ↦ seqOf f n + seqOf g n) sorry }

/- Above, we omit the proof that the addition of two Cauchy sequences is again
a Cauchy sequence.

Next, we need to show that this addition is compatible with `≈`: -/

theorem Setoid_add {f f' g g' : CauchySeq} (hf : f ≈ f')
    (hg : g ≈ g') :
  f + g ≈ f' + g' :=
  by
    intro ε₀ hε₀
    simp [Setoid_iff]
    cases hf (ε₀ / 2) (half_pos hε₀) with
    | intro Nf hNf =>
      cases hg (ε₀ / 2) (half_pos hε₀) with
      | intro Ng hNg =>
        apply Exists.intro (max Nf Ng)
        intro m hm
        calc
          abs (seqOf (f + g) m - seqOf (f' + g') m)
          = abs ((seqOf f m + seqOf g m)
            - (seqOf f' m + seqOf g' m)) :=
            by rfl
          _ = abs ((seqOf f m - seqOf f' m)
              + (seqOf g m - seqOf g' m)) :=
            by
              have arg_eq :
                seqOf f m + seqOf g m
                  - (seqOf f' m + seqOf g' m) =
                seqOf f m - seqOf f' m
                  + (seqOf g m - seqOf g' m) :=
                by linarith
              rw [arg_eq]
          _ ≤ abs (seqOf f m - seqOf f' m)
              + abs (seqOf g m - seqOf g' m) :=
            by apply abs_add
          _ < ε₀ / 2 + ε₀ / 2 :=
            add_lt_add (hNf m (le_of_max_le_left hm))
              (hNg m (le_of_max_le_right hm))
          _ = ε₀ :=
            by simp

end CauchySeq

/- The real numbers are the quotient: -/

def Real : Type :=
  Quotient CauchySeq.Setoid

namespace Real

instance Zero : Zero Real :=
  { zero := ⟦CauchySeq.const 0⟧ }

instance One : One Real :=
  { one := ⟦CauchySeq.const 1⟧ }

instance Add : Add Real :=
{ add := Quotient.lift₂ (fun a b : CauchySeq ↦ ⟦a + b⟧)
    (by
       intro a b a' b' ha hb
       apply Quotient.sound
       exact CauchySeq.Setoid_add ha hb) }

end Real


/- ### Alternative Definitions of `ℝ`

* Dedekind cuts: `r : ℝ` is represented essentially as `{x : ℚ | x < r}`.

* Binary sequences `ℕ → Bool` can represent the interval `[0, 1]`. This can be
  used to build `ℝ`. -/

end LoVe
