import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.PrimeCounting
import PrimeFactorUnimodality.Helpers.PrimeSequence.AverageGap
import PrimeFactorUnimodality.Helpers.Analytic.ShortIntervalPrime

set_option autoImplicit false

/-! # Interfaces for explicit prime-counting estimates -/

namespace PrimeFactorUnimodality

noncomputable section

/-- Dusart's lower comparison function
`x / log x * (1 + 1 / log x)`. -/
def dusartPiLower (x : Real) : Real :=
  x / Real.log x * (1 + 1 / Real.log x)

/-- Dusart's upper comparison function
`x / log x * (1 + 1.2762 / log x)`, with the decimal represented exactly. -/
def dusartPiUpper (x : Real) : Real :=
  x / Real.log x * (1 + (6381 / 5000 : Real) / Real.log x)

/-! The exact Abel-summation identity underlying the prime-counting
asymptotic.  Keeping the identity in this namespace makes the later
remainder estimates explicit instead of treating `π` as an opaque provider. -/
theorem primeCounting_from_theta_integral {x : Real} (hx : 2 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : Real) =
      Chebyshev.theta x / Real.log x +
        ∫ t in (2 : Real)..x,
          Chebyshev.theta t / (t * (Real.log t) ^ 2) := by
  exact Chebyshev.primeCounting_eq_theta_div_log_add_integral hx

/-- The exact explicit prime-counting statements needed downstream.  This
interface lets the structural argument compile independently of the eventual
proof of the analytic provider. -/
def HasDusartPrimeCountingBounds : Prop :=
  (∀ n : Nat, 599 ≤ n →
    dusartPiLower n ≤ (Nat.primeCounting n : Real)) ∧
  (∀ n : Nat, 2 ≤ n →
    (Nat.primeCounting n : Real) ≤ dusartPiUpper n)

/-! A real-variable form is convenient when importing an explicit analytic
estimate stated for `π x`.  The final tail lemmas use the natural-number form
above, so this adapter is kept here rather than repeated at each call site. -/
def HasDusartRealPrimeCountingBounds : Prop :=
  (∀ x : Real, 599 ≤ x →
    dusartPiLower x ≤ (Nat.primeCounting ⌊x⌋₊ : Real)) ∧
  (∀ x : Real, 2 ≤ x →
    (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x)

def HasDusartRealPrimeCountingBoundsBelow (X : Real) : Prop :=
  (∀ x : Real, 599 ≤ x → x ≤ X →
    dusartPiLower x ≤ (Nat.primeCounting ⌊x⌋₊ : Real)) ∧
  (∀ x : Real, 2 ≤ x → x ≤ X →
    (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x)

def HasDusartRealPrimeCountingBoundsAbove (X : Real) : Prop :=
  (∀ x : Real, X ≤ x →
    dusartPiLower x ≤ (Nat.primeCounting ⌊x⌋₊ : Real)) ∧
  (∀ x : Real, X ≤ x →
    (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x)

/-! The prime-counting estimates are recorded in the paper in the simpler
denominator form below.  Keep that published interface separate from the
stronger comparison functions consumed by the tail proof; the conversion is
elementary and therefore belongs in the formalization rather than being
silently folded into an analytic assumption. -/
def HasDusartPublishedPrimeCountingBounds : Prop :=
  (∀ x : Real, (5393 : Real) < x →
    x / (Real.log x - 1) ≤ (Nat.primeCounting ⌊x⌋₊ : Real)) ∧
  (∀ x : Real, (60184 : Real) < x →
    (Nat.primeCounting ⌊x⌋₊ : Real) ≤ x / (Real.log x - (11 / 10 : Real)))

def HasDusartPublishedPrimeCountingBoundsBelow (X : Real) : Prop :=
  (∀ x : Real, (5393 : Real) < x → x ≤ X →
    x / (Real.log x - 1) ≤ (Nat.primeCounting ⌊x⌋₊ : Real)) ∧
  (∀ x : Real, (60184 : Real) < x → x ≤ X →
    (Nat.primeCounting ⌊x⌋₊ : Real) ≤ x / (Real.log x - (11 / 10 : Real)))

theorem hasDusartRealPrimeCountingBoundsAbove_of_published
    (published : HasDusartPublishedPrimeCountingBounds) :
    HasDusartRealPrimeCountingBoundsAbove (4e18 : Real) := by
  constructor
  · intro x hx
    have hx5393 : (5393 : Real) < x := by
      norm_num at hx ⊢
      linarith
    have hpublished := published.1 x hx5393
    have hlog := log_large_x_gt_ten hx
    have hlog_pos : 0 < Real.log x := by linarith
    have hx_pos : 0 < x := by linarith
    have hcomparison : dusartPiLower x ≤ x / (Real.log x - 1) := by
      dsimp [dusartPiLower]
      have hden : 0 < Real.log x - 1 := by linarith
      have hrewrite :
          x / Real.log x * (1 + 1 / Real.log x) =
            x * (Real.log x + 1) / (Real.log x) ^ 2 := by
        field_simp [ne_of_gt hlog_pos]
      rw [hrewrite]
      apply (div_le_div_iff₀ (sq_pos_of_pos hlog_pos) hden).2
      nlinarith [sq_nonneg (Real.log x - 1)]
    exact hcomparison.trans hpublished
  · intro x hx
    have hx60184 : (60184 : Real) < x := by
      norm_num at hx ⊢
      linarith
    have hpublished := published.2 x hx60184
    have hlog := log_large_x_gt_ten hx
    have hlog_pos : 0 < Real.log x := by linarith
    have hx_pos : 0 < x := by linarith
    have hcomparison : x / (Real.log x - (11 / 10 : Real)) ≤ dusartPiUpper x := by
      dsimp [dusartPiUpper]
      have hden : 0 < Real.log x - (11 / 10 : Real) := by linarith
      have hrewrite :
          x / (Real.log x - (11 / 10 : Real)) ≤
            x * (Real.log x + (6381 / 5000 : Real)) / (Real.log x) ^ 2 := by
        apply (div_le_div_iff₀ hden (sq_pos_of_pos hlog_pos)).2
        nlinarith [sq_nonneg (Real.log x - 1)]
      convert hrewrite using 1 <;> field_simp <;> ring
    exact hpublished.trans hcomparison

/-! A provider form matching Dusart's explicit asymptotic formula.  The
reduction below is deliberately arithmetic: once the asymptotic remainder is
kernel-checked, it supplies the two comparison bounds used by the tail. -/
def HasDusartPrimeCountingAsymptoticAbove (X : Real) : Prop :=
  ∀ x : Real, X ≤ x →
    ∃ E : Real,
      (Nat.primeCounting ⌊x⌋₊ : Real) =
        x / Real.log x *
          (1 + 1 / Real.log x + 2 / (Real.log x) ^ 2 + E) ∧
        |E| ≤ (732 : Real) / 100 / (Real.log x) ^ 3

def HasDusartPublishedPrimeCountingBoundsAbove (X : Real) : Prop :=
  (∀ x : Real, X ≤ x →
    x / (Real.log x - 1) ≤ (Nat.primeCounting ⌊x⌋₊ : Real)) ∧
  (∀ x : Real, X ≤ x →
    (Nat.primeCounting ⌊x⌋₊ : Real) ≤
      x / (Real.log x - (11 / 10 : Real)))

theorem hasDusartPublishedPrimeCountingBoundsAbove_of_asymptotic
    (asymptotic : HasDusartPrimeCountingAsymptoticAbove (4e9 : Real)) :
    HasDusartPublishedPrimeCountingBoundsAbove (4e9 : Real) := by
  constructor
  · intro x hx
    obtain ⟨E, hformula, hE⟩ := asymptotic x hx
    have hlog : (20 : Real) < Real.log x := by
      apply (Real.lt_log_iff_exp_lt (by linarith)).2
      have hexp_three : Real.exp 20 < (3 : Real) ^ 20 := by
        rw [show (20 : Real) = (20 : ℕ) * 1 by norm_num,
          Real.exp_nat_mul]
        exact pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le
          (by norm_num)
      have hthree : (3 : Real) ^ 20 < (4e9 : Real) := by norm_num
      exact hexp_three.trans hthree |>.trans_le hx
    have hlog_pos : 0 < Real.log x := by linarith
    have hx_pos : 0 < x := by linarith
    rw [hformula]
    have hE_lower : -(732 : Real) / 100 / (Real.log x) ^ 3 ≤ E := by
      convert neg_le_of_abs_le hE using 1 <;> ring
    have hbracket :
        1 + 1 / Real.log x + 2 / (Real.log x) ^ 2 + E ≥
          Real.log x / (Real.log x - 1) := by
      have hden : 0 < Real.log x - 1 := by linarith
      apply (div_le_iff₀ hden).2
      have hlog_cube : (0 : Real) < (Real.log x) ^ 3 := by positivity
      have hE_lower' : -(732 : Real) / 100 ≤ E * (Real.log x) ^ 3 :=
        (div_le_iff₀ hlog_cube).mp hE_lower
      have hE_prod := mul_le_mul_of_nonneg_right hE_lower' hden.le
      field_simp [hlog_pos.ne', hden.ne']
      nlinarith [hE_prod, sq_nonneg (Real.log x - 20)]
    have hfactor : 0 ≤ x / Real.log x := by positivity
    have hmul := mul_le_mul_of_nonneg_left hbracket hfactor
    have htarget : x / Real.log x * (Real.log x / (Real.log x - 1)) =
        x / (Real.log x - 1) := by
      field_simp [hlog_pos.ne', (by linarith : Real.log x - 1 ≠ 0)]
    rw [htarget] at hmul
    exact hmul
  · intro x hx
    obtain ⟨E, hformula, hE⟩ := asymptotic x hx
    have hlog : (20 : Real) < Real.log x := by
      apply (Real.lt_log_iff_exp_lt (by linarith)).2
      have hexp_three : Real.exp 20 < (3 : Real) ^ 20 := by
        rw [show (20 : Real) = (20 : ℕ) * 1 by norm_num,
          Real.exp_nat_mul]
        exact pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le
          (by norm_num)
      have hthree : (3 : Real) ^ 20 < (4e9 : Real) := by norm_num
      exact hexp_three.trans hthree |>.trans_le hx
    have hlog_pos : 0 < Real.log x := by linarith
    have hx_pos : 0 < x := by linarith
    rw [hformula]
    have hE_upper : E ≤ (732 : Real) / 100 / (Real.log x) ^ 3 :=
      le_of_abs_le hE
    have hbracket :
        1 + 1 / Real.log x + 2 / (Real.log x) ^ 2 + E ≤
          Real.log x / (Real.log x - (11 / 10 : Real)) := by
      have hden : 0 < Real.log x - (11 / 10 : Real) := by linarith
      apply (le_div_iff₀ hden).2
      have hlog_cube : (0 : Real) < (Real.log x) ^ 3 := by positivity
      have hE_upper' : E * (Real.log x) ^ 3 ≤ (732 : Real) / 100 :=
        (le_div_iff₀ hlog_cube).mp hE_upper
      have hE_prod := mul_le_mul_of_nonneg_right hE_upper' hden.le
      field_simp [hlog_pos.ne', hden.ne']
      nlinarith [hE_prod, sq_nonneg (Real.log x - 20)]
    have hfactor : 0 ≤ x / Real.log x := by positivity
    have hmul := mul_le_mul_of_nonneg_left hbracket hfactor
    have htarget : x / Real.log x *
        (Real.log x / (Real.log x - (11 / 10 : Real))) =
        x / (Real.log x - (11 / 10 : Real)) := by
      field_simp [hlog_pos.ne', (by linarith : Real.log x - (11 / 10 : Real) ≠ 0)]
    rw [htarget] at hmul
    exact hmul

theorem hasDusartPublishedPrimeCountingBounds_of_below_and_above
    {X : Real} (finite : HasDusartPublishedPrimeCountingBoundsBelow X)
    (tail : HasDusartPublishedPrimeCountingBoundsAbove X) :
    HasDusartPublishedPrimeCountingBounds := by
  constructor
  · intro x hx
    by_cases hsmall : x ≤ X
    · exact finite.1 x hx hsmall
    · exact tail.1 x (le_of_lt (lt_of_not_ge hsmall))
  · intro x hx
    by_cases hsmall : x ≤ X
    · exact finite.2 x hx hsmall
    · exact tail.2 x (le_of_lt (lt_of_not_ge hsmall))

theorem hasDusartPublishedPrimeCountingBounds_of_finite_and_asymptotic
    (finite : HasDusartPublishedPrimeCountingBoundsBelow (4e9 : Real))
    (asymptotic : HasDusartPrimeCountingAsymptoticAbove (4e9 : Real)) :
    HasDusartPublishedPrimeCountingBounds := by
  exact hasDusartPublishedPrimeCountingBounds_of_below_and_above finite
    (hasDusartPublishedPrimeCountingBoundsAbove_of_asymptotic asymptotic)

theorem hasDusartRealPrimeCountingBoundsAbove_of_asymptotic
    (asymptotic : HasDusartPrimeCountingAsymptoticAbove (4e9 : Real)) :
    HasDusartRealPrimeCountingBoundsAbove (4e18 : Real) := by
  constructor
  · intro x hx
    have hx9 : (4e9 : Real) ≤ x := by
      norm_num at hx ⊢
      linarith
    obtain ⟨E, hformula, hE⟩ := asymptotic x hx9
    have hlog := log_large_x_gt_ten hx
    have hlog_pos : 0 < Real.log x := by linarith
    have hx_pos : 0 < x := by linarith
    have hlog_sq : (100 : Real) < (Real.log x) ^ 2 := by
      nlinarith [mul_self_lt_mul_self (by norm_num : (0 : Real) ≤ 10) hlog]
    have hlog_cube : (1000 : Real) < (Real.log x) ^ 3 := by
      nlinarith [mul_self_lt_mul_self (by norm_num : (0 : Real) ≤ 10) hlog,
        mul_pos hlog_pos (show 0 < (Real.log x) ^ 2 by positivity)]
    rw [hformula]
    have hElower : -(732 : Real) / 100 / (Real.log x) ^ 3 ≤ E := by
      convert neg_le_of_abs_le hE using 1 <;> ring
    have hmain : (1 : Real) + 1 / Real.log x + 2 / (Real.log x) ^ 2 + E ≥
        1 + 1 / Real.log x := by
      have hrem : (732 : Real) / 100 / (Real.log x) ^ 3 ≤
          2 / (Real.log x) ^ 2 := by
        field_simp
        nlinarith [hlog_cube]
      have hElower' : -(2 / (Real.log x) ^ 2) ≤ E := by
        calc
          -(2 / (Real.log x) ^ 2) ≤
              -((732 : Real) / 100 / (Real.log x) ^ 3) := by
                linarith
          _ ≤ E := by convert hElower using 1 <;> ring
      linarith
    have hfactor : 0 ≤ x / Real.log x := by positivity
    have := mul_le_mul_of_nonneg_left hmain.le hfactor
    convert this using 1 <;> dsimp [dusartPiLower] <;> field_simp <;> ring
  · intro x hx
    have hx9 : (4e9 : Real) ≤ x := by
      norm_num at hx ⊢
      linarith
    obtain ⟨E, hformula, hE⟩ := asymptotic x hx9
    have hlog := log_large_x_gt_ten hx
    have hlog_pos : 0 < Real.log x := by linarith
    have hx_pos : 0 < x := by linarith
    have hupper : (1 : Real) + 1 / Real.log x + 2 / (Real.log x) ^ 2 + E ≤
        1 + (6381 : Real) / 5000 / Real.log x := by
      have hEupper : E ≤ (732 : Real) / 100 / (Real.log x) ^ 3 :=
        le_of_abs_le hE
      have hlog_sq : (100 : Real) < (Real.log x) ^ 2 := by
        nlinarith [mul_self_lt_mul_self (by norm_num : (0 : Real) ≤ 10) hlog]
      have hlog_pos' : 0 ≤ Real.log x := hlog_pos.le
      have hcoef :
          2 / (Real.log x) ^ 2 + (732 : Real) / 100 / (Real.log x) ^ 3 ≤
            (1381 : Real) / 5000 / Real.log x := by
        field_simp
        nlinarith
      calc
        1 + 1 / Real.log x + 2 / (Real.log x) ^ 2 + E =
            1 + 1 / Real.log x + (2 / (Real.log x) ^ 2 + E) := by ring
        _ ≤ 1 + 1 / Real.log x +
            (2 / (Real.log x) ^ 2 + (732 : Real) / 100 /
              (Real.log x) ^ 3) := by linarith
        _ ≤ 1 + 1 / Real.log x + (1381 : Real) / 5000 / Real.log x :=
          by
            convert add_le_add_left hcoef (1 + 1 / Real.log x) using 1 <;> ring
        _ = 1 + (6381 : Real) / 5000 / Real.log x := by ring
    rw [hformula]
    dsimp [dusartPiUpper]
    have hfactor : 0 ≤ x / Real.log x := by positivity
    have := mul_le_mul_of_nonneg_left hupper hfactor
    convert this using 1 <;> dsimp [dusartPiUpper] <;> field_simp <;> ring

theorem hasDusartRealPrimeCountingBounds_of_below_and_above
    {X : Real} (finite : HasDusartRealPrimeCountingBoundsBelow X)
    (tail : HasDusartRealPrimeCountingBoundsAbove X) :
    HasDusartRealPrimeCountingBounds := by
  constructor
  · intro x hx
    by_cases hsmall : x ≤ X
    · exact finite.1 x hx hsmall
    · exact tail.1 x (le_of_lt (lt_of_not_ge hsmall))
  · intro x hx
    by_cases hsmall : x ≤ X
    · exact finite.2 x hx hsmall
    · exact tail.2 x (le_of_lt (lt_of_not_ge hsmall))

theorem hasDusartRealPrimeCountingBounds_of_finite_and_asymptotic
    (finite : HasDusartRealPrimeCountingBoundsBelow (4e18 : Real))
    (asymptotic : HasDusartPrimeCountingAsymptoticAbove (4e9 : Real)) :
    HasDusartRealPrimeCountingBounds :=
  hasDusartRealPrimeCountingBounds_of_below_and_above finite
    (hasDusartRealPrimeCountingBoundsAbove_of_asymptotic asymptotic)

theorem hasDusartRealPrimeCountingBounds_of_finite_published_and_asymptotic
    (finite : HasDusartRealPrimeCountingBoundsBelow (4e18 : Real))
    (finitePublished : HasDusartPublishedPrimeCountingBoundsBelow (4e9 : Real))
    (asymptotic : HasDusartPrimeCountingAsymptoticAbove (4e9 : Real)) :
    HasDusartRealPrimeCountingBounds := by
  have published : HasDusartPublishedPrimeCountingBounds :=
    hasDusartPublishedPrimeCountingBounds_of_finite_and_asymptotic
      finitePublished asymptotic
  exact hasDusartRealPrimeCountingBounds_of_below_and_above finite
    (hasDusartRealPrimeCountingBoundsAbove_of_published published)

theorem hasDusartRealPrimeCountingBounds_of_below_and_above_at_cutoff
    (finite : HasDusartRealPrimeCountingBoundsBelow (4e18 : Real))
    (tail : HasDusartRealPrimeCountingBoundsAbove (4e18 : Real)) :
    HasDusartRealPrimeCountingBounds :=
  hasDusartRealPrimeCountingBounds_of_below_and_above finite tail

theorem hasDusartPrimeCountingBounds_of_real
    (bounds : HasDusartRealPrimeCountingBounds) :
    HasDusartPrimeCountingBounds := by
  constructor
  · intro n hn
    simpa only [Nat.floor_natCast] using
      bounds.1 (n : Real) (by exact_mod_cast hn)
  · intro n hn
    simpa only [Nat.floor_natCast] using
      bounds.2 (n : Real) (by exact_mod_cast hn)

theorem primeCounting_sub_lower_of_dusart
    (bounds : HasDusartPrimeCountingBounds)
    {x y : Nat} (hx : 2 ≤ x) (hy : 599 ≤ y) (hxy : x ≤ y) :
    dusartPiLower y - dusartPiUpper x ≤
      (Nat.primeCounting y - Nat.primeCounting x : Nat) := by
  have lower := bounds.1 y hy
  have upper := bounds.2 x hx
  have countMono := Nat.monotone_primeCounting hxy
  rw [Nat.cast_sub countMono]
  exact sub_le_sub lower upper

/-- A real lower bound exceeding a natural target yields the corresponding
natural lower bound on the number of primes in a shell. -/
theorem nat_le_primeCounting_sub_of_lt_dusart
    (bounds : HasDusartPrimeCountingBounds)
    {x y target : Nat} (hx : 2 ≤ x) (hy : 599 ≤ y) (hxy : x ≤ y)
    (numeric : (target : Real) < dusartPiLower y - dusartPiUpper x) :
    target + 1 ≤ Nat.primeCounting y - Nat.primeCounting x := by
  have lower := numeric.trans_le
    (primeCounting_sub_lower_of_dusart bounds hx hy hxy)
  exact_mod_cast lower

/-- A lower bound for a prime-counting shell, expressed in the same units as
an intended average-gap bound, directly supplies both discrete hypotheses of
the average-gap lemma.  This avoids introducing a rounded auxiliary target. -/
theorem count_and_width_of_dusart
    (bounds : HasDusartPrimeCountingBounds)
    {x y width bound : Nat} (hx : 2 ≤ x) (hy : 599 ≤ y) (hxy : x ≤ y)
    (bound_pos : 1 ≤ bound)
    (numeric : (width : Real) / bound + 1 <
      dusartPiLower y - dusartPiUpper x) :
    2 ≤ Nat.primeCounting y - Nat.primeCounting x ∧
      width < (Nat.primeCounting y - Nat.primeCounting x - 1) * bound := by
  let count := Nat.primeCounting y - Nat.primeCounting x
  have shellLower := primeCounting_sub_lower_of_dusart bounds hx hy hxy
  have countBound : (width : Real) / bound + 1 < (count : Real) := by
    exact numeric.trans_le (by simpa only [count] using shellLower)
  have boundRealPos : (0 : Real) < bound := by exact_mod_cast bound_pos
  have countGtOne : (1 : Real) < count := by
    have widthNonneg : (0 : Real) ≤ width := by positivity
    have divNonneg : (0 : Real) ≤ (width : Real) / bound :=
      div_nonneg widthNonneg boundRealPos.le
    linarith
  have countTwo : 2 ≤ count := by exact_mod_cast countGtOne
  refine ⟨by simpa only [count] using countTwo, ?_⟩
  have productBound : (width : Real) < ((count - 1) * bound : Nat) := by
    have divided : (width : Real) / bound < (count : Real) - 1 := by
      linarith
    rw [div_lt_iff₀ boundRealPos] at divided
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ count)]
    norm_num
    exact divided
  exact_mod_cast productBound

/-- A numerical lower bound for Dusart's comparison function converts
directly into an upper bound for an indexed prime. -/
theorem primeAt_le_of_dusart_lower
    (bounds : HasDusartPrimeCountingBounds) {i upper : Nat}
    (upper_large : 599 ≤ upper)
    (numeric : ((i + 1 : Nat) : Real) ≤ dusartPiLower upper) :
    primeAt i ≤ upper := by
  apply primeAt_le_of_succ_le_primeCounting'
  have castCount : ((i + 1 : Nat) : Real) ≤ Nat.primeCounting upper :=
    numeric.trans (bounds.1 upper upper_large)
  have natCount : i + 1 ≤ Nat.primeCounting upper := by exact_mod_cast castCount
  simpa only [Nat.primeCounting] using natCount

end

end PrimeFactorUnimodality
