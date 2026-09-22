import PrimeFactorUnimodality.Helpers.Analytic.XiLowReciprocalMass
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.FinsetAbel

/-! # Abel summation for the actual multiplicity-counted xi zeros

The positive-height counting function counts divisor labels, not distinct
ordinates. Finite summation by parts applies on `(a,b]` with the exact
increment `N(x)-N(a)`. This is the finite analytic identity needed before
passing to the infinite Lehman tail; it assumes no numerical estimate for
the counting function and no location of zeros on the critical line.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory Set

local instance : DecidableEq RiemannXiDivisorZeroIndex := Classical.decEq _

/-- There are finitely many positive-ordinate divisor labels below a fixed height. -/
theorem finite_xi_divisor_pos_im_le (H : ℝ) :
    {p : RiemannXiDivisorZeroIndex | 0 < (riemannXiDivisorZeroValue p).im ∧
      (riemannXiDivisorZeroValue p).im ≤ H}.Finite := by
  apply (finite_xi_divisor_abs_im_le H).subset
  intro p hp
  change |(riemannXiDivisorZeroValue p).im| ≤ H
  rw [abs_of_pos hp.1]
  exact hp.2

/-- Positive xi zeros through a closed upper cutoff, with analytic multiplicity. -/
def xiPositiveHeightIndices (H : ℝ) : Finset RiemannXiDivisorZeroIndex :=
  (finite_xi_divisor_pos_im_le H).toFinset

@[simp] theorem mem_xiPositiveHeightIndices (H : ℝ) (p : RiemannXiDivisorZeroIndex) :
    p ∈ xiPositiveHeightIndices H ↔
      0 < (riemannXiDivisorZeroValue p).im ∧ (riemannXiDivisorZeroValue p).im ≤ H := by
  simp [xiPositiveHeightIndices]

/-- The actual positive-ordinate counting function. -/
def xiZeroCount (H : ℝ) : ℕ := (xiPositiveHeightIndices H).card

theorem xiPositiveHeightIndices_mono : Monotone xiPositiveHeightIndices := by
  intro a b hab p hp
  rw [mem_xiPositiveHeightIndices] at hp ⊢
  exact ⟨hp.1, hp.2.trans hab⟩

/-- A half-open ordinate window of actual divisor labels. -/
def xiHeightWindowIndices (a b : ℝ) : Finset RiemannXiDivisorZeroIndex :=
  (xiPositiveHeightIndices b).filter (fun p => a < (riemannXiDivisorZeroValue p).im)

@[simp] theorem mem_xiHeightWindowIndices (a b : ℝ) (p : RiemannXiDivisorZeroIndex) :
    p ∈ xiHeightWindowIndices a b ↔
      (0 < (riemannXiDivisorZeroValue p).im ∧ (riemannXiDivisorZeroValue p).im ≤ b) ∧
        a < (riemannXiDivisorZeroValue p).im := by
  classical
  simp [xiHeightWindowIndices]

/-- All labels at the lower cutoff are subtracted, and those at the upper cutoff remain. -/
theorem xiHeightWindowIndices_eq_sdiff (a b : ℝ) :
    xiHeightWindowIndices a b = xiPositiveHeightIndices b \ xiPositiveHeightIndices a := by
  classical
  ext p
  simp only [mem_xiHeightWindowIndices, Finset.mem_sdiff, mem_xiPositiveHeightIndices]
  constructor
  · rintro ⟨hp, ha⟩
    exact ⟨hp, fun h => (not_le_of_gt ha) h.2⟩
  · rintro ⟨hp, ha⟩
    exact ⟨hp, lt_of_not_ge (fun h => ha ⟨hp.1, h⟩)⟩

/-- The window cardinality is the difference of the actual cumulative counts. -/
theorem card_xiHeightWindowIndices {a b : ℝ} (hab : a ≤ b) :
    ((xiHeightWindowIndices a b).card : ℝ) = (xiZeroCount b : ℝ) - xiZeroCount a := by
  rw [xiHeightWindowIndices_eq_sdiff]
  have h := Finset.card_sdiff_add_card_eq_card (xiPositiveHeightIndices_mono hab)
  have hc := congrArg (fun n : ℕ => (n : ℝ)) h
  push_cast at hc
  change _ = ((xiPositiveHeightIndices b).card : ℝ) - (xiPositiveHeightIndices a).card
  linarith

/-- Filtering a bounded window at an intermediate height gives the shorter window. -/
theorem filter_xiHeightWindowIndices_le (a : ℝ) {x b : ℝ} (hxb : x ≤ b) :
    (xiHeightWindowIndices a b).filter (fun p => (riemannXiDivisorZeroValue p).im ≤ x) =
      xiHeightWindowIndices a x := by
  classical
  ext p
  simp only [Finset.mem_filter, mem_xiHeightWindowIndices]
  exact ⟨fun h => ⟨⟨h.1.1.1, h.2⟩, h.1.2⟩,
    fun h => ⟨⟨⟨h.1.1, h.1.2.trans hxb⟩, h.2⟩, h.1.2⟩⟩

/-- The counting increment times an integrable function is integrable on a finite interval. -/
theorem integrableOn_xiZeroCount_sub_mul {a b : ℝ} {g : ℝ → ℝ}
    (hg : IntegrableOn g (Icc a b)) :
    IntegrableOn (fun x => ((xiZeroCount x : ℝ) - xiZeroCount a) * g x) (Icc a b) := by
  classical
  have h := Finset.integrableOn_sum_filter_mul (xiHeightWindowIndices a b)
    (fun p => (riemannXiDivisorZeroValue p).im) (fun _ => (1 : ℝ)) hg
  apply h.congr_fun _ measurableSet_Icc
  intro x hx
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [filter_xiHeightWindowIndices_le a hx.2, card_xiHeightWindowIndices hx.1]

/-- Multiplication by the full counting function also preserves finite-interval integrability. -/
theorem integrableOn_xiZeroCount_mul {a b : ℝ} {g : ℝ → ℝ}
    (hg : IntegrableOn g (Icc a b)) :
    IntegrableOn (fun x => (xiZeroCount x : ℝ) * g x) (Icc a b) := by
  apply ((integrableOn_xiZeroCount_sub_mul hg).add
    (hg.const_mul (xiZeroCount a : ℝ))).congr_fun _ measurableSet_Icc
  intro x _
  simp only [Pi.add_apply]
  ring

/-- Exact finite Abel summation for the actual xi zeros in a half-open ordinate window. -/
theorem sum_xi_height_window_eq_count_sub_integral {a b : ℝ} {f g : ℝ → ℝ}
    (hab : a ≤ b) (hf : ∀ x ∈ Icc a b, HasDerivAt f (g x) x)
    (hg : IntegrableOn g (Icc a b)) :
    ∑ p ∈ xiHeightWindowIndices a b, f (riemannXiDivisorZeroValue p).im =
      ((xiZeroCount b : ℝ) - xiZeroCount a) * f b -
        ∫ x in Icc a b, ((xiZeroCount x : ℝ) - xiZeroCount a) * g x := by
  classical
  have h := Finset.sum_mul_eq_sum_mul_sub_integral_count (xiHeightWindowIndices a b)
    (fun p => (riemannXiDivisorZeroValue p).im) (fun _ => (1 : ℝ))
    (fun p hp => ⟨((mem_xiHeightWindowIndices a b p).mp hp).2.le,
      ((mem_xiHeightWindowIndices a b p).mp hp).1.2⟩) hf hg
  simp only [one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [card_xiHeightWindowIndices hab] at h
  rw [h]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  dsimp only
  rw [filter_xiHeightWindowIndices_le a hx.2, card_xiHeightWindowIndices hx.1]

/-- The classical boundary form retains the full counting function at both endpoints. -/
theorem sum_xi_height_window_eq_boundary_sub_integral {a b : ℝ} {f g : ℝ → ℝ}
    (hab : a ≤ b) (hf : ∀ x ∈ Icc a b, HasDerivAt f (g x) x)
    (hg : IntegrableOn g (Icc a b)) :
    ∑ p ∈ xiHeightWindowIndices a b, f (riemannXiDivisorZeroValue p).im =
      (xiZeroCount b : ℝ) * f b - (xiZeroCount a : ℝ) * f a -
        ∫ x in Icc a b, (xiZeroCount x : ℝ) * g x := by
  have hint : (∫ x in Icc a b, g x) = f b - f a := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (by simpa only [uIcc_of_le hab] using hf)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hg)
  rw [sum_xi_height_window_eq_count_sub_integral hab hf hg]
  simp_rw [sub_mul]
  rw [integral_sub (integrableOn_xiZeroCount_mul hg) (hg.const_mul _),
    integral_const_mul, hint]
  ring

end

end PrimeFactorUnimodality
