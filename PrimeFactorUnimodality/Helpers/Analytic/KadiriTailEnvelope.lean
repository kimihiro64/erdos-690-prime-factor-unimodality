import PrimeFactorUnimodality.Helpers.Analytic.KadiriBootstrapBudget
import PrimeFactorUnimodality.Helpers.Analytic.XiLehmanAffine

/-! # Harmonic tail and pole envelopes for the actual correction

Sum the logarithmic Lehman envelope over arbitrary natural harmonics,
retaining the exact zero-height subtraction. The pole coefficient decreases
with positive base height. Nonnegativity of the actual tail majorant is
derived from the proved bound on the actual nonnegative zero sum.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The pole coefficient is nonnegative for nonnegative polynomial coefficients. -/
theorem kadiriPoleCoefficient_nonneg (S : Finset ℕ) (a : ℕ → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) (t : ℝ) : 0 ≤ kadiriPoleCoefficient S a t :=
  Finset.sum_nonneg (fun i hi => div_nonneg (ha i (Finset.mem_of_mem_erase hi)) (sq_nonneg _))

/-- The positive-height pole coefficient is antitone. -/
theorem antitoneOn_kadiriPoleCoefficient (S : Finset ℕ) (a : ℕ → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) :
    AntitoneOn (kadiriPoleCoefficient S a) (Set.Ioi 0) := by
  intro t ht u hu htu
  apply Finset.sum_le_sum
  intro i hi
  have hi₀ : 0 < (i : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Finset.mem_erase.mp hi).1)
  exact div_le_div_of_nonneg_left (ha i (Finset.mem_of_mem_erase hi))
    (sq_pos_of_pos (mul_pos hi₀ ht))
    ((sq_le_sq₀ (mul_nonneg hi₀.le ht.le) (mul_nonneg hi₀.le hu.le)).mpr
      (mul_le_mul_of_nonneg_left htu hi₀.le))

/-- Weighted logarithmic slope, omitting the zero harmonic. -/
def kadiriTailLogCoefficient (T H : ℝ) (S : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  xiLehmanLogCoefficient T H * ∑ i ∈ S.erase 0, a i

/-- Weighted constant term, preserving the exact finite low-zero subtraction. -/
def kadiriTailAffineConstant (T H : ℝ) (S : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  a 0 * xiLehmanTailMajorant 0 H +
    ∑ i ∈ S.erase 0, a i *
      (xiLehmanLogCoefficient T H * Real.log (i : ℝ) + xiLehmanAffineConstant T H)

/-- The weighted slope is nonnegative. -/
theorem kadiriTailLogCoefficient_nonneg {T H : ℝ} (hT : 0 < T) (hH : 0 < H)
    (S : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ i ∈ S, 0 ≤ a i) :
    0 ≤ kadiriTailLogCoefficient T H S a :=
  mul_nonneg (xiLehmanLogCoefficient_nonneg hT hH)
    (Finset.sum_nonneg (fun i hi => ha i (Finset.mem_of_mem_erase hi)))

/-- The constant term is nonnegative without assuming a low-zero numerical certificate. -/
theorem kadiriTailAffineConstant_nonneg {T H : ℝ} (hT : 0 < T) (hH : 0 < H)
    (S : Finset ℕ) (h₀ : 0 ∈ S) (a : ℕ → ℝ) (ha : ∀ i ∈ S, 0 ≤ a i) :
    0 ≤ kadiriTailAffineConstant T H S a := by
  have hzero : 0 ≤ xiLehmanTailMajorant 0 H :=
    (xiHeightTail_nonneg 0 H).trans (xiHeightTail_le_lehmanMajorant hH (by simp))
  apply add_nonneg (mul_nonneg (ha 0 h₀) hzero)
  apply Finset.sum_nonneg
  intro i hi
  have hi₁ : (1 : ℝ) ≤ i := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finset.mem_erase.mp hi).1
  exact mul_nonneg (ha i (Finset.mem_of_mem_erase hi))
    (add_nonneg (mul_nonneg (xiLehmanLogCoefficient_nonneg hT hH) (Real.log_nonneg hi₁))
      (xiLehmanAffineConstant_nonneg hT hH))

/-- All harmonic tails obey a single affine bound in the base-height logarithm. -/
theorem sum_xiLehmanTailMajorant_le_affine {T t H : ℝ}
    (hT : 2 ≤ T) (ht : T ≤ t) (hH : 4 ≤ H)
    (S : Finset ℕ) (h₀ : 0 ∈ S) (a : ℕ → ℝ) (ha : ∀ i ∈ S, 0 ≤ a i) :
    (∑ i ∈ S, a i * xiLehmanTailMajorant ((i : ℝ) * t) H) ≤
      kadiriTailLogCoefficient T H S a * Real.log t + kadiriTailAffineConstant T H S a := by
  have htpos : 0 < t := by linarith
  have hs : (∑ i ∈ S.erase 0, a i * xiLehmanTailMajorant ((i : ℝ) * t) H) ≤
      ∑ i ∈ S.erase 0, a i * (xiLehmanLogCoefficient T H * Real.log t +
        (xiLehmanLogCoefficient T H * Real.log (i : ℝ) + xiLehmanAffineConstant T H)) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi₁ : (1 : ℝ) ≤ i := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finset.mem_erase.mp hi).1
    have hi₀ : 0 < (i : ℝ) := by linarith
    have hit := mul_pos hi₀ htpos
    apply mul_le_mul_of_nonneg_left _ (ha i (Finset.mem_of_mem_erase hi))
    simp only [xiLehmanTailMajorant, hit.ne', ↓reduceIte, abs_of_pos hit]
    have hb := xiLehmanHighBound_le_affine hT
      (ht.trans (by nlinarith : t ≤ (i : ℝ) * t)) hH
    rw [Real.log_mul hi₀.ne' htpos.ne'] at hb
    convert! hb using 1
    ring
  rw [← Finset.add_sum_erase S _ h₀]
  simp only [Nat.cast_zero, zero_mul]
  apply (add_le_add le_rfl hs).trans_eq
  unfold kadiriTailLogCoefficient kadiriTailAffineConstant
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

/-- At the proved high cutoff, the actual weighted majorant is nonnegative. -/
theorem sum_xiLehmanTailMajorant_nonneg {t H : ℝ} (ht : 10 ^ 9 ≤ t) (hH : 0 < H)
    (S : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ i ∈ S, 0 ≤ a i) :
    0 ≤ ∑ i ∈ S, a i * xiLehmanTailMajorant ((i : ℝ) * t) H :=
  (Finset.sum_nonneg (fun i hi => mul_nonneg (ha i hi) (xiHeightTail_nonneg _ _))).trans
    (sum_xiHeightTail_nat_harmonics_le S a ha ht hH)

end

end PrimeFactorUnimodality
