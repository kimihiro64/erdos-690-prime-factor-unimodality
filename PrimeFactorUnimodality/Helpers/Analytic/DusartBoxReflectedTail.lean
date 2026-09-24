import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserTail
import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiDivisorPairing

/-! # Reflection improves the complete high-zero box tail

Pair each multiplicity label with its same-height reflection. At least one
member lies on or to the left of the critical line, so only one member pays
the zero-free-region bound. The other retains square-root damping and the
full inverse-height power. Exact reindexing includes critical-line fixed
points, both ordinate signs and every zero at the closed cutoff.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real intervalIntegral
open Complex (sub_im one_im conj_im sub_re one_re conj_re)
open scoped ComplexConjugate

/-- A left-half-strip atom retains both critical-line damping and full height decay. -/
theorem norm_dusartBox_atom_le_half_power (m : ℕ) {h x : ℝ} {s : ℂ}
    (hh : 0 < h) (hx : 1 < x) (hγ : 0 < |s.im|)
    (hβ0 : 0 ≤ s.re) (hβ : s.re ≤ 1 / 2) :
    ‖iteratedBoxAverageComplex h (m + 3) (fun t => (t : ℂ) ^ s / s) x‖ ≤
      (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
        (exp (-(1 / 2) * Real.log x) * logDampedPower 0 (m + 4 : ℕ) |s.im|) := by
  have hs : s ≠ 0 := fun he => (abs_pos.mp hγ) (by simp [he])
  have hb := norm_dusartBox_paired_atom_le_height_gap m hh hx
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (abs_pos.mp hγ) hβ0 (by linarith)
  rw [finiteLaplace_dusartBoxWeight_add_inv m hh hx hs] at hb
  refine hb.trans_eq ?_
  rw [logDampedPower_eq_rpow_mul hγ, Real.rpow_neg hγ.le, Real.rpow_natCast]
  simp only [neg_zero, zero_div, Real.exp_zero, mul_one]
  ring

/-- Each actual reflected pair pays one region term and one critical-line term. -/
theorem norm_dusartBox_xi_reflected_pair_le (m : ℕ) {h x R T : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) (hT : 1 < T)
    (hreg : ∀ p : RiemannXiDivisorZeroIndex, T ≤ |(riemannXiDivisorZeroValue p).im| →
      (riemannXiDivisorZeroValue p).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue p).im|))
    (p : RiemannXiDivisorZeroIndex) (hp : T ≤ |(riemannXiDivisorZeroValue p).im|) :
    ‖iteratedBoxAverageComplex h (m + 3)
      (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p / riemannXiDivisorZeroValue p) x‖ +
    ‖iteratedBoxAverageComplex h (m + 3)
      (fun t => (t : ℂ) ^ (1 - conj (riemannXiDivisorZeroValue p)) /
        (1 - conj (riemannXiDivisorZeroValue p))) x‖ ≤
      (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
        (logDampedPower (Real.log x / R) (m + 4 : ℕ) |(riemannXiDivisorZeroValue p).im| +
          exp (-(1 / 2) * Real.log x) *
            logDampedPower 0 (m + 4 : ℕ) |(riemannXiDivisorZeroValue p).im|) := by
  have hγ := hT.trans_le hp
  have hstrip := riemannXi_zero_mem_critical_strip (riemannXiDivisorZeroValue_eq_zero p)
  have hrp : T ≤ |(riemannXiDivisorZeroValue (riemannXiDivisorSameHeightReflection p)).im| := by
    simpa using hp
  have hrstrip := riemannXi_zero_mem_critical_strip
    (riemannXiDivisorZeroValue_eq_zero (riemannXiDivisorSameHeightReflection p))
  have hmain := norm_dusartBox_atom_le_abs_rosser_kernel m hh hx hR hγ hstrip.1 (hreg p hp)
  have hrmain := norm_dusartBox_atom_le_abs_rosser_kernel m hh hx hR
    (hT.trans_le hrp) hrstrip.1 (hreg _ hrp)
  simp only [riemannXiDivisorZeroValue_sameHeightReflection, sub_im, one_im,
    conj_im, sub_neg_eq_add, zero_add] at hrmain hrstrip
  by_cases hβ : (riemannXiDivisorZeroValue p).re ≤ 1 / 2
  · have hhalf := norm_dusartBox_atom_le_half_power m hh hx
      (lt_trans zero_lt_one hγ) hstrip.1 hβ
    exact (add_le_add hhalf hrmain).trans_eq (by ring)
  · have hrβ : (1 - conj (riemannXiDivisorZeroValue p)).re ≤ 1 / 2 := by
      simp only [sub_re, one_re, conj_re]
      linarith
    have hrγ : 0 < |(1 - conj (riemannXiDivisorZeroValue p)).im| := by
      simpa using (lt_trans zero_lt_one hγ)
    have hhalf := norm_dusartBox_atom_le_half_power m hh hx hrγ hrstrip.1 hrβ
    simp only [sub_im, one_im, conj_im, sub_neg_eq_add, zero_add] at hhalf
    exact (add_le_add hmain hhalf).trans_eq (by ring)

/-- Reindexing the complete convergent tail yields the reflected half-sum bound. -/
theorem norm_dusartBoxXiHighSum_le_reflected_tail (m : ℕ) {h x R T : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) (hT : 1 < T)
    (hreg : ∀ p : RiemannXiDivisorZeroIndex, T ≤ |(riemannXiDivisorZeroValue p).im| →
      (riemannXiDivisorZeroValue p).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue p).im|)) :
    ‖dusartBoxXiHighSum m h x T‖ ≤
      (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
        ((xiRosserAbsoluteTail (Real.log x / R) (m + 4 : ℕ) T +
          exp (-(1 / 2) * Real.log x) * xiRosserAbsoluteTail 0 (m + 4 : ℕ) T) / 2) := by
  let P : ℂ → Prop := fun z => T ≤ |z.im|
  let G : ℂ → ℝ := fun z =>
    ‖iteratedBoxAverageComplex h (m + 3) (fun t => (t : ℂ) ^ z / z) x‖
  let C := 2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)
  have hP : ∀ z, P z ↔ P (1 - conj z) := by intro z; simp [P]
  have hG : Summable (fun p : RiemannXiDivisorZeroIndex => G (riemannXiDivisorZeroValue p)) :=
    (summable_dusartBox_xi_power_average m hh hx).norm
  have hs := hG.subtype (fun p => P (riemannXiDivisorZeroValue p))
  have hr := (hG.comp_injective riemannXiDivisorSameHeightReflection.injective).subtype
    (fun p => P (riemannXiDivisorZeroValue p))
  change Summable (fun p : {p : RiemannXiDivisorZeroIndex // P (riemannXiDivisorZeroValue p)} =>
    G (riemannXiDivisorZeroValue (riemannXiDivisorSameHeightReflection p.1))) at hr
  simp only [riemannXiDivisorZeroValue_sameHeightReflection] at hr
  have hq : (2 : ℝ) ≤ (m + 4 : ℕ) := by norm_cast; omega
  have hd := summable_xi_abs_logDampedPower
    (div_nonneg (Real.log_pos hx).le hR.le) hq hT (P := fun p => P (riemannXiDivisorZeroValue p))
    (fun _ hp => hp)
  have hu := summable_xi_abs_logDampedPower (a := 0) le_rfl hq hT
    (P := fun p => P (riemannXiDivisorZeroValue p)) (fun _ hp => hp)
  have hpoint (p : {p : RiemannXiDivisorZeroIndex // P (riemannXiDivisorZeroValue p)}) :
      G (riemannXiDivisorZeroValue p.1) + G (1 - conj (riemannXiDivisorZeroValue p.1)) ≤
        C * (logDampedPower (Real.log x / R) (m + 4 : ℕ) |(riemannXiDivisorZeroValue p.1).im| +
          exp (-(1 / 2) * Real.log x) *
            logDampedPower 0 (m + 4 : ℕ) |(riemannXiDivisorZeroValue p.1).im|) :=
    norm_dusartBox_xi_reflected_pair_le m hh hx hR hT hreg p.1 p.2
  have hmajor : Summable (fun p : {p : RiemannXiDivisorZeroIndex // P (riemannXiDivisorZeroValue p)} =>
      C * (logDampedPower (Real.log x / R) (m + 4 : ℕ) |(riemannXiDivisorZeroValue p.1).im| +
        exp (-(1 / 2) * Real.log x) *
          logDampedPower 0 (m + 4 : ℕ) |(riemannXiDivisorZeroValue p.1).im|)) :=
    (hd.add (hu.mul_left (exp (-(1 / 2) * Real.log x)))).mul_left C
  have hsum := (hs.add hr).tsum_le_tsum hpoint hmajor
  calc
    ‖dusartBoxXiHighSum m h x T‖ ≤ _ := norm_tsum_le_tsum_norm hs
    _ = (1 / 2 : ℝ) * ∑' p : {p : RiemannXiDivisorZeroIndex // P (riemannXiDivisorZeroValue p)},
        (G (riemannXiDivisorZeroValue p.1) + G (1 - conj (riemannXiDivisorZeroValue p.1))) :=
      tsum_xi_divisor_subtype_eq_half_pair P hP hG
    _ ≤ (1 / 2 : ℝ) * ∑' p : {p : RiemannXiDivisorZeroIndex // P (riemannXiDivisorZeroValue p)},
        C * (logDampedPower (Real.log x / R) (m + 4 : ℕ) |(riemannXiDivisorZeroValue p.1).im| +
          exp (-(1 / 2) * Real.log x) *
            logDampedPower 0 (m + 4 : ℕ) |(riemannXiDivisorZeroValue p.1).im|) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = _ := by
      rw [tsum_mul_left, hd.tsum_add (hu.mul_left _), tsum_mul_left]
      unfold xiRosserAbsoluteTail
      dsimp only [P, C]
      ring

end

end PrimeFactorUnimodality
