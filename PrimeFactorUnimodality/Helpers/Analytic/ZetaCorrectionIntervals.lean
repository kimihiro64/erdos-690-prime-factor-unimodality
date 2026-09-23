import PrimeFactorUnimodality.Helpers.Analytic.ComplexIntervalInverse
import PrimeFactorUnimodality.Helpers.Analytic.DirichletEndpointIntervals
import PrimeFactorUnimodality.Helpers.Analytic.EulerBernoulliIntervals

/-! # Executable enclosure checks for the complete short Euler correction

The shared endpoint amplitude and logarithm are reused at every sample.
Sample heights may be any real values inside their checked intervals.
Successful checks retain every Bernoulli term and imply the exact correction
premise of the existing zeta-grid theorem; the Euler remainder is not removed.
-/

namespace PrimeFactorUnimodality

open Complex LeanCert.Core Polynomial

namespace ZetaCorrectionIntervals

/-- A rectangle on the critical line with the supplied real-height interval. -/
def critical (T : IntervalRat) : ComplexInterval := ⟨IntervalRat.singleton (1 / 2), T⟩

/-- Exact critical-line membership requires only the height enclosure. -/
theorem mem_critical {t : ℝ} {T : IntervalRat} (ht : t ∈ T) :
    (1 / 2 : ℂ) + t * I ∈ critical T := by
  constructor
  · norm_num [critical, IntervalRat.mem_def, IntervalRat.singleton]
  · simpa [critical] using ht

/-- The short rational-algebraic factor, rejecting an uncertified reciprocal. -/
def factor? (N : ℕ) (T : IntervalRat) (coefficients : List ℚ) : Option ComplexInterval :=
  let S := critical T
  let W := ComplexInterval.scale (1 / (N : ℚ)) S
  ((S.add (ComplexInterval.point ⟨-1, 0⟩)).inverse?).map (fun R =>
    ((ComplexInterval.scale N R).add (ComplexInterval.point ⟨-1 / 2, 0⟩)).add
      (eulerBernoulliInterval N S 1 W coefficients))

/-- The optional algebraic enclosure contains the whole factored correction polynomial. -/
theorem mem_factor {N m : ℕ} {T : IntervalRat} {t : ℝ} (ht : t ∈ T)
    {coefficients : List ℚ} (hb : coefficients = eulerBernoulliCoefficients 1 m)
    {J : ComplexInterval} (hJ : factor? N T coefficients = some J) :
    let s := (1 / 2 : ℂ) + t * I
    (N : ℂ) / (s - 1) - 1 / 2 +
      ((List.range' 1 m).map (fun j =>
        (bernoulliNormalizedReal (j + 1) 0 : ℂ) *
          (zetaRisingFactor s j / (N : ℂ) ^ j))).sum ∈ J := by
  dsimp only
  let s : ℂ := (1 / 2 : ℂ) + t * I
  have hs : s ∈ critical T := mem_critical ht
  have hm : (-1 : ℂ) ∈ ComplexInterval.point ⟨-1, 0⟩ := by
    simpa using ComplexInterval.mem_constant (-1)
  have hh : (-1 / 2 : ℂ) ∈ ComplexInterval.point ⟨-1 / 2, 0⟩ := by
    simpa using ComplexInterval.mem_constant (-1 / 2)
  have hstart : zetaRisingFactor s 1 / (N : ℂ) ^ 1 ∈
      ComplexInterval.scale (1 / (N : ℚ)) (critical T) := by
    simpa [zetaRisingFactor, div_eq_mul_inv, mul_comm] using
      ComplexInterval.mem_scale (1 / (N : ℚ)) hs
  have hsum := mem_eulerBernoulliInterval N hs 1 m hstart
  rw [← hb] at hsum
  unfold factor? at hJ
  dsimp only at hJ
  cases hi : ((critical T).add (ComplexInterval.point ⟨-1, 0⟩)).inverse? with
  | none => simp only [hi, Option.map_none] at hJ; cases hJ
  | some R =>
    rw [hi, Option.map_some] at hJ
    cases Option.some.inj hJ
    have hrec : (s - 1)⁻¹ ∈ R := by
      simpa only [sub_eq_add_neg] using
        ComplexInterval.mem_inverse hi (ComplexInterval.mem_add hs hm)
    have h := ComplexInterval.mem_add
      (ComplexInterval.mem_add (ComplexInterval.mem_scale (N : ℚ) hrec) hh) hsum
    simpa only [s, Rat.cast_natCast, div_eq_mul_inv, sub_eq_add_neg, neg_mul] using h

/-- Multiply the short factor by the one shared-endpoint Dirichlet atom. -/
def evaluate? (d : DirichletEndpointIntervals) (c : SharedTaylorIntervals)
    (P T : IntervalRat) (turns : ℤ) (coefficients : List ℚ) : Option ComplexInterval :=
  (factor? d.cutoff T coefficients).map (fun J => (d.weight c P T turns).mul J)

/-- Every successfully constructed rectangle encloses the actual Euler correction. -/
theorem mem_evaluate {d : DirichletEndpointIntervals} (hd : d.Valid)
    {c : SharedTaylorIntervals} (hc : c.Prepared) {P T : IntervalRat}
    (hpi : Real.pi ∈ P) {t : ℝ} (ht : t ∈ T) (turns : ℤ)
    {m : ℕ} {coefficients : List ℚ} (hb : coefficients = eulerBernoulliCoefficients 1 m)
    {J : ComplexInterval} (hJ : evaluate? d c P T turns coefficients = some J) :
    zetaEulerCorrection d.cutoff ((1 / 2 : ℂ) + t * I) m ∈ J := by
  unfold evaluate? at hJ
  cases hf : factor? d.cutoff T coefficients with
  | none => simp only [hf, Option.map_none] at hJ; cases hJ
  | some F =>
    rw [hf, Option.map_some] at hJ
    cases Option.some.inj hJ
    rw [zetaEulerCorrection_eq_list d.cutoff m hd.1]
    exact ComplexInterval.mem_mul
      (DirichletEndpointIntervals.mem_weight hd hc hpi ht turns) (mem_factor ht hb hf)

/-- A complete squared-norm error check; failed interval inversion is rejected. -/
def check (d : DirichletEndpointIntervals) (c : SharedTaylorIntervals)
    (P T : IntervalRat) (turns : ℤ) (coefficients : List ℚ) (q : RationalPoint) (e : ℚ) : Bool :=
  match evaluate? d c P T turns coefficients with
  | none => false
  | some J => J.close q e

/-- Successful executable checks prove the full correction error bound. -/
theorem norm_sub_le_of_check {d : DirichletEndpointIntervals} (hd : d.Valid)
    {c : SharedTaylorIntervals} (hc : c.Prepared) {P T : IntervalRat}
    (hpi : Real.pi ∈ P) {t : ℝ} (ht : t ∈ T) (turns : ℤ)
    {m : ℕ} {coefficients : List ℚ} (hb : coefficients = eulerBernoulliCoefficients 1 m)
    {q : RationalPoint} {e : ℚ} (h : check d c P T turns coefficients q e = true) :
    ‖zetaEulerCorrection d.cutoff ((1 / 2 : ℂ) + t * I) m - q.toComplex‖ ≤ (e : ℝ) := by
  unfold check at h
  cases hj : evaluate? d c P T turns coefficients with
  | none => simp only [hj, Bool.false_eq_true] at h
  | some J =>
    rw [hj] at h
    exact ComplexInterval.norm_sub_le_of_close h (mem_evaluate hd hc hpi ht turns hb hj)

end ZetaCorrectionIntervals

end PrimeFactorUnimodality
