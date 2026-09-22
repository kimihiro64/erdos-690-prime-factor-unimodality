import PrimeFactorUnimodality.Helpers.Analytic.XiHeightTailEndpoint
import PrimeFactorUnimodality.Helpers.Analytic.XiZeroCountingImproper
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.ReciprocalSquarePairDeriv

/-! # Unconditional counting-integral identity for the Lehman pair

The actual strict positive zero tail equals its counting-function integral
minus the lower boundary. Absolute integrability and disappearance of the
upper boundary follow from the already-proved zero-kernel summability,
not a numerical zero-counting theorem. The closed height tail also retains
the exact cutoff multiplicity.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology

/-- The strict positive pair tail is summable, without losing any divisor labels. -/
theorem summable_xi_strict_height_pair {t H : ℝ} (ht : 0 ≤ t) (hH : 0 < H) :
    Summable (fun p : {p : RiemannXiDivisorZeroIndex //
      t + H < (riemannXiDivisorZeroValue p).im} =>
        Real.reciprocalSquarePair t (riemannXiDivisorZeroValue p.1).im) := by
  let e : {p : RiemannXiDivisorZeroIndex // t + H < (riemannXiDivisorZeroValue p).im} →
      {p : RiemannXiDivisorZeroIndex // |t| + H ≤ (riemannXiDivisorZeroValue p).im} :=
    fun p => ⟨p.1, by simpa only [abs_of_nonneg ht] using p.2.le⟩
  have he : Function.Injective e := by
    intro p q h
    apply Subtype.ext
    exact congrArg (fun r : {p : RiemannXiDivisorZeroIndex //
      |t| + H ≤ (riemannXiDivisorZeroValue p).im} => r.val) h
  have hclosed : Summable (fun p : {p : RiemannXiDivisorZeroIndex //
      |t| + H ≤ (riemannXiDivisorZeroValue p).im} =>
      Real.reciprocalSquarePair t (riemannXiDivisorZeroValue p.1).im) :=
    summable_xi_positive_height_pair hH t
  exact hclosed.comp_injective (i := e) he

/-- The full actual count times the pair has zero upper boundary, unconditionally. -/
theorem tendsto_xiZeroCount_mul_reciprocalSquarePair {t H : ℝ} (ht : 0 ≤ t) (hH : 0 < H) :
    Tendsto (fun T => (xiZeroCount T : ℝ) * Real.reciprocalSquarePair t T) atTop (𝓝 0) := by
  apply tendsto_xiZeroCount_mul_of_antitone (a := t + H) (by linarith)
    (summable_xi_strict_height_pair ht hH)
  · intro x hx
    exact (Real.reciprocalSquarePair_pos ht (by have : t + H < x := hx; linarith)).le
  · exact (Real.antitoneOn_reciprocalSquarePair ht).mono (Ioi_subset_Ioi (by linarith))
  · exact Real.tendsto_reciprocalSquarePair_atTop t

/-- The strict tail equals an actually integrable nonnegative counting integral. -/
theorem xi_strict_pair_tail_eq_count_integral {t H : ℝ} (ht : 0 ≤ t) (hH : 0 < H) :
    IntegrableOn (fun x => (xiZeroCount x : ℝ) * (2 / (x - t) ^ 3 + 2 / (x + t) ^ 3))
      (Ioi (t + H)) ∧
      (∑' p : {p : RiemannXiDivisorZeroIndex // t + H < (riemannXiDivisorZeroValue p).im},
        Real.reciprocalSquarePair t (riemannXiDivisorZeroValue p.1).im) =
      (∫ x in Ioi (t + H), (xiZeroCount x : ℝ) * (2 / (x - t) ^ 3 + 2 / (x + t) ^ 3)) -
        (xiZeroCount (t + H) : ℝ) * Real.reciprocalSquarePair t (t + H) := by
  let g (x : ℝ) := -(2 / (x - t) ^ 3 + 2 / (x + t) ^ 3)
  have hp (x : ℝ) (hx : t + H ≤ x) : 0 < x - t ∧ 0 < x + t := by constructor <;> linarith
  have hf (x : ℝ) (hx : x ∈ Ici (t + H)) :
      HasDerivAt (Real.reciprocalSquarePair t) (g x) x :=
    Real.hasDerivAt_reciprocalSquarePair (hp x hx).1.ne' (hp x hx).2.ne'
  have hg (b : ℝ) : IntegrableOn g (Icc (t + H) b) := by
    apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.neg
    apply ContinuousOn.add
    · exact continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow 3)
        (fun x hx => pow_ne_zero _ (hp x hx.1).1.ne')
    · exact continuousOn_const.div ((continuousOn_id.add continuousOn_const).pow 3)
        (fun x hx => pow_ne_zero _ (hp x hx.1).2.ne')
  have hneg (x : ℝ) (hx : x ∈ Ioi (t + H)) : g x ≤ 0 := by
    obtain ⟨hm, hp⟩ := hp x hx.le
    dsimp [g]
    exact neg_nonpos.mpr (add_nonneg (by positivity) (by positivity))
  have h := xi_strict_tail_eq_integral_of_count_boundary (by linarith : 0 ≤ t + H)
    (summable_xi_strict_height_pair ht hH) hf hg hneg
    (tendsto_xiZeroCount_mul_reciprocalSquarePair ht hH)
  have he : (fun x => (xiZeroCount x : ℝ) * g x) =
      fun x => -((xiZeroCount x : ℝ) * (2 / (x - t) ^ 3 + 2 / (x + t) ^ 3)) := by
    funext x
    simp only [g, mul_neg]
  constructor
  · apply h.1.neg.congr_fun _ measurableSet_Ioi
    intro x _
    simp only [Pi.neg_apply, g, mul_neg, neg_neg]
  · rw [he, integral_neg] at h
    linarith [h.2]

/-- The paper's closed height tail has the same integral plus its cutoff multiplicity. -/
theorem xiHeightTail_eq_count_integral_add_boundary {t H : ℝ} (ht : 0 ≤ t) (hH : 0 < H) :
    xiHeightTail t H =
      (∫ x in Ioi (t + H), (xiZeroCount x : ℝ) * (2 / (x - t) ^ 3 + 2 / (x + t) ^ 3)) -
        (xiZeroCount (t + H) : ℝ) * Real.reciprocalSquarePair t (t + H) +
        (xiOrdinateMultiplicity (t + H) : ℝ) * Real.reciprocalSquarePair t (t + H) := by
  rw [xiHeightTail_eq_strict_positive_add_boundary hH, abs_of_nonneg ht,
    (xi_strict_pair_tail_eq_count_integral ht hH).2]

end

end PrimeFactorUnimodality
