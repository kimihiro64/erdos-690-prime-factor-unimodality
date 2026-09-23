import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPhaseBudget
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPhaseConjugation
import PrimeFactorUnimodality.Helpers.Analytic.XiTuringEnumeration

/-! # Complete positive zero rows supply the actual phase-budget input

The coefficient profile is defined for an arbitrary enclosed real ordinate,
independently of the noncomputable divisor labels. Saturation of the total
count chooses one complete family once, then every smoothing order, center
and sample uses that same family. Numerical enclosures may cover the entire
row interval without identifying the zero within it.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Finset intervalIntegral

/-- A label-independent centered coefficient on the critical line. -/
def dusartBoxOrdinateCoefficient (m : ℕ) (s u γ : ℝ) : ℂ :=
  iteratedBoxAverageComplex s (m + 3)
    (fun t => (t : ℂ) ^ ((1 / 2 : ℂ) + γ * I) / ((1 / 2 : ℂ) + γ * I)) 1 *
      exp (I * ((u * γ : ℝ) : ℂ))

/-- The ordinate profile is the actual coefficient at every critical-line divisor label. -/
theorem dusartBoxZeroCoefficient_eq_ordinate (m : ℕ) (s u : ℝ)
    {p : RiemannXiDivisorZeroIndex} (hp : (riemannXiDivisorZeroValue p).re = 1 / 2) :
    dusartBoxZeroCoefficient m s u p =
      dusartBoxOrdinateCoefficient m s u (riemannXiDivisorZeroValue p).im := by
  have he : riemannXiDivisorZeroValue p =
      (1 / 2 : ℂ) + (riemannXiDivisorZeroValue p).im * I := by
    apply Complex.ext <;> simp [hp]
  unfold dusartBoxZeroCoefficient dusartBoxOrdinateCoefficient
  conv_lhs => arg 1; arg 3; ext t; rw [he]

namespace XiSignRows

/-- The same complete enclosed ordinate family represents all phase sums. -/
theorem Valid.exists_phase_ordinates {n : ℕ} {rows : Fin n → XiSignRow}
    {a b : ℚ} {T : ℝ} (h : Valid rows a b) (ha : 0 ≤ a) (hb : (b : ℝ) ≤ T)
    (hcount : xiStrictZeroCount T ≤ n) :
    ∃ γ : Fin n → ℝ,
      (∀ i, γ i ∈ Set.Ioo ((rows i).lower : ℝ) (rows i).upper) ∧
      ∀ (m : ℕ) (s u v : ℝ), 0 ≤ s →
        dusartBoxLowPhaseSum m s u T v =
          ((2 * (∑ i, dusartBoxOrdinateCoefficient m s u (γ i) *
            exp (I * ((v * γ i : ℝ) : ℂ))).re : ℝ) : ℂ) := by
  classical
  obtain ⟨f, hf, hi, he⟩ := h.exists_complete_indices ha hb hcount
  refine ⟨fun i => (riemannXiDivisorZeroValue (f i)).im, fun i => (hi i).2, ?_⟩
  intro m s u v hs
  have hsum : (∑ p ∈ xiStrictPositiveHeightIndices T, dusartBoxZeroCoefficient m s u p *
      exp (I * ((v * (riemannXiDivisorZeroValue p).im : ℝ) : ℂ))) =
      ∑ i, dusartBoxOrdinateCoefficient m s u (riemannXiDivisorZeroValue (f i)).im *
        exp (I * ((v * (riemannXiDivisorZeroValue (f i)).im : ℝ) : ℂ)) := by
    rw [he, sum_map]
    apply sum_congr rfl
    intro i hi'
    exact congrArg (fun c => c * exp (I *
      ((v * (riemannXiDivisorZeroValue (f i)).im : ℝ) : ℂ)))
        (dusartBoxZeroCoefficient_eq_ordinate m s u (hi i).1)
  rw [dusartBoxLowPhaseSum_eq_twice_re m hs, hsum]

/-- A uniform enclosure over the rational zero rows controls the full signed phase sum. -/
theorem Valid.norm_phase_sub_real_enclosure_le {n : ℕ} {rows : Fin n → XiSignRow}
    {a b : ℚ} {T : ℝ} (h : Valid rows a b) (ha : 0 ≤ a) (hb : (b : ℝ) ≤ T)
    (hcount : xiStrictZeroCount T ≤ n) (m : ℕ) {s : ℝ} (hs : 0 ≤ s) (u v : ℝ)
    {z : ℂ} {e : ℝ}
    (hbound : ∀ γ : Fin n → ℝ,
      (∀ i, γ i ∈ Set.Ioo ((rows i).lower : ℝ) (rows i).upper) →
      ‖(∑ i, dusartBoxOrdinateCoefficient m s u (γ i) *
        exp (I * ((v * γ i : ℝ) : ℂ))) - z‖ ≤ e) :
    ‖dusartBoxLowPhaseSum m s u T v - ((2 * z.re : ℝ) : ℂ)‖ ≤ 2 * e := by
  obtain ⟨γ, hγ, he⟩ := h.exists_phase_ordinates ha hb hcount
  have hreal := (abs_re_le_norm _).trans (hbound γ hγ)
  rw [he m s u v hs, ← ofReal_sub, norm_real, Real.norm_eq_abs, ← mul_sub, abs_mul]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left (by simpa only [sub_re] using hreal) (by norm_num)

/-- The real positive-sum enclosure gives the phase bound without doubling the data. -/
theorem Valid.norm_phase_le_of_enclosure {n : ℕ} {rows : Fin n → XiSignRow}
    {a b : ℚ} {T : ℝ} (h : Valid rows a b) (ha : 0 ≤ a) (hb : (b : ℝ) ≤ T)
    (hcount : xiStrictZeroCount T ≤ n) (m : ℕ) {s : ℝ} (hs : 0 ≤ s) (u v : ℝ)
    {z : ℂ} {e : ℝ}
    (hbound : ∀ γ : Fin n → ℝ,
      (∀ i, γ i ∈ Set.Ioo ((rows i).lower : ℝ) (rows i).upper) →
      ‖(∑ i, dusartBoxOrdinateCoefficient m s u (γ i) *
        exp (I * ((v * γ i : ℝ) : ℂ))) - z‖ ≤ e) :
    ‖dusartBoxLowPhaseSum m s u T v‖ ≤ 2 * |z.re| + 2 * e := by
  have he := h.norm_phase_sub_real_enclosure_le ha hb hcount m hs u v hbound
  have hn := (norm_le_norm_add_norm_sub' (dusartBoxLowPhaseSum m s u T v)
    ((2 * z.re : ℝ) : ℂ)).trans (add_le_add le_rfl he)
  simpa only [norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using hn

/-- Complete checked zero rows and their numerical enclosure feed the actual psi average. -/
theorem Valid.abs_psi_average_le_of_phase_enclosure {n : ℕ} {rows : Fin n → XiSignRow}
    {a b : ℚ} {T : ℝ} (h : Valid rows a b) (ha : 0 ≤ a) (hb : (b : ℝ) ≤ T)
    (hcount : xiStrictZeroCount T ≤ n) (m : ℕ) {s x : ℝ} (u : ℝ)
    (hs : 0 < s) (hx : 1 < x) (hT : 10 < T) {z : ℂ} {e : ℝ}
    (hbound : ∀ γ : Fin n → ℝ,
      (∀ i, γ i ∈ Set.Ioo ((rows i).lower : ℝ) (rows i).upper) →
      ‖(∑ i, dusartBoxOrdinateCoefficient m s u (γ i) *
        exp (I * (((Real.log x - u) * γ i : ℝ) : ℂ))) - z‖ ≤ e) :
    |dusartPsiAverageError (m + 3) (s * x) x| / x ≤
      dusartBoxPhaseBudget m s x T (2 * |z.re| + 2 * e) :=
  abs_dusartPsiAverageError_div_le_phase m u hs hx hT (h.low_criticalLine ha hb hcount)
    (h.norm_phase_le_of_enclosure ha hb hcount m hs.le u (Real.log x - u) hbound)

/-- Turing padding closes the count obligation before the actual psi-average consumer. -/
theorem Valid.abs_psi_average_le_of_turing_phase_enclosure {n k : ℕ}
    {rows : Fin n → XiSignRow} {padding : Fin k → XiSignRow} {a b : ℚ}
    (h : Valid rows 0 a) (hpad : Valid padding a b) (ha : 32 ≤ a)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a +
      turingCountErrorBudget a b <
        (b : ℝ) - a + (completedAreaRat (Fin.append rows padding) a b : ℝ))
    (m : ℕ) {s x : ℝ} (u : ℝ) (hs : 0 < s) (hx : 1 < x) {z : ℂ} {e : ℝ}
    (hbound : ∀ γ : Fin n → ℝ,
      (∀ i, γ i ∈ Set.Ioo ((rows i).lower : ℝ) (rows i).upper) →
      ‖(∑ i, dusartBoxOrdinateCoefficient m s u (γ i) *
        exp (I * (((Real.log x - u) * γ i : ℝ) : ℂ))) - z‖ ≤ e) :
    |dusartPsiAverageError (m + 3) (s * x) x| / x ≤
      dusartBoxPhaseBudget m s x a (2 * |z.re| + 2 * e) := by
  have har : (32 : ℝ) ≤ a := by exact_mod_cast ha
  exact h.abs_psi_average_le_of_phase_enclosure le_rfl le_rfl
    (h.strictCount_le_of_turing_padding hpad ha hmargin) m u hs hx (by linarith) hbound

end XiSignRows

end

end PrimeFactorUnimodality
