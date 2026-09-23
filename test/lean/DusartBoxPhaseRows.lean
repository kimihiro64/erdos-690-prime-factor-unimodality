import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPhaseRows

/-! # One complete ordinate family and the real-enclosure consumer for actual psi -/

open PrimeFactorUnimodality Complex Finset

example {n : ℕ} {rows : Fin n → XiSignRow} {a b : ℚ} {T : ℝ}
    (h : XiSignRows.Valid rows a b) (ha : 0 ≤ a) (hb : (b : ℝ) ≤ T)
    (hc : xiStrictZeroCount T ≤ n) :
    ∃ γ : Fin n → ℝ,
      (∀ i, γ i ∈ Set.Ioo ((rows i).lower : ℝ) (rows i).upper) ∧
      ∀ (m : ℕ) (s u v : ℝ), 0 ≤ s →
        dusartBoxLowPhaseSum m s u T v =
          ((2 * (∑ i, dusartBoxOrdinateCoefficient m s u (γ i) *
            exp (I * ((v * γ i : ℝ) : ℂ))).re : ℝ) : ℂ) :=
  h.exists_phase_ordinates ha hb hc

example {n : ℕ} {rows : Fin n → XiSignRow} {a b : ℚ} {T : ℝ}
    (h : XiSignRows.Valid rows a b) (ha : 0 ≤ a) (hb : (b : ℝ) ≤ T)
    (hc : xiStrictZeroCount T ≤ n) (m : ℕ) {s : ℝ} (hs : 0 ≤ s) (u v : ℝ)
    {z : ℂ} {e : ℝ}
    (he : ∀ γ : Fin n → ℝ,
      (∀ i, γ i ∈ Set.Ioo ((rows i).lower : ℝ) (rows i).upper) →
      ‖(∑ i, dusartBoxOrdinateCoefficient m s u (γ i) *
        exp (I * ((v * γ i : ℝ) : ℂ))) - z‖ ≤ e) :
    ‖dusartBoxLowPhaseSum m s u T v - ((2 * z.re : ℝ) : ℂ)‖ ≤ 2 * e :=
  h.norm_phase_sub_real_enclosure_le ha hb hc m hs u v he

example {n : ℕ} {rows : Fin n → XiSignRow} {a b : ℚ} {T : ℝ}
    (h : XiSignRows.Valid rows a b) (ha : 0 ≤ a) (hb : (b : ℝ) ≤ T)
    (hc : xiStrictZeroCount T ≤ n) (m : ℕ) {s x : ℝ} (u : ℝ)
    (hs : 0 < s) (hx : 1 < x) (hT : 10 < T) {z : ℂ} {e : ℝ}
    (he : ∀ γ : Fin n → ℝ,
      (∀ i, γ i ∈ Set.Ioo ((rows i).lower : ℝ) (rows i).upper) →
      ‖(∑ i, dusartBoxOrdinateCoefficient m s u (γ i) *
        exp (I * (((Real.log x - u) * γ i : ℝ) : ℂ))) - z‖ ≤ e) :
    |dusartPsiAverageError (m + 3) (s * x) x| / x ≤
      dusartBoxPhaseBudget m s x T (2 * |z.re| + 2 * e) :=
  h.abs_psi_average_le_of_phase_enclosure ha hb hc m u hs hx hT he

example {n k : ℕ} {rows : Fin n → XiSignRow} {padding : Fin k → XiSignRow} {a b : ℚ}
    (h : XiSignRows.Valid rows 0 a) (hp : XiSignRows.Valid padding a b) (ha : 32 ≤ a)
    (hm : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a +
      turingCountErrorBudget a b <
        (b : ℝ) - a + (XiSignRows.completedAreaRat (Fin.append rows padding) a b : ℝ))
    (m : ℕ) {s x : ℝ} (u : ℝ) (hs : 0 < s) (hx : 1 < x) {z : ℂ} {e : ℝ}
    (he : ∀ γ : Fin n → ℝ,
      (∀ i, γ i ∈ Set.Ioo ((rows i).lower : ℝ) (rows i).upper) →
      ‖(∑ i, dusartBoxOrdinateCoefficient m s u (γ i) *
        exp (I * (((Real.log x - u) * γ i : ℝ) : ℂ))) - z‖ ≤ e) :
    |dusartPsiAverageError (m + 3) (s * x) x| / x ≤
      dusartBoxPhaseBudget m s x a (2 * |z.re| + 2 * e) :=
  h.abs_psi_average_le_of_turing_phase_enclosure hp ha hm m u hs hx he
