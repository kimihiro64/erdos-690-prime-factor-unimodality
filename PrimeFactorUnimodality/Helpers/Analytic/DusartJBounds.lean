import Mathlib.NumberTheory.Chebyshev

set_option autoImplicit false

/-! # Dusart's anchored prime-counting comparison

This is the function `J` in the proof of the prime-counting estimates in
Dusart, *Estimates of some functions over primes without R.H.* (2010),
Section 6.2. Abel summation starts at an arbitrary `x₀ ≥ 2`: the small
range contributes the exact constant `π(x₀) - θ(x₀) / log x₀`.
Only the theta estimate on `[x₀, x]` is used, not an estimate starting at 2.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- The anchored integral comparison, with signed error coefficient `η`. -/
def dusartJ (k : Nat) (η x₀ x : Real) : Real :=
  (Nat.primeCounting ⌊x₀⌋₊ : Real) - Chebyshev.theta x₀ / Real.log x₀ +
    x / Real.log x + η * x / Real.log x ^ (k + 1) +
    ∫ t in x₀..x, (1 / Real.log t ^ 2 + η / Real.log t ^ (k + 2))

/-- The anchor check contains no integral: it needs only `π`, `θ`, and `log`. -/
theorem dusartJ_self (k : Nat) (η x₀ : Real) :
    dusartJ k η x₀ x₀ = (Nat.primeCounting ⌊x₀⌋₊ : Real) +
      (x₀ - Chebyshev.theta x₀) / Real.log x₀ + η * x₀ / Real.log x₀ ^ (k + 1) := by
  simp only [dusartJ, intervalIntegral.integral_same, add_zero]
  ring

private theorem theta_integrable_from {x₀ x : Real}
    (h₀ : 2 ≤ x₀) (hx : x₀ ≤ x) :
    IntervalIntegrable (fun t : Real => Chebyshev.theta t /
      (t * Real.log t ^ 2)) MeasureTheory.volume x₀ x := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
  exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq x).mono_set
    (by intro t ht; exact ⟨h₀.trans ht.1.le, ht.2⟩)

/-- Continuity of the smooth integrand away from the logarithmic singularity. -/
theorem continuousOn_dusartJ_integrand (k : Nat) (η : Real)
    {x₀ : Real} (h₀ : 1 < x₀) :
    ContinuousOn (fun t : Real => 1 / Real.log t ^ 2 +
      η / Real.log t ^ (k + 2)) (Set.Ici x₀) := by
  have hlog : ContinuousOn Real.log (Set.Ici x₀) :=
    Real.continuousOn_log.mono (by
      intro t ht
      exact ne_of_gt (lt_of_lt_of_le (by linarith : 0 < x₀) ht))
  have hn : ∀ n : Nat, ∀ t ∈ Set.Ici x₀, Real.log t ^ n ≠ 0 := by
    intro n t ht
    exact pow_ne_zero n (Real.log_pos (h₀.trans_le ht)).ne'
  exact (continuousOn_const.div (hlog.pow 2) (hn 2)).add
    (continuousOn_const.div (hlog.pow (k + 2)) (hn (k + 2)))

private theorem pi_from_anchor {x₀ x : Real} (h₀ : 2 ≤ x₀) (hx : x₀ ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : Real) =
      (Nat.primeCounting ⌊x₀⌋₊ : Real) - Chebyshev.theta x₀ / Real.log x₀ +
        Chebyshev.theta x / Real.log x +
        ∫ t in x₀..x, Chebyshev.theta t / (t * Real.log t ^ 2) := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (theta_integrable_from (by norm_num : (2 : Real) ≤ 2) h₀)
    (theta_integrable_from h₀ hx)
  have hpi₀ := Chebyshev.primeCounting_eq_theta_div_log_add_integral h₀
  have hpi := Chebyshev.primeCounting_eq_theta_div_log_add_integral (h₀.trans hx)
  linarith

/-- The upper comparison uses only a one-sided theta bound on the suffix. -/
theorem primeCounting_le_dusartJ {k : Nat} {η x₀ x : Real}
    (h₀ : 2 ≤ x₀) (hx : x₀ ≤ x)
    (hθ : ∀ t ∈ Set.Icc x₀ x,
      Chebyshev.theta t ≤ t + η * t / Real.log t ^ k) :
    (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartJ k η x₀ x := by
  have hp : ∀ t ∈ Set.Icc x₀ x, 0 < Real.log t := by
    intro t ht
    exact Real.log_pos (by linarith [ht.1])
  have hint := (continuousOn_dusartJ_integrand k η (by linarith : 1 < x₀)).mono
    (show Set.uIcc x₀ x ⊆ Set.Ici x₀ by rw [Set.uIcc_of_le hx]; exact fun _ ht => ht.1)
  have hmono := intervalIntegral.integral_mono_on hx (theta_integrable_from h₀ hx)
    hint.intervalIntegrable (show ∀ t ∈ Set.Icc x₀ x,
      Chebyshev.theta t / (t * Real.log t ^ 2) ≤
        1 / Real.log t ^ 2 + η / Real.log t ^ (k + 2) by
      intro t ht
      have htpos : 0 < t := by linarith [ht.1]
      calc
        _ ≤ (t + η * t / Real.log t ^ k) / (t * Real.log t ^ 2) :=
          div_le_div_of_nonneg_right (hθ t ht) (by positivity)
        _ = _ := by
          rw [pow_add]
          field_simp [htpos.ne', (hp t ht).ne'])
  have hend : Chebyshev.theta x / Real.log x ≤
      x / Real.log x + η * x / Real.log x ^ (k + 1) := by
    calc
      _ ≤ (x + η * x / Real.log x ^ k) / Real.log x :=
        div_le_div_of_nonneg_right (hθ x ⟨hx, le_rfl⟩) (hp x ⟨hx, le_rfl⟩).le
      _ = _ := by rw [pow_succ]; field_simp
  rw [pi_from_anchor h₀ hx]
  unfold dusartJ
  linarith

/-- The lower comparison likewise allows a signed coefficient. -/
theorem dusartJ_le_primeCounting {k : Nat} {η x₀ x : Real}
    (h₀ : 2 ≤ x₀) (hx : x₀ ≤ x)
    (hθ : ∀ t ∈ Set.Icc x₀ x,
      t + η * t / Real.log t ^ k ≤ Chebyshev.theta t) :
    dusartJ k η x₀ x ≤ (Nat.primeCounting ⌊x⌋₊ : Real) := by
  have hp : ∀ t ∈ Set.Icc x₀ x, 0 < Real.log t := by
    intro t ht
    exact Real.log_pos (by linarith [ht.1])
  have hint := (continuousOn_dusartJ_integrand k η (by linarith : 1 < x₀)).mono
    (show Set.uIcc x₀ x ⊆ Set.Ici x₀ by rw [Set.uIcc_of_le hx]; exact fun _ ht => ht.1)
  have hmono := intervalIntegral.integral_mono_on hx hint.intervalIntegrable
    (theta_integrable_from h₀ hx) (show ∀ t ∈ Set.Icc x₀ x,
      1 / Real.log t ^ 2 + η / Real.log t ^ (k + 2) ≤
        Chebyshev.theta t / (t * Real.log t ^ 2) by
      intro t ht
      have htpos : 0 < t := by linarith [ht.1]
      calc
        _ = (t + η * t / Real.log t ^ k) / (t * Real.log t ^ 2) := by
          rw [pow_add]
          field_simp [htpos.ne', (hp t ht).ne']
        _ ≤ _ := div_le_div_of_nonneg_right (hθ t ht) (by positivity))
  have hend : x / Real.log x + η * x / Real.log x ^ (k + 1) ≤
      Chebyshev.theta x / Real.log x := by
    calc
      _ = (x + η * x / Real.log x ^ k) / Real.log x := by
        rw [pow_succ]
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (hθ x ⟨hx, le_rfl⟩) (hp x ⟨hx, le_rfl⟩).le
  rw [pi_from_anchor h₀ hx]
  unfold dusartJ
  linarith

/-- The paper's two inequalities for `J(x; ±η)` at once. -/
theorem dusartJ_sandwich {k : Nat} {η x₀ x : Real}
    (h₀ : 2 ≤ x₀) (hx : x₀ ≤ x)
    (hθ : ∀ t ∈ Set.Icc x₀ x,
      |Chebyshev.theta t - t| ≤ η * t / Real.log t ^ k) :
    dusartJ k (-η) x₀ x ≤ (Nat.primeCounting ⌊x⌋₊ : Real) ∧
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartJ k η x₀ x := by
  constructor
  · apply dusartJ_le_primeCounting h₀ hx
    intro t ht
    have h := (abs_le.mp (hθ t ht)).1
    simpa only [neg_mul, neg_div] using (show t + -(η * t / Real.log t ^ k) ≤
      Chebyshev.theta t by linarith)
  · apply primeCounting_le_dusartJ h₀ hx
    intro t ht
    have h := (abs_le.mp (hθ t ht)).2
    linarith

end

end PrimeFactorUnimodality
