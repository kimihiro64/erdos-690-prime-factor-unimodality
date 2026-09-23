import PrimeFactorUnimodality.Helpers.Analytic.XiTuringEnumeration

/-! # Padding certifies the prefix count and all its weighted sums -/

open PrimeFactorUnimodality Finset XiSignRows

example {n k : ℕ} {rows : Fin n → XiSignRow} {padding : Fin k → XiSignRow} {a b : ℚ}
    (h : Valid rows 0 a) (hp : Valid padding a b)
    (hb : (∫ t in (a : ℝ)..(b : ℝ), (xiZeroCount t : ℝ)) <
      (b : ℝ) - a + completedArea (Fin.append rows padding) a b) :
    xiStrictZeroCount (a : ℝ) ≤ n :=
  h.strictCount_le_of_padded_integral hp hb

example {n k : ℕ} {rows : Fin n → XiSignRow} {padding : Fin k → XiSignRow} {a b : ℚ}
    (h : Valid rows 0 a) (hp : Valid padding a b) (ha : 32 ≤ a)
    (hm : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a +
      turingCountErrorBudget a b <
        (b : ℝ) - a + (completedAreaRat (Fin.append rows padding) a b : ℝ)) :
    xiStrictZeroCount (a : ℝ) ≤ n :=
  h.strictCount_le_of_turing_padding hp ha hm

example {n k : ℕ} {rows : Fin n → XiSignRow} {padding : Fin k → XiSignRow} {a b : ℚ}
    (h : Valid rows 0 a) (hp : Valid padding a b) (ha : 32 ≤ a)
    (hm : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a +
      turingCountErrorBudget a b <
        (b : ℝ) - a + (completedAreaRat (Fin.append rows padding) a b : ℝ)) :
    ∃ f : Fin n → RiemannXiDivisorZeroIndex,
      (∀ i, (riemannXiDivisorZeroValue (f i)).re = 1 / 2 ∧
        (riemannXiDivisorZeroValue (f i)).im ∈ Set.Ioo ((rows i).lower : ℝ) (rows i).upper) ∧
      ∀ F : RiemannXiDivisorZeroIndex → ℂ,
        (∑ p ∈ xiLowHeightIndices (a : ℝ), F p) =
          ∑ i, (F (f i) + F (riemannXiDivisorConjugation (f i))) :=
  h.exists_weighted_enumeration_of_turing_padding hp ha hm
