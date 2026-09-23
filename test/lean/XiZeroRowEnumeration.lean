import PrimeFactorUnimodality.Helpers.Analytic.XiZeroRowEnumeration

/-! # Exact count saturation retains the same enclosed labels for all weights -/

open PrimeFactorUnimodality Finset

example {n : ℕ} {T : ℝ} (f : Fin n → RiemannXiDivisorZeroIndex)
    (hf : Function.Injective f) (hm : ∀ i, f i ∈ xiStrictPositiveHeightIndices T)
    (hc : xiStrictZeroCount T ≤ n) :
    xiStrictPositiveHeightIndices T = univ.map ⟨f, hf⟩ :=
  xiStrictPositive_eq_map_of_count f hf hm hc

example {E : Type*} [AddCommMonoid E] {n : ℕ} {T : ℝ}
    (f : Fin n → RiemannXiDivisorZeroIndex) (hf : Function.Injective f)
    (he : xiStrictPositiveHeightIndices T = univ.map ⟨f, hf⟩)
    (F : RiemannXiDivisorZeroIndex → E) :
    (∑ p ∈ xiLowHeightIndices T, F p) =
      ∑ i, (F (f i) + F (riemannXiDivisorConjugation (f i))) :=
  sum_xiLow_eq_enumeration f hf he F

example {n : ℕ} {rows : Fin n → XiSignRow} {a b : ℚ} {T : ℝ}
    (h : XiSignRows.Valid rows a b) (ha : 0 ≤ a) (hb : (b : ℝ) ≤ T)
    (hc : xiStrictZeroCount T ≤ n) :
    ∃ f : Fin n → RiemannXiDivisorZeroIndex,
      (∀ i, (riemannXiDivisorZeroValue (f i)).re = 1 / 2 ∧
        (riemannXiDivisorZeroValue (f i)).im ∈ Set.Ioo ((rows i).lower : ℝ) (rows i).upper) ∧
      ∀ F : RiemannXiDivisorZeroIndex → ℂ,
        (∑ p ∈ xiLowHeightIndices T, F p) =
          ∑ i, (F (f i) + F (riemannXiDivisorConjugation (f i))) :=
  h.exists_weighted_enumeration ha hb hc

example {T : ℝ} (h : xiStrictZeroCount T ≤ 0) (F : RiemannXiDivisorZeroIndex → ℂ) :
    (∑ p ∈ xiLowHeightIndices T, F p) = 0 := by
  have hf : Function.Injective (Fin.elim0 : Fin 0 → RiemannXiDivisorZeroIndex) :=
    fun i => Fin.elim0 i
  have he := xiStrictPositive_eq_map_of_count Fin.elim0 hf (fun i => Fin.elim0 i) h
  simpa using sum_xiLow_eq_enumeration Fin.elim0 hf he F
