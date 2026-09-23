import PrimeFactorUnimodality.Helpers.Analytic.XiLowConjugatePartition
import PrimeFactorUnimodality.Helpers.Analytic.XiZeroExhaustion

/-! # Exhaustive weighted enumeration from ordered zero-enclosure rows

The total multiplicity count upgrades an injective family of witnessed
positive zeros to an exact finite enumeration. Their original ordinate
enclosures are retained, and arbitrary weights transport to both signs.
No enumeration completeness or simplicity is assumed from sign changes alone.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Finset

/-- Saturation of the actual positive multiplicity count gives equality of finite sets. -/
theorem xiStrictPositive_eq_map_of_count {n : ℕ} {T : ℝ}
    (f : Fin n → RiemannXiDivisorZeroIndex) (hf : Function.Injective f)
    (hmem : ∀ i, f i ∈ xiStrictPositiveHeightIndices T) (hcount : xiStrictZeroCount T ≤ n) :
    xiStrictPositiveHeightIndices T = univ.map ⟨f, hf⟩ := by
  classical
  have hsub : univ.map ⟨f, hf⟩ ⊆ xiStrictPositiveHeightIndices T := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := mem_map.mp hp
    exact hmem i
  have hcard : (univ.map ⟨f, hf⟩).card = n := by simp
  exact (eq_of_subset_of_card_le hsub (hcount.trans_eq hcard.symm)).symm

/-- Exact positive enumeration transports any additive weight to both signed copies. -/
theorem sum_xiLow_eq_enumeration {E : Type*} [AddCommMonoid E] {n : ℕ} {T : ℝ}
    (f : Fin n → RiemannXiDivisorZeroIndex) (hf : Function.Injective f)
    (he : xiStrictPositiveHeightIndices T = univ.map ⟨f, hf⟩)
    (F : RiemannXiDivisorZeroIndex → E) :
    (∑ p ∈ xiLowHeightIndices T, F p) =
      ∑ i, (F (f i) + F (riemannXiDivisorConjugation (f i))) := by
  rw [sum_xiLow_eq_positive_conjugate T F, he, sum_map]
  rfl

namespace XiSignRows

/-- A complete row block retains actual enclosed ordinates and an exact positive enumeration. -/
theorem Valid.exists_complete_indices {n : ℕ} {rows : Fin n → XiSignRow} {a b : ℚ} {T : ℝ}
    (h : Valid rows a b) (ha : 0 ≤ a) (hb : (b : ℝ) ≤ T) (hcount : xiStrictZeroCount T ≤ n) :
    ∃ (f : Fin n → RiemannXiDivisorZeroIndex) (hf : Function.Injective f),
      (∀ i, (riemannXiDivisorZeroValue (f i)).re = 1 / 2 ∧
        (riemannXiDivisorZeroValue (f i)).im ∈ Set.Ioo ((rows i).lower : ℝ) (rows i).upper) ∧
      xiStrictPositiveHeightIndices T = univ.map ⟨f, hf⟩ := by
  obtain ⟨f, hf, hi⟩ := h.exists_indices
  refine ⟨f, hf, hi, xiStrictPositive_eq_map_of_count f hf ?_ hcount⟩
  intro i
  rw [mem_xiStrictPositiveHeightIndices]
  have hl : (0 : ℝ) ≤ (rows i).lower := by exact_mod_cast ha.trans (h.lower i)
  have hu : ((rows i).upper : ℝ) ≤ (b : ℝ) := by exact_mod_cast h.upper i
  exact ⟨hl.trans_lt (hi i).2.1, (hi i).2.2.trans_le (hu.trans hb)⟩

/-- The same complete family transports all weights, not a separately chosen family per sample. -/
theorem Valid.exists_weighted_enumeration {n : ℕ} {rows : Fin n → XiSignRow}
    {a b : ℚ} {T : ℝ} (h : Valid rows a b) (ha : 0 ≤ a) (hb : (b : ℝ) ≤ T)
    (hcount : xiStrictZeroCount T ≤ n) :
    ∃ f : Fin n → RiemannXiDivisorZeroIndex,
      (∀ i, (riemannXiDivisorZeroValue (f i)).re = 1 / 2 ∧
        (riemannXiDivisorZeroValue (f i)).im ∈ Set.Ioo ((rows i).lower : ℝ) (rows i).upper) ∧
      ∀ F : RiemannXiDivisorZeroIndex → ℂ,
        (∑ p ∈ xiLowHeightIndices T, F p) =
          ∑ i, (F (f i) + F (riemannXiDivisorConjugation (f i))) := by
  obtain ⟨f, hf, hi, he⟩ := h.exists_complete_indices ha hb hcount
  exact ⟨f, hi, fun F => sum_xiLow_eq_enumeration f hf he F⟩

end XiSignRows

end

end PrimeFactorUnimodality
