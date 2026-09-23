import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.ExponentialStability

/-! # Repeated frequencies, empty sums, enclosure errors and interval interpolation -/

open Complex Finset

example {ι : Type*} (S : Finset ι) (w : ι → ℂ) (f : ι → ℝ) (u v : ℝ) :
    ‖(∑ i ∈ S, w i * exp (I * ((u * f i : ℝ) : ℂ))) -
      ∑ i ∈ S, w i * exp (I * ((v * f i : ℝ) : ℂ))‖ ≤
      |u - v| * ∑ i ∈ S, ‖w i‖ * |f i| :=
  norm_expSum_sub_expSum_le_frequency_mass S w f u v

example {ι : Type*} (S : Finset ι) (w a : ι → ℂ) (f g ε δ : ι → ℝ)
    {v V : ℝ} (hv : |v| ≤ V)
    (hw : ∀ i ∈ S, ‖w i - a i‖ ≤ ε i) (hf : ∀ i ∈ S, |f i - g i| ≤ δ i) :
    ‖(∑ i ∈ S, w i * exp (I * ((v * f i : ℝ) : ℂ))) -
      ∑ i ∈ S, a i * exp (I * ((v * g i : ℝ) : ℂ))‖ ≤
      ∑ i ∈ S, (ε i + ‖a i‖ * (V * δ i)) :=
  norm_expSum_sub_expSum_le_of_enclosures S w a f g ε δ hv hw hf

example (w : ℕ → ℂ) (f : ℕ → ℝ) (u v : ℝ) :
    ‖(∑ i ∈ (∅ : Finset ℕ), w i * exp (I * ((u * f i : ℝ) : ℂ))) -
      ∑ i ∈ (∅ : Finset ℕ), w i * exp (I * ((v * f i : ℝ) : ℂ))‖ ≤ 0 := by
  exact (norm_expSum_sub_expSum_le_frequency_mass (∅ : Finset ℕ) w f u v).trans_eq (by simp)

example (a : ℂ) (g v : ℝ) :
    (∑ i ∈ (univ : Finset (Fin 2)), (if i = 0 then a else -a) *
      exp (I * ((v * g : ℝ) : ℂ))) = 0 := by
  simp [Fin.sum_univ_two]

example {ι : Type*} (S : Finset ι) (w : ι → ℂ) (f : ι → ℝ)
    {u v d e : ℝ} {z : ℂ} (hd : |u - v| ≤ d)
    (hz : ‖(∑ i ∈ S, w i * exp (I * ((v * f i : ℝ) : ℂ))) - z‖ ≤ e) :
    ‖∑ i ∈ S, w i * exp (I * ((u * f i : ℝ) : ℂ))‖ ≤
      ‖z‖ + e + d * ∑ i ∈ S, ‖w i‖ * |f i| :=
  norm_expSum_le_of_sample S w f hd hz
