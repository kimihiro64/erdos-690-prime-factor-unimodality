import PrimeNumberTheoremAnd.ZetaBounds

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

open Complex Set

/-! A fixed real-axis estimate used when making the numerical zeta constants
    in the explicit formula chain concrete. -/
theorem riemannZeta_norm_real_le_three_div_sub_one
    {σ : Real} (hσ₁ : 1 < σ) (hσ₂ : σ ≤ 2) :
    ‖riemannZeta (σ : Complex)‖ ≤ 3 / (σ - 1) := by
  have hσne : (σ : Complex) ≠ 1 := by
    intro h
    have : σ = 1 := by exact_mod_cast congrArg Complex.re h
    linarith
  have hσdom : (σ : Complex) ∈ zetaAbelContinuationDomain :=
    mem_zetaAbelContinuationDomain_of_re hσne (by
      change (1 / 10 : Real) < σ
      linarith)
  have hbound := norm_riemannZeta_le (σ : Complex) hσdom
  have hσpos : 0 < σ := by linarith
  have hsubpos : 0 < σ - 1 := by linarith
  have hnorm : ‖(σ : Complex)‖ = σ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσpos]
  have hnormsub : ‖(σ : Complex) - 1‖ = σ - 1 := by
    rw [show (σ : Complex) - 1 = (σ - 1 : Real) by norm_num,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsubpos]
  have hre : (σ : Complex).re = σ := by rfl
  rw [hnormsub, hnorm, hre] at hbound
  have hσne0 : σ ≠ 0 := ne_of_gt hσpos
  have hratio : σ / σ = (1 : Real) := by field_simp
  rw [hratio] at hbound
  apply le_trans hbound
  apply (div_le_div_iff₀ hsubpos).2
  nlinarith [hσ₂]

theorem riemannZeta_near_one_explicit :
    ∀ (σ : Real), σ ∈ Ioc 1 2 →
      ‖riemannZeta (σ : Complex)‖ ≤ 3 / (σ - 1) := by
  intro σ hσ
  exact riemannZeta_norm_real_le_three_div_sub_one hσ.1 hσ.2

theorem zetaNear1BndExact_explicit :
    ∃ (c : Real), 0 < c ∧ ∀ (σ : Real), σ ∈ Ioc 1 2 →
      ‖riemannZeta (σ : Complex)‖ ≤ c / (σ - 1) := by
  refine ⟨3, by norm_num, ?_⟩
  exact riemannZeta_near_one_explicit

theorem zetaUpperBnd_explicit
    (σ t : Real) (ht : 3 < |t|)
    (hσ : σ ∈ Icc (1 - (1 / 2 : Real) / Real.log |t|) 2) :
    ‖riemannZeta (σ + t * Complex.I)‖ ≤
      Real.exp (1 / 2 : Real) * (5 + 8 * 2) * Real.log |t| := by
  obtain ⟨Npos, _, _, _, σPos, neOne⟩ :=
    UpperBnd_aux ⟨by norm_num, by norm_num⟩ ht hσ.1
  rw [← Zeta0EqZeta Npos (by simp [σPos]) neOne]
  apply le_trans (by apply norm_add₄_le)
  convert! ZetaUpperBnd' ⟨by norm_num, le_rfl⟩ ht hσ using 1
  simp

theorem zetaDerivUpperBnd_explicit
    (σ t : Real) (ht : 3 < |t|)
    (hσ : σ ∈ Icc (1 - (1 / 2 : Real) / Real.log |t|) 2) :
    ‖deriv riemannZeta (σ + t * Complex.I)‖ ≤
      Real.exp (1 / 2 : Real) * 59 * Real.log |t| ^ 2 := by
  obtain ⟨Npos, _, _, _, σPos, neOne⟩ :=
    UpperBnd_aux ⟨by norm_num, by norm_num⟩ ht hσ.1
  rw [← DerivZeta0EqDerivZeta Npos (by simp [σPos]) neOne]
  set N : Nat := ⌊|t|⌋₊
  rw [(HasDerivAtZeta0 Npos (s := σ + t * Complex.I)
    (by simp [σPos]) neOne).deriv]
  dsimp only [ζ₀']
  set aa := ∑ n ∈ Finset.range (N + 1),
    -1 / (n : Complex) ^ (σ + t * Complex.I) * (Real.log n)
  set bb := -(N : Complex) ^ (1 - (σ + t * Complex.I)) /
    (1 - (σ + t * Complex.I)) ^ 2
  set cc := (Real.log N) * (N : Complex) ^ (1 - (σ + t * Complex.I)) /
    (1 - (σ + t * Complex.I))
  set dd := (Real.log N) * (N : Complex) ^ (-(σ + t * Complex.I)) / 2
  set ee := 1 * ∫ x in Ioi (N : Real),
    (⌊x⌋ + 1 / 2 - x) * (x : Complex) ^ (-(σ + t * Complex.I) - 1)
  set ff := (σ + t * Complex.I) * ∫ x in Ioi (N : Real),
    (⌊x⌋ + 1 / 2 - x) * (x : Complex) ^ (-(σ + t * Complex.I) - 1) *
      -(Real.log x)
  rw [(by ring : aa + (bb + cc) + dd + ee + ff = aa + bb + cc + dd + ee + ff)]
  apply le_trans (by apply norm_add₆)
  convert! ZetaDerivUpperBnd' ⟨by norm_num, le_rfl⟩ ht hσ using 1

theorem zetaDiffBnd_explicit
    (σ₁ σ₂ t : Real) (ht : 3 < |t|)
    (hσ₁ : 1 - (1 / 2 : Real) / Real.log |t| ≤ σ₁)
    (hσ₂ : σ₂ ≤ 2) (hσ₁₂ : σ₁ < σ₂) :
    ‖riemannZeta (σ₂ + t * Complex.I) -
        riemannZeta (σ₁ + t * Complex.I)‖ ≤
      Real.exp (1 / 2 : Real) * 59 * Real.log |t| ^ 2 * (σ₂ - σ₁) := by
  have htne : t ≠ 0 := by
    contrapose! ht
    simp
  rw [← Zeta_eq_int_derivZeta htne]
  convert intervalIntegral.norm_integral_le_of_norm_le_const (C :=
    Real.exp (1 / 2 : Real) * 59 * Real.log |t| ^ 2) ?_ using 1
  · congr
    rw [abs_of_nonneg (by linarith)]
  · intro σ hσ
    rw [uIoc_of_le hσ₁₂.le, mem_Ioc] at hσ
    exact zetaDerivUpperBnd_explicit σ t ht ⟨le_trans hσ₁ hσ.1.le,
      le_trans hσ.2 hσ₂⟩

theorem zetaLowerBound3_explicit_fixed :
    ∀ {σ : Real} (_ : σ ∈ Ioc 1 2) (t : Real) (_ : 3 < |t|),
      (1 / (3 ^ ((3 : Real) / 4) *
        (2 * (Real.exp (1 / 2 : Real) * (5 + 8 * 2))) ^ ((1 : Real) / 4))) *
          (σ - 1) ^ ((3 : Real) / 4) / (Real.log |t|) ^ ((1 : Real) / 4) ≤
        ‖riemannZeta (σ + t * Complex.I)‖ := by
  intro σ hσ t ht
  let C₀ : Real := Real.exp (1 / 2 : Real) * (5 + 8 * 2)
  change (1 / (3 ^ ((3 : Real) / 4) * (2 * C₀) ^ ((1 : Real) / 4))) *
      (σ - 1) ^ ((3 : Real) / 4) / (Real.log |t|) ^ ((1 : Real) / 4) ≤ _
  obtain ⟨σ_gt, σ_le⟩ := hσ
  have lower := ZetaLowerBound2 (t := t) σ_gt
  apply le_trans _ lower
  have ζσ_bound : ‖riemannZeta (σ : Complex)‖ ≤ 3 / (σ - 1) :=
    riemannZeta_norm_real_le_three_div_sub_one σ_gt σ_le
  have ht₂ : 3 < |2 * t| := by
    simp only [abs_mul, Nat.abs_ofNat]
    linarith
  have σ_range : σ ∈ Icc
      (1 - (1 / 2 : Real) / Real.log |2 * t|) 2 := by
    constructor
    · have hpos : 0 < (1 / 2 : Real) / Real.log |2 * t| := by
        exact div_pos (by norm_num) (Real.log_pos (by linarith))
      nlinarith
    · exact σ_le
  have ζ₂t_bound := zetaUpperBnd_explicit σ (2 * t) ht₂ σ_range
  have denom_bound :
      ‖riemannZeta (σ : Complex)‖ ^ ((3 : Real) / 4) *
          ‖riemannZeta (σ + 2 * t * Complex.I)‖ ^ ((1 : Real) / 4) ≤
        (3 / (σ - 1)) ^ ((3 : Real) / 4) *
          (C₀ * Real.log |2 * t|) ^ ((1 : Real) / 4) := by
    apply mul_le_mul
    · exact Real.rpow_le_rpow (norm_nonneg _) ζσ_bound (by norm_num)
    · apply ZetaLowerBound3_aux2
      convert ζ₂t_bound
      norm_num [C₀]
    · positivity
    · positivity
  have denom_bound' :
      ‖riemannZeta (σ : Complex)‖ ^ ((3 : Real) / 4) *
          ‖riemannZeta (σ + 2 * t * Complex.I)‖ ^ ((1 : Real) / 4) ≤
        3 ^ ((3 : Real) / 4) * (σ - 1) ^ (-(3 : Real) / 4) *
          C₀ ^ ((1 : Real) / 4) * (Real.log |2 * t|) ^ ((1 : Real) / 4) := by
    convert denom_bound using 1
    rw [Real.div_rpow (by linarith) (by linarith),
      Real.mul_rpow (by linarith) (Real.log_nonneg (by linarith))]
    ring_nf
  have pos_left : 0 <
      3 ^ ((3 : Real) / 4) * (σ - 1) ^ (-(3 : Real) / 4) *
        C₀ ^ ((1 : Real) / 4) * (Real.log |2 * t|) ^ ((1 : Real) / 4) := by
    exact ZetaLowerBound3_aux4 C₀ (by
      dsimp [C₀]
      positivity) 3 (by norm_num) t ht σ_gt
  have pos_right : 0 <
      ‖riemannZeta (σ : Complex)‖ ^ ((3 : Real) / 4) *
        ‖riemannZeta (σ + 2 * t * Complex.I)‖ ^ ((1 : Real) / 4) := by
    apply ZetaLowerBound3_aux5
    exact ZetaLowerBound1 (t := t) σ_gt
  use (div_le_div_of_nonneg_left zero_le_one pos_right denom_bound').trans' ?_
  simp_rw [abs_mul, abs_two, neg_div,
    Real.rpow_neg (sub_pos.2 σ_gt).le]
  have hlog : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hlog₂ : 0 < Real.log (2 * |t|) := Real.log_pos (by linarith)
  have hlogpow : 0 < Real.log |t| ^ ((1 : Real) / 4) :=
    Real.rpow_pos_of_pos hlog _
  have hlog₂pow : 0 < Real.log (2 * |t|) ^ ((1 : Real) / 4) :=
    Real.rpow_pos_of_pos hlog₂ _
  field_simp
  rw [Real.mul_rpow (by norm_num) (by positivity)]
  move_mul [C₀ ^ ((1 : Real) / 4)]
  rw [mul_le_mul_iff_left₀]
  swap
  · positivity
  rw [← Real.mul_rpow (by norm_num) hlog.le]
  apply Real.rpow_le_rpow hlog₂.le _ (by norm_num)
  rw [← Real.log_rpow (by linarith : 0 < |t|)]
  apply Real.log_le_log (by linarith) (by nlinarith)
  rw [Real.rpow_two, sq]
  gcongr
  linarith

theorem zetaLowerBound3_explicit :
    ∃ c > 0, ∀ {σ : Real} (_ : σ ∈ Ioc 1 2) (t : Real) (_ : 3 < |t|),
      c * (σ - 1) ^ ((3 : Real) / 4) / (Real.log |t|) ^ ((1 : Real) / 4) ≤
        ‖riemannZeta (σ + t * Complex.I)‖ := by
  refine ⟨1 / (3 ^ ((3 : Real) / 4) *
    (2 * (Real.exp (1 / 2 : Real) * (5 + 8 * 2))) ^ ((1 : Real) / 4)), ?_, ?_⟩
  · positivity
  · exact zetaLowerBound3_explicit_fixed


end
end PrimeFactorUnimodality
