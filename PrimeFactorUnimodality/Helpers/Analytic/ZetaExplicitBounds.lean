import PrimeNumberTheoremAnd.ZetaBounds
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaConvexity
import PrimeNumberTheoremAnd.MediumPNT

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
  have hsum : aa + (bb + cc) + dd + (ee + ff) =
      aa + bb + cc + dd + ee + ff := by ring
  rw [hsum]
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
    intro ht0
    subst t
    norm_num at ht
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
    have hC₀ : 0 < C₀ := by
      dsimp [C₀]
      positivity
    rw [Real.div_rpow (by linarith) (by linarith),
      Real.mul_rpow (by linarith) hC₀.le]
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

theorem zetaZeroFree_explicit :
    ∃ (A : Real) (_ : A ∈ Ioc 0 (1 / 2)) (c : Real) (_ : 0 < c),
    ∀ (σ t : Real) (_ : 3 < |t|)
      (_ : σ ∈ Ico (1 - A / (Real.log |t|) ^ 9)
        (1 + A / (Real.log |t|) ^ 9)),
      c / (Real.log |t|) ^ 7 ≤ ‖riemannZeta (σ + t * Complex.I)‖ ∧
        riemannZeta (σ + t * Complex.I) ≠ 0 := by
  let C₁ : Real := 1 / (3 ^ ((3 : Real) / 4) *
    (2 * (Real.exp (1 / 2 : Real) * (5 + 8 * 2))) ^ ((1 : Real) / 4))
  let C₂ : Real := Real.exp (1 / 2 : Real) * 59
  have hC₁ : 0 < C₁ := by
    dsimp [C₁]
    positivity
  have hC₂ : 0 < C₂ := by
    dsimp [C₂]
    positivity
  let A : Real := min (1 / 2 : Real) ((C₁ / (4 * C₂)) ^ (4 : Nat))
  have hA : A ∈ Ioc (0 : Real) (1 / 2) := by
    constructor
    · dsimp [A]
      positivity
    · exact min_le_left _ _
  let c : Real := C₁ * A ^ ((3 : Real) / 4) - 2 * C₂ * A
  have hc : 0 < c := by
    have hpow := A.rpow_le_rpow hA.1.le (min_le_right _ _)
      (inv_pos.mpr four_pos).le
    erw [Real.pow_rpow_inv_natCast
      (div_pos hC₁ (mul_pos four_pos hC₂)).le four_ne_zero,
      le_div_iff₀ (mul_pos four_pos hC₂)] at hpow
    norm_num [mul_assoc, c, mul_left_comm, hC₂, hA.1,
      (mul_le_mul_of_nonneg_right hpow
        (A.rpow_nonneg hA.1.le _)).trans_lt', ← A.rpow_add]
  refine ⟨A, hA, c, hc, ?_⟩
  intro σ t ht hσ
  let σ' : Real := 1 + A / Real.log |t| ^ (9 : Real)
  have hlog : 1 ≤ Real.log |t| := (logt_gt_one ht.le).le
  have hlogpow : (1 / 2 : Real) ≤ Real.log |t| ^ 9 :=
    one_half_lt_one.le.trans (one_le_pow₀ hlog)
  have hσ'gt : 1 < σ' := by
    dsimp [σ']
    have hpos : 0 < A / Real.log |t| ^ (9 : Nat) := by
      exact div_pos hA.1 (by positivity)
    linarith
  have hσ'le : σ' ≤ 2 := by
    dsimp [σ']
    have hfrac : A / Real.log |t| ^ (9 : Nat) < 1 := by
      apply (div_lt_one (by positivity)).2
      exact hA.2.trans_lt (lt_of_lt_of_le (by norm_num)
        (one_le_pow₀ (logt_gt_one ht.le).le))
    linarith
  have hσ'upper : σ' ∈ Ioc (1 : Real) 2 := ⟨hσ'gt, hσ'le⟩
  have hlower := zetaLowerBound3_explicit_fixed hσ'upper t ht
  have hlower' :
      C₁ * A ^ ((3 : Real) / 4) / Real.log |t| ^ (7 : Real) ≤
        ‖riemannZeta (σ' + t * Complex.I)‖ := by
    have hbase : C₁ * (σ' - 1) ^ ((3 : Real) / 4) /
        Real.log |t| ^ ((1 : Real) / 4) ≤
        ‖riemannZeta (σ' + t * Complex.I)‖ := by
      simpa [C₁] using hlower
    apply hbase.trans'
    norm_num only [σ', add_sub_cancel_left, A.div_rpow hA.1.le, mul_div,
      pow_pos, ← Real.rpow_natCast, ← Real.rpow_mul, le_of_lt,
      Real.log_pos, refl, div_div, ← Real.rpow_sub]
  have hdiff := zetaDiffBnd_explicit σ σ' t ht
  have hdiff' :
      ‖riemannZeta (σ + t * Complex.I) -
          riemannZeta (σ' + t * Complex.I)‖ ≤
        C₂ * Real.log |t| ^ 2 * (σ' - σ) := by
    have hdiff1 := hdiff σ σ' t ht
      (by
        dsimp [A]
        apply le_trans hσ.1
        gcongr
        exact ZetaInvBnd_aux (logt_gt_one ht.le))
      hσ'le
      (by
        dsimp [σ']
        have h : 0 < A / Real.log |t| ^ 9 := by positivity
        linarith [hσ.2])
    convert hdiff1 using 1
    rw [show riemannZeta (σ + t * Complex.I) -
        riemannZeta (σ' + t * Complex.I) =
        -(riemannZeta (σ' + t * Complex.I) -
          riemannZeta (σ + t * Complex.I)) by ring, norm_neg]
  have hσ'diff : σ' - σ ≤ 2 * A / Real.log |t| ^ 9 := by
    dsimp [σ']
    linarith [hσ.1]
  have hdiff'' :
      ‖riemannZeta (σ + t * Complex.I) -
          riemannZeta (σ' + t * Complex.I)‖ ≤
        2 * C₂ * A / Real.log |t| ^ 7 := by
    calc
      _ ≤ C₂ * Real.log |t| ^ 2 * (2 * A / Real.log |t| ^ 9) :=
        mul_le_mul_of_nonneg_left hσ'diff (by positivity)
      _ = 2 * C₂ * A / Real.log |t| ^ 7 := by
        rw [← Real.rpow_natCast]
        field_simp
        ring
  have hnorm :
      c / Real.log |t| ^ 7 ≤ ‖riemannZeta (σ + t * Complex.I)‖ := by
    have htriangle := norm_sub_norm_le
      (riemannZeta (σ' + t * Complex.I))
      (riemannZeta (σ' + t * Complex.I) -
        riemannZeta (σ + t * Complex.I))
    have hdiffsymm :
        ‖riemannZeta (σ' + t * Complex.I) -
            riemannZeta (σ + t * Complex.I)‖ ≤
          2 * C₂ * A / Real.log |t| ^ 7 := by
      convert hdiff'' using 1
      rw [show riemannZeta (σ' + t * Complex.I) -
          riemannZeta (σ + t * Complex.I) =
          -(riemannZeta (σ + t * Complex.I) -
            riemannZeta (σ' + t * Complex.I)) by ring, norm_neg]
    have hmain : c / Real.log |t| ^ 7 ≤
        ‖riemannZeta (σ' + t * Complex.I)‖ -
          ‖riemannZeta (σ' + t * Complex.I) -
            riemannZeta (σ + t * Complex.I)‖ := by
      rw [div_le_iff₀ (by positivity)]
      dsimp [c]
      nlinarith [hlower', hdiffsymm]
    exact hmain.trans (by
      convert htriangle using 1 <;> ring)
  refine ⟨hnorm, ?_⟩
  intro hz
  have : ‖riemannZeta (σ + t * Complex.I)‖ = 0 := by simp [hz]
  have hpos : 0 < c / Real.log |t| ^ 7 := by positivity
  linarith

theorem zetaLowerBnd_explicit :
    ∃ (A : Real) (_ : A ∈ Ioc 0 (1 / 2)) (c : Real) (_ : 0 < c),
    ∀ (σ t : Real) (_ : 3 < |t|)
      (_ : σ ∈ Ico (1 - A / (Real.log |t|) ^ 9)
        (1 + A / (Real.log |t|) ^ 9)),
      c / (Real.log |t|) ^ 7 ≤ ‖riemannZeta (σ + t * Complex.I)‖ := by
  obtain ⟨A, hA, c, hc, h⟩ := zetaZeroFree_explicit
  refine ⟨A, hA, c, hc, ?_⟩
  intro σ t ht hσ
  exact (h σ t ht hσ).1

theorem zetaZeroFree_explicit_only :
    ∃ (A : Real) (_ : A ∈ Ioc 0 (1 / 2)),
    ∀ (σ t : Real) (_ : 3 < |t|)
      (_ : σ ∈ Ico (1 - A / (Real.log |t|) ^ 9)
        (1 + A / (Real.log |t|) ^ 9)),
      riemannZeta (σ + t * Complex.I) ≠ 0 := by
  obtain ⟨A, hA, c, hc, h⟩ := zetaZeroFree_explicit
  refine ⟨A, hA, ?_⟩
  intro σ t ht hσ
  exact (h σ t ht hσ).2

theorem zetaLogDeriv_explicit_below :
    ∃ (A : Real) (_ : A ∈ Ioc 0 (1 / 2)) (C : Real) (_ : 0 < C),
    ∀ (σ t : Real) (_ : 3 < |t|)
      (_ : σ ∈ Ico (1 - A / (Real.log |t|) ^ 9)
        (1 + A / (Real.log |t|) ^ 9)),
      ‖deriv riemannZeta (σ + t * Complex.I) /
        riemannZeta (σ + t * Complex.I)‖ ≤
        C * Real.log |t| ^ 9 := by
  obtain ⟨A, hA, c, hc, hbound⟩ := zetaZeroFree_explicit
  let D : Real := Real.exp (1 / 2 : Real) * 59
  refine ⟨A, hA, D / c, div_pos (by positivity) hc, ?_⟩
  intro σ t ht hσ
  have hlogpos : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hlogpow : Real.log |t| ≤ Real.log |t| ^ (9 : ℕ) :=
    ZetaInvBnd_aux (logt_gt_one ht.le)
  have hσderiv : σ ∈ Icc
      (1 - (1 / 2 : Real) / Real.log |t|) 2 := by
    constructor
    · have hdiv : A / Real.log |t| ^ (9 : ℕ) ≤
          (1 / 2 : Real) / Real.log |t| := by
        calc
          A / Real.log |t| ^ (9 : ℕ) ≤
              (1 / 2 : Real) / Real.log |t| ^ (9 : ℕ) := by
            exact div_le_div_of_nonneg_right hA.2 (by positivity)
          _ ≤ (1 / 2 : Real) / Real.log |t| := by
            gcongr
    · linarith [hσ.2]
  have hderiv := zetaDerivUpperBnd_explicit σ t ht hσderiv
  have hlower := (hbound σ t ht hσ).1
  have hlower_pos : 0 <
      ‖riemannZeta (σ + t * Complex.I)‖ := by
    have h : 0 < c / Real.log |t| ^ 7 := by positivity
    exact h.trans_le hlower
  rw [norm_div]
  apply le_trans (div_le_div_of_nonneg_left hderiv
    (le_of_lt hlower_pos) (norm_nonneg _))
  dsimp [D]
  field_simp [ne_of_gt hlogpos, ne_of_gt hc]
  ring

/-! Uniformize the local strip estimate.  Above the explicit strip we use the
    Dirichlet-series monotonicity of the logarithmic derivative; in the small
    real part range outside the strip we use the elementary pole-distance
    bound. -/
theorem zetaLogDeriv_explicit_uniform :
    ∃ (A C : Real), 0 < C ∧ A ∈ Ioc 0 (1 / 2) ∧
      LogDerivZetaHasBound A C := by
  obtain ⟨A, hA, C₀, hC₀, hlocal⟩ := zetaLogDeriv_explicit_below
  obtain ⟨K, hK, htriv⟩ := triv_bound_zeta
  let B : Real := ‖deriv riemannZeta (2 : Complex) /
    riemannZeta (2 : Complex)‖
  let C : Real := C₀ + K + 1 / A + B + 1
  have hApos : 0 < A := hA.1
  have hB : 0 ≤ B := norm_nonneg _
  have hCpos : 0 < C := by
    dsimp [C]
    have : 0 < 1 / A := by positivity
    linarith
  refine ⟨A, C, hCpos, hA, ?_⟩
  intro σ t ht hσ
  have hlog : 1 ≤ Real.log |t| := (logt_gt_one ht.le).le
  have hpow : 1 ≤ Real.log |t| ^ (9 : Nat) := one_le_pow₀ hlog
  have hpow_pos : 0 < Real.log |t| ^ (9 : Nat) := by positivity
  by_cases hσ2 : σ ≤ 2
  · by_cases hlocal_upper : σ < 1 + A / Real.log |t| ^ (9 : Nat)
    · have hC₀C : C₀ ≤ C := by
        dsimp [C]
        have hInv : 0 < 1 / A := by positivity
        have h : 0 ≤ K + 1 / A + B + 1 := by linarith
        linarith
      exact (hlocal σ t ht ⟨hσ, hlocal_upper⟩).trans
        (mul_le_mul_of_nonneg_right hC₀C (by positivity))
    · have hσgt : 1 < σ := by
        have : 1 + A / Real.log |t| ^ (9 : Nat) ≤ σ := le_of_not_gt hlocal_upper
        have : 1 < 1 + A / Real.log |t| ^ (9 : Nat) := by positivity
        linarith
      have htriv' := htriv σ t hσgt
      rw [neg_div, norm_neg] at htriv'
      have hinv : (σ - 1)⁻¹ ≤
          (1 / A) * Real.log |t| ^ (9 : Nat) := by
        apply (inv_le_iff₀ (by linarith)).2
        have hdist : A / Real.log |t| ^ (9 : Nat) ≤ σ - 1 := by
          linarith [le_of_not_gt hlocal_upper]
        have := (div_le_iff₀ hpow_pos).1 hdist
        nlinarith
      calc
        ‖deriv riemannZeta (σ + t * Complex.I) /
            riemannZeta (σ + t * Complex.I)‖ =
            ‖-(deriv riemannZeta (σ + t * Complex.I) /
              riemannZeta (σ + t * Complex.I))‖ := by rw [norm_neg]
        _ ≤ (σ - 1)⁻¹ + K := htriv'
        _ ≤ (1 / A) * Real.log |t| ^ (9 : Nat) +
              K * Real.log |t| ^ (9 : Nat) := by
          exact add_le_add hinv
            (mul_le_mul_of_nonneg_left hpow hK)
        _ = ((1 / A) + K) * Real.log |t| ^ (9 : Nat) := by ring
        _ ≤ C * Real.log |t| ^ (9 : Nat) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          dsimp [C]
          have h : 0 ≤ C₀ + B + 1 := by positivity
          linarith
  · have hgen := dlog_riemannZeta_bdd_on_vertical_lines_generalized
      (2 : Real) σ t (by norm_num) (le_of_not_ge hσ2)
    rw [neg_div, norm_neg] at hgen
    calc
      ‖deriv riemannZeta (σ + t * Complex.I) /
          riemannZeta (σ + t * Complex.I)‖ =
          ‖-(deriv riemannZeta (σ + t * Complex.I) /
            riemannZeta (σ + t * Complex.I))‖ := by rw [norm_neg]
      _ ≤ B := hgen.trans_eq rfl
      _ ≤ B * Real.log |t| ^ (9 : Nat) := by
        exact mul_le_mul_of_nonneg_left hpow hB
      _ ≤ C * Real.log |t| ^ (9 : Nat) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [C]
        have h : 0 ≤ C₀ + K + 1 / A + 1 := by positivity
        linarith


end
end PrimeFactorUnimodality
