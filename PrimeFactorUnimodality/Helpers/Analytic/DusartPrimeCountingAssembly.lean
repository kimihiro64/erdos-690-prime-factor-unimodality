import PrimeFactorUnimodality.Helpers.Analytic.DusartJComparison
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.PrimeCountingRows
import PrimeFactorUnimodality.Helpers.Analytic.MediumPNT

set_option autoImplicit false

/-! # Assembly of the explicit prime-counting estimates

The bounded endpoint coverage and analytic remainder are independent inputs.
This module checks their composition without importing generated gap rows.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- Dusart's calculus proof with the paper's `η₂ = .05`, `η₃ = 1`,
and upper model coefficient `2.334`. The anchor and suffix theta estimates
remain separate, genuine numerical and analytic obligations. -/
theorem hasDusartRealPrimeCountingBoundsAbove_of_paper_theta_estimates
    {x₀ : Real} (h₀ : 2 ≤ x₀) (hlog : 25 ≤ Real.log x₀)
    (thetaTwo : ∀ x : Real, x₀ ≤ x →
      |Chebyshev.theta x - x| ≤ (1 / 20 : Real) * x / Real.log x ^ 2)
    (thetaThree : ∀ x : Real, x₀ ≤ x →
      |Chebyshev.theta x - x| ≤ x / Real.log x ^ 3)
    (lowerAnchor : dusartM 2 x₀ ≤ dusartJ 3 (-1) x₀ x₀)
    (upperAnchor : dusartJ 2 (1 / 20) x₀ x₀ ≤ dusartM (1167 / 500) x₀) :
    HasDusartRealPrimeCountingBoundsAbove x₀ := by
  have h₀1 : 1 < x₀ := by linarith
  constructor
  · intro x hx
    have hxpos : 0 < x := by linarith
    have hl := Real.log_pos (h₀1.trans_le hx)
    have hj := (dusartJ_sandwich (k := 3) (η := 1) h₀ hx (by
      intro t ht
      simpa only [one_mul] using thetaThree t ht.1)).1
    have hm := dusartM_two_le_dusartJ_three h₀1 hx (by norm_num) (by norm_num) lowerAnchor
    apply le_trans _ (hm.trans hj)
    calc
      dusartPiLower x = x / Real.log x + x / Real.log x ^ 2 := by
        unfold dusartPiLower
        ring
      _ ≤ x / Real.log x + x / Real.log x ^ 2 + 2 * x / Real.log x ^ 3 :=
        le_add_of_nonneg_right (by positivity)
  · intro x hx
    have hxpos : 0 < x := by linarith
    have hl := Real.log_pos (h₀1.trans_le hx)
    have hl25 := hlog.trans (Real.log_le_log (by linarith : 0 < x₀) hx)
    have hj := (dusartJ_sandwich (k := 2) (η := 1 / 20) h₀ hx (by
      intro t ht
      exact thetaTwo t ht.1)).2
    have hm := dusartJ_two_le_dusartM h₀1 hx (by norm_num)
      (by nlinarith : 3 * (1167 / 500 : Real) - 2 * (1 / 20) ≤
        (1167 / 500 - 2 - 1 / 20) * Real.log x₀) upperAnchor
    apply (hj.trans hm).trans
    apply le_of_sub_nonneg
    have heq : dusartPiUpper x - dusartM (1167 / 500) x =
        ((1381 / 5000 : Real) * Real.log x - 1167 / 500) * x / Real.log x ^ 3 := by
      unfold dusartPiUpper dusartM
      field_simp
      ring
    rw [heq]
    exact div_nonneg (mul_nonneg (by nlinarith) hxpos.le) (by positivity)

/-- Gluing the paper's analytic comparison to a bounded prime-counting prefix. -/
theorem wangCrapis_primeCounting_of_paper_theta_estimates
    {x₀ : Real} (h₀ : 599 ≤ x₀) (hlog : 25 ≤ Real.log x₀)
    (finite : HasDusartRealPrimeCountingBoundsBelow x₀)
    (thetaTwo : ∀ x : Real, x₀ ≤ x →
      |Chebyshev.theta x - x| ≤ (1 / 20 : Real) * x / Real.log x ^ 2)
    (thetaThree : ∀ x : Real, x₀ ≤ x →
      |Chebyshev.theta x - x| ≤ x / Real.log x ^ 3)
    (lowerAnchor : dusartM 2 x₀ ≤ dusartJ 3 (-1) x₀ x₀)
    (upperAnchor : dusartJ 2 (1 / 20) x₀ x₀ ≤ dusartM (1167 / 500) x₀) :
    HasDusartPrimeCountingBounds := by
  exact hasDusartPrimeCountingBounds_of_real
    (hasDusartRealPrimeCountingBounds_of_below_and_above finite
      (hasDusartRealPrimeCountingBoundsAbove_of_paper_theta_estimates
        (by linarith) hlog thetaTwo thetaThree lowerAnchor upperAnchor))

/-! Direct Abel assembly for the prime-counting provider.  The finite
prime-counting rows and the finite Abel core are independent inputs. A sharp
theta remainder is required only above `X`, not throughout the small range. -/
theorem wangCrapis_primeCounting_of_finite_and_core_and_thetaTail
    {A X Y : Real}
    (finite : HasDusartRealPrimeCountingBoundsBelow Y)
    (hXpos : 0 < X) (h2X : 2 ≤ X) (hXY : X ≤ Y)
    (hA0 : 0 ≤ A) (hA : A ≤ 1)
    (hlog : (42 : Real) ≤ Real.log X)
    (hcore : |primeCountingCore X| ≤ (3 / 5 : Real) * X / Real.log X ^ 4)
    (thetaAbove : HasThetaLogFourthErrorAbove A X) :
    HasDusartPrimeCountingBounds := by
  have thetaError : HasThetaLogFourthError A X := by
    intro x hx
    exact thetaAbove x hx
  exact hasDusartPrimeCountingBounds_of_finite_and_core_and_theta_error
    finite hXpos h2X hXY hA0 hA (by norm_num) (by norm_num) hlog hcore
    thetaError

/-! Selected-cutoff form used by the split all-`k` assembly. -/
theorem wangCrapis_primeCounting_of_selected_cutoff
    {A C X : Real}
    (finite : HasDusartRealPrimeCountingBoundsBelow X)
    (_hX : (4e18 : Real) ≤ X)
    (hXpos : 0 < X) (h2X : 2 ≤ X)
    (hA0 : 0 ≤ A) (hA : A ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hlog : (42 : Real) ≤ Real.log X)
    (hcore : |primeCountingCore X| ≤ C * X / Real.log X ^ 4)
    (thetaError : HasThetaLogFourthErrorAbove A X) :
    HasDusartPrimeCountingBounds := by
  apply hasDusartPrimeCountingBounds_of_finite_and_core_and_theta_error
    finite hXpos h2X le_rfl hA0 hA hC0 hC hlog hcore
  intro x hx
  exact thetaError x hx

/-! Direct compact-certificate boundary for the prime-counting provider. The
indexed endpoint rows discharge only the bounded real prime-counting range;
the Abel core and the unbounded theta error remain explicit inputs. -/
theorem wangCrapis_primeCounting_of_indexed_endpoint_rows_and_thetaTail
    {A X Y : Real} {n : Nat}
    (rows : Fin n → DusartPrimeCountingEndpointRow)
    (cover : DusartPrimeCountingEndpointIndexedCoverFrom599 rows Y)
    (smallUpper : ∀ x : Real, 2 ≤ x → x < 599 →
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x)
    (hXpos : 0 < X) (h2X : 2 ≤ X) (hXY : X ≤ Y)
    (hA0 : 0 ≤ A) (hA : A ≤ 1)
    (hlog : (42 : Real) ≤ Real.log X)
    (hcore : |primeCountingCore X| ≤ (3 / 5 : Real) * X / Real.log X ^ 4)
    (thetaAbove : HasThetaLogFourthErrorAbove A X) :
    HasDusartPrimeCountingBounds := by
  exact wangCrapis_primeCounting_of_finite_and_core_and_thetaTail
    (hasDusartRealPrimeCountingBoundsBelow_of_indexed_endpoint_rows
      cover smallUpper)
    hXpos h2X hXY hA0 hA hlog hcore thetaAbove

theorem wangCrapis_primeCounting_of_endpoint_chunks_and_thetaTail
    {A X : Real} (first : DusartPrimeCountingEndpointChunk)
    (rest : List DusartPrimeCountingEndpointChunk)
    (smallUpper : ∀ x : Real, 2 ≤ x → x < 599 →
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x)
    (hXpos : 0 < X) (h2X : 2 ≤ X)
    (hXY : X ≤ (DusartPrimeCountingEndpointChunk.appendMany first rest).cutoff)
    (hA0 : 0 ≤ A) (hA : A ≤ 1)
    (hlog : (42 : Real) ≤ Real.log X)
    (hcore : |primeCountingCore X| ≤ (3 / 5 : Real) * X / Real.log X ^ 4)
    (thetaAbove : HasThetaLogFourthErrorAbove A X) :
    HasDusartPrimeCountingBounds := by
  exact wangCrapis_primeCounting_of_finite_and_core_and_thetaTail
    (hasDusartRealPrimeCountingBoundsBelow_of_endpoint_chunks
      first rest smallUpper)
    hXpos h2X hXY hA0 hA hlog hcore thetaAbove

/-! An eventual-cutoff adapter. Its uniform core and prime-counting inputs
are analytic obligations, not a single finite certificate. -/
theorem wangCrapis_primeCounting_of_mediumPNT
    (core : ∀ Y : Real, (4e18 : Real) ≤ Y →
      |primeCountingCore Y| ≤ (3 / 5 : Real) * Y / Real.log Y ^ 4)
    (finitePrimeCounting : ∀ Y : Real, (4e18 : Real) ≤ Y →
      HasDusartRealPrimeCountingBoundsBelow Y) :
    HasDusartPrimeCountingBounds := by
  obtain ⟨Y, hXY, htail, _⟩ :=
    exists_mediumPNT_real_dusart_tail_inputs (X := (4e18 : Real))
      le_rfl (by norm_num) (by norm_num) core
  exact hasDusartPrimeCountingBounds_of_real
    (hasDusartRealPrimeCountingBounds_of_below_and_above
      (finitePrimeCounting Y hXY) htail)

end

end PrimeFactorUnimodality
