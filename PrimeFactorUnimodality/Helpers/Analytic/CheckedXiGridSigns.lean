import PrimeFactorUnimodality.Helpers.Analytic.RationalGridHeights
import PrimeFactorUnimodality.Helpers.Analytic.SharedXiGridCheck

/-! # Checked rational computations supply actual xi sign rows

The sample Boolean discharges the correction, full Euler remainder, phase
and strict-margin obligations. The shared configuration discharges all long
moment and transform work. Opposite accepted signs at increasing rational
grid heights feed the unchanged sign-row and Turing interfaces.
-/

namespace PrimeFactorUnimodality

namespace SharedXiGridCheck

/-- The executable sample check proves every premise of the existing xi-grid evaluator. -/
theorem validated {c : SharedXiGridCheck} (hc : c.Valid) (s : XiGridSignData)
    (h : c.check s = true) :
    s.point.toGridPoint.Valid c.grid ∧
    |turingStirlingPhase (s.point.toGridPoint.height c.grid) - (s.phase : ℝ)| ≤
      (s.phaseError : ℝ) ∧
    (if s.positive then
      s.point.toGridPoint.xiError c.grid s.phaseError < s.point.toGridPoint.xiApprox c.grid s.phase
    else s.point.toGridPoint.xiApprox c.grid s.phase <
      -s.point.toGridPoint.xiError c.grid s.phaseError) := by
  simp only [check, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨hpoint, hphase⟩, htail⟩, hmargin⟩
  have hp := s.point.valid_of_check (g := c.grid) hc.endpoint hc.cutoff hc.scalar
    hc.pi hc.base hc.radius hc.coefficients hpoint
  have hw : intervalWithinUnit
      (zetaGridCoordinateInterval c.pi c.rows.levels s.point.index) = true := by
    have hh := hpoint
    simp only [RationalGridPoint.check, Bool.and_eq_true] at hh
    exact hh.1
  have he := s.point.error_le_of_checks c.rows c.model hc.grid c.errors hc.moments
    hc.exponential hc.budget hc.endpoint hc.cutoff hc.pi hc.base hc.radius hw hc.bernoulli htail
  exact ⟨hp, XiSimplePhaseIntervals.abs_stirling_sub_le_of_check hc.phase hc.scalar
    (mem_height hc s.point) hphase,
    s.margin_of_check c.rows c.model hc.scalar hc.pi c.errors.cap he hmargin⟩

/-- The accepted orientation is the sign of the actual xi function, not its numerical model. -/
theorem sign_of_check {c : SharedXiGridCheck} (hc : c.Valid) (s : XiGridSignData)
    (h : c.check s = true) :
    if s.positive then 0 < xiCriticalLineValue (s.point.toGridPoint.height c.grid)
    else xiCriticalLineValue (s.point.toGridPoint.height c.grid) < 0 := by
  rcases validated hc s h with ⟨hp, hphase, hmargin⟩
  have hθ := (abs_sub_le (turingCountingPhase (s.point.toGridPoint.height c.grid))
    (turingStirlingPhase (s.point.toGridPoint.height c.grid)) (s.phase : ℝ)).trans
      (add_le_add (abs_turingCountingPhase_sub_stirling_le _) hphase)
  cases hs : s.positive with
  | true =>
    simp only [hs, ↓reduceIte] at hmargin ⊢
    exact xiCriticalLineValue_pos_of_approx (hp.norm_zeta_sub_value_le hc.grid) hθ hmargin
  | false =>
    simp only [hs, Bool.false_eq_true, ↓reduceIte] at hmargin ⊢
    exact xiCriticalLineValue_neg_of_approx (hp.norm_zeta_sub_value_le hc.grid) hθ hmargin

/-- Any proved actual phase bound can feed the unchanged zeta and sign-margin checks. -/
theorem sign_of_phase_bound {c : SharedXiGridCheck} (hc : c.Valid) (s : XiGridSignData)
    (hpoint : s.point.check c.rows.levels c.endpoint c.scalar c.pi c.base c.radius
      c.coefficients = true)
    (hθ : |turingCountingPhase (s.point.toGridPoint.height c.grid) - (s.phase : ℝ)| ≤
      1 / 10 + (s.phaseError : ℝ))
    (htail : checkEulerRemainder c.endpoint (ZetaCorrectionIntervals.critical (c.height s.point))
      c.model.order c.bernoulliCap s.risingCap s.tailCap = true)
    (hmargin : (s.checkCardinalMargin c.rows c.model.degree c.pi c.errors.cap ||
      s.checkSignMargin c.rows c.model.degree c.scalar c.pi c.errors.cap) = true) :
    if s.positive then 0 < xiCriticalLineValue (s.point.toGridPoint.height c.grid)
    else xiCriticalLineValue (s.point.toGridPoint.height c.grid) < 0 := by
  simp only [XiGridSignData.checkSignMargin, Bool.or_eq_true] at hmargin
  have hp := s.point.valid_of_check (g := c.grid) hc.endpoint hc.cutoff hc.scalar
    hc.pi hc.base hc.radius hc.coefficients hpoint
  have hw : intervalWithinUnit
      (zetaGridCoordinateInterval c.pi c.rows.levels s.point.index) = true := by
    have hh := hpoint
    simp only [RationalGridPoint.check, Bool.and_eq_true] at hh
    exact hh.1
  have he := s.point.error_le_of_checks c.rows c.model hc.grid c.errors hc.moments
    hc.exponential hc.budget hc.endpoint hc.cutoff hc.pi hc.base hc.radius hw hc.bernoulli htail
  rcases hmargin with hcardinal | hprojection | hlegacy
  · have hm := s.cardinal_margin_of_check c.rows c.model hc.pi c.errors.cap he hcardinal
    have hφ := s.cardinal_phase_of_check c.rows c.model.degree hc.pi c.errors.cap hθ hcardinal
    cases hs : s.positive with
    | true =>
      simp only [hs, ↓reduceIte] at hm ⊢
      exact xiCriticalLineValue_pos_of_projection (hp.norm_zeta_sub_value_le hc.grid) hφ hm
    | false =>
      simp only [hs, Bool.false_eq_true, ↓reduceIte] at hm ⊢
      exact xiCriticalLineValue_neg_of_projection (hp.norm_zeta_sub_value_le hc.grid) hφ hm
  · have hm := s.projection_margin_of_check c.rows c.model hc.scalar hc.pi
      c.errors.cap he hprojection
    have hφ := hθ.trans_lt hm.1
    cases hs : s.positive with
    | true =>
      simp only [hs, ↓reduceIte] at hm ⊢
      exact xiCriticalLineValue_pos_of_projection (hp.norm_zeta_sub_value_le hc.grid) hφ hm.2
    | false =>
      simp only [hs, Bool.false_eq_true, ↓reduceIte] at hm ⊢
      exact xiCriticalLineValue_neg_of_projection (hp.norm_zeta_sub_value_le hc.grid) hφ hm.2
  · have hm := s.margin_of_check c.rows c.model hc.scalar hc.pi c.errors.cap he hlegacy
    cases hs : s.positive with
    | true =>
      simp only [hs, ↓reduceIte] at hm ⊢
      exact xiCriticalLineValue_pos_of_approx (hp.norm_zeta_sub_value_le hc.grid) hθ hm
    | false =>
      simp only [hs, Bool.false_eq_true, ↓reduceIte] at hm ⊢
      exact xiCriticalLineValue_neg_of_approx (hp.norm_zeta_sub_value_le hc.grid) hθ hm

/-- Cardinal and rational-angle margins prove actual signs with the same shared zeta errors. -/
theorem sign_of_sign_check {c : SharedXiGridCheck} (hc : c.Valid) (s : XiGridSignData)
    (h : c.checkSign s = true) :
    if s.positive then 0 < xiCriticalLineValue (s.point.toGridPoint.height c.grid)
    else xiCriticalLineValue (s.point.toGridPoint.height c.grid) < 0 := by
  simp only [checkSign, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨hpoint, hphase⟩, htail⟩, hmargin⟩
  exact sign_of_phase_bound hc s hpoint
    (XiSimplePhaseIntervals.abs_counting_sub_le_of_check hc.phase hc.scalar
      (mem_height hc s.point) hphase) htail hmargin

end SharedXiGridCheck

/-- Actual sample signs feed rational rows independently of the chosen phase checker. -/
theorem XiSignRow.valid_of_grid_signs (c : SharedXiGridCheck)
    (base span : ℚ) (hs : 0 < span) (hb : c.model.base = (base : ℝ))
    (hr : c.model.radius = rationalGridRadius span) (p q : XiGridSignData)
    (hpos : if p.positive then 0 < xiCriticalLineValue (p.point.toGridPoint.height c.grid)
      else xiCriticalLineValue (p.point.toGridPoint.height c.grid) < 0)
    (hneg : if q.positive then 0 < xiCriticalLineValue (q.point.toGridPoint.height c.grid)
      else xiCriticalLineValue (q.point.toGridPoint.height c.grid) < 0)
    (hij : p.point.index < q.point.index) (hopposite : p.positive ≠ q.positive) :
    (rationalGridSignRow base span c.rows.levels p.point.index q.point.index).Valid := by
  have hl := p.point.toGridPoint.height_eq_rational c.grid base span hb hr
  have hu := q.point.toGridPoint.height_eq_rational c.grid base span hb hr
  rw [hl] at hpos
  rw [hu] at hneg
  refine ⟨rationalGridHeight_strictMono base span c.rows.levels hs hij, ?_⟩
  cases hp' : p.positive <;> cases hq' : q.positive <;>
    simp only [hp', hq', Bool.false_eq_true, ↓reduceIte] at hpos hneg hopposite
  · exact (hopposite rfl).elim
  · exact mul_neg_of_neg_of_pos hpos hneg
  · exact mul_neg_of_pos_of_neg hpos hneg
  · exact (hopposite rfl).elim

/-- Sign-only or legacy sample checks feed the unchanged rational sign-row interface. -/
theorem XiSignRow.valid_of_checked_sign_grid {c : SharedXiGridCheck} (hc : c.Valid)
    (base span : ℚ) (hs : 0 < span) (hb : c.model.base = (base : ℝ))
    (hr : c.model.radius = rationalGridRadius span) (p q : XiGridSignData)
    (hp : c.checkSign p = true) (hq : c.checkSign q = true)
    (hij : p.point.index < q.point.index) (hopposite : p.positive ≠ q.positive) :
    (rationalGridSignRow base span c.rows.levels p.point.index q.point.index).Valid :=
  valid_of_grid_signs c base span hs hb hr p q
    (SharedXiGridCheck.sign_of_sign_check hc p hp)
    (SharedXiGridCheck.sign_of_sign_check hc q hq) hij hopposite

/-- The original complete-error checks reuse the same rational sign-row assembler. -/
theorem XiSignRow.valid_of_checked_grid {c : SharedXiGridCheck} (hc : c.Valid)
    (base span : ℚ) (hs : 0 < span) (hb : c.model.base = (base : ℝ))
    (hr : c.model.radius = rationalGridRadius span) (p q : XiGridSignData)
    (hp : c.check p = true) (hq : c.check q = true)
    (hij : p.point.index < q.point.index) (hopposite : p.positive ≠ q.positive) :
    (rationalGridSignRow base span c.rows.levels p.point.index q.point.index).Valid :=
  valid_of_checked_sign_grid hc base span hs hb hr p q
    (SharedXiGridCheck.checkSign_of_check hp) (SharedXiGridCheck.checkSign_of_check hq)
    hij hopposite

end PrimeFactorUnimodality
