import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import PrimeFactorUnimodality.Helpers.Analytic.ThetaFromPsi

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

open Filter Set
open Asymptotics
open scoped Topology

/-! A quantitative interface for the error term supplied by an explicit
prime-number theorem.  The point of this definition is that it records the
analytic estimate itself, rather than treating the desired log-fourth bound
as an imported theorem. -/
def HasPsiSqrtLogDecay (C c X : Real) : Prop :=
  ∀ x : Real, X ≤ x →
    |Chebyshev.psi x - x| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x))

def HasPsiLogRpowDecay (C c α X : Real) : Prop :=
  ∀ x : Real, X ≤ x →
    |Chebyshev.psi x - x| ≤
      C * x * Real.exp (-c * (Real.log x) ^ α)

def HasPsiLogRpowBigO (c α : Real) : Prop :=
  (fun x : Real => |Chebyshev.psi x - x|) =O[atTop]
    (fun x : Real => x * Real.exp (-c * (Real.log x) ^ α))

theorem exists_hasPsiLogRpowDecay_of_isBigO
    {c α : Real} (hbigO : HasPsiLogRpowBigO c α) :
    ∃ C X : Real, 0 ≤ C ∧ 0 < X ∧ HasPsiLogRpowDecay C c α X := by
  change (fun x : Real => |Chebyshev.psi x - x|) =O[atTop]
    (fun x : Real => x * Real.exp (-c * (Real.log x) ^ α)) at hbigO
  rw [isBigO_iff] at hbigO
  obtain ⟨K, hK⟩ := hbigO
  obtain ⟨T, hT⟩ := eventually_atTop.1 hK
  let C : Real := max K 0 + 1
  let X : Real := max T 2
  refine ⟨C, X, ?_, by dsimp [X]; linarith [le_max_right T 2], ?_⟩
  · dsimp [C]
    linarith [le_max_right K 0]
  · intro x hx
    have hx2 : (2 : Real) ≤ x := le_trans (le_max_right T 2) hx
    have hx_pos : 0 < x := by linarith
    have hg : 0 ≤ x * Real.exp (-c * (Real.log x) ^ α) := by positivity
    have hKx := hT x (le_trans (le_max_left T 2) hx)
    have hKC : K ≤ C := by
      dsimp [C]
      linarith [le_max_left K 0]
    calc
      |Chebyshev.psi x - x| ≤
          K * (x * Real.exp (-c * (Real.log x) ^ α)) := by
        simpa [Real.norm_eq_abs, norm_mul, Real.norm_of_nonneg hx_pos.le,
          abs_of_nonneg (Real.exp_pos _).le] using hKx
      _ ≤ C * (x * Real.exp (-c * (Real.log x) ^ α)) :=
        mul_le_mul_of_nonneg_right hKC hg
      _ = C * x * Real.exp (-c * (Real.log x) ^ α) := by ring

theorem exists_logFourth_envelope_of_rpow_decay
    {C c α : Real} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) :
    ∃ T : Real, ∀ t : Real, T ≤ t →
      C * Real.exp (-c * t ^ α) ≤ 1 / t ^ (4 : ℕ) := by
  by_cases hCzero : C = 0
  · refine ⟨1, ?_⟩
    intro t ht
    rw [hCzero, zero_mul]
    exact div_nonneg zero_le_one (by positivity)
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCzero)
    have hbase :
        Tendsto (fun u : Real => u ^ (4 / α : Real) * Real.exp (-c * u))
          atTop (𝓝 0) :=
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4 / α) c hc
    have harg : Tendsto (fun t : Real => t ^ α) atTop atTop :=
      tendsto_rpow_atTop hα
    have hcomp :
        Tendsto (fun t : Real => (t ^ α) ^ (4 / α : Real) *
          Real.exp (-c * t ^ α)) atTop (𝓝 0) := hbase.comp harg
    have hsmall : ∀ᶠ t : Real in atTop,
        (t ^ α) ^ (4 / α : Real) * Real.exp (-c * t ^ α) < C⁻¹ := by
      exact hcomp.eventually (Iio_mem_nhds (inv_pos.mpr hCpos))
    obtain ⟨T, hT⟩ := eventually_atTop.1 hsmall
    refine ⟨max T 1, ?_⟩
    intro t ht
    have ht1 : 1 ≤ t := le_trans (le_max_right T 1) ht
    have ht0 : 0 ≤ t := by linarith
    have hpow : (t ^ α) ^ (4 / α : Real) = t ^ (4 : ℕ) := by
      rw [← Real.rpow_mul ht0]
      field_simp [ne_of_gt hα]
      norm_num [Real.rpow_natCast]
    have hsmall_t := hT t (le_trans (le_max_left T 1) ht)
    have hmul := (mul_lt_mul_of_pos_left hsmall_t hCpos).le
    have hmul' : C * t ^ (4 : ℕ) * Real.exp (-c * t ^ α) ≤ 1 := by
      calc
        C * t ^ (4 : ℕ) * Real.exp (-c * t ^ α) =
            C * ((t ^ α) ^ (4 / α : Real) *
              Real.exp (-c * t ^ α)) := by rw [hpow]; ring
        _ ≤ 1 := by simpa [hCpos.ne'] using hmul
    have ht4pos : 0 < t ^ (4 : ℕ) := by positivity
    exact (le_div_iff₀ ht4pos).2 (by simpa [mul_assoc, mul_comm, mul_left_comm]
      using hmul')

theorem hasPsiLogFourthError_of_logRpowDecay_of_envelope
    {C D c α X : Real} (hX : 0 < X)
    (hdecay : HasPsiLogRpowDecay C c α X)
    (henvelope : ∀ x : Real, X ≤ x →
      C * Real.exp (-c * (Real.log x) ^ α) ≤
        D / (Real.log x) ^ (4 : ℕ)) :
    HasPsiLogFourthError D X := by
  intro x hx
  have hx_pos : 0 < x := lt_of_lt_of_le hX hx
  have herror := hdecay x hx
  have henvelope_x := henvelope x hx
  calc
    |Chebyshev.psi x - x| ≤
        C * x * Real.exp (-c * (Real.log x) ^ α) := herror
    _ = (C * Real.exp (-c * (Real.log x) ^ α)) * x := by ring
    _ ≤ (D / (Real.log x) ^ (4 : ℕ)) * x :=
      mul_le_mul_of_nonneg_right henvelope_x hx_pos.le
    _ = D * x / (Real.log x) ^ 4 := by ring_nf

/-! The same conversion with a unit coefficient is useful when an explicit
PNT gives an arbitrary Big-O constant: the cutoff absorbs that constant. -/
theorem exists_hasPsiLogFourthError_of_logRpowDecay_unit
    {C c α X : Real} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α)
    (hdecay : HasPsiLogRpowDecay C c α X) :
    ∃ Y : Real, X ≤ Y ∧ HasPsiLogFourthError 1 Y := by
  obtain ⟨T, hT⟩ := exists_logFourth_envelope_of_rpow_decay hC hc hα
  let Y : Real := max X (max (Real.exp T) 2)
  refine ⟨Y, le_max_left _ _, ?_⟩
  intro x hx
  have hmax_le_x : max (Real.exp T) 2 ≤ x :=
    le_trans (le_max_right X (max (Real.exp T) 2)) hx
  have hx2 : (2 : Real) ≤ x :=
    le_trans (le_max_right (Real.exp T) 2) hmax_le_x
  have hx_pos : 0 < x := by linarith
  have hYpos : 0 < Y := by
    dsimp [Y]
    positivity
  have hdecayY : HasPsiLogRpowDecay C c α Y := by
    intro z hz
    exact hdecay z (le_trans (le_max_left X (max (Real.exp T) 2)) hz)
  have henvY : ∀ z : Real, Y ≤ z →
      C * Real.exp (-c * (Real.log z) ^ α) ≤
        1 / (Real.log z) ^ (4 : ℕ) := by
    intro z hz
    have hz_pos : 0 < z := lt_of_lt_of_le hYpos hz
    have hzmax : max (Real.exp T) 2 ≤ z :=
      le_trans (le_max_right X (max (Real.exp T) 2)) hz
    exact hT (Real.log z) ((Real.le_log_iff_exp_le hz_pos).2
      (le_trans (le_max_left (Real.exp T) 2) hzmax))
  exact (hasPsiLogFourthError_of_logRpowDecay_of_envelope
    (C := C) (D := 1) hYpos hdecayY henvY) x hx

/-! The same envelope conversion is needed when the analytic argument is
stated directly for Chebyshev's theta function.  Keeping this bridge here
means that a zero-free-region proof can expose a theta error estimate without
passing through a pre-packaged Dusart theorem. -/
def HasThetaLogRpowDecay (C c α X : Real) : Prop :=
  ∀ x : Real, X ≤ x →
    |Chebyshev.theta x - x| ≤
      C * x * Real.exp (-c * (Real.log x) ^ α)

/-! The source-level decay bridge is kept separate from the numerical
prime-power correction.  Once an independently proved correction has the
same r-power envelope, the psi estimate transfers by the triangle inequality
without passing through a pre-packaged Dusart theorem. -/
theorem hasThetaLogRpowDecay_of_psiLogRpowDecay_of_correction
    {C D c α X : Real}
    (psiDecay : HasPsiLogRpowDecay C c α X)
    (correction : ∀ x : Real, X ≤ x →
      |Chebyshev.theta x - Chebyshev.psi x| ≤
        D * x * Real.exp (-c * (Real.log x) ^ α)) :
    HasThetaLogRpowDecay (C + D) c α X := by
  intro x hx
  calc
    |Chebyshev.theta x - x| ≤
        |Chebyshev.theta x - Chebyshev.psi x| +
          |Chebyshev.psi x - x| := by
      rw [show Chebyshev.theta x - x =
        (Chebyshev.theta x - Chebyshev.psi x) +
          (Chebyshev.psi x - x) by ring]
      exact abs_add_le _ _
    _ ≤ D * x * Real.exp (-c * (Real.log x) ^ α) +
          C * x * Real.exp (-c * (Real.log x) ^ α) :=
      add_le_add (correction x hx) (psiDecay x hx)
    _ = (C + D) * x * Real.exp (-c * (Real.log x) ^ α) := by ring

/-! A direct classical-bound interface for theta.  The envelope hypothesis is
kept explicit: proving it is part of the numerical zero-free-region argument,
not an imported Dusart estimate. -/
def HasThetaClassicalBound (A B C R X : Real) : Prop :=
  ∀ x : Real, X ≤ x →
    |Chebyshev.theta x - x| ≤
      A * (Real.log x / R) ^ B *
        Real.exp (-C * (Real.log x / R) ^ ((1 : Real) / 2)) * x

theorem hasThetaLogFourthError_of_classicalBound_of_envelope
    {A B C R D X : Real} (hX : 0 < X)
    (bound : HasThetaClassicalBound A B C R X)
    (envelope : ∀ x : Real, X ≤ x →
      A * (Real.log x / R) ^ B *
          Real.exp (-C * (Real.log x / R) ^ ((1 : Real) / 2)) ≤
        D / (Real.log x) ^ (4 : ℕ)) :
    HasThetaLogFourthError D X := by
  intro x hx
  have hx_pos : 0 < x := lt_of_lt_of_le hX hx
  have hbound := bound x hx
  have henvelope := envelope x hx
  calc
    |Chebyshev.theta x - x| ≤
        A * (Real.log x / R) ^ B *
            Real.exp (-C * (Real.log x / R) ^ ((1 : Real) / 2)) * x := hbound
    _ = (A * (Real.log x / R) ^ B *
          Real.exp (-C * (Real.log x / R) ^ ((1 : Real) / 2))) * x := by ring
    _ ≤ (D / (Real.log x) ^ (4 : ℕ)) * x :=
      mul_le_mul_of_nonneg_right henvelope hx_pos.le
    _ = D * x / (Real.log x) ^ 4 := by ring_nf

theorem hasThetaLogFourthError_of_logRpowDecay_of_envelope
    {C D c α X : Real} (hX : 0 < X)
    (hdecay : HasThetaLogRpowDecay C c α X)
    (henvelope : ∀ x : Real, X ≤ x →
      C * Real.exp (-c * (Real.log x) ^ α) ≤
        D / (Real.log x) ^ (4 : ℕ)) :
    HasThetaLogFourthError D X := by
  intro x hx
  have hx_pos : 0 < x := lt_of_lt_of_le hX hx
  have herror := hdecay x hx
  have henvelope_x := henvelope x hx
  calc
    |Chebyshev.theta x - x| ≤
        C * x * Real.exp (-c * (Real.log x) ^ α) := herror
    _ = (C * Real.exp (-c * (Real.log x) ^ α)) * x := by ring
    _ ≤ (D / (Real.log x) ^ (4 : ℕ)) * x :=
      mul_le_mul_of_nonneg_right henvelope_x hx_pos.le
    _ = D * x / (Real.log x) ^ 4 := by ring_nf

theorem exists_hasThetaLogFourthError_of_logRpowDecay_unit
    {C c α X : Real} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α)
    (hdecay : HasThetaLogRpowDecay C c α X) :
    ∃ Y : Real, X ≤ Y ∧ HasThetaLogFourthError 1 Y := by
  obtain ⟨T, hT⟩ := exists_logFourth_envelope_of_rpow_decay hC hc hα
  let Y : Real := max X (max (Real.exp T) 2)
  refine ⟨Y, le_max_left _ _, ?_⟩
  intro x hx
  have hmax_le_x : max (Real.exp T) 2 ≤ x :=
    le_trans (le_max_right X (max (Real.exp T) 2)) hx
  have hx2 : (2 : Real) ≤ x :=
    le_trans (le_max_right (Real.exp T) 2) hmax_le_x
  have hx_pos : 0 < x := by linarith
  have hYpos : 0 < Y := by
    dsimp [Y]
    positivity
  have hdecayY : HasThetaLogRpowDecay C c α Y := by
    intro z hz
    exact hdecay z (le_trans (le_max_left X (max (Real.exp T) 2)) hz)
  have henvY : ∀ z : Real, Y ≤ z →
      C * Real.exp (-c * (Real.log z) ^ α) ≤
        1 / (Real.log z) ^ (4 : ℕ) := by
    intro z hz
    have hz_pos : 0 < z := lt_of_lt_of_le hYpos hz
    have hzmax : max (Real.exp T) 2 ≤ z :=
      le_trans (le_max_right X (max (Real.exp T) 2)) hz
    exact hT (Real.log z) ((Real.le_log_iff_exp_le hz_pos).2
      (le_trans (le_max_left (Real.exp T) 2) hzmax))
  exact (hasThetaLogFourthError_of_logRpowDecay_of_envelope
    (C := C) (D := 1) hYpos hdecayY henvY) x hx

theorem exists_hasThetaLogFourthError_of_logRpowDecay_of_pos_coefficient
    {C D c α X : Real} (hC : 0 ≤ C) (hD : 0 < D)
    (hc : 0 < c) (hα : 0 < α)
    (hdecay : HasThetaLogRpowDecay C c α X) :
    ∃ Y : Real, X ≤ Y ∧ HasThetaLogFourthError D Y := by
  have hCD : 0 ≤ C / D := div_nonneg hC hD.le
  obtain ⟨T, hT⟩ := exists_logFourth_envelope_of_rpow_decay
    (C := C / D) hCD hc hα
  let Y : Real := max X (max (Real.exp T) 2)
  refine ⟨Y, le_max_left _ _, ?_⟩
  have hYpos : 0 < Y := by
    dsimp [Y]
    positivity
  have hdecayY : HasThetaLogRpowDecay C c α Y := by
    intro z hz
    exact hdecay z (le_trans (le_max_left X (max (Real.exp T) 2)) hz)
  have henv : ∀ z : Real, Y ≤ z →
      C * Real.exp (-c * (Real.log z) ^ α) ≤
        D / (Real.log z) ^ (4 : ℕ) := by
    intro z hz
    have hz_pos : 0 < z := lt_of_lt_of_le hYpos hz
    have hzmax : max (Real.exp T) 2 ≤ z :=
      le_trans (le_max_right X (max (Real.exp T) 2)) hz
    have henv_unit := hT (Real.log z) ((Real.le_log_iff_exp_le hz_pos).2
      (le_trans (le_max_left (Real.exp T) 2) hzmax))
    have hscaled := mul_le_mul_of_nonneg_left henv_unit hD.le
    have hscaled' : C * Real.exp (-c * (Real.log z) ^ α) ≤
        D * (1 / (Real.log z) ^ (4 : ℕ)) := by
      calc
        C * Real.exp (-c * (Real.log z) ^ α) =
            D * ((C / D) * Real.exp (-c * (Real.log z) ^ α)) := by
              field_simp
        _ ≤ D * (1 / (Real.log z) ^ (4 : ℕ)) := hscaled
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaled'
  exact hasThetaLogFourthError_of_logRpowDecay_of_envelope
    (C := C) (D := D) hYpos hdecayY henv

/-! Any strictly positive target coefficient can be reached by increasing the
cutoff.  This is the quantitative form needed when an explicit PNT supplies
an arbitrary Big-O constant but the downstream Dusart budget reserves a
smaller fixed coefficient. -/
theorem exists_hasPsiLogFourthError_of_logRpowDecay_of_pos_coefficient
    {C D c α X : Real} (hC : 0 ≤ C) (hD : 0 < D)
    (hc : 0 < c) (hα : 0 < α)
    (hdecay : HasPsiLogRpowDecay C c α X) :
    ∃ Y : Real, X ≤ Y ∧ HasPsiLogFourthError D Y := by
  have hCD : 0 ≤ C / D := div_nonneg hC hD.le
  obtain ⟨T, hT⟩ := exists_logFourth_envelope_of_rpow_decay
    (C := C / D) hCD hc hα
  let Y : Real := max X (max (Real.exp T) 2)
  refine ⟨Y, le_max_left _ _, ?_⟩
  have hYpos : 0 < Y := by
    dsimp [Y]
    positivity
  have hdecayY : HasPsiLogRpowDecay C c α Y := by
    intro z hz
    exact hdecay z (le_trans (le_max_left X (max (Real.exp T) 2)) hz)
  have henvY : ∀ z : Real, Y ≤ z →
      C * Real.exp (-c * (Real.log z) ^ α) ≤
        D / (Real.log z) ^ (4 : ℕ) := by
    intro z hz
    have hz_pos : 0 < z := lt_of_lt_of_le hYpos hz
    have hzmax : max (Real.exp T) 2 ≤ z :=
      le_trans (le_max_right X (max (Real.exp T) 2)) hz
    have henv_unit := hT (Real.log z) ((Real.le_log_iff_exp_le hz_pos).2
      (le_trans (le_max_left (Real.exp T) 2) hzmax))
    have hscaled := mul_le_mul_of_nonneg_left henv_unit hD.le
    have hscaled' : C * Real.exp (-c * (Real.log z) ^ α) ≤
        D * (1 / (Real.log z) ^ (4 : ℕ)) := by
      calc
        C * Real.exp (-c * (Real.log z) ^ α) =
            D * ((C / D) * Real.exp (-c * (Real.log z) ^ α)) := by
              field_simp
        _ ≤ D * (1 / (Real.log z) ^ (4 : ℕ)) := hscaled
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaled'
  exact hasPsiLogFourthError_of_logRpowDecay_of_envelope
    (C := C) (D := D) hYpos hdecayY henvY

theorem exists_hasPsiLogFourthError_of_logRpowBigO_of_pos_coefficient
    {D c α : Real} (hD : 0 < D) (hc : 0 < c) (hα : 0 < α)
    (hbigO : HasPsiLogRpowBigO c α) :
    ∃ Y : Real, HasPsiLogFourthError D Y := by
  obtain ⟨C, X, hC, hX, hdecay⟩ :=
    exists_hasPsiLogRpowDecay_of_isBigO hbigO
  obtain ⟨Y, hXY, herror⟩ :=
    exists_hasPsiLogFourthError_of_logRpowDecay_of_pos_coefficient
      hC hD hc hα hdecay
  exact ⟨Y, herror⟩

theorem exists_hasPsiLogFourthError_of_logRpowDecay
    {C c α X : Real} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α)
    (hdecay : HasPsiLogRpowDecay C c α X) :
    ∃ Y : Real, X ≤ Y ∧ HasPsiLogFourthError C Y := by
  obtain ⟨T, hT⟩ := exists_logFourth_envelope_of_rpow_decay
    (C := (1 : Real)) (by norm_num) hc hα
  let Y : Real := max X (max (Real.exp T) 2)
  refine ⟨Y, le_max_left _ _, ?_⟩
  intro x hx
  have hmax_le_x : max (Real.exp T) 2 ≤ x :=
    le_trans (le_max_right X (max (Real.exp T) 2)) hx
  have hx2 : (2 : Real) ≤ x :=
    le_trans (le_max_right (Real.exp T) 2) hmax_le_x
  have hx_pos : 0 < x := by linarith
  have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have henv_unit := hT (Real.log x) ((Real.le_log_iff_exp_le hx_pos).2
    (le_trans (le_max_left (Real.exp T) 2) hmax_le_x))
  have henv : C * Real.exp (-c * (Real.log x) ^ α) ≤
      C / (Real.log x) ^ (4 : ℕ) := by
    have hscaled := mul_le_mul_of_nonneg_left henv_unit hC
    simp only [one_mul] at hscaled
    calc
      C * Real.exp (-c * (Real.log x) ^ α) ≤
          C * (1 / (Real.log x) ^ (4 : ℕ)) := hscaled
      _ = C / (Real.log x) ^ (4 : ℕ) := by ring
  have hbound := hdecay x (le_trans (le_max_left _ _) hx)
  calc
    |Chebyshev.psi x - x| ≤
        C * x * Real.exp (-c * (Real.log x) ^ α) := hbound
    _ = (C * Real.exp (-c * (Real.log x) ^ α)) * x := by ring
    _ ≤ (C / (Real.log x) ^ (4 : ℕ)) * x :=
      mul_le_mul_of_nonneg_right henv hx_pos.le
    _ = C * x / (Real.log x) ^ 4 := by ring

private theorem sqrtLog_pow_eight_eq_log_pow_four
    {t : Real} (ht : 0 ≤ t) :
    (Real.sqrt t) ^ (8 : ℕ) = t ^ (4 : ℕ) := by
  rw [show (8 : ℕ) = 2 * 4 by norm_num, pow_mul]
  rw [show (Real.sqrt t) ^ 2 = t by exact Real.sq_sqrt ht]

/-! Exponential square-root-log decay is eventually stronger than every fixed
power of `log`.  This is the analytic conversion needed before an explicit
finite cutoff is supplied. -/
theorem exists_hasPsiLogFourthError_of_sqrtLogDecay
    {C c X : Real} (hC : 0 ≤ C) (hc : 0 < c) (hX : 0 < X)
    (hdecay : HasPsiSqrtLogDecay C c X) :
    ∃ Y : Real, X ≤ Y ∧ HasPsiLogFourthError 1 Y := by
  by_cases hCzero : C = 0
  · refine ⟨X, le_rfl, ?_⟩
    intro x hx
    have hzero : |Chebyshev.psi x - x| ≤ 0 := by
      simpa [hCzero] using hdecay x hx
    have hx_nonneg : 0 ≤ x := (lt_of_lt_of_le hX hx).le
    have habs : |Chebyshev.psi x - x| = 0 := le_antisymm hzero (abs_nonneg _)
    rw [habs]
    exact div_nonneg (by positivity) (by positivity)
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCzero)
    have hdecay_zero :
        Tendsto (fun t : Real => t ^ (8 : Real) * Real.exp (-c * t))
          atTop (𝓝 0) :=
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 8 c hc
    have hsqrt_atTop : Tendsto (fun t : Real => Real.sqrt t) atTop atTop := by
      simpa [Real.sqrt_eq_rpow] using
        (tendsto_rpow_atTop (by norm_num : (0 : Real) < 1 / 2))
    have hdecay_sqrt :
        Tendsto (fun t : Real => (Real.sqrt t) ^ (8 : Real) *
          Real.exp (-c * Real.sqrt t)) atTop (𝓝 0) := by
      exact hdecay_zero.comp hsqrt_atTop
    have hsmall : ∀ᶠ t : Real in atTop,
        (Real.sqrt t) ^ (8 : Real) * Real.exp (-c * Real.sqrt t) < C⁻¹ := by
      apply (hdecay_sqrt.eventually (show Set.Iio C⁻¹ ∈ 𝓝 (0 : Real) by
        exact Iio_mem_nhds (inv_pos.mpr hCpos))).mono
      intro t ht
      exact ht
    obtain ⟨T, hT⟩ := (eventually_atTop.1 hsmall)
    let Y : Real := max X (max (Real.exp T) 2)
    refine ⟨Y, le_max_left _ _, ?_⟩
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le hX (le_trans (le_max_left _ _) hx)
    have hY_le_x : Y ≤ x := hx
    have hmax_le_x : max (Real.exp T) 2 ≤ x :=
      le_trans (le_max_right X (max (Real.exp T) 2)) hY_le_x
    have hT_exp : Real.exp T ≤ x :=
      le_trans (le_max_left (Real.exp T) 2) hmax_le_x
    have hx_two : (2 : Real) ≤ x :=
      le_trans (le_max_right (Real.exp T) 2) hmax_le_x
    have hT_log : T ≤ Real.log x := by
      exact (Real.le_log_iff_exp_le hx_pos).2 hT_exp
    have hlog_nonneg : 0 ≤ Real.log x := by
      exact (Real.log_pos (by linarith)).le
    have hsmall_x := hT (Real.log x) hT_log
    have hpow := sqrtLog_pow_eight_eq_log_pow_four hlog_nonneg
    have hbound :
        C * Real.exp (-c * Real.sqrt (Real.log x)) ≤
          1 / (Real.log x) ^ (4 : ℕ) := by
      have hmul := (mul_lt_mul_of_pos_left hsmall_x hCpos).le
      have hpow' : (Real.sqrt (Real.log x)) ^ (8 : Real) =
          (Real.log x) ^ (4 : ℕ) := by
        simpa [Real.rpow_natCast] using hpow
      have hmul' : C * ((Real.log x) ^ (4 : ℕ) *
          Real.exp (-c * Real.sqrt (Real.log x))) ≤ C * C⁻¹ := by
        calc
          C * ((Real.log x) ^ (4 : ℕ) *
              Real.exp (-c * Real.sqrt (Real.log x))) =
              C * ((Real.sqrt (Real.log x)) ^ (8 : Real) *
                Real.exp (-c * Real.sqrt (Real.log x))) := by rw [hpow']
          _ ≤ C * C⁻¹ := hmul
      have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
      have hlog4_pos : 0 < (Real.log x) ^ (4 : ℕ) := by positivity
      have hmul'' : C * Real.exp (-c * Real.sqrt (Real.log x)) *
          (Real.log x) ^ (4 : ℕ) ≤ 1 := by
        calc
          C * Real.exp (-c * Real.sqrt (Real.log x)) *
              (Real.log x) ^ (4 : ℕ) =
              C * ((Real.log x) ^ (4 : ℕ) *
                Real.exp (-c * Real.sqrt (Real.log x))) := by ring
          _ ≤ 1 := by simpa [hCpos.ne'] using hmul'
      exact (le_div_iff₀ hlog4_pos).2 hmul''
    calc
      |Chebyshev.psi x - x| ≤
          C * x * Real.exp (-c * Real.sqrt (Real.log x)) := hdecay x
            (le_trans (le_max_left _ _) hx)
      _ = (C * Real.exp (-c * Real.sqrt (Real.log x))) * x := by ring
      _ ≤ (1 / (Real.log x) ^ (4 : ℕ)) * x :=
        mul_le_mul_of_nonneg_right hbound hx_pos.le
      _ = 1 * x / (Real.log x) ^ 4 := by ring

/-! The same square-root-log conversion can be closed across the explicit
prime-power cutoff.  This is the source-level bridge needed when an analytic
PNT supplies a square-root-log estimate for `psi`: the only extra unit in the
theta coefficient is the independently proved `theta - psi` envelope. -/
theorem exists_hasThetaLogFourthError_of_sqrtLogDecay
    {C c X : Real} (hC : 0 ≤ C) (hc : 0 < c) (hX : 0 < X)
    (hdecay : HasPsiSqrtLogDecay C c X) :
    ∃ Y : Real, X ≤ Y ∧ (4e18 : Real) ≤ Y ∧
      HasThetaLogFourthError 2 Y := by
  obtain ⟨Y₀, hXY₀, hpsi⟩ :=
    exists_hasPsiLogFourthError_of_sqrtLogDecay hC hc hX hdecay
  let Y : Real := max (4e18 : Real) Y₀
  have h4Y : (4e18 : Real) ≤ Y := le_max_left _ _
  have hY₀ : Y₀ ≤ Y := le_max_right _ _
  have hXY : X ≤ Y := hXY₀.trans hY₀
  have hpsiY : HasPsiLogFourthError 1 Y := by
    intro x hx
    exact hpsi x (hY₀.trans hx)
  refine ⟨Y, hXY, h4Y, ?_⟩
  convert hasThetaLogFourthError_of_psiLogFourthError h4Y hpsiY using 1
  norm_num

/-! The general log-power version of the preceding bridge.  This keeps the
source-level decay supplied by the medium PNT separate from the explicit
prime-power correction: the former first yields a logarithmic fourth-power
error for `psi`, and the latter is then added once at the published cutoff. -/
theorem exists_hasThetaLogFourthError_of_psiLogRpowDecay
    {C c α X : Real} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α)
    (hdecay : HasPsiLogRpowDecay C c α X) :
    ∃ Y : Real, X ≤ Y ∧ (4e18 : Real) ≤ Y ∧
      HasThetaLogFourthError (C + 1) Y := by
  obtain ⟨Y₀, hXY₀, hpsi⟩ :=
    exists_hasPsiLogFourthError_of_logRpowDecay hC hc hα hdecay
  let Y : Real := max (4e18 : Real) Y₀
  have h4Y : (4e18 : Real) ≤ Y := le_max_left _ _
  have hY₀ : Y₀ ≤ Y := le_max_right _ _
  have hXY : X ≤ Y := hXY₀.trans hY₀
  have hpsiY : HasPsiLogFourthError C Y := by
    intro x hx
    exact hpsi x (hY₀.trans hx)
  refine ⟨Y, hXY, h4Y, ?_⟩
  exact hasThetaLogFourthError_of_psiLogFourthError h4Y hpsiY

end

end PrimeFactorUnimodality
