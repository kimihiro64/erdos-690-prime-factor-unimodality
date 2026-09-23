import Mathlib.Logic.Relation
import PrimeFactorUnimodality.Helpers.Analytic.KadiriElementaryBootstrap

/-! # Composable endpoint rows for the numerical zero-free bootstrap

A row contains only five scalar choices. Its validity consists of the
elementary side conditions, a nonpositive correction, and two closed-form
transform margins. The one-cell specialization of the existing grid theorem
covers every positive scale: no scale enumeration or quadrature is needed.
Ordered chains reuse a single polynomial and the same low-height condition.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- Scalar choices for one improvement of the high-zero region. -/
structure KadiriEndpointRow where
  angle : ℝ
  delta : ℝ
  kappa : ℝ
  cutoff : ℝ
  supportBound : ℝ

/-- An actual region for every multiplicity label and both signs of the ordinate. -/
def KadiriHighRegion (R T : ℝ) : Prop :=
  ∀ p : RiemannXiDivisorZeroIndex, T ≤ |(riemannXiDivisorZeroValue p).im| →
    1 / (R * log |(riemannXiDivisorZeroValue p).im|) ≤ 1 - (riemannXiDivisorZeroValue p).re

namespace KadiriEndpointRow

/-- The endpoint scale is determined by the target region, not by a generated witness. -/
def scale (r T : ℝ) : ℝ := 1 / (r * log T)

/-- The endpoint real coordinate retains the previous region and complete harmonic cutoff. -/
def sigma (row : KadiriEndpointRow) (R T : ℝ) (n : ℕ) : ℝ :=
  kadiriBootstrapSigma R n row.cutoff T

/-- The exact elementary correction, shared by all scales covered by this row. -/
def correction (row : KadiriEndpointRow) (R r T : ℝ) (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  kadiriElementaryCorrectionPolynomial row.angle (scale r T) (scale r T)
    (row.sigma R T n) row.kappa row.delta row.cutoff T (1 / r) (Finset.range (n + 1)) a

/-- Local numerical validity. No zero-location or polynomial hypotheses are hidden here. -/
structure Valid (row : KadiriEndpointRow) (R r T : ℝ) (n : ℕ) (a : ℕ → ℝ) : Prop where
  previous_pos : 0 < R
  target_pos : 0 < r
  height_ge : 10 ^ 9 ≤ T
  cutoff_ge : 4 ≤ row.cutoff
  degree_ge : 1 ≤ n
  angle_mem : π / 2 < row.angle ∧ row.angle < π
  scale_le : scale r T ≤ 1 / 2
  sigma_gt : 1 / 2 < row.sigma R T n
  delta_ge : 1 / 2 ≤ row.delta
  kappa_nonneg : 0 ≤ row.kappa
  kappa_lt : row.kappa < 1
  kappa_two : row.kappa ≤
    kadiriKappa₂ row.angle (scale r T) (2 * row.sigma R T n - 1) row.delta
  kappa_three : row.kappa ≤
    kadiriKappa₃ row.angle (scale r T) (2 * row.sigma R T n - 1) row.delta
  pole_pos : 0 < row.sigma R T n - scale r T + row.delta
  separation_nonneg : 0 ≤ 2 * row.sigma R T n - 1 - row.kappa * (1 + 2 * row.delta)
  cutoff_slack : row.kappa * (1 + 2 * row.delta) + 1 - row.sigma R T n ≤
    (2 * row.sigma R T n - 1 - row.kappa * (1 + 2 * row.delta)) * row.cutoff ^ 2
  support_pos : 0 < row.supportBound
  support_le : kadiriSupport row.angle ≤ row.supportBound
  exp_le : exp row.supportBound ≤
    1 + row.supportBound + row.supportBound ^ 2 / 2 + row.supportBound ^ 3 / (345 / 100)
  correction_nonpos : row.correction R r T n a ≤ 0
  lower_margin : kadiriBootstrapLogCoefficient row.angle row.kappa (Finset.range (n + 1)) a / r ≤
    kadiriTransformGapClosedForm row.angle (a 0) (a 1)
      (kadiriBootstrapLowerArgument R r n row.cutoff T)
  upper_margin : kadiriBootstrapLogCoefficient row.angle row.kappa (Finset.range (n + 1)) a / r ≤
    kadiriTransformGapClosedForm row.angle (a 0) (a 1) 1

/-- A single endpoint row covers the entire scale interval and absolute-height ray. -/
theorem Valid.highRegion {row : KadiriEndpointRow} {R r T : ℝ} {n : ℕ} {a : ℕ → ℝ}
    (h : row.Valid R r T n a)
    (ha : ∀ i ∈ Finset.range (n + 1), 0 ≤ a i) (ha₀ : 0 < a 0) (ha₁ : 0 < a 1)
    (hpoly : ∀ u : ℝ, 0 ≤ ∑ i ∈ Finset.range (n + 1), a i * cos ((i : ℝ) * u))
    (hlow : ∀ p : RiemannXiDivisorZeroIndex,
      |(riemannXiDivisorZeroValue p).im| < T → (riemannXiDivisorZeroValue p).re ≤ 1 / 2)
    (hhigh : KadiriHighRegion R T) : KadiriHighRegion r T := by
  intro p hp
  apply xi_zero_gap_of_elementary_grid_budget h.previous_pos h.target_pos h.height_ge
    h.cutoff_ge h.degree_ge h.angle_mem rfl h.scale_le rfl h.sigma_gt h.delta_ge
    h.kappa_nonneg h.kappa_lt h.kappa_two h.kappa_three h.pole_pos
    h.separation_nonneg h.cutoff_slack h.support_pos h.support_le h.exp_le
    a ha ha₀ ha₁ hpoly (fun q hq => (hlow q hq).trans h.sigma_gt.le) hhigh
    h.correction_nonpos 1 (by norm_num) (fun _ => T) (fun _ => by linarith [h.height_ge])
    (fun _ => Or.inl le_rfl) _ p hp
  intro j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  simp only [Fin.val_zero, Nat.cast_zero, zero_div, zero_mul, sub_zero]
  rw [kadiriTransformGap_eq_closedForm h.angle_mem,
    kadiriTransformGap_eq_closedForm h.angle_mem]
  exact le_min h.lower_margin h.upper_margin

end KadiriEndpointRow

/-- An ordered chain requires each target region to be exactly the next row's input. -/
def KadiriEndpointChain (n : ℕ) (a : ℕ → ℝ) (T R r : ℝ) : Prop :=
  Relation.ReflTransGen (fun previous target =>
    ∃ row : KadiriEndpointRow, row.Valid previous target T n a) R r

/-- One checked row gives a one-step chain. -/
theorem KadiriEndpointRow.Valid.chain {row : KadiriEndpointRow} {R r T : ℝ}
    {n : ℕ} {a : ℕ → ℝ} (h : row.Valid R r T n a) : KadiriEndpointChain n a T R r :=
  Relation.ReflTransGen.single ⟨row, h⟩

/-- Joining chains checks the common region exactly, without replaying any numerical row. -/
theorem KadiriEndpointChain.append {n : ℕ} {a : ℕ → ℝ} {T R r s : ℝ}
    (h : KadiriEndpointChain n a T R r) (h' : KadiriEndpointChain n a T r s) :
    KadiriEndpointChain n a T R s := h.trans h'

/-- The reusable assembler retains the same low-height input at every bootstrap step. -/
theorem KadiriEndpointChain.highRegion {n : ℕ} {a : ℕ → ℝ} {T R r : ℝ}
    (h : KadiriEndpointChain n a T R r)
    (ha : ∀ i ∈ Finset.range (n + 1), 0 ≤ a i) (ha₀ : 0 < a 0) (ha₁ : 0 < a 1)
    (hpoly : ∀ u : ℝ, 0 ≤ ∑ i ∈ Finset.range (n + 1), a i * cos ((i : ℝ) * u))
    (hlow : ∀ p : RiemannXiDivisorZeroIndex,
      |(riemannXiDivisorZeroValue p).im| < T → (riemannXiDivisorZeroValue p).re ≤ 1 / 2)
    (hhigh : KadiriHighRegion R T) : KadiriHighRegion r T := by
  induction h with
  | refl => exact hhigh
  | tail _ hstep ih =>
    obtain ⟨row, hrow⟩ := hstep
    exact hrow.highRegion ha ha₀ ha₁ hpoly hlow ih

end

end PrimeFactorUnimodality
