import PrimeFactorUnimodality.Helpers.Analytic.RadixTwiddleChecks
import PrimeFactorUnimodality.Helpers.Analytic.XiGridEvaluation
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.RationalAlias

/-! # Rational checks discharge actual zeta-grid transform obligations

Shared moment enclosures remain a separate analytic input. Every Fourier
input, twiddle and arithmetic check is executable rational computation,
and its soundness feeds the existing zeta and actual xi sign consumers.
-/

namespace PrimeFactorUnimodality

open Complex Fourier Finset

/-- Compact coefficient rows and shared rational transform data. -/
structure RationalGridRows where
  groups : List ℤ
  coefficient : ℤ → ℕ → RationalPoint
  levels : ℕ
  twiddles : RationalTwiddles
  trace : ℕ → RationalTrace levels

/-- Interpret the rational coefficients and traces in the existing actual evaluator. -/
def RationalGridRows.attach (r : RationalGridRows) (d : ZetaGroupedBlock) : ZetaGridBlock :=
  ⟨{d with groups := r.groups.toFinset, coefficient := fun b j => (r.coefficient b j).toComplex},
    r.levels, fun j => (r.trace j).semantic r.twiddles⟩

/-- One shared phase check and one bounded rational check per transform column. -/
def RationalGridRows.check (r : RationalGridRows) (degree order : ℕ) : Bool :=
  decide r.groups.Nodup && checkTwiddleTables r.twiddles r.levels order &&
    allIndices fun j : Fin degree => (r.trace j.val).check r.twiddles
      (rationalAliasVector r.levels r.groups (fun b => r.coefficient b j.val))

/-- Successful rational checks establish all Fourier premises of the actual shared block. -/
theorem RationalGridRows.valid_of_check (r : RationalGridRows) (d : ZetaGroupedBlock)
    (hd : (r.attach d).shared.Valid) (order : ℕ)
    (h : r.check d.degree order = true) : (r.attach d).Valid := by
  simp only [RationalGridRows.check, Bool.and_eq_true, decide_eq_true_eq,
    allIndices_eq_true] at h
  have hp := checkTwiddleTables_sound r.twiddles r.levels order h.1.2
  refine ⟨hd, ?_⟩
  intro j hj
  have hcol := (r.trace j).valid_of_check hp
    (rationalAliasVector r.levels r.groups (fun b => r.coefficient b j))
    (h.2 ⟨j, mem_range.mp hj⟩)
  rw [rationalAliasVector_map _ _ h.1.1] at hcol
  exact hcol

/-- The executable checks feed the bound for actual zeta, not only a model Fourier sum. -/
theorem RationalGridRows.norm_zeta_sub_value_le (r : RationalGridRows) (d : ZetaGroupedBlock)
    (hd : (r.attach d).shared.Valid) (order : ℕ) (h : r.check d.degree order = true)
    (p : ZetaGridPoint) (hp : p.Valid (r.attach d)) :
    ‖riemannZeta ((1 / 2 : ℂ) + p.height (r.attach d) * I) - p.value (r.attach d)‖ ≤
      p.error (r.attach d) :=
  hp.norm_zeta_sub_value_le (r.valid_of_check d hd order h)

end PrimeFactorUnimodality
