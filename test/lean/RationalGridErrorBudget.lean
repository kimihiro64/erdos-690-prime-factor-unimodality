import PrimeFactorUnimodality.Helpers.Analytic.RationalGridErrorBudget

/-! # Full grid-error interfaces and small rational boundary regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset
open LeanCert.Core
open Fourier
open PrimeFactorUnimodality.RationalGridErrorBudget

example (b : RationalGridErrorBudget) (r : RationalGridRows)
    (d : ZetaGroupedBlock) (hd : (r.attach d).Valid)
    (hm : ∀ k j, d.coefficientError k j = (b.moment k j : ℝ))
    {expHalf : IntervalRat} (he : Real.exp (1 / 2) ∈ expHalf)
    (h : b.check r d.cutoff d.degree expHalf = true) (p : RationalGridPoint)
    (hp : |p.toGridPoint.coordinate (r.attach d)| ≤ 1) :
    p.toGridPoint.error (r.attach d) ≤
      zetaEulerError d.cutoff ((1 / 2 : ℂ) + p.toGridPoint.height (r.attach d) * I) d.order +
        b.cap + p.error := by
  exact PrimeFactorUnimodality.RationalGridErrorBudget.error_le_of_check b r d hd hm he h p hp

def sampleRows : RationalGridRows :=
  ⟨[0], fun _ _ => ⟨2, 0⟩, 0,
    ⟨fun n => Vector.replicate (2 ^ (n + 1)) ⟨1, 0⟩, fun _ => 0⟩,
    fun _ => .leaf ⟨2, 0⟩ (1 / 4)⟩
def samplePoint : RationalGridPoint := ⟨0, 0, ⟨3, 0⟩, 0⟩
def piBox : IntervalRat := ⟨3, 4, by norm_num⟩

def sharedBudget : RationalGridErrorBudget := ⟨fun _ _ => 3 / 2, 15 / 4⟩
example : sharedBudget.bound sampleRows 2 1 (IntervalRat.singleton 2) = 15 / 4 :=
  by decide +kernel
example : sharedBudget.check sampleRows 2 1 (IntervalRat.singleton 2) = true :=
  by decide +kernel
example : ({sharedBudget with cap := 3}).check sampleRows 2 1 (IntervalRat.singleton 2) = false :=
  by decide +kernel

end

end PrimeFactorUnimodality.Tests
