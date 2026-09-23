import PrimeFactorUnimodality.Helpers.Analytic.CheckedZetaGridPoints
import PrimeFactorUnimodality.Helpers.Analytic.ComplexPolynomialIntervals

/-! # Short per-sample enclosures from retained rational Fourier arrays

One lookup per Taylor column and a Horner fold enclose the existing grid
value. No input moment, transform or Dirichlet prefix is replayed per sample.
The short rational correction is included without dropping its separate
error budget from the actual zeta theorem.
-/

namespace PrimeFactorUnimodality.RationalGridRows

open Complex Fourier Finset LeanCert.Core ZMod

/-- Select one coefficient from the retained transform output, including signed indices. -/
def sampleCoefficient (r : RationalGridRows) (index : ℤ) (column : ℕ) : RationalPoint :=
  (r.trace column).values[(index : ZMod (2 ^ r.levels)).val]'(val_lt _)

/-- A short Horner enclosure followed by the stored rational correction. -/
def valueInterval (r : RationalGridRows) (p : RationalGridPoint) (P : IntervalRat)
    (degree : ℕ) : ComplexInterval :=
  (ComplexInterval.polynomial
    (ComplexInterval.real (zetaGridCoordinateInterval P r.levels p.index))
    (fun j => ComplexInterval.point (r.sampleCoefficient p.index j)) 0 degree).add
      (ComplexInterval.point p.correction)

/-- The interval encloses the exact interpreted grid value, not a new approximate model. -/
theorem mem_valueInterval (r : RationalGridRows) (d : ZetaGroupedBlock) (p : RationalGridPoint)
    {P : IntervalRat} (hpi : Real.pi ∈ P) :
    p.toGridPoint.value (r.attach d) ∈ r.valueInterval p P d.degree := by
  have hcoord : p.toGridPoint.coordinate (r.attach d) ∈
      zetaGridCoordinateInterval P r.levels p.index :=
    mem_zetaGridCoordinateInterval hpi r.levels p.index
  have hpoly := ComplexInterval.mem_polynomial (ComplexInterval.mem_real hcoord)
    (fun j => (r.sampleCoefficient p.index j).toComplex)
    (fun j => ComplexInterval.point (r.sampleCoefficient p.index j)) 0 d.degree
    (fun j _ => ComplexInterval.mem_point (r.sampleCoefficient p.index j))
  have h := ComplexInterval.mem_add hpoly (ComplexInterval.mem_point p.correction)
  convert h using 1 <;> simp only [valueInterval, ZetaGridPoint.value, RationalGridRows.attach,
    RationalGridPoint.toGridPoint, RationalTrace.values_semantic, Vector.getElem_map,
    Nat.zero_add, sampleCoefficient, ZetaGridPoint.coordinate]
  rfl

end PrimeFactorUnimodality.RationalGridRows
