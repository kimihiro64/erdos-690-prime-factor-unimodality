import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.Table66Assembly
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.Table66EndpointData

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

/-! A published Table 6.6 row is certified by a covering list of smaller
intervals. Each cell reuses one proved theta enclosure for all six columns.
A pair of whole-row endpoint values cannot certify the published ranges. -/
structure DusartThetaTable66EndpointFacts
    (data : DusartThetaTable66CoefficientData) : Prop where
  cells : ∃ cells : List DusartThetaTable66Cell,
    DusartThetaTable66CellsCover data cells ∧ ∀ cell ∈ cells, cell.Valid data

theorem dusartThetaTable66_formula_bounds_of_endpoint_facts
    {data : DusartThetaTable66CoefficientData}
    (hdata : data ∈ dusartThetaTable6_6CoefficientData)
    (facts : DusartThetaTable66EndpointFacts data) :
    DusartThetaTable66FormulaBounds data := by
  obtain ⟨cells, cover, valid⟩ := facts.cells
  exact dusartThetaTable66_formula_bounds_of_cells
    (dusartThetaTable6_6CoefficientData_left_at_least_eight data hdata)
    (dusartThetaTable6_6CoefficientData_coefficients_nonneg data hdata)
    (dusartThetaTable6_6CoefficientData_correction_coefficients data hdata)
    cover valid

theorem hasDusartSymmetricThetaBoundsBelow_of_prefix_and_table66_endpoint_facts
    {x₀ X : Real} (h2x₀ : (2 : Real) ≤ x₀)
    (hprefix : HasDusartSymmetricThetaBoundsBelow x₀)
    (cover : ∀ x : Real, x₀ ≤ x → x ≤ X →
      ∃ data ∈ dusartThetaTable6_6CoefficientData,
        (data.left : Real) ≤ x ∧ x ≤ data.right)
    (facts : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      DusartThetaTable66EndpointFacts data) :
    HasDusartSymmetricThetaBoundsBelow X := by
  apply hasDusartSymmetricThetaBoundsBelow_of_prefix_and_table66_coefficient_bounds
    h2x₀ hprefix cover
  · intro data hdata
    exact (dusartThetaTable66_formula_bounds_of_endpoint_facts hdata
      (facts data hdata)).lower_zero
  · intro data hdata
    exact (dusartThetaTable66_formula_bounds_of_endpoint_facts hdata
      (facts data hdata)).upper_zero

end

end PrimeFactorUnimodality
