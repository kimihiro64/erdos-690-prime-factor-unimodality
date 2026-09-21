import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

/-! A Table 6.6 endpoint certificate is one reusable fact about one published
    coefficient row.  The later compact data generator can emit one such
    object per interval and the existing formula assembler can project all six
    inequalities without duplicating its row proof. -/
structure DusartThetaTable66EndpointFacts
    (data : DusartThetaTable66CoefficientData) : Prop where
  lower_zero : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
    data.a0 * x ≤ Chebyshev.theta x
  upper_zero : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
    Chebyshev.theta x ≤ data.b0 * x
  lower_one_endpoint :
    data.right - data.a1 * data.right / Real.log data.right ≤
      Chebyshev.theta data.left
  upper_one_endpoint :
    Chebyshev.theta data.right ≤
      data.left + data.b1 * data.left / Real.log data.left
  lower_two_endpoint :
    data.right - data.a2 * data.right / Real.log data.right ^ 2 ≤
      Chebyshev.theta data.left
  upper_two_endpoint :
    Chebyshev.theta data.right ≤
      data.left + data.b2 * data.left / Real.log data.left ^ 2

theorem dusartThetaTable66_formula_bounds_of_endpoint_facts
    {data : DusartThetaTable66CoefficientData}
    (hdata : data ∈ dusartThetaTable6_6CoefficientData)
    (facts : DusartThetaTable66EndpointFacts data) :
    DusartThetaTable66FormulaBounds data := by
  exact dusartThetaTable66_formula_bounds_of_published_endpoints hdata
    facts.lower_zero facts.upper_zero facts.lower_one_endpoint
    facts.upper_one_endpoint facts.lower_two_endpoint facts.upper_two_endpoint

theorem hasDusartSymmetricThetaBoundsBelow_of_table66_endpoint_facts
    {X : Real}
    (cover : ∀ x : Real, 2 ≤ x → x ≤ X →
      ∃ data ∈ dusartThetaTable6_6CoefficientData,
        (data.left : Real) ≤ x ∧ x ≤ data.right)
    (facts : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      DusartThetaTable66EndpointFacts data) :
    HasDusartSymmetricThetaBoundsBelow X := by
  apply hasDusartSymmetricThetaBoundsBelow_of_table66_formula_data cover
  intro data hdata
  exact dusartThetaTable66_formula_bounds_of_endpoint_facts hdata
    (facts data hdata)

end

end PrimeFactorUnimodality
