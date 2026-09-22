import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.Table66Subintervals

set_option autoImplicit false

/-! # Published theta-table coefficients and checked interval coverage

The decimal coefficients are data, not proofs about theta. This module checks
their arithmetic side conditions and closed-interval coverage independently
of any prime enumeration.
-/

namespace PrimeFactorUnimodality

noncomputable section

def dusartThetaTable6_6CoefficientData :
    List DusartThetaTable66CoefficientData := [
  { left := 100000000, right := 200000000,
    a0 := 99985 / 100000, b0 := 99998 / 100000,
    a1 := 275 / 100000, b1 := -44 / 100000,
    a2 := 5062 / 100000, b2 := -851 / 100000 },
  { left := 200000000, right := 300000000,
    a0 := 99989 / 100000, b0 := 99997 / 100000,
    a1 := 201 / 100000, b1 := -65 / 100000,
    a2 := 3847 / 100000, b2 := -1275 / 100000 },
  { left := 300000000, right := 400000000,
    a0 := 99991 / 100000, b0 := 99998 / 100000,
    a1 := 165 / 100000, b1 := -57 / 100000,
    a2 := 3256 / 100000, b2 := -1131 / 100000 },
  { left := 400000000, right := 500000000,
    a0 := 99993 / 100000, b0 := 99998 / 100000,
    a1 := 124 / 100000, b1 := -49 / 100000,
    a2 := 2447 / 100000, b2 := -988 / 100000 },
  { left := 500000000, right := 600000000,
    a0 := 99992 / 100000, b0 := 99998 / 100000,
    a1 := 152 / 100000, b1 := -52 / 100000,
    a2 := 3039 / 100000, b2 := -1061 / 100000 },
  { left := 600000000, right := 700000000,
    a0 := 99994 / 100000, b0 := 99999 / 100000,
    a1 := 103 / 100000, b1 := -38 / 100000,
    a2 := 2095 / 100000, b2 := -785 / 100000 },
  { left := 700000000, right := 800000000,
    a0 := 99993 / 100000, b0 := 99998 / 100000,
    a1 := 126 / 100000, b1 := -51 / 100000,
    a2 := 2577 / 100000, b2 := -1054 / 100000 },
  { left := 800000000, right := 900000000,
    a0 := 99994 / 100000, b0 := 99998 / 100000,
    a1 := 110 / 100000, b1 := -44 / 100000,
    a2 := 2268 / 100000, b2 := -916 / 100000 },
  { left := 900000000, right := 1000000000,
    a0 := 99994 / 100000, b0 := 99998 / 100000,
    a1 := 117 / 100000, b1 := -50 / 100000,
    a2 := 2398 / 100000, b2 := -1050 / 100000 },
  { left := 1000000000, right := 2000000000,
    a0 := 99995 / 100000, b0 := 99999 / 100000,
    a1 := 96 / 100000, b1 := -21 / 100000,
    a2 := 2009 / 100000, b2 := -455 / 100000 },
  { left := 2000000000, right := 3000000000,
    a0 := 99996 / 100000, b0 := 1,
    a1 := 67 / 100000, b1 := -18 / 100000,
    a2 := 1427 / 100000, b2 := -401 / 100000 },
  { left := 3000000000, right := 4000000000,
    a0 := 99997 / 100000, b0 := 1,
    a1 := 62 / 100000, b1 := -15 / 100000,
    a2 := 1340 / 100000, b2 := -333 / 100000 },
  { left := 4000000000, right := 5000000000,
    a0 := 99997 / 100000, b0 := 1,
    a1 := 50 / 100000, b1 := -17 / 100000,
    a2 := 1087 / 100000, b2 := -390 / 100000 },
  { left := 5000000000, right := 6000000000,
    a0 := 99997 / 100000, b0 := 1,
    a1 := 46 / 100000, b1 := -18 / 100000,
    a2 := 1026 / 100000, b2 := -410 / 100000 },
  { left := 6000000000, right := 7000000000,
    a0 := 99998 / 100000, b0 := 1,
    a1 := 40 / 100000, b1 := -13 / 100000,
    a2 := 900 / 100000, b2 := -313 / 100000 },
  { left := 7000000000, right := 8000000000,
    a0 := 99998 / 100000, b0 := 1,
    a1 := 45 / 100000, b1 := -18 / 100000,
    a2 := 1011 / 100000, b2 := -415 / 100000 },
  { left := 8000000000, right := 9000000000,
    a0 := 99998 / 100000, b0 := 1,
    a1 := 34 / 100000, b1 := -16 / 100000,
    a2 := 774 / 100000, b2 := -367 / 100000 },
  { left := 9000000000, right := 10000000000,
    a0 := 99998 / 100000, b0 := 1,
    a1 := 37 / 100000, b1 := -10 / 100000,
    a2 := 840 / 100000, b2 := -249 / 100000 },
  { left := 10000000000, right := 20000000000,
    a0 := 99998 / 100000, b0 := 1,
    a1 := 38 / 100000, b1 := -8 / 100000,
    a2 := 876 / 100000, b2 := -203 / 100000 },
  { left := 20000000000, right := 30000000000,
    a0 := 99998 / 100000, b0 := 1,
    a1 := 25 / 100000, b1 := -6 / 100000,
    a2 := 584 / 100000, b2 := -152 / 100000 },
  { left := 30000000000, right := 40000000000,
    a0 := 99999 / 100000, b0 := 1,
    a1 := 20 / 100000, b1 := -5 / 100000,
    a2 := 473 / 100000, b2 := -122 / 100000 },
  { left := 40000000000, right := 50000000000,
    a0 := 99999 / 100000, b0 := 1,
    a1 := 18 / 100000, b1 := -7 / 100000,
    a2 := 431 / 100000, b2 := -183 / 100000 },
  { left := 50000000000, right := 60000000000,
    a0 := 99999 / 100000, b0 := 1,
    a1 := 19 / 100000, b1 := -4 / 100000,
    a2 := 458 / 100000, b2 := -119 / 100000 },
  { left := 60000000000, right := 70000000000,
    a0 := 99999 / 100000, b0 := 1,
    a1 := 15 / 100000, b1 := -6 / 100000,
    a2 := 356 / 100000, b2 := -167 / 100000 },
  { left := 70000000000, right := 80000000000,
    a0 := 99999 / 100000, b0 := 1,
    a1 := 14 / 100000, b1 := -4 / 100000,
    a2 := 338 / 100000, b2 := -117 / 100000 },
  { left := 80000000000, right := 90000000000,
    a0 := 99999 / 100000, b0 := 1,
    a1 := 11 / 100000, b1 := -6 / 100000,
    a2 := 276 / 100000, b2 := -164 / 100000 },
  { left := 90000000000, right := 100000000000,
    a0 := 99999 / 100000, b0 := 1,
    a1 := 11 / 100000, b1 := -4 / 100000,
    a2 := 262 / 100000, b2 := -114 / 100000 },
  { left := 100000000000, right := 200000000000,
    a0 := 99999 / 100000, b0 := 1,
    a1 := 14 / 100000, b1 := -2 / 100000,
    a2 := 341 / 100000, b2 := -58 / 100000 },
  { left := 200000000000, right := 300000000000,
    a0 := 99999 / 100000, b0 := 1,
    a1 := 8 / 100000, b1 := -2 / 100000,
    a2 := 206 / 100000, b2 := -57 / 100000 },
  { left := 300000000000, right := 400000000000,
    a0 := 99999 / 100000, b0 := 1,
    a1 := 7 / 100000, b1 := -1 / 100000,
    a2 := 170 / 100000, b2 := -31 / 100000 },
  { left := 400000000000, right := 500000000000,
    a0 := 99999 / 100000, b0 := 1,
    a1 := 8 / 100000, b1 := -2 / 100000,
    a2 := 188 / 100000, b2 := -61 / 100000 },
  { left := 500000000000, right := 600000000000,
    a0 := 99999 / 100000, b0 := 1,
    a1 := 6 / 100000, b1 := -1 / 100000,
    a2 := 138 / 100000, b2 := -38 / 100000 },
  { left := 600000000000, right := 700000000000,
    a0 := 99999 / 100000, b0 := 1,
    a1 := 5 / 100000, b1 := -2 / 100000,
    a2 := 131 / 100000, b2 := -70 / 100000 },
  { left := 700000000000, right := 800000000000,
    a0 := 99999 / 100000, b0 := 1,
    a1 := 6 / 100000, b1 := -1 / 100000,
    a2 := 144 / 100000, b2 := -39 / 100000 }
]

theorem dusartThetaTable6_6CoefficientData_length :
    dusartThetaTable6_6CoefficientData.length = 34 := by decide

theorem dusartThetaTable6_6CoefficientData_side_conditions :
    ∀ row ∈ dusartThetaTable6_6CoefficientData,
      0 ≤ row.a1 ∧ row.a1 < (12323 : Real) / 10000 ∧ row.b0 ≤ 1 := by
  norm_num [dusartThetaTable6_6CoefficientData]

theorem dusartThetaTable6_6CoefficientData_coefficients_nonneg :
    ∀ row ∈ dusartThetaTable6_6CoefficientData,
      0 ≤ row.a0 ∧ 0 ≤ row.b0 := by
  norm_num [dusartThetaTable6_6CoefficientData]

theorem dusartThetaTable6_6CoefficientData_upper_one_coeff_negative :
    ∀ row ∈ dusartThetaTable6_6CoefficientData, row.b1 < 0 := by
  norm_num [dusartThetaTable6_6CoefficientData]

theorem dusartThetaTable6_6CoefficientData_correction_coefficients :
    ∀ row ∈ dusartThetaTable6_6CoefficientData,
      0 ≤ row.a1 ∧ row.a1 ≤ 1 ∧ -1 ≤ row.b1 ∧ row.b1 ≤ 0 ∧
      0 ≤ row.a2 ∧ row.a2 ≤ 1 ∧ -1 ≤ row.b2 ∧ row.b2 ≤ 0 := by
  norm_num [dusartThetaTable6_6CoefficientData]

theorem dusartThetaTable6_6CoefficientData_left_at_least_eight :
    ∀ row ∈ dusartThetaTable6_6CoefficientData, 8 ≤ row.left := by
  norm_num [dusartThetaTable6_6CoefficientData]

theorem dusartThetaTable6_6CoefficientData_correction_monotonicity :
    ∀ row ∈ dusartThetaTable6_6CoefficientData,
      MonotoneOn
          (fun x : Real => x - row.a1 * x / Real.log x)
          (Set.Icc (row.left : Real) (row.right : Real)) ∧
      MonotoneOn
          (fun x : Real => x + row.b1 * x / Real.log x)
          (Set.Icc (row.left : Real) (row.right : Real)) ∧
      MonotoneOn
          (fun x : Real => x - row.a2 * x / Real.log x ^ 2)
          (Set.Icc (row.left : Real) (row.right : Real)) ∧
      MonotoneOn
          (fun x : Real => x + row.b2 * x / Real.log x ^ 2)
          (Set.Icc (row.left : Real) (row.right : Real)) := by
  intro row hrow
  have hleft8 : (8 : Real) ≤ row.left := by
    exact_mod_cast
      (dusartThetaTable6_6CoefficientData_left_at_least_eight row hrow)
  have hleft : (1 : Real) < row.left := by linarith
  have hlog : (2 : Real) ≤ Real.log row.left :=
    log_ge_two_of_eight_le hleft8
  have hc := dusartThetaTable6_6CoefficientData_correction_coefficients
    row hrow
  have hlowerOne := id_sub_mul_id_div_log_monotoneOn
    (a := (row.left : Real)) (c := row.a1) hleft (by linarith) hc.1 hc.2.1
  have hupperOne := id_add_mul_id_div_log_monotoneOn
    (a := (row.left : Real)) (b := row.b1) hleft (by linarith)
      hc.2.2.1 hc.2.2.2.1
  have hlowerTwo := id_sub_mul_id_div_log_sq_monotoneOn
    (a := (row.left : Real)) (c := row.a2) hleft hlog
      hc.2.2.2.2.1 hc.2.2.2.2.2.1
  have hupperTwo := id_add_mul_id_div_log_sq_monotoneOn
    (a := (row.left : Real)) (b := row.b2) hleft hlog
      hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hlowerOne hx.1 hy.1 hxy
  · intro x hx y hy hxy
    exact hupperOne hx.1 hy.1 hxy
  · intro x hx y hy hxy
    exact hlowerTwo hx.1 hy.1 hxy
  · intro x hx y hy hxy
    exact hupperTwo hx.1 hy.1 hxy

theorem dusartThetaTable6_6CoefficientData_row_bounds :
    ∀ row ∈ dusartThetaTable6_6CoefficientData,
      2 ≤ row.left ∧ row.left ≤ row.right ∧
      (row.right : Real) ≤ (8e11 : Real) ∧
      (99985 : Real) / 100000 ≤ row.a0 ∧ row.b0 ≤ 1 := by
  norm_num [dusartThetaTable6_6CoefficientData]

theorem dusartThetaTable66_formula_bounds_of_published_endpoints
    {data : DusartThetaTable66CoefficientData}
    (hdata : data ∈ dusartThetaTable6_6CoefficientData)
    (lower_zero : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      data.a0 * x ≤ Chebyshev.theta x)
    (upper_zero : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      Chebyshev.theta x ≤ data.b0 * x)
    (lower_one_endpoint :
      data.right - data.a1 * data.right / Real.log data.right ≤
        Chebyshev.theta data.left)
    (upper_one_endpoint :
      Chebyshev.theta data.right ≤
        data.left + data.b1 * data.left / Real.log data.left)
    (lower_two_endpoint :
      data.right - data.a2 * data.right / Real.log data.right ^ 2 ≤
        Chebyshev.theta data.left)
    (upper_two_endpoint :
      Chebyshev.theta data.right ≤
        data.left + data.b2 * data.left / Real.log data.left ^ 2) :
    DusartThetaTable66FormulaBounds data := by
  have hrow := dusartThetaTable6_6CoefficientData_row_bounds data hdata
  have hleft8 := dusartThetaTable6_6CoefficientData_left_at_least_eight data hdata
  have hleft : (1 : Real) < data.left := by
    have : (8 : Real) ≤ data.left := by exact_mod_cast hleft8
    linarith
  exact dusartThetaTable66_formula_bounds_of_endpoints data hrow.2.1 hleft
    (log_ge_two_of_eight_le (by exact_mod_cast hleft8)) lower_zero upper_zero
    (dusartThetaTable6_6CoefficientData_correction_coefficients data hdata)
    lower_one_endpoint upper_one_endpoint lower_two_endpoint upper_two_endpoint

theorem strictThetaUpper_of_table66_formula_data
    (data : DusartThetaTable66CoefficientData)
    (hdata : data ∈ dusartThetaTable6_6CoefficientData)
    (formula : DusartThetaTable66FormulaBounds data)
    {x : Real} (hleft : (data.left : Real) ≤ x)
    (hright : x ≤ data.right) :
    Chebyshev.theta x < x := by
  have hrow := dusartThetaTable6_6CoefficientData_row_bounds data hdata
  have hleft_large : (2 : Real) ≤ data.left := by
    exact_mod_cast hrow.1
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hupper := formula.upper_one x hleft hright
  have hb1 := dusartThetaTable6_6CoefficientData_upper_one_coeff_negative
    data hdata
  have hcorrection : data.b1 * x / Real.log x < 0 := by
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hb1 hxpos) hlogpos
  nlinarith

def dusartThetaTable6_6CoefficientDataNatRanges : List (Nat × Nat) :=
  dusartThetaTable6_6CoefficientData.map fun row => (row.left, row.right)

theorem dusartThetaTable6_6CoefficientDataNatRanges_length :
    dusartThetaTable6_6CoefficientDataNatRanges.length = 34 := by
  simp [dusartThetaTable6_6CoefficientDataNatRanges,
    dusartThetaTable6_6CoefficientData_length]

theorem dusartThetaTable6_6CoefficientDataNatRanges_adjacent :
    dusartThetaTable6_6CoefficientDataNatRanges.IsChain
      (fun first second => first.2 = second.1) := by
  decide

theorem dusartThetaTable6_6CoefficientDataNatRanges_cover :
    ∀ n : Nat, 100000000 ≤ n → n ≤ 800000000000 →
      ∃ range ∈ dusartThetaTable6_6CoefficientDataNatRanges,
        range.1 ≤ n ∧ n ≤ range.2 := by
  intro n hn hN
  simp [dusartThetaTable6_6CoefficientDataNatRanges,
    dusartThetaTable6_6CoefficientData]
  omega

theorem dusartThetaTable6_6CoefficientData_cover_real :
    ∀ x : Real, (100000000 : Real) ≤ x → x ≤ (8e11 : Real) →
      ∃ data ∈ dusartThetaTable6_6CoefficientData,
        (data.left : Real) ≤ x ∧ x ≤ data.right := by
  intro x hlow hhigh
  let cells : List DusartThetaTable66Cell :=
    dusartThetaTable6_6CoefficientData.map fun data =>
      ⟨data.left, data.right, 0, 0⟩
  have chain : dusartThetaTable66CellsChain 100000000 800000000000 cells = true := by
    decide
  obtain ⟨cell, hcell, hl, hr⟩ := dusartThetaTable66CellsChain_covers chain hlow
    (by norm_num at hhigh ⊢; exact hhigh)
  obtain ⟨data, hdata, rfl⟩ := List.mem_map.mp hcell
  exact ⟨data, hdata, hl, hr⟩

end

end PrimeFactorUnimodality
