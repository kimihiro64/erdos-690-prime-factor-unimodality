import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.EndpointBounds

namespace PrimeFactorUnimodality

noncomputable section

theorem log_18958_le_197_over_20 :
    Real.log (18958 : Real) ≤ (197 : Real) / 20 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 9 (r := (17 : Real) / 20) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_197_over_20_of_18041_le
    {a : Nat} (ha : 18041 ≤ a) (ha18958 : a ≤ 18958) :
    Real.log a ≤ (197 : Real) / 20 := by
  have hmono : Real.log (a : Real) ≤ Real.log (18958 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha18958
  exact hmono.trans log_18958_le_197_over_20

theorem log_18033_le_49_over_5 :
    Real.log (18033 : Real) ≤ (49 : Real) / 5 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 9 (r := (8 : Real) / 10) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_49_over_5_of_17159_le
    {a : Nat} (ha : 17159 ≤ a) (ha18033 : a ≤ 18033) :
    Real.log a ≤ (49 : Real) / 5 := by
  have hmono : Real.log (a : Real) ≤ Real.log (18033 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha18033
  exact hmono.trans log_18033_le_49_over_5

theorem log_17154_le_39_over_4 :
    Real.log (17154 : Real) ≤ (39 : Real) / 4 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 9 (r := (3 : Real) / 4) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_39_over_4_of_16319_le
    {a : Nat} (ha : 16319 ≤ a) (ha17154 : a ≤ 17154) :
    Real.log a ≤ (39 : Real) / 4 := by
  have hmono : Real.log (a : Real) ≤ Real.log (17154 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha17154
  exact hmono.trans log_17154_le_39_over_4

theorem log_le_116_over_10_of_89693_le
    {a : Nat} (ha : (89693 : Nat) ≤ a) (ha100000 : a ≤ 100000) :
    Real.log a ≤ (116 : Real) / 10 := by
  have hmono : Real.log (a : Real) ≤ Real.log (100000 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha100000
  exact hmono.trans log_100000_le_116_over_10

end

end PrimeFactorUnimodality
