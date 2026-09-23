import Mathlib.Tactic.FinCases
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.RadixError

/-! # Radix/grid interfaces, collisions and boundary cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset Fourier ZMod



example {n : ℕ} {t : RadixTrace n}
    {w : ℂ} {a : Vector ℂ (2 ^ n)} (ht : t.Valid w a) (hw : ‖w‖ = 1)
    (k : Fin (2 ^ n)) : ‖(radixTwo n w a)[k.val] - t.values[k.val]‖ ≤ t.error := by
  exact Fourier.RadixTrace.Valid.norm_radixTwo_sub_le ht hw k

example {n : ℕ} {t : RadixTrace n}
    {w : ℂ} {a : Vector ℂ (2 ^ n)} (ht : t.Valid w a) (hw : ‖w‖ = 1)
    (hperiod : w ^ (2 ^ n) = 1) (k : Fin (2 ^ n)) :
    ‖(∑ j : Fin (2 ^ n), a[j.val] * w ^ (k.val * j.val)) - t.values[k.val]‖ ≤ t.error := by
  exact Fourier.RadixTrace.Valid.norm_sum_sub_le ht hw hperiod k

def binaryTrace : RadixTrace 1 :=
  .node (.leaf 1 0) (.leaf 3 0) #v[4, -2] #v[1, -1] 0 0 3

example : binaryTrace.Valid (-1) #v[1, 3] := by
  refine ⟨?_, ?_, by norm_num, ?_, ?_, ?_⟩
  · norm_num [RadixTrace.Valid, evenSamples]
  · norm_num [RadixTrace.Valid, oddSamples]
  · intro k
    fin_cases k <;> norm_num [binaryTrace]
  · intro k
    fin_cases k <;> norm_num [RadixTrace.values]
  · intro k
    fin_cases k <;> norm_num [RadixTrace.values]

example : binaryTrace.error = 0 := by norm_num [binaryTrace, RadixTrace.error]

def coarseTrace : RadixTrace 1 :=
  .node (.leaf 1 0) (.leaf 3 0) #v[4, 1] #v[1, 0] 0 1 3

example : coarseTrace.Valid (-1) #v[1, 3] := by
  refine ⟨?_, ?_, by norm_num, ?_, ?_, ?_⟩
  · norm_num [RadixTrace.Valid, evenSamples]
  · norm_num [RadixTrace.Valid, oddSamples]
  · intro k
    fin_cases k <;> norm_num [coarseTrace]
  · intro k
    fin_cases k <;> norm_num [RadixTrace.values]
  · intro k
    fin_cases k <;> norm_num [RadixTrace.values]

example : coarseTrace.error = 3 := by norm_num [coarseTrace, RadixTrace.error]

example : ¬(RadixTrace.leaf 0 (-1)).Valid 1 #v[0] := by norm_num [RadixTrace.Valid]

end

end PrimeFactorUnimodality.Tests
