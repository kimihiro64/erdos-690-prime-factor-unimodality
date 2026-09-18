import PrimeFactorUnimodality.Proof.LargeRange.TailStructuralBounds

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

/-! The elementary theta constants leave a very wide margin for the shell
target used by the CRT valley. -/
theorem elementary_tail_shell_numeric {q : Nat} (hq : 3501 ≤ q) :
    ((5 * primorial q : Nat) : Real) / tailGapBound q + 1 <
      (86 : Real) / 100 * (9 * primorial q) -
        (111 : Real) / 100 * (4 * primorial q) := by
  have gapLower := tailGapBound_gt_onePointZeroOne q
  have qPos : (0 : Real) < q := by exact_mod_cast (show 0 < q by omega)
  have gapPos : (0 : Real) < (tailGapBound q : Real) := by
    exact_mod_cast (show 0 < tailGapBound q by
      simp only [tailGapBound]
      omega)
  have pPos : (0 : Real) < primorial q := by
    exact_mod_cast primorial_pos q
  have pOne : (1 : Real) ≤ primorial q := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (primorial_pos q)))
  have qLower : (3500 : Real) < q := by exact_mod_cast (by omega : 3500 < q)
  have widthBound :
      ((5 * primorial q : Nat) : Real) / tailGapBound q <
        (1 : Real) / 700 * primorial q := by
    rw [div_lt_iff₀ gapPos]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith [mul_lt_mul_of_pos_right gapLower pPos]
  have rightPos : (0 : Real) <
      (86 : Real) / 100 * (9 * primorial q) -
        (111 : Real) / 100 * (4 * primorial q) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith [pPos]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at widthBound ⊢
  nlinarith [pPos, pOne]

end

end PrimeFactorUnimodality
