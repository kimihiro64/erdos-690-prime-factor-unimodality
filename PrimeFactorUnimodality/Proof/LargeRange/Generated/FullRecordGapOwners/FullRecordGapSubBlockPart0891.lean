import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapFermat

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

theorem fullRecordGapSubBlock_part0891 (d : Nat) (455681 ≤ d) (d ≤ 455703) : ¬(recordGapCenter - d).Prime := by
  by_cases h : 455693 ≤ d
  ·
    by_cases h : 455699 ≤ d
    ·
      by_cases h : 455702 ≤ d
      ·
        by_cases h : 455703 ≤ d
        ·
          have : d = 455703 := by omega
          subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          have : d = 455702 := by omega
          subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 455701 ≤ d
        ·
          have : d = 455701 := by omega
          subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 455700 ≤ d
          ·
            have : d = 455700 := by omega
            subst d
      apply fullRecordGap_sub_not_prime (q := 31) (by norm_num)
      exact by decide
          ·
            have : d = 455699 := by omega
            subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 455696 ≤ d
      ·
        by_cases h : 455698 ≤ d
        ·
          have : d = 455698 := by omega
          subst d
      apply fullRecordGap_sub_not_prime (q := 169373) (by norm_num)
      right
      exact ⟨116952, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 455697 ≤ d
          ·
            have : d = 455697 := by omega
            subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            have : d = 455696 := by omega
            subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 455695 ≤ d
        ·
          have : d = 455695 := by omega
          subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 455694 ≤ d
          ·
            have : d = 455694 := by omega
            subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            have : d = 455693 := by omega
            subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
  ·
    by_cases h : 455687 ≤ d
    ·
      by_cases h : 455690 ≤ d
      ·
        by_cases h : 455692 ≤ d
        ·
          have : d = 455692 := by omega
          subst d
      apply fullRecordGap_sub_not_prime (q := 37) (by norm_num)
      exact by decide
        ·
          by_cases h : 455691 ≤ d
          ·
            have : d = 455691 := by omega
            subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            have : d = 455690 := by omega
            subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 455689 ≤ d
        ·
          have : d = 455689 := by omega
          subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 455688 ≤ d
          ·
            have : d = 455688 := by omega
            subst d
      apply fullRecordGap_sub_not_prime (q := 6329) (by norm_num)
      exact by decide
          ·
            have : d = 455687 := by omega
            subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 455684 ≤ d
      ·
        by_cases h : 455686 ≤ d
        ·
          have : d = 455686 := by omega
          subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 455685 ≤ d
          ·
            have : d = 455685 := by omega
            subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            have : d = 455684 := by omega
            subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 455683 ≤ d
        ·
          have : d = 455683 := by omega
          subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 455682 ≤ d
          ·
            have : d = 455682 := by omega
            subst d
      apply fullRecordGap_sub_not_prime (q := 173) (by norm_num)
      exact by decide
          ·
            have : d = 455681 := by omega
            subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩

end PrimeFactorUnimodality
