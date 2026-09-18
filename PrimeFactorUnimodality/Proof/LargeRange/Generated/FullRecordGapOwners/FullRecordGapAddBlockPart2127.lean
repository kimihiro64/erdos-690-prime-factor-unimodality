import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapFermat

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

theorem fullRecordGapAddBlock_part2127 (d : Nat) (632321 ≤ d) (d ≤ 632832) : ¬(recordGapCenter + d).Prime := by
  by_cases h : 632577 ≤ d
  ·
    by_cases h : 632705 ≤ d
    ·
      by_cases h : 632769 ≤ d
      ·
        by_cases h : 632801 ≤ d
        ·
          by_cases h : 632817 ≤ d
          ·
            by_cases h : 632825 ≤ d
            ·
              by_cases h : 632829 ≤ d
              ·
                by_cases h : 632831 ≤ d
                ·
                  by_cases h : 632832 ≤ d
                  ·
                    have : d = 632832 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 103)
      exact by decide
                  ·
                    have : d = 632831 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632830 ≤ d
                  ·
                    have : d = 632830 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632829 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632827 ≤ d
                ·
                  by_cases h : 632828 ≤ d
                  ·
                    have : d = 632828 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 97)
      exact by decide
                  ·
                    have : d = 632827 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632826 ≤ d
                  ·
                    have : d = 632826 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632825 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632821 ≤ d
              ·
                by_cases h : 632823 ≤ d
                ·
                  by_cases h : 632824 ≤ d
                  ·
                    have : d = 632824 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632823 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632822 ≤ d
                  ·
                    have : d = 632822 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 632821 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632819 ≤ d
                ·
                  by_cases h : 632820 ≤ d
                  ·
                    have : d = 632820 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632819 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632818 ≤ d
                  ·
                    have : d = 632818 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632817 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 632809 ≤ d
            ·
              by_cases h : 632813 ≤ d
              ·
                by_cases h : 632815 ≤ d
                ·
                  by_cases h : 632816 ≤ d
                  ·
                    have : d = 632816 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 39551)
      exact by decide
                  ·
                    have : d = 632815 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632814 ≤ d
                  ·
                    have : d = 632814 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632813 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632811 ≤ d
                ·
                  by_cases h : 632812 ≤ d
                  ·
                    have : d = 632812 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632811 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632810 ≤ d
                  ·
                    have : d = 632810 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 105970393)
      right
      exact ⟨105337583, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632809 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632805 ≤ d
              ·
                by_cases h : 632807 ≤ d
                ·
                  by_cases h : 632808 ≤ d
                  ·
                    have : d = 632808 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 632807 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632806 ≤ d
                  ·
                    have : d = 632806 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632805 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632803 ≤ d
                ·
                  by_cases h : 632804 ≤ d
                  ·
                    have : d = 632804 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632803 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632802 ≤ d
                  ·
                    have : d = 632802 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3475639)
      right
      exact ⟨2842837, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632801 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 632785 ≤ d
          ·
            by_cases h : 632793 ≤ d
            ·
              by_cases h : 632797 ≤ d
              ·
                by_cases h : 632799 ≤ d
                ·
                  by_cases h : 632800 ≤ d
                  ·
                    have : d = 632800 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632799 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632798 ≤ d
                  ·
                    have : d = 632798 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 107)
      exact by decide
                  ·
                    have : d = 632797 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632795 ≤ d
                ·
                  by_cases h : 632796 ≤ d
                  ·
                    have : d = 632796 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2863401283)
      right
      exact ⟨2862768487, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632795 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632794 ≤ d
                  ·
                    have : d = 632794 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632793 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632789 ≤ d
              ·
                by_cases h : 632791 ≤ d
                ·
                  by_cases h : 632792 ≤ d
                  ·
                    have : d = 632792 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632791 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632790 ≤ d
                  ·
                    have : d = 632790 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 79)
      exact by decide
                  ·
                    have : d = 632789 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632787 ≤ d
                ·
                  by_cases h : 632788 ≤ d
                  ·
                    have : d = 632788 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632787 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632786 ≤ d
                  ·
                    have : d = 632786 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 587)
      exact by decide
                  ·
                    have : d = 632785 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 632777 ≤ d
            ·
              by_cases h : 632781 ≤ d
              ·
                by_cases h : 632783 ≤ d
                ·
                  by_cases h : 632784 ≤ d
                  ·
                    have : d = 632784 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632783 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632782 ≤ d
                  ·
                    have : d = 632782 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632781 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632779 ≤ d
                ·
                  by_cases h : 632780 ≤ d
                  ·
                    have : d = 632780 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 632779 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632778 ≤ d
                  ·
                    have : d = 632778 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632777 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632773 ≤ d
              ·
                by_cases h : 632775 ≤ d
                ·
                  by_cases h : 632776 ≤ d
                  ·
                    have : d = 632776 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632775 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632774 ≤ d
                  ·
                    have : d = 632774 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632773 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632771 ≤ d
                ·
                  by_cases h : 632772 ≤ d
                  ·
                    have : d = 632772 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 632771 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632770 ≤ d
                  ·
                    have : d = 632770 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632769 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 632737 ≤ d
        ·
          by_cases h : 632753 ≤ d
          ·
            by_cases h : 632761 ≤ d
            ·
              by_cases h : 632765 ≤ d
              ·
                by_cases h : 632767 ≤ d
                ·
                  by_cases h : 632768 ≤ d
                  ·
                    have : d = 632768 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 9887)
      exact by decide
                  ·
                    have : d = 632767 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632766 ≤ d
                  ·
                    have : d = 632766 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 163)
      exact by decide
                  ·
                    have : d = 632765 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632763 ≤ d
                ·
                  by_cases h : 632764 ≤ d
                  ·
                    have : d = 632764 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632763 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632762 ≤ d
                  ·
                    have : d = 632762 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 632761 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632757 ≤ d
              ·
                by_cases h : 632759 ≤ d
                ·
                  by_cases h : 632760 ≤ d
                  ·
                    have : d = 632760 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632759 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632758 ≤ d
                  ·
                    have : d = 632758 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632757 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632755 ≤ d
                ·
                  by_cases h : 632756 ≤ d
                  ·
                    have : d = 632756 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 30209923)
      right
      exact ⟨29577167, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632755 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632754 ≤ d
                  ·
                    have : d = 632754 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632753 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 632745 ≤ d
            ·
              by_cases h : 632749 ≤ d
              ·
                by_cases h : 632751 ≤ d
                ·
                  by_cases h : 632752 ≤ d
                  ·
                    have : d = 632752 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632751 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632750 ≤ d
                  ·
                    have : d = 632750 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632749 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632747 ≤ d
                ·
                  by_cases h : 632748 ≤ d
                  ·
                    have : d = 632748 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 67)
      exact by decide
                  ·
                    have : d = 632747 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632746 ≤ d
                  ·
                    have : d = 632746 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632745 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632741 ≤ d
              ·
                by_cases h : 632743 ≤ d
                ·
                  by_cases h : 632744 ≤ d
                  ·
                    have : d = 632744 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632743 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632742 ≤ d
                  ·
                    have : d = 632742 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 9587)
      exact by decide
                  ·
                    have : d = 632741 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632739 ≤ d
                ·
                  by_cases h : 632740 ≤ d
                  ·
                    have : d = 632740 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632739 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632738 ≤ d
                  ·
                    have : d = 632738 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632737 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 632721 ≤ d
          ·
            by_cases h : 632729 ≤ d
            ·
              by_cases h : 632733 ≤ d
              ·
                by_cases h : 632735 ≤ d
                ·
                  by_cases h : 632736 ≤ d
                  ·
                    have : d = 632736 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632735 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632734 ≤ d
                  ·
                    have : d = 632734 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632733 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632731 ≤ d
                ·
                  by_cases h : 632732 ≤ d
                  ·
                    have : d = 632732 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 317)
      exact by decide
                  ·
                    have : d = 632731 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632730 ≤ d
                  ·
                    have : d = 632730 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 632729 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632725 ≤ d
              ·
                by_cases h : 632727 ≤ d
                ·
                  by_cases h : 632728 ≤ d
                  ·
                    have : d = 632728 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632727 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632726 ≤ d
                  ·
                    have : d = 632726 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 130199)
      right
      exact ⟨18269, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632725 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632723 ≤ d
                ·
                  by_cases h : 632724 ≤ d
                  ·
                    have : d = 632724 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632723 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632722 ≤ d
                  ·
                    have : d = 632722 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632721 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 632713 ≤ d
            ·
              by_cases h : 632717 ≤ d
              ·
                by_cases h : 632719 ≤ d
                ·
                  by_cases h : 632720 ≤ d
                  ·
                    have : d = 632720 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 719)
      exact by decide
                  ·
                    have : d = 632719 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632718 ≤ d
                  ·
                    have : d = 632718 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11717)
      exact by decide
                  ·
                    have : d = 632717 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632715 ≤ d
                ·
                  by_cases h : 632716 ≤ d
                  ·
                    have : d = 632716 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632715 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632714 ≤ d
                  ·
                    have : d = 632714 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632713 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632709 ≤ d
              ·
                by_cases h : 632711 ≤ d
                ·
                  by_cases h : 632712 ≤ d
                  ·
                    have : d = 632712 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 41)
      exact by decide
                  ·
                    have : d = 632711 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632710 ≤ d
                  ·
                    have : d = 632710 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632709 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632707 ≤ d
                ·
                  by_cases h : 632708 ≤ d
                  ·
                    have : d = 632708 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632707 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632706 ≤ d
                  ·
                    have : d = 632706 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 632705 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 632641 ≤ d
      ·
        by_cases h : 632673 ≤ d
        ·
          by_cases h : 632689 ≤ d
          ·
            by_cases h : 632697 ≤ d
            ·
              by_cases h : 632701 ≤ d
              ·
                by_cases h : 632703 ≤ d
                ·
                  by_cases h : 632704 ≤ d
                  ·
                    have : d = 632704 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632703 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632702 ≤ d
                  ·
                    have : d = 632702 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 43)
      exact by decide
                  ·
                    have : d = 632701 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632699 ≤ d
                ·
                  by_cases h : 632700 ≤ d
                  ·
                    have : d = 632700 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 632699 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632698 ≤ d
                  ·
                    have : d = 632698 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632697 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632693 ≤ d
              ·
                by_cases h : 632695 ≤ d
                ·
                  by_cases h : 632696 ≤ d
                  ·
                    have : d = 632696 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 72646741829)
      right
      exact ⟨72646109133, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632695 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632694 ≤ d
                  ·
                    have : d = 632694 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632693 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632691 ≤ d
                ·
                  by_cases h : 632692 ≤ d
                  ·
                    have : d = 632692 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632691 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632690 ≤ d
                  ·
                    have : d = 632690 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 151)
      exact by decide
                  ·
                    have : d = 632689 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 632681 ≤ d
            ·
              by_cases h : 632685 ≤ d
              ·
                by_cases h : 632687 ≤ d
                ·
                  by_cases h : 632688 ≤ d
                  ·
                    have : d = 632688 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 269)
      exact by decide
                  ·
                    have : d = 632687 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632686 ≤ d
                  ·
                    have : d = 632686 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632685 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632683 ≤ d
                ·
                  by_cases h : 632684 ≤ d
                  ·
                    have : d = 632684 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632683 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632682 ≤ d
                  ·
                    have : d = 632682 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 35149)
      exact by decide
                  ·
                    have : d = 632681 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632677 ≤ d
              ·
                by_cases h : 632679 ≤ d
                ·
                  by_cases h : 632680 ≤ d
                  ·
                    have : d = 632680 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632679 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632678 ≤ d
                  ·
                    have : d = 632678 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1303693)
      right
      exact ⟨671015, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632677 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632675 ≤ d
                ·
                  by_cases h : 632676 ≤ d
                  ·
                    have : d = 632676 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 4793)
      exact by decide
                  ·
                    have : d = 632675 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632674 ≤ d
                  ·
                    have : d = 632674 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632673 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 632657 ≤ d
          ·
            by_cases h : 632665 ≤ d
            ·
              by_cases h : 632669 ≤ d
              ·
                by_cases h : 632671 ≤ d
                ·
                  by_cases h : 632672 ≤ d
                  ·
                    have : d = 632672 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632671 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632670 ≤ d
                  ·
                    have : d = 632670 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 21089)
      exact by decide
                  ·
                    have : d = 632669 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632667 ≤ d
                ·
                  by_cases h : 632668 ≤ d
                  ·
                    have : d = 632668 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632667 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632666 ≤ d
                  ·
                    have : d = 632666 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632665 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632661 ≤ d
              ·
                by_cases h : 632663 ≤ d
                ·
                  by_cases h : 632664 ≤ d
                  ·
                    have : d = 632664 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632663 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632662 ≤ d
                  ·
                    have : d = 632662 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632661 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632659 ≤ d
                ·
                  by_cases h : 632660 ≤ d
                  ·
                    have : d = 632660 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 4519)
      exact by decide
                  ·
                    have : d = 632659 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632658 ≤ d
                  ·
                    have : d = 632658 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 632657 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 632649 ≤ d
            ·
              by_cases h : 632653 ≤ d
              ·
                by_cases h : 632655 ≤ d
                ·
                  by_cases h : 632656 ≤ d
                  ·
                    have : d = 632656 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632655 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632654 ≤ d
                  ·
                    have : d = 632654 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632653 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632651 ≤ d
                ·
                  by_cases h : 632652 ≤ d
                  ·
                    have : d = 632652 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632651 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632650 ≤ d
                  ·
                    have : d = 632650 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632649 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632645 ≤ d
              ·
                by_cases h : 632647 ≤ d
                ·
                  by_cases h : 632648 ≤ d
                  ·
                    have : d = 632648 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 632647 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632646 ≤ d
                  ·
                    have : d = 632646 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5021)
      exact by decide
                  ·
                    have : d = 632645 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632643 ≤ d
                ·
                  by_cases h : 632644 ≤ d
                  ·
                    have : d = 632644 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632643 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632642 ≤ d
                  ·
                    have : d = 632642 := by omega
                    subst d
      exact fullRecordGapTerm10487_not_prime
                  ·
                    have : d = 632641 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 632609 ≤ d
        ·
          by_cases h : 632625 ≤ d
          ·
            by_cases h : 632633 ≤ d
            ·
              by_cases h : 632637 ≤ d
              ·
                by_cases h : 632639 ≤ d
                ·
                  by_cases h : 632640 ≤ d
                  ·
                    have : d = 632640 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 659)
      exact by decide
                  ·
                    have : d = 632639 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632638 ≤ d
                  ·
                    have : d = 632638 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632637 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632635 ≤ d
                ·
                  by_cases h : 632636 ≤ d
                  ·
                    have : d = 632636 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 109)
      exact by decide
                  ·
                    have : d = 632635 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632634 ≤ d
                  ·
                    have : d = 632634 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632633 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632629 ≤ d
              ·
                by_cases h : 632631 ≤ d
                ·
                  by_cases h : 632632 ≤ d
                  ·
                    have : d = 632632 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632631 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632630 ≤ d
                  ·
                    have : d = 632630 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 41)
      exact by decide
                  ·
                    have : d = 632629 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632627 ≤ d
                ·
                  by_cases h : 632628 ≤ d
                  ·
                    have : d = 632628 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632627 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632626 ≤ d
                  ·
                    have : d = 632626 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632625 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 632617 ≤ d
            ·
              by_cases h : 632621 ≤ d
              ·
                by_cases h : 632623 ≤ d
                ·
                  by_cases h : 632624 ≤ d
                  ·
                    have : d = 632624 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632623 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632622 ≤ d
                  ·
                    have : d = 632622 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 207197)
      right
      exact ⟨196166, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632621 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632619 ≤ d
                ·
                  by_cases h : 632620 ≤ d
                  ·
                    have : d = 632620 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632619 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632618 ≤ d
                  ·
                    have : d = 632618 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 73)
      exact by decide
                  ·
                    have : d = 632617 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632613 ≤ d
              ·
                by_cases h : 632615 ≤ d
                ·
                  by_cases h : 632616 ≤ d
                  ·
                    have : d = 632616 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 43)
      exact by decide
                  ·
                    have : d = 632615 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632614 ≤ d
                  ·
                    have : d = 632614 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632613 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632611 ≤ d
                ·
                  by_cases h : 632612 ≤ d
                  ·
                    have : d = 632612 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 89)
      exact by decide
                  ·
                    have : d = 632611 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632610 ≤ d
                  ·
                    have : d = 632610 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632609 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 632593 ≤ d
          ·
            by_cases h : 632601 ≤ d
            ·
              by_cases h : 632605 ≤ d
              ·
                by_cases h : 632607 ≤ d
                ·
                  by_cases h : 632608 ≤ d
                  ·
                    have : d = 632608 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632607 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632606 ≤ d
                  ·
                    have : d = 632606 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632605 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632603 ≤ d
                ·
                  by_cases h : 632604 ≤ d
                  ·
                    have : d = 632604 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632603 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632602 ≤ d
                  ·
                    have : d = 632602 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632601 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632597 ≤ d
              ·
                by_cases h : 632599 ≤ d
                ·
                  by_cases h : 632600 ≤ d
                  ·
                    have : d = 632600 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3163)
      exact by decide
                  ·
                    have : d = 632599 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632598 ≤ d
                  ·
                    have : d = 632598 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 59)
      exact by decide
                  ·
                    have : d = 632597 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632595 ≤ d
                ·
                  by_cases h : 632596 ≤ d
                  ·
                    have : d = 632596 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632595 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632594 ≤ d
                  ·
                    have : d = 632594 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632593 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 632585 ≤ d
            ·
              by_cases h : 632589 ≤ d
              ·
                by_cases h : 632591 ≤ d
                ·
                  by_cases h : 632592 ≤ d
                  ·
                    have : d = 632592 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 632591 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632590 ≤ d
                  ·
                    have : d = 632590 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632589 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632587 ≤ d
                ·
                  by_cases h : 632588 ≤ d
                  ·
                    have : d = 632588 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1307)
      exact by decide
                  ·
                    have : d = 632587 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632586 ≤ d
                  ·
                    have : d = 632586 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 632585 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632581 ≤ d
              ·
                by_cases h : 632583 ≤ d
                ·
                  by_cases h : 632584 ≤ d
                  ·
                    have : d = 632584 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632583 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632582 ≤ d
                  ·
                    have : d = 632582 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632581 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632579 ≤ d
                ·
                  by_cases h : 632580 ≤ d
                  ·
                    have : d = 632580 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 632579 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632578 ≤ d
                  ·
                    have : d = 632578 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632577 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
  ·
    by_cases h : 632449 ≤ d
    ·
      by_cases h : 632513 ≤ d
      ·
        by_cases h : 632545 ≤ d
        ·
          by_cases h : 632561 ≤ d
          ·
            by_cases h : 632569 ≤ d
            ·
              by_cases h : 632573 ≤ d
              ·
                by_cases h : 632575 ≤ d
                ·
                  by_cases h : 632576 ≤ d
                  ·
                    have : d = 632576 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 353)
      exact by decide
                  ·
                    have : d = 632575 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632574 ≤ d
                  ·
                    have : d = 632574 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632573 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632571 ≤ d
                ·
                  by_cases h : 632572 ≤ d
                  ·
                    have : d = 632572 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632571 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632570 ≤ d
                  ·
                    have : d = 632570 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 632569 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632565 ≤ d
              ·
                by_cases h : 632567 ≤ d
                ·
                  by_cases h : 632568 ≤ d
                  ·
                    have : d = 632568 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632567 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632566 ≤ d
                  ·
                    have : d = 632566 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632565 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632563 ≤ d
                ·
                  by_cases h : 632564 ≤ d
                  ·
                    have : d = 632564 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632563 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632562 ≤ d
                  ·
                    have : d = 632562 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632561 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 632553 ≤ d
            ·
              by_cases h : 632557 ≤ d
              ·
                by_cases h : 632559 ≤ d
                ·
                  by_cases h : 632560 ≤ d
                  ·
                    have : d = 632560 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632559 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632558 ≤ d
                  ·
                    have : d = 632558 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 359)
      exact by decide
                  ·
                    have : d = 632557 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632555 ≤ d
                ·
                  by_cases h : 632556 ≤ d
                  ·
                    have : d = 632556 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5857)
      exact by decide
                  ·
                    have : d = 632555 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632554 ≤ d
                  ·
                    have : d = 632554 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632553 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632549 ≤ d
              ·
                by_cases h : 632551 ≤ d
                ·
                  by_cases h : 632552 ≤ d
                  ·
                    have : d = 632552 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 632551 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632550 ≤ d
                  ·
                    have : d = 632550 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 4217)
      exact by decide
                  ·
                    have : d = 632549 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632547 ≤ d
                ·
                  by_cases h : 632548 ≤ d
                  ·
                    have : d = 632548 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632547 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632546 ≤ d
                  ·
                    have : d = 632546 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 632545 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 632529 ≤ d
          ·
            by_cases h : 632537 ≤ d
            ·
              by_cases h : 632541 ≤ d
              ·
                by_cases h : 632543 ≤ d
                ·
                  by_cases h : 632544 ≤ d
                  ·
                    have : d = 632544 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632543 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632542 ≤ d
                  ·
                    have : d = 632542 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632541 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632539 ≤ d
                ·
                  by_cases h : 632540 ≤ d
                  ·
                    have : d = 632540 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632539 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632538 ≤ d
                  ·
                    have : d = 632538 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 35141)
      exact by decide
                  ·
                    have : d = 632537 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632533 ≤ d
              ·
                by_cases h : 632535 ≤ d
                ·
                  by_cases h : 632536 ≤ d
                  ·
                    have : d = 632536 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632535 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632534 ≤ d
                  ·
                    have : d = 632534 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632533 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632531 ≤ d
                ·
                  by_cases h : 632532 ≤ d
                  ·
                    have : d = 632532 := by omega
                    subst d
      exact fullRecordGapTerm10486_not_prime
                  ·
                    have : d = 632531 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632530 ≤ d
                  ·
                    have : d = 632530 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632529 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 632521 ≤ d
            ·
              by_cases h : 632525 ≤ d
              ·
                by_cases h : 632527 ≤ d
                ·
                  by_cases h : 632528 ≤ d
                  ·
                    have : d = 632528 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 632527 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632526 ≤ d
                  ·
                    have : d = 632526 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632525 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632523 ≤ d
                ·
                  by_cases h : 632524 ≤ d
                  ·
                    have : d = 632524 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632523 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632522 ≤ d
                  ·
                    have : d = 632522 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 28751)
      exact by decide
                  ·
                    have : d = 632521 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632517 ≤ d
              ·
                by_cases h : 632519 ≤ d
                ·
                  by_cases h : 632520 ≤ d
                  ·
                    have : d = 632520 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 251)
      exact by decide
                  ·
                    have : d = 632519 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632518 ≤ d
                  ·
                    have : d = 632518 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632517 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632515 ≤ d
                ·
                  by_cases h : 632516 ≤ d
                  ·
                    have : d = 632516 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 76907)
      right
      exact ⟨59647, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632515 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632514 ≤ d
                  ·
                    have : d = 632514 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632513 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 632481 ≤ d
        ·
          by_cases h : 632497 ≤ d
          ·
            by_cases h : 632505 ≤ d
            ·
              by_cases h : 632509 ≤ d
              ·
                by_cases h : 632511 ≤ d
                ·
                  by_cases h : 632512 ≤ d
                  ·
                    have : d = 632512 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632511 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632510 ≤ d
                  ·
                    have : d = 632510 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 632509 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632507 ≤ d
                ·
                  by_cases h : 632508 ≤ d
                  ·
                    have : d = 632508 := by omega
                    subst d
      exact fullRecordGapTerm10485_not_prime
                  ·
                    have : d = 632507 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632506 ≤ d
                  ·
                    have : d = 632506 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632505 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632501 ≤ d
              ·
                by_cases h : 632503 ≤ d
                ·
                  by_cases h : 632504 ≤ d
                  ·
                    have : d = 632504 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632503 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632502 ≤ d
                  ·
                    have : d = 632502 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 632501 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632499 ≤ d
                ·
                  by_cases h : 632500 ≤ d
                  ·
                    have : d = 632500 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632499 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632498 ≤ d
                  ·
                    have : d = 632498 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632497 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 632489 ≤ d
            ·
              by_cases h : 632493 ≤ d
              ·
                by_cases h : 632495 ≤ d
                ·
                  by_cases h : 632496 ≤ d
                  ·
                    have : d = 632496 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632495 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632494 ≤ d
                  ·
                    have : d = 632494 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632493 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632491 ≤ d
                ·
                  by_cases h : 632492 ≤ d
                  ·
                    have : d = 632492 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 461)
      exact by decide
                  ·
                    have : d = 632491 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632490 ≤ d
                  ·
                    have : d = 632490 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 632489 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632485 ≤ d
              ·
                by_cases h : 632487 ≤ d
                ·
                  by_cases h : 632488 ≤ d
                  ·
                    have : d = 632488 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632487 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632486 ≤ d
                  ·
                    have : d = 632486 := by omega
                    subst d
      exact fullRecordGapTerm10484_not_prime
                  ·
                    have : d = 632485 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632483 ≤ d
                ·
                  by_cases h : 632484 ≤ d
                  ·
                    have : d = 632484 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632483 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632482 ≤ d
                  ·
                    have : d = 632482 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632481 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 632465 ≤ d
          ·
            by_cases h : 632473 ≤ d
            ·
              by_cases h : 632477 ≤ d
              ·
                by_cases h : 632479 ≤ d
                ·
                  by_cases h : 632480 ≤ d
                  ·
                    have : d = 632480 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 59)
      exact by decide
                  ·
                    have : d = 632479 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632478 ≤ d
                  ·
                    have : d = 632478 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 632477 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632475 ≤ d
                ·
                  by_cases h : 632476 ≤ d
                  ·
                    have : d = 632476 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632475 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632474 ≤ d
                  ·
                    have : d = 632474 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632473 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632469 ≤ d
              ·
                by_cases h : 632471 ≤ d
                ·
                  by_cases h : 632472 ≤ d
                  ·
                    have : d = 632472 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 632471 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632470 ≤ d
                  ·
                    have : d = 632470 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632469 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632467 ≤ d
                ·
                  by_cases h : 632468 ≤ d
                  ·
                    have : d = 632468 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 632467 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632466 ≤ d
                  ·
                    have : d = 632466 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 41)
      exact by decide
                  ·
                    have : d = 632465 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 632457 ≤ d
            ·
              by_cases h : 632461 ≤ d
              ·
                by_cases h : 632463 ≤ d
                ·
                  by_cases h : 632464 ≤ d
                  ·
                    have : d = 632464 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632463 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632462 ≤ d
                  ·
                    have : d = 632462 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 632461 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632459 ≤ d
                ·
                  by_cases h : 632460 ≤ d
                  ·
                    have : d = 632460 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 83)
      exact by decide
                  ·
                    have : d = 632459 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632458 ≤ d
                  ·
                    have : d = 632458 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632457 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632453 ≤ d
              ·
                by_cases h : 632455 ≤ d
                ·
                  by_cases h : 632456 ≤ d
                  ·
                    have : d = 632456 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632455 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632454 ≤ d
                  ·
                    have : d = 632454 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632453 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632451 ≤ d
                ·
                  by_cases h : 632452 ≤ d
                  ·
                    have : d = 632452 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632451 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632450 ≤ d
                  ·
                    have : d = 632450 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 632449 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 632385 ≤ d
      ·
        by_cases h : 632417 ≤ d
        ·
          by_cases h : 632433 ≤ d
          ·
            by_cases h : 632441 ≤ d
            ·
              by_cases h : 632445 ≤ d
              ·
                by_cases h : 632447 ≤ d
                ·
                  by_cases h : 632448 ≤ d
                  ·
                    have : d = 632448 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 61)
      exact by decide
                  ·
                    have : d = 632447 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632446 ≤ d
                  ·
                    have : d = 632446 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632445 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632443 ≤ d
                ·
                  by_cases h : 632444 ≤ d
                  ·
                    have : d = 632444 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632443 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632442 ≤ d
                  ·
                    have : d = 632442 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632441 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632437 ≤ d
              ·
                by_cases h : 632439 ≤ d
                ·
                  by_cases h : 632440 ≤ d
                  ·
                    have : d = 632440 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632439 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632438 ≤ d
                  ·
                    have : d = 632438 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1761029)
      right
      exact ⟨1128591, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632437 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632435 ≤ d
                ·
                  by_cases h : 632436 ≤ d
                  ·
                    have : d = 632436 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7529)
      exact by decide
                  ·
                    have : d = 632435 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632434 ≤ d
                  ·
                    have : d = 632434 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632433 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 632425 ≤ d
            ·
              by_cases h : 632429 ≤ d
              ·
                by_cases h : 632431 ≤ d
                ·
                  by_cases h : 632432 ≤ d
                  ·
                    have : d = 632432 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 632431 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632430 ≤ d
                  ·
                    have : d = 632430 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632429 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632427 ≤ d
                ·
                  by_cases h : 632428 ≤ d
                  ·
                    have : d = 632428 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632427 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632426 ≤ d
                  ·
                    have : d = 632426 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 43669)
      right
      exact ⟨22609, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632425 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632421 ≤ d
              ·
                by_cases h : 632423 ≤ d
                ·
                  by_cases h : 632424 ≤ d
                  ·
                    have : d = 632424 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632423 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632422 ≤ d
                  ·
                    have : d = 632422 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632421 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632419 ≤ d
                ·
                  by_cases h : 632420 ≤ d
                  ·
                    have : d = 632420 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 103)
      exact by decide
                  ·
                    have : d = 632419 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632418 ≤ d
                  ·
                    have : d = 632418 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 109)
      exact by decide
                  ·
                    have : d = 632417 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 632401 ≤ d
          ·
            by_cases h : 632409 ≤ d
            ·
              by_cases h : 632413 ≤ d
              ·
                by_cases h : 632415 ≤ d
                ·
                  by_cases h : 632416 ≤ d
                  ·
                    have : d = 632416 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632415 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632414 ≤ d
                  ·
                    have : d = 632414 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632413 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632411 ≤ d
                ·
                  by_cases h : 632412 ≤ d
                  ·
                    have : d = 632412 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1597)
      exact by decide
                  ·
                    have : d = 632411 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632410 ≤ d
                  ·
                    have : d = 632410 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632409 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632405 ≤ d
              ·
                by_cases h : 632407 ≤ d
                ·
                  by_cases h : 632408 ≤ d
                  ·
                    have : d = 632408 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632407 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632406 ≤ d
                  ·
                    have : d = 632406 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13739439949)
      right
      exact ⟨13738807543, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632405 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632403 ≤ d
                ·
                  by_cases h : 632404 ≤ d
                  ·
                    have : d = 632404 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632403 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632402 ≤ d
                  ·
                    have : d = 632402 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 498367)
      right
      exact ⟨364332, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632401 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 632393 ≤ d
            ·
              by_cases h : 632397 ≤ d
              ·
                by_cases h : 632399 ≤ d
                ·
                  by_cases h : 632400 ≤ d
                  ·
                    have : d = 632400 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632399 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632398 ≤ d
                  ·
                    have : d = 632398 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632397 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632395 ≤ d
                ·
                  by_cases h : 632396 ≤ d
                  ·
                    have : d = 632396 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 632395 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632394 ≤ d
                  ·
                    have : d = 632394 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632393 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632389 ≤ d
              ·
                by_cases h : 632391 ≤ d
                ·
                  by_cases h : 632392 ≤ d
                  ·
                    have : d = 632392 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632391 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632390 ≤ d
                  ·
                    have : d = 632390 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5749)
      exact by decide
                  ·
                    have : d = 632389 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632387 ≤ d
                ·
                  by_cases h : 632388 ≤ d
                  ·
                    have : d = 632388 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 151)
      exact by decide
                  ·
                    have : d = 632387 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632386 ≤ d
                  ·
                    have : d = 632386 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632385 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 632353 ≤ d
        ·
          by_cases h : 632369 ≤ d
          ·
            by_cases h : 632377 ≤ d
            ·
              by_cases h : 632381 ≤ d
              ·
                by_cases h : 632383 ≤ d
                ·
                  by_cases h : 632384 ≤ d
                  ·
                    have : d = 632384 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632383 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632382 ≤ d
                  ·
                    have : d = 632382 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2583419)
      right
      exact ⟨1951037, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632381 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632379 ≤ d
                ·
                  by_cases h : 632380 ≤ d
                  ·
                    have : d = 632380 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632379 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632378 ≤ d
                  ·
                    have : d = 632378 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 82219)
      right
      exact ⟨25374, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632377 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632373 ≤ d
              ·
                by_cases h : 632375 ≤ d
                ·
                  by_cases h : 632376 ≤ d
                  ·
                    have : d = 632376 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 8783)
      exact by decide
                  ·
                    have : d = 632375 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632374 ≤ d
                  ·
                    have : d = 632374 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632373 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632371 ≤ d
                ·
                  by_cases h : 632372 ≤ d
                  ·
                    have : d = 632372 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632371 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632370 ≤ d
                  ·
                    have : d = 632370 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 107)
      exact by decide
                  ·
                    have : d = 632369 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 632361 ≤ d
            ·
              by_cases h : 632365 ≤ d
              ·
                by_cases h : 632367 ≤ d
                ·
                  by_cases h : 632368 ≤ d
                  ·
                    have : d = 632368 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632367 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632366 ≤ d
                  ·
                    have : d = 632366 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 632365 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632363 ≤ d
                ·
                  by_cases h : 632364 ≤ d
                  ·
                    have : d = 632364 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632363 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632362 ≤ d
                  ·
                    have : d = 632362 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632361 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632357 ≤ d
              ·
                by_cases h : 632359 ≤ d
                ·
                  by_cases h : 632360 ≤ d
                  ·
                    have : d = 632360 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 15809)
      exact by decide
                  ·
                    have : d = 632359 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632358 ≤ d
                  ·
                    have : d = 632358 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632357 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632355 ≤ d
                ·
                  by_cases h : 632356 ≤ d
                  ·
                    have : d = 632356 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632355 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632354 ≤ d
                  ·
                    have : d = 632354 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632353 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 632337 ≤ d
          ·
            by_cases h : 632345 ≤ d
            ·
              by_cases h : 632349 ≤ d
              ·
                by_cases h : 632351 ≤ d
                ·
                  by_cases h : 632352 ≤ d
                  ·
                    have : d = 632352 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 941)
      exact by decide
                  ·
                    have : d = 632351 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632350 ≤ d
                  ·
                    have : d = 632350 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632349 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632347 ≤ d
                ·
                  by_cases h : 632348 ≤ d
                  ·
                    have : d = 632348 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 113)
      exact by decide
                  ·
                    have : d = 632347 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632346 ≤ d
                  ·
                    have : d = 632346 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 632345 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632341 ≤ d
              ·
                by_cases h : 632343 ≤ d
                ·
                  by_cases h : 632344 ≤ d
                  ·
                    have : d = 632344 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632343 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632342 ≤ d
                  ·
                    have : d = 632342 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632341 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632339 ≤ d
                ·
                  by_cases h : 632340 ≤ d
                  ·
                    have : d = 632340 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1171)
      exact by decide
                  ·
                    have : d = 632339 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632338 ≤ d
                  ·
                    have : d = 632338 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632337 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 632329 ≤ d
            ·
              by_cases h : 632333 ≤ d
              ·
                by_cases h : 632335 ≤ d
                ·
                  by_cases h : 632336 ≤ d
                  ·
                    have : d = 632336 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 39521)
      exact by decide
                  ·
                    have : d = 632335 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632334 ≤ d
                  ·
                    have : d = 632334 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632333 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632331 ≤ d
                ·
                  by_cases h : 632332 ≤ d
                  ·
                    have : d = 632332 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632331 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632330 ≤ d
                  ·
                    have : d = 632330 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632329 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 632325 ≤ d
              ·
                by_cases h : 632327 ≤ d
                ·
                  by_cases h : 632328 ≤ d
                  ·
                    have : d = 632328 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 26347)
      exact by decide
                  ·
                    have : d = 632327 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632326 ≤ d
                  ·
                    have : d = 632326 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632325 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 632323 ≤ d
                ·
                  by_cases h : 632324 ≤ d
                  ·
                    have : d = 632324 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 632323 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 632322 ≤ d
                  ·
                    have : d = 632322 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 35129)
      exact by decide
                  ·
                    have : d = 632321 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩

end PrimeFactorUnimodality
