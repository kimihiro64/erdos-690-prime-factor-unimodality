import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapFermat

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

theorem fullRecordGapAddBlock_part1963 (d : Nat) (548353 ≤ d) (d ≤ 548864) : ¬(recordGapCenter + d).Prime := by
  by_cases h : 548609 ≤ d
  ·
    by_cases h : 548737 ≤ d
    ·
      by_cases h : 548801 ≤ d
      ·
        by_cases h : 548833 ≤ d
        ·
          by_cases h : 548849 ≤ d
          ·
            by_cases h : 548857 ≤ d
            ·
              by_cases h : 548861 ≤ d
              ·
                by_cases h : 548863 ≤ d
                ·
                  by_cases h : 548864 ≤ d
                  ·
                    have : d = 548864 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548863 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548862 ≤ d
                  ·
                    have : d = 548862 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548861 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548859 ≤ d
                ·
                  by_cases h : 548860 ≤ d
                  ·
                    have : d = 548860 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548859 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548858 ≤ d
                  ·
                    have : d = 548858 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 548857 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548853 ≤ d
              ·
                by_cases h : 548855 ≤ d
                ·
                  by_cases h : 548856 ≤ d
                  ·
                    have : d = 548856 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3839923)
      right
      exact ⟨3291067, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548855 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548854 ≤ d
                  ·
                    have : d = 548854 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548853 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548851 ≤ d
                ·
                  by_cases h : 548852 ≤ d
                  ·
                    have : d = 548852 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548851 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548850 ≤ d
                  ·
                    have : d = 548850 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3659)
      exact by decide
                  ·
                    have : d = 548849 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 548841 ≤ d
            ·
              by_cases h : 548845 ≤ d
              ·
                by_cases h : 548847 ≤ d
                ·
                  by_cases h : 548848 ≤ d
                  ·
                    have : d = 548848 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548847 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548846 ≤ d
                  ·
                    have : d = 548846 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 435907)
      right
      exact ⟨322968, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548845 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548843 ≤ d
                ·
                  by_cases h : 548844 ≤ d
                  ·
                    have : d = 548844 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548843 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548842 ≤ d
                  ·
                    have : d = 548842 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548841 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548837 ≤ d
              ·
                by_cases h : 548839 ≤ d
                ·
                  by_cases h : 548840 ≤ d
                  ·
                    have : d = 548840 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13721)
      exact by decide
                  ·
                    have : d = 548839 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548838 ≤ d
                  ·
                    have : d = 548838 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 30491)
      exact by decide
                  ·
                    have : d = 548837 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548835 ≤ d
                ·
                  by_cases h : 548836 ≤ d
                  ·
                    have : d = 548836 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548835 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548834 ≤ d
                  ·
                    have : d = 548834 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548833 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 548817 ≤ d
          ·
            by_cases h : 548825 ≤ d
            ·
              by_cases h : 548829 ≤ d
              ·
                by_cases h : 548831 ≤ d
                ·
                  by_cases h : 548832 ≤ d
                  ·
                    have : d = 548832 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5717)
      exact by decide
                  ·
                    have : d = 548831 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548830 ≤ d
                  ·
                    have : d = 548830 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548829 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548827 ≤ d
                ·
                  by_cases h : 548828 ≤ d
                  ·
                    have : d = 548828 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 548827 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548826 ≤ d
                  ·
                    have : d = 548826 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 548825 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548821 ≤ d
              ·
                by_cases h : 548823 ≤ d
                ·
                  by_cases h : 548824 ≤ d
                  ·
                    have : d = 548824 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548823 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548822 ≤ d
                  ·
                    have : d = 548822 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 137)
      exact by decide
                  ·
                    have : d = 548821 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548819 ≤ d
                ·
                  by_cases h : 548820 ≤ d
                  ·
                    have : d = 548820 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548819 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548818 ≤ d
                  ·
                    have : d = 548818 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548817 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 548809 ≤ d
            ·
              by_cases h : 548813 ≤ d
              ·
                by_cases h : 548815 ≤ d
                ·
                  by_cases h : 548816 ≤ d
                  ·
                    have : d = 548816 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 34301)
      exact by decide
                  ·
                    have : d = 548815 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548814 ≤ d
                  ·
                    have : d = 548814 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548813 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548811 ≤ d
                ·
                  by_cases h : 548812 ≤ d
                  ·
                    have : d = 548812 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548811 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548810 ≤ d
                  ·
                    have : d = 548810 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 533051)
      right
      exact ⟨517292, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548809 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548805 ≤ d
              ·
                by_cases h : 548807 ≤ d
                ·
                  by_cases h : 548808 ≤ d
                  ·
                    have : d = 548808 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548807 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548806 ≤ d
                  ·
                    have : d = 548806 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548805 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548803 ≤ d
                ·
                  by_cases h : 548804 ≤ d
                  ·
                    have : d = 548804 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548803 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548802 ≤ d
                  ·
                    have : d = 548802 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 10163)
      exact by decide
                  ·
                    have : d = 548801 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 548769 ≤ d
        ·
          by_cases h : 548785 ≤ d
          ·
            by_cases h : 548793 ≤ d
            ·
              by_cases h : 548797 ≤ d
              ·
                by_cases h : 548799 ≤ d
                ·
                  by_cases h : 548800 ≤ d
                  ·
                    have : d = 548800 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548799 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548798 ≤ d
                  ·
                    have : d = 548798 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 331)
      exact by decide
                  ·
                    have : d = 548797 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548795 ≤ d
                ·
                  by_cases h : 548796 ≤ d
                  ·
                    have : d = 548796 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 548795 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548794 ≤ d
                  ·
                    have : d = 548794 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548793 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548789 ≤ d
              ·
                by_cases h : 548791 ≤ d
                ·
                  by_cases h : 548792 ≤ d
                  ·
                    have : d = 548792 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548791 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548790 ≤ d
                  ·
                    have : d = 548790 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1663)
      exact by decide
                  ·
                    have : d = 548789 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548787 ≤ d
                ·
                  by_cases h : 548788 ≤ d
                  ·
                    have : d = 548788 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548787 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548786 ≤ d
                  ·
                    have : d = 548786 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548785 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 548777 ≤ d
            ·
              by_cases h : 548781 ≤ d
              ·
                by_cases h : 548783 ≤ d
                ·
                  by_cases h : 548784 ≤ d
                  ·
                    have : d = 548784 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548783 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548782 ≤ d
                  ·
                    have : d = 548782 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548781 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548779 ≤ d
                ·
                  by_cases h : 548780 ≤ d
                  ·
                    have : d = 548780 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 548779 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548778 ≤ d
                  ·
                    have : d = 548778 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548777 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548773 ≤ d
              ·
                by_cases h : 548775 ≤ d
                ·
                  by_cases h : 548776 ≤ d
                  ·
                    have : d = 548776 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548775 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548774 ≤ d
                  ·
                    have : d = 548774 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548773 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548771 ≤ d
                ·
                  by_cases h : 548772 ≤ d
                  ·
                    have : d = 548772 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 47)
      exact by decide
                  ·
                    have : d = 548771 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548770 ≤ d
                  ·
                    have : d = 548770 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548769 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 548753 ≤ d
          ·
            by_cases h : 548761 ≤ d
            ·
              by_cases h : 548765 ≤ d
              ·
                by_cases h : 548767 ≤ d
                ·
                  by_cases h : 548768 ≤ d
                  ·
                    have : d = 548768 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1559)
      exact by decide
                  ·
                    have : d = 548767 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548766 ≤ d
                  ·
                    have : d = 548766 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 43)
      exact by decide
                  ·
                    have : d = 548765 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548763 ≤ d
                ·
                  by_cases h : 548764 ≤ d
                  ·
                    have : d = 548764 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548763 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548762 ≤ d
                  ·
                    have : d = 548762 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 548761 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548757 ≤ d
              ·
                by_cases h : 548759 ≤ d
                ·
                  by_cases h : 548760 ≤ d
                  ·
                    have : d = 548760 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 548759 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548758 ≤ d
                  ·
                    have : d = 548758 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548757 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548755 ≤ d
                ·
                  by_cases h : 548756 ≤ d
                  ·
                    have : d = 548756 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 548755 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548754 ≤ d
                  ·
                    have : d = 548754 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548753 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 548745 ≤ d
            ·
              by_cases h : 548749 ≤ d
              ·
                by_cases h : 548751 ≤ d
                ·
                  by_cases h : 548752 ≤ d
                  ·
                    have : d = 548752 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548751 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548750 ≤ d
                  ·
                    have : d = 548750 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548749 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548747 ≤ d
                ·
                  by_cases h : 548748 ≤ d
                  ·
                    have : d = 548748 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5081)
      exact by decide
                  ·
                    have : d = 548747 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548746 ≤ d
                  ·
                    have : d = 548746 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548745 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548741 ≤ d
              ·
                by_cases h : 548743 ≤ d
                ·
                  by_cases h : 548744 ≤ d
                  ·
                    have : d = 548744 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548743 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548742 ≤ d
                  ·
                    have : d = 548742 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548741 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548739 ≤ d
                ·
                  by_cases h : 548740 ≤ d
                  ·
                    have : d = 548740 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548739 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548738 ≤ d
                  ·
                    have : d = 548738 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 548737 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 548673 ≤ d
      ·
        by_cases h : 548705 ≤ d
        ·
          by_cases h : 548721 ≤ d
          ·
            by_cases h : 548729 ≤ d
            ·
              by_cases h : 548733 ≤ d
              ·
                by_cases h : 548735 ≤ d
                ·
                  by_cases h : 548736 ≤ d
                  ·
                    have : d = 548736 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548735 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548734 ≤ d
                  ·
                    have : d = 548734 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548733 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548731 ≤ d
                ·
                  by_cases h : 548732 ≤ d
                  ·
                    have : d = 548732 := by omega
                    subst d
      exact fullRecordGapTerm09159_not_prime
                  ·
                    have : d = 548731 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548730 ≤ d
                  ·
                    have : d = 548730 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 548729 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548725 ≤ d
              ·
                by_cases h : 548727 ≤ d
                ·
                  by_cases h : 548728 ≤ d
                  ·
                    have : d = 548728 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548727 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548726 ≤ d
                  ·
                    have : d = 548726 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 548725 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548723 ≤ d
                ·
                  by_cases h : 548724 ≤ d
                  ·
                    have : d = 548724 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548723 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548722 ≤ d
                  ·
                    have : d = 548722 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548721 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 548713 ≤ d
            ·
              by_cases h : 548717 ≤ d
              ·
                by_cases h : 548719 ≤ d
                ·
                  by_cases h : 548720 ≤ d
                  ·
                    have : d = 548720 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548719 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548718 ≤ d
                  ·
                    have : d = 548718 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 14741543)
      right
      exact ⟨14192825, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548717 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548715 ≤ d
                ·
                  by_cases h : 548716 ≤ d
                  ·
                    have : d = 548716 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548715 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548714 ≤ d
                  ·
                    have : d = 548714 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548713 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548709 ≤ d
              ·
                by_cases h : 548711 ≤ d
                ·
                  by_cases h : 548712 ≤ d
                  ·
                    have : d = 548712 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7621)
      exact by decide
                  ·
                    have : d = 548711 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548710 ≤ d
                  ·
                    have : d = 548710 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548709 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548707 ≤ d
                ·
                  by_cases h : 548708 ≤ d
                  ·
                    have : d = 548708 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548707 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548706 ≤ d
                  ·
                    have : d = 548706 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 109)
      exact by decide
                  ·
                    have : d = 548705 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 548689 ≤ d
          ·
            by_cases h : 548697 ≤ d
            ·
              by_cases h : 548701 ≤ d
              ·
                by_cases h : 548703 ≤ d
                ·
                  by_cases h : 548704 ≤ d
                  ·
                    have : d = 548704 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548703 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548702 ≤ d
                  ·
                    have : d = 548702 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 509)
      exact by decide
                  ·
                    have : d = 548701 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548699 ≤ d
                ·
                  by_cases h : 548700 ≤ d
                  ·
                    have : d = 548700 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 548699 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548698 ≤ d
                  ·
                    have : d = 548698 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548697 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548693 ≤ d
              ·
                by_cases h : 548695 ≤ d
                ·
                  by_cases h : 548696 ≤ d
                  ·
                    have : d = 548696 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 107)
      exact by decide
                  ·
                    have : d = 548695 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548694 ≤ d
                  ·
                    have : d = 548694 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548693 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548691 ≤ d
                ·
                  by_cases h : 548692 ≤ d
                  ·
                    have : d = 548692 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548691 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548690 ≤ d
                  ·
                    have : d = 548690 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 74294867)
      right
      exact ⟨73746177, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548689 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 548681 ≤ d
            ·
              by_cases h : 548685 ≤ d
              ·
                by_cases h : 548687 ≤ d
                ·
                  by_cases h : 548688 ≤ d
                  ·
                    have : d = 548688 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 548687 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548686 ≤ d
                  ·
                    have : d = 548686 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548685 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548683 ≤ d
                ·
                  by_cases h : 548684 ≤ d
                  ·
                    have : d = 548684 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548683 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548682 ≤ d
                  ·
                    have : d = 548682 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 548681 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548677 ≤ d
              ·
                by_cases h : 548679 ≤ d
                ·
                  by_cases h : 548680 ≤ d
                  ·
                    have : d = 548680 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548679 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548678 ≤ d
                  ·
                    have : d = 548678 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 548677 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548675 ≤ d
                ·
                  by_cases h : 548676 ≤ d
                  ·
                    have : d = 548676 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548675 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548674 ≤ d
                  ·
                    have : d = 548674 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548673 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 548641 ≤ d
        ·
          by_cases h : 548657 ≤ d
          ·
            by_cases h : 548665 ≤ d
            ·
              by_cases h : 548669 ≤ d
              ·
                by_cases h : 548671 ≤ d
                ·
                  by_cases h : 548672 ≤ d
                  ·
                    have : d = 548672 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 8573)
      exact by decide
                  ·
                    have : d = 548671 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548670 ≤ d
                  ·
                    have : d = 548670 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 18289)
      exact by decide
                  ·
                    have : d = 548669 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548667 ≤ d
                ·
                  by_cases h : 548668 ≤ d
                  ·
                    have : d = 548668 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548667 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548666 ≤ d
                  ·
                    have : d = 548666 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548665 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548661 ≤ d
              ·
                by_cases h : 548663 ≤ d
                ·
                  by_cases h : 548664 ≤ d
                  ·
                    have : d = 548664 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548663 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548662 ≤ d
                  ·
                    have : d = 548662 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548661 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548659 ≤ d
                ·
                  by_cases h : 548660 ≤ d
                  ·
                    have : d = 548660 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3919)
      exact by decide
                  ·
                    have : d = 548659 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548658 ≤ d
                  ·
                    have : d = 548658 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 548657 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 548649 ≤ d
            ·
              by_cases h : 548653 ≤ d
              ·
                by_cases h : 548655 ≤ d
                ·
                  by_cases h : 548656 ≤ d
                  ·
                    have : d = 548656 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548655 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548654 ≤ d
                  ·
                    have : d = 548654 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548653 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548651 ≤ d
                ·
                  by_cases h : 548652 ≤ d
                  ·
                    have : d = 548652 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548651 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548650 ≤ d
                  ·
                    have : d = 548650 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548649 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548645 ≤ d
              ·
                by_cases h : 548647 ≤ d
                ·
                  by_cases h : 548648 ≤ d
                  ·
                    have : d = 548648 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 136453)
      right
      exact ⟨133617, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548647 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548646 ≤ d
                  ·
                    have : d = 548646 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13063)
      exact by decide
                  ·
                    have : d = 548645 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548643 ≤ d
                ·
                  by_cases h : 548644 ≤ d
                  ·
                    have : d = 548644 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548643 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548642 ≤ d
                  ·
                    have : d = 548642 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 548641 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 548625 ≤ d
          ·
            by_cases h : 548633 ≤ d
            ·
              by_cases h : 548637 ≤ d
              ·
                by_cases h : 548639 ≤ d
                ·
                  by_cases h : 548640 ≤ d
                  ·
                    have : d = 548640 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 127)
      exact by decide
                  ·
                    have : d = 548639 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548638 ≤ d
                  ·
                    have : d = 548638 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548637 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548635 ≤ d
                ·
                  by_cases h : 548636 ≤ d
                  ·
                    have : d = 548636 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 548635 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548634 ≤ d
                  ·
                    have : d = 548634 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548633 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548629 ≤ d
              ·
                by_cases h : 548631 ≤ d
                ·
                  by_cases h : 548632 ≤ d
                  ·
                    have : d = 548632 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548631 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548630 ≤ d
                  ·
                    have : d = 548630 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 83)
      exact by decide
                  ·
                    have : d = 548629 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548627 ≤ d
                ·
                  by_cases h : 548628 ≤ d
                  ·
                    have : d = 548628 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 131)
      exact by decide
                  ·
                    have : d = 548627 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548626 ≤ d
                  ·
                    have : d = 548626 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548625 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 548617 ≤ d
            ·
              by_cases h : 548621 ≤ d
              ·
                by_cases h : 548623 ≤ d
                ·
                  by_cases h : 548624 ≤ d
                  ·
                    have : d = 548624 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548623 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548622 ≤ d
                  ·
                    have : d = 548622 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 548621 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548619 ≤ d
                ·
                  by_cases h : 548620 ≤ d
                  ·
                    have : d = 548620 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548619 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548618 ≤ d
                  ·
                    have : d = 548618 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 149)
      exact by decide
                  ·
                    have : d = 548617 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548613 ≤ d
              ·
                by_cases h : 548615 ≤ d
                ·
                  by_cases h : 548616 ≤ d
                  ·
                    have : d = 548616 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 22859)
      exact by decide
                  ·
                    have : d = 548615 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548614 ≤ d
                  ·
                    have : d = 548614 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548613 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548611 ≤ d
                ·
                  by_cases h : 548612 ≤ d
                  ·
                    have : d = 548612 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 25141789)
      right
      exact ⟨24593177, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548611 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548610 ≤ d
                  ·
                    have : d = 548610 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548609 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
  ·
    by_cases h : 548481 ≤ d
    ·
      by_cases h : 548545 ≤ d
      ·
        by_cases h : 548577 ≤ d
        ·
          by_cases h : 548593 ≤ d
          ·
            by_cases h : 548601 ≤ d
            ·
              by_cases h : 548605 ≤ d
              ·
                by_cases h : 548607 ≤ d
                ·
                  by_cases h : 548608 ≤ d
                  ·
                    have : d = 548608 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548607 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548606 ≤ d
                  ·
                    have : d = 548606 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 548605 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548603 ≤ d
                ·
                  by_cases h : 548604 ≤ d
                  ·
                    have : d = 548604 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548603 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548602 ≤ d
                  ·
                    have : d = 548602 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548601 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548597 ≤ d
              ·
                by_cases h : 548599 ≤ d
                ·
                  by_cases h : 548600 ≤ d
                  ·
                    have : d = 548600 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 548599 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548598 ≤ d
                  ·
                    have : d = 548598 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 440581)
      right
      exact ⟨332564, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548597 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548595 ≤ d
                ·
                  by_cases h : 548596 ≤ d
                  ·
                    have : d = 548596 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548595 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548594 ≤ d
                  ·
                    have : d = 548594 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548593 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 548585 ≤ d
            ·
              by_cases h : 548589 ≤ d
              ·
                by_cases h : 548591 ≤ d
                ·
                  by_cases h : 548592 ≤ d
                  ·
                    have : d = 548592 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1039)
      exact by decide
                  ·
                    have : d = 548591 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548590 ≤ d
                  ·
                    have : d = 548590 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548589 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548587 ≤ d
                ·
                  by_cases h : 548588 ≤ d
                  ·
                    have : d = 548588 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548587 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548586 ≤ d
                  ·
                    have : d = 548586 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 10159)
      exact by decide
                  ·
                    have : d = 548585 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548581 ≤ d
              ·
                by_cases h : 548583 ≤ d
                ·
                  by_cases h : 548584 ≤ d
                  ·
                    have : d = 548584 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548583 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548582 ≤ d
                  ·
                    have : d = 548582 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548581 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548579 ≤ d
                ·
                  by_cases h : 548580 ≤ d
                  ·
                    have : d = 548580 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 41)
      exact by decide
                  ·
                    have : d = 548579 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548578 ≤ d
                  ·
                    have : d = 548578 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548577 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 548561 ≤ d
          ·
            by_cases h : 548569 ≤ d
            ·
              by_cases h : 548573 ≤ d
              ·
                by_cases h : 548575 ≤ d
                ·
                  by_cases h : 548576 ≤ d
                  ·
                    have : d = 548576 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 548575 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548574 ≤ d
                  ·
                    have : d = 548574 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548573 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548571 ≤ d
                ·
                  by_cases h : 548572 ≤ d
                  ·
                    have : d = 548572 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548571 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548570 ≤ d
                  ·
                    have : d = 548570 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 4987)
      exact by decide
                  ·
                    have : d = 548569 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548565 ≤ d
              ·
                by_cases h : 548567 ≤ d
                ·
                  by_cases h : 548568 ≤ d
                  ·
                    have : d = 548568 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548567 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548566 ≤ d
                  ·
                    have : d = 548566 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548565 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548563 ≤ d
                ·
                  by_cases h : 548564 ≤ d
                  ·
                    have : d = 548564 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548563 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548562 ≤ d
                  ·
                    have : d = 548562 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 548561 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 548553 ≤ d
            ·
              by_cases h : 548557 ≤ d
              ·
                by_cases h : 548559 ≤ d
                ·
                  by_cases h : 548560 ≤ d
                  ·
                    have : d = 548560 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548559 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548558 ≤ d
                  ·
                    have : d = 548558 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 157)
      exact by decide
                  ·
                    have : d = 548557 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548555 ≤ d
                ·
                  by_cases h : 548556 ≤ d
                  ·
                    have : d = 548556 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 548555 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548554 ≤ d
                  ·
                    have : d = 548554 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548553 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548549 ≤ d
              ·
                by_cases h : 548551 ≤ d
                ·
                  by_cases h : 548552 ≤ d
                  ·
                    have : d = 548552 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 191)
      exact by decide
                  ·
                    have : d = 548551 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548550 ≤ d
                  ·
                    have : d = 548550 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 548549 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548547 ≤ d
                ·
                  by_cases h : 548548 ≤ d
                  ·
                    have : d = 548548 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548547 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548546 ≤ d
                  ·
                    have : d = 548546 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 71)
      exact by decide
                  ·
                    have : d = 548545 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 548513 ≤ d
        ·
          by_cases h : 548529 ≤ d
          ·
            by_cases h : 548537 ≤ d
            ·
              by_cases h : 548541 ≤ d
              ·
                by_cases h : 548543 ≤ d
                ·
                  by_cases h : 548544 ≤ d
                  ·
                    have : d = 548544 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548543 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548542 ≤ d
                  ·
                    have : d = 548542 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548541 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548539 ≤ d
                ·
                  by_cases h : 548540 ≤ d
                  ·
                    have : d = 548540 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548539 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548538 ≤ d
                  ·
                    have : d = 548538 := by omega
                    subst d
      exact fullRecordGapTerm09158_not_prime
                  ·
                    have : d = 548537 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548533 ≤ d
              ·
                by_cases h : 548535 ≤ d
                ·
                  by_cases h : 548536 ≤ d
                  ·
                    have : d = 548536 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548535 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548534 ≤ d
                  ·
                    have : d = 548534 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548533 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548531 ≤ d
                ·
                  by_cases h : 548532 ≤ d
                  ·
                    have : d = 548532 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1693)
      exact by decide
                  ·
                    have : d = 548531 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548530 ≤ d
                  ·
                    have : d = 548530 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548529 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 548521 ≤ d
            ·
              by_cases h : 548525 ≤ d
              ·
                by_cases h : 548527 ≤ d
                ·
                  by_cases h : 548528 ≤ d
                  ·
                    have : d = 548528 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 34283)
      exact by decide
                  ·
                    have : d = 548527 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548526 ≤ d
                  ·
                    have : d = 548526 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548525 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548523 ≤ d
                ·
                  by_cases h : 548524 ≤ d
                  ·
                    have : d = 548524 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548523 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548522 ≤ d
                  ·
                    have : d = 548522 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548521 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548517 ≤ d
              ·
                by_cases h : 548519 ≤ d
                ·
                  by_cases h : 548520 ≤ d
                  ·
                    have : d = 548520 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 653)
      exact by decide
                  ·
                    have : d = 548519 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548518 ≤ d
                  ·
                    have : d = 548518 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548517 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548515 ≤ d
                ·
                  by_cases h : 548516 ≤ d
                  ·
                    have : d = 548516 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 241)
      exact by decide
                  ·
                    have : d = 548515 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548514 ≤ d
                  ·
                    have : d = 548514 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548513 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 548497 ≤ d
          ·
            by_cases h : 548505 ≤ d
            ·
              by_cases h : 548509 ≤ d
              ·
                by_cases h : 548511 ≤ d
                ·
                  by_cases h : 548512 ≤ d
                  ·
                    have : d = 548512 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548511 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548510 ≤ d
                  ·
                    have : d = 548510 := by omega
                    subst d
      exact fullRecordGapTerm09157_not_prime
                  ·
                    have : d = 548509 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548507 ≤ d
                ·
                  by_cases h : 548508 ≤ d
                  ·
                    have : d = 548508 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 43)
      exact by decide
                  ·
                    have : d = 548507 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548506 ≤ d
                  ·
                    have : d = 548506 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548505 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548501 ≤ d
              ·
                by_cases h : 548503 ≤ d
                ·
                  by_cases h : 548504 ≤ d
                  ·
                    have : d = 548504 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548503 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548502 ≤ d
                  ·
                    have : d = 548502 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 113)
      exact by decide
                  ·
                    have : d = 548501 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548499 ≤ d
                ·
                  by_cases h : 548500 ≤ d
                  ·
                    have : d = 548500 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548499 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548498 ≤ d
                  ·
                    have : d = 548498 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548497 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 548489 ≤ d
            ·
              by_cases h : 548493 ≤ d
              ·
                by_cases h : 548495 ≤ d
                ·
                  by_cases h : 548496 ≤ d
                  ·
                    have : d = 548496 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 548495 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548494 ≤ d
                  ·
                    have : d = 548494 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548493 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548491 ≤ d
                ·
                  by_cases h : 548492 ≤ d
                  ·
                    have : d = 548492 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 548491 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548490 ≤ d
                  ·
                    have : d = 548490 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 47)
      exact by decide
                  ·
                    have : d = 548489 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548485 ≤ d
              ·
                by_cases h : 548487 ≤ d
                ·
                  by_cases h : 548488 ≤ d
                  ·
                    have : d = 548488 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548487 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548486 ≤ d
                  ·
                    have : d = 548486 := by omega
                    subst d
      exact fullRecordGapTerm09156_not_prime
                  ·
                    have : d = 548485 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548483 ≤ d
                ·
                  by_cases h : 548484 ≤ d
                  ·
                    have : d = 548484 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548483 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548482 ≤ d
                  ·
                    have : d = 548482 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548481 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 548417 ≤ d
      ·
        by_cases h : 548449 ≤ d
        ·
          by_cases h : 548465 ≤ d
          ·
            by_cases h : 548473 ≤ d
            ·
              by_cases h : 548477 ≤ d
              ·
                by_cases h : 548479 ≤ d
                ·
                  by_cases h : 548480 ≤ d
                  ·
                    have : d = 548480 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 857)
      exact by decide
                  ·
                    have : d = 548479 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548478 ≤ d
                  ·
                    have : d = 548478 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548477 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548475 ≤ d
                ·
                  by_cases h : 548476 ≤ d
                  ·
                    have : d = 548476 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548475 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548474 ≤ d
                  ·
                    have : d = 548474 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548473 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548469 ≤ d
              ·
                by_cases h : 548471 ≤ d
                ·
                  by_cases h : 548472 ≤ d
                  ·
                    have : d = 548472 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 22853)
      exact by decide
                  ·
                    have : d = 548471 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548470 ≤ d
                  ·
                    have : d = 548470 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548469 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548467 ≤ d
                ·
                  by_cases h : 548468 ≤ d
                  ·
                    have : d = 548468 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 47797)
      right
      exact ⟨25096, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548467 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548466 ≤ d
                  ·
                    have : d = 548466 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 155521)
      right
      exact ⟨73618, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548465 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 548457 ≤ d
            ·
              by_cases h : 548461 ≤ d
              ·
                by_cases h : 548463 ≤ d
                ·
                  by_cases h : 548464 ≤ d
                  ·
                    have : d = 548464 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548463 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548462 ≤ d
                  ·
                    have : d = 548462 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 67)
      exact by decide
                  ·
                    have : d = 548461 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548459 ≤ d
                ·
                  by_cases h : 548460 ≤ d
                  ·
                    have : d = 548460 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 277)
      exact by decide
                  ·
                    have : d = 548459 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548458 ≤ d
                  ·
                    have : d = 548458 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548457 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548453 ≤ d
              ·
                by_cases h : 548455 ≤ d
                ·
                  by_cases h : 548456 ≤ d
                  ·
                    have : d = 548456 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548455 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548454 ≤ d
                  ·
                    have : d = 548454 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548453 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548451 ≤ d
                ·
                  by_cases h : 548452 ≤ d
                  ·
                    have : d = 548452 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548451 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548450 ≤ d
                  ·
                    have : d = 548450 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1567)
      exact by decide
                  ·
                    have : d = 548449 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 548433 ≤ d
          ·
            by_cases h : 548441 ≤ d
            ·
              by_cases h : 548445 ≤ d
              ·
                by_cases h : 548447 ≤ d
                ·
                  by_cases h : 548448 ≤ d
                  ·
                    have : d = 548448 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 548447 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548446 ≤ d
                  ·
                    have : d = 548446 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548445 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548443 ≤ d
                ·
                  by_cases h : 548444 ≤ d
                  ·
                    have : d = 548444 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548443 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548442 ≤ d
                  ·
                    have : d = 548442 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548441 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548437 ≤ d
              ·
                by_cases h : 548439 ≤ d
                ·
                  by_cases h : 548440 ≤ d
                  ·
                    have : d = 548440 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548439 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548438 ≤ d
                  ·
                    have : d = 548438 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 97)
      exact by decide
                  ·
                    have : d = 548437 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548435 ≤ d
                ·
                  by_cases h : 548436 ≤ d
                  ·
                    have : d = 548436 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 6529)
      exact by decide
                  ·
                    have : d = 548435 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548434 ≤ d
                  ·
                    have : d = 548434 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548433 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 548425 ≤ d
            ·
              by_cases h : 548429 ≤ d
              ·
                by_cases h : 548431 ≤ d
                ·
                  by_cases h : 548432 ≤ d
                  ·
                    have : d = 548432 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 151)
      exact by decide
                  ·
                    have : d = 548431 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548430 ≤ d
                  ·
                    have : d = 548430 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 101)
      exact by decide
                  ·
                    have : d = 548429 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548427 ≤ d
                ·
                  by_cases h : 548428 ≤ d
                  ·
                    have : d = 548428 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548427 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548426 ≤ d
                  ·
                    have : d = 548426 := by omega
                    subst d
      exact fullRecordGapTerm09155_not_prime
                  ·
                    have : d = 548425 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548421 ≤ d
              ·
                by_cases h : 548423 ≤ d
                ·
                  by_cases h : 548424 ≤ d
                  ·
                    have : d = 548424 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548423 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548422 ≤ d
                  ·
                    have : d = 548422 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548421 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548419 ≤ d
                ·
                  by_cases h : 548420 ≤ d
                  ·
                    have : d = 548420 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 548419 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548418 ≤ d
                  ·
                    have : d = 548418 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 548417 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 548385 ≤ d
        ·
          by_cases h : 548401 ≤ d
          ·
            by_cases h : 548409 ≤ d
            ·
              by_cases h : 548413 ≤ d
              ·
                by_cases h : 548415 ≤ d
                ·
                  by_cases h : 548416 ≤ d
                  ·
                    have : d = 548416 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548415 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548414 ≤ d
                  ·
                    have : d = 548414 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548413 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548411 ≤ d
                ·
                  by_cases h : 548412 ≤ d
                  ·
                    have : d = 548412 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548411 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548410 ≤ d
                  ·
                    have : d = 548410 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548409 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548405 ≤ d
              ·
                by_cases h : 548407 ≤ d
                ·
                  by_cases h : 548408 ≤ d
                  ·
                    have : d = 548408 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1399)
      exact by decide
                  ·
                    have : d = 548407 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548406 ≤ d
                  ·
                    have : d = 548406 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 30467)
      exact by decide
                  ·
                    have : d = 548405 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548403 ≤ d
                ·
                  by_cases h : 548404 ≤ d
                  ·
                    have : d = 548404 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548403 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548402 ≤ d
                  ·
                    have : d = 548402 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 75079)
      right
      exact ⟨52230, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548401 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 548393 ≤ d
            ·
              by_cases h : 548397 ≤ d
              ·
                by_cases h : 548399 ≤ d
                ·
                  by_cases h : 548400 ≤ d
                  ·
                    have : d = 548400 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548399 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548398 ≤ d
                  ·
                    have : d = 548398 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548397 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548395 ≤ d
                ·
                  by_cases h : 548396 ≤ d
                  ·
                    have : d = 548396 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 47)
      exact by decide
                  ·
                    have : d = 548395 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548394 ≤ d
                  ·
                    have : d = 548394 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548393 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548389 ≤ d
              ·
                by_cases h : 548391 ≤ d
                ·
                  by_cases h : 548392 ≤ d
                  ·
                    have : d = 548392 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548391 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548390 ≤ d
                  ·
                    have : d = 548390 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548389 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548387 ≤ d
                ·
                  by_cases h : 548388 ≤ d
                  ·
                    have : d = 548388 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 15233)
      exact by decide
                  ·
                    have : d = 548387 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548386 ≤ d
                  ·
                    have : d = 548386 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548385 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 548369 ≤ d
          ·
            by_cases h : 548377 ≤ d
            ·
              by_cases h : 548381 ≤ d
              ·
                by_cases h : 548383 ≤ d
                ·
                  by_cases h : 548384 ≤ d
                  ·
                    have : d = 548384 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548383 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548382 ≤ d
                  ·
                    have : d = 548382 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 72046147)
      right
      exact ⟨71497765, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548381 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548379 ≤ d
                ·
                  by_cases h : 548380 ≤ d
                  ·
                    have : d = 548380 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548379 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548378 ≤ d
                  ·
                    have : d = 548378 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 548377 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548373 ≤ d
              ·
                by_cases h : 548375 ≤ d
                ·
                  by_cases h : 548376 ≤ d
                  ·
                    have : d = 548376 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 73)
      exact by decide
                  ·
                    have : d = 548375 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548374 ≤ d
                  ·
                    have : d = 548374 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548373 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548371 ≤ d
                ·
                  by_cases h : 548372 ≤ d
                  ·
                    have : d = 548372 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548371 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548370 ≤ d
                  ·
                    have : d = 548370 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 677)
      exact by decide
                  ·
                    have : d = 548369 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 548361 ≤ d
            ·
              by_cases h : 548365 ≤ d
              ·
                by_cases h : 548367 ≤ d
                ·
                  by_cases h : 548368 ≤ d
                  ·
                    have : d = 548368 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548367 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548366 ≤ d
                  ·
                    have : d = 548366 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 548365 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548363 ≤ d
                ·
                  by_cases h : 548364 ≤ d
                  ·
                    have : d = 548364 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548363 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548362 ≤ d
                  ·
                    have : d = 548362 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548361 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 548357 ≤ d
              ·
                by_cases h : 548359 ≤ d
                ·
                  by_cases h : 548360 ≤ d
                  ·
                    have : d = 548360 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13709)
      exact by decide
                  ·
                    have : d = 548359 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548358 ≤ d
                  ·
                    have : d = 548358 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548357 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 548355 ≤ d
                ·
                  by_cases h : 548356 ≤ d
                  ·
                    have : d = 548356 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548355 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 548354 ≤ d
                  ·
                    have : d = 548354 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 548353 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩

end PrimeFactorUnimodality
