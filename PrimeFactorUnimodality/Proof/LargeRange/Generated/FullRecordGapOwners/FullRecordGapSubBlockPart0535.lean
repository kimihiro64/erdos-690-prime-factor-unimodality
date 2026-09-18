import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapFermat

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

theorem fullRecordGapSubBlock_part0535 (d : Nat) (273409 ≤ d) (d ≤ 273920) : ¬(recordGapCenter - d).Prime := by
  by_cases h : 273665 ≤ d
  ·
    by_cases h : 273793 ≤ d
    ·
      by_cases h : 273857 ≤ d
      ·
        by_cases h : 273889 ≤ d
        ·
          by_cases h : 273905 ≤ d
          ·
            by_cases h : 273913 ≤ d
            ·
              by_cases h : 273917 ≤ d
              ·
                by_cases h : 273919 ≤ d
                ·
                  by_cases h : 273920 ≤ d
                  ·
                    have : d = 273920 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273919 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273918 ≤ d
                  ·
                    have : d = 273918 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273917 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273915 ≤ d
                ·
                  by_cases h : 273916 ≤ d
                  ·
                    have : d = 273916 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273915 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273914 ≤ d
                  ·
                    have : d = 273914 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273913 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273909 ≤ d
              ·
                by_cases h : 273911 ≤ d
                ·
                  by_cases h : 273912 ≤ d
                  ·
                    have : d = 273912 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 101) (by norm_num)
      exact by decide
                  ·
                    have : d = 273911 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273910 ≤ d
                  ·
                    have : d = 273910 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 273909 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273907 ≤ d
                ·
                  by_cases h : 273908 ≤ d
                  ·
                    have : d = 273908 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273907 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273906 ≤ d
                  ·
                    have : d = 273906 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273905 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 273897 ≤ d
            ·
              by_cases h : 273901 ≤ d
              ·
                by_cases h : 273903 ≤ d
                ·
                  by_cases h : 273904 ≤ d
                  ·
                    have : d = 273904 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273903 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273902 ≤ d
                  ·
                    have : d = 273902 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273901 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273899 ≤ d
                ·
                  by_cases h : 273900 ≤ d
                  ·
                    have : d = 273900 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 83) (by norm_num)
      exact by decide
                  ·
                    have : d = 273899 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273898 ≤ d
                  ·
                    have : d = 273898 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3166549) (by norm_num)
      right
      exact ⟨273898, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273897 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273893 ≤ d
              ·
                by_cases h : 273895 ≤ d
                ·
                  by_cases h : 273896 ≤ d
                  ·
                    have : d = 273896 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273895 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273894 ≤ d
                  ·
                    have : d = 273894 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 191) (by norm_num)
      exact by decide
                  ·
                    have : d = 273893 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273891 ≤ d
                ·
                  by_cases h : 273892 ≤ d
                  ·
                    have : d = 273892 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 527099) (by norm_num)
      right
      exact ⟨273892, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273891 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273890 ≤ d
                  ·
                    have : d = 273890 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273889 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 273873 ≤ d
          ·
            by_cases h : 273881 ≤ d
            ·
              by_cases h : 273885 ≤ d
              ·
                by_cases h : 273887 ≤ d
                ·
                  by_cases h : 273888 ≤ d
                  ·
                    have : d = 273888 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 317) (by norm_num)
      exact by decide
                  ·
                    have : d = 273887 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273886 ≤ d
                  ·
                    have : d = 273886 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273885 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273883 ≤ d
                ·
                  by_cases h : 273884 ≤ d
                  ·
                    have : d = 273884 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273883 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273882 ≤ d
                  ·
                    have : d = 273882 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273881 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273877 ≤ d
              ·
                by_cases h : 273879 ≤ d
                ·
                  by_cases h : 273880 ≤ d
                  ·
                    have : d = 273880 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 41) (by norm_num)
      exact by decide
                  ·
                    have : d = 273879 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273878 ≤ d
                  ·
                    have : d = 273878 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273877 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273875 ≤ d
                ·
                  by_cases h : 273876 ≤ d
                  ·
                    have : d = 273876 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273875 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273874 ≤ d
                  ·
                    have : d = 273874 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 37) (by norm_num)
      exact by decide
                  ·
                    have : d = 273873 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 273865 ≤ d
            ·
              by_cases h : 273869 ≤ d
              ·
                by_cases h : 273871 ≤ d
                ·
                  by_cases h : 273872 ≤ d
                  ·
                    have : d = 273872 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273871 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273870 ≤ d
                  ·
                    have : d = 273870 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 273869 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273867 ≤ d
                ·
                  by_cases h : 273868 ≤ d
                  ·
                    have : d = 273868 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 9781) (by norm_num)
      exact by decide
                  ·
                    have : d = 273867 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273866 ≤ d
                  ·
                    have : d = 273866 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273865 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273861 ≤ d
              ·
                by_cases h : 273863 ≤ d
                ·
                  by_cases h : 273864 ≤ d
                  ·
                    have : d = 273864 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11411) (by norm_num)
      exact by decide
                  ·
                    have : d = 273863 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273862 ≤ d
                  ·
                    have : d = 273862 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273861 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273859 ≤ d
                ·
                  by_cases h : 273860 ≤ d
                  ·
                    have : d = 273860 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273859 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273858 ≤ d
                  ·
                    have : d = 273858 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 273857 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 273825 ≤ d
        ·
          by_cases h : 273841 ≤ d
          ·
            by_cases h : 273849 ≤ d
            ·
              by_cases h : 273853 ≤ d
              ·
                by_cases h : 273855 ≤ d
                ·
                  by_cases h : 273856 ≤ d
                  ·
                    have : d = 273856 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273855 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273854 ≤ d
                  ·
                    have : d = 273854 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273853 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273851 ≤ d
                ·
                  by_cases h : 273852 ≤ d
                  ·
                    have : d = 273852 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7607) (by norm_num)
      exact by decide
                  ·
                    have : d = 273851 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273850 ≤ d
                  ·
                    have : d = 273850 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5477) (by norm_num)
      exact by decide
                  ·
                    have : d = 273849 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273845 ≤ d
              ·
                by_cases h : 273847 ≤ d
                ·
                  by_cases h : 273848 ≤ d
                  ·
                    have : d = 273848 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273847 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273846 ≤ d
                  ·
                    have : d = 273846 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273845 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273843 ≤ d
                ·
                  by_cases h : 273844 ≤ d
                  ·
                    have : d = 273844 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 223) (by norm_num)
      exact by decide
                  ·
                    have : d = 273843 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273842 ≤ d
                  ·
                    have : d = 273842 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273841 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 273833 ≤ d
            ·
              by_cases h : 273837 ≤ d
              ·
                by_cases h : 273839 ≤ d
                ·
                  by_cases h : 273840 ≤ d
                  ·
                    have : d = 273840 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 163) (by norm_num)
      exact by decide
                  ·
                    have : d = 273839 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273838 ≤ d
                  ·
                    have : d = 273838 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273837 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273835 ≤ d
                ·
                  by_cases h : 273836 ≤ d
                  ·
                    have : d = 273836 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273835 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273834 ≤ d
                  ·
                    have : d = 273834 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273833 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273829 ≤ d
              ·
                by_cases h : 273831 ≤ d
                ·
                  by_cases h : 273832 ≤ d
                  ·
                    have : d = 273832 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 273831 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273830 ≤ d
                  ·
                    have : d = 273830 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273829 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273827 ≤ d
                ·
                  by_cases h : 273828 ≤ d
                  ·
                    have : d = 273828 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 273827 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273826 ≤ d
                  ·
                    have : d = 273826 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273825 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 273809 ≤ d
          ·
            by_cases h : 273817 ≤ d
            ·
              by_cases h : 273821 ≤ d
              ·
                by_cases h : 273823 ≤ d
                ·
                  by_cases h : 273824 ≤ d
                  ·
                    have : d = 273824 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273823 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273822 ≤ d
                  ·
                    have : d = 273822 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 47) (by norm_num)
      exact by decide
                  ·
                    have : d = 273821 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273819 ≤ d
                ·
                  by_cases h : 273820 ≤ d
                  ·
                    have : d = 273820 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273819 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273818 ≤ d
                  ·
                    have : d = 273818 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273817 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273813 ≤ d
              ·
                by_cases h : 273815 ≤ d
                ·
                  by_cases h : 273816 ≤ d
                  ·
                    have : d = 273816 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273815 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273814 ≤ d
                  ·
                    have : d = 273814 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 79) (by norm_num)
      exact by decide
                  ·
                    have : d = 273813 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273811 ≤ d
                ·
                  by_cases h : 273812 ≤ d
                  ·
                    have : d = 273812 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273811 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273810 ≤ d
                  ·
                    have : d = 273810 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 9127) (by norm_num)
      exact by decide
                  ·
                    have : d = 273809 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 273801 ≤ d
            ·
              by_cases h : 273805 ≤ d
              ·
                by_cases h : 273807 ≤ d
                ·
                  by_cases h : 273808 ≤ d
                  ·
                    have : d = 273808 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 109) (by norm_num)
      exact by decide
                  ·
                    have : d = 273807 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273806 ≤ d
                  ·
                    have : d = 273806 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273805 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273803 ≤ d
                ·
                  by_cases h : 273804 ≤ d
                  ·
                    have : d = 273804 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 22817) (by norm_num)
      exact by decide
                  ·
                    have : d = 273803 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273802 ≤ d
                  ·
                    have : d = 273802 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 273801 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273797 ≤ d
              ·
                by_cases h : 273799 ≤ d
                ·
                  by_cases h : 273800 ≤ d
                  ·
                    have : d = 273800 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273799 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273798 ≤ d
                  ·
                    have : d = 273798 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 41) (by norm_num)
      exact by decide
                  ·
                    have : d = 273797 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273795 ≤ d
                ·
                  by_cases h : 273796 ≤ d
                  ·
                    have : d = 273796 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273795 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273794 ≤ d
                  ·
                    have : d = 273794 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273793 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 273729 ≤ d
      ·
        by_cases h : 273761 ≤ d
        ·
          by_cases h : 273777 ≤ d
          ·
            by_cases h : 273785 ≤ d
            ·
              by_cases h : 273789 ≤ d
              ·
                by_cases h : 273791 ≤ d
                ·
                  by_cases h : 273792 ≤ d
                  ·
                    have : d = 273792 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273791 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273790 ≤ d
                  ·
                    have : d = 273790 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 273789 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273787 ≤ d
                ·
                  by_cases h : 273788 ≤ d
                  ·
                    have : d = 273788 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273787 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273786 ≤ d
                  ·
                    have : d = 273786 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273785 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273781 ≤ d
              ·
                by_cases h : 273783 ≤ d
                ·
                  by_cases h : 273784 ≤ d
                  ·
                    have : d = 273784 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 4889) (by norm_num)
      exact by decide
                  ·
                    have : d = 273783 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273782 ≤ d
                  ·
                    have : d = 273782 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273781 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273779 ≤ d
                ·
                  by_cases h : 273780 ≤ d
                  ·
                    have : d = 273780 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 273779 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273778 ≤ d
                  ·
                    have : d = 273778 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273777 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 273769 ≤ d
            ·
              by_cases h : 273773 ≤ d
              ·
                by_cases h : 273775 ≤ d
                ·
                  by_cases h : 273776 ≤ d
                  ·
                    have : d = 273776 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273775 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273774 ≤ d
                  ·
                    have : d = 273774 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 103) (by norm_num)
      exact by decide
                  ·
                    have : d = 273773 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273771 ≤ d
                ·
                  by_cases h : 273772 ≤ d
                  ·
                    have : d = 273772 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273771 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273770 ≤ d
                  ·
                    have : d = 273770 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273769 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273765 ≤ d
              ·
                by_cases h : 273767 ≤ d
                ·
                  by_cases h : 273768 ≤ d
                  ·
                    have : d = 273768 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 273767 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273766 ≤ d
                  ·
                    have : d = 273766 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273765 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273763 ≤ d
                ·
                  by_cases h : 273764 ≤ d
                  ·
                    have : d = 273764 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273763 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273762 ≤ d
                  ·
                    have : d = 273762 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 67) (by norm_num)
      exact by decide
                  ·
                    have : d = 273761 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 273745 ≤ d
          ·
            by_cases h : 273753 ≤ d
            ·
              by_cases h : 273757 ≤ d
              ·
                by_cases h : 273759 ≤ d
                ·
                  by_cases h : 273760 ≤ d
                  ·
                    have : d = 273760 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 29) (by norm_num)
      exact by decide
                  ·
                    have : d = 273759 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273758 ≤ d
                  ·
                    have : d = 273758 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273757 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273755 ≤ d
                ·
                  by_cases h : 273756 ≤ d
                  ·
                    have : d = 273756 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273755 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273754 ≤ d
                  ·
                    have : d = 273754 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 273753 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273749 ≤ d
              ·
                by_cases h : 273751 ≤ d
                ·
                  by_cases h : 273752 ≤ d
                  ·
                    have : d = 273752 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273751 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273750 ≤ d
                  ·
                    have : d = 273750 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273749 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273747 ≤ d
                ·
                  by_cases h : 273748 ≤ d
                  ·
                    have : d = 273748 := by omega
                    subst d
      exact fullRecordGapTerm02212_not_prime
                  ·
                    have : d = 273747 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273746 ≤ d
                  ·
                    have : d = 273746 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273745 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 273737 ≤ d
            ·
              by_cases h : 273741 ≤ d
              ·
                by_cases h : 273743 ≤ d
                ·
                  by_cases h : 273744 ≤ d
                  ·
                    have : d = 273744 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1901) (by norm_num)
      exact by decide
                  ·
                    have : d = 273743 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273742 ≤ d
                  ·
                    have : d = 273742 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19553) (by norm_num)
      exact by decide
                  ·
                    have : d = 273741 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273739 ≤ d
                ·
                  by_cases h : 273740 ≤ d
                  ·
                    have : d = 273740 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273739 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273738 ≤ d
                  ·
                    have : d = 273738 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 43) (by norm_num)
      exact by decide
                  ·
                    have : d = 273737 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273733 ≤ d
              ·
                by_cases h : 273735 ≤ d
                ·
                  by_cases h : 273736 ≤ d
                  ·
                    have : d = 273736 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273735 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273734 ≤ d
                  ·
                    have : d = 273734 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273733 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273731 ≤ d
                ·
                  by_cases h : 273732 ≤ d
                  ·
                    have : d = 273732 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 22811) (by norm_num)
      exact by decide
                  ·
                    have : d = 273731 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273730 ≤ d
                  ·
                    have : d = 273730 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 31) (by norm_num)
      exact by decide
                  ·
                    have : d = 273729 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 273697 ≤ d
        ·
          by_cases h : 273713 ≤ d
          ·
            by_cases h : 273721 ≤ d
            ·
              by_cases h : 273725 ≤ d
              ·
                by_cases h : 273727 ≤ d
                ·
                  by_cases h : 273728 ≤ d
                  ·
                    have : d = 273728 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273727 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273726 ≤ d
                  ·
                    have : d = 273726 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273725 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273723 ≤ d
                ·
                  by_cases h : 273724 ≤ d
                  ·
                    have : d = 273724 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 6221) (by norm_num)
      exact by decide
                  ·
                    have : d = 273723 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273722 ≤ d
                  ·
                    have : d = 273722 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273721 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273717 ≤ d
              ·
                by_cases h : 273719 ≤ d
                ·
                  by_cases h : 273720 ≤ d
                  ·
                    have : d = 273720 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2281) (by norm_num)
      exact by decide
                  ·
                    have : d = 273719 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273718 ≤ d
                  ·
                    have : d = 273718 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5429923) (by norm_num)
      right
      exact ⟨273718, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273717 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273715 ≤ d
                ·
                  by_cases h : 273716 ≤ d
                  ·
                    have : d = 273716 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273715 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273714 ≤ d
                  ·
                    have : d = 273714 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 273713 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 273705 ≤ d
            ·
              by_cases h : 273709 ≤ d
              ·
                by_cases h : 273711 ≤ d
                ·
                  by_cases h : 273712 ≤ d
                  ·
                    have : d = 273712 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17107) (by norm_num)
      exact by decide
                  ·
                    have : d = 273711 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273710 ≤ d
                  ·
                    have : d = 273710 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273709 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273707 ≤ d
                ·
                  by_cases h : 273708 ≤ d
                  ·
                    have : d = 273708 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273707 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273706 ≤ d
                  ·
                    have : d = 273706 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273705 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273701 ≤ d
              ·
                by_cases h : 273703 ≤ d
                ·
                  by_cases h : 273704 ≤ d
                  ·
                    have : d = 273704 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273703 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273702 ≤ d
                  ·
                    have : d = 273702 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 273701 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273699 ≤ d
                ·
                  by_cases h : 273700 ≤ d
                  ·
                    have : d = 273700 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 273699 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273698 ≤ d
                  ·
                    have : d = 273698 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273697 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 273681 ≤ d
          ·
            by_cases h : 273689 ≤ d
            ·
              by_cases h : 273693 ≤ d
              ·
                by_cases h : 273695 ≤ d
                ·
                  by_cases h : 273696 ≤ d
                  ·
                    have : d = 273696 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273695 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273694 ≤ d
                  ·
                    have : d = 273694 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273693 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273691 ≤ d
                ·
                  by_cases h : 273692 ≤ d
                  ·
                    have : d = 273692 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273691 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273690 ≤ d
                  ·
                    have : d = 273690 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3041) (by norm_num)
      exact by decide
                  ·
                    have : d = 273689 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273685 ≤ d
              ·
                by_cases h : 273687 ≤ d
                ·
                  by_cases h : 273688 ≤ d
                  ·
                    have : d = 273688 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 34211) (by norm_num)
      exact by decide
                  ·
                    have : d = 273687 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273686 ≤ d
                  ·
                    have : d = 273686 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273685 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273683 ≤ d
                ·
                  by_cases h : 273684 ≤ d
                  ·
                    have : d = 273684 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273683 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273682 ≤ d
                  ·
                    have : d = 273682 := by omega
                    subst d
      exact fullRecordGapTerm02213_not_prime
                  ·
                    have : d = 273681 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 273673 ≤ d
            ·
              by_cases h : 273677 ≤ d
              ·
                by_cases h : 273679 ≤ d
                ·
                  by_cases h : 273680 ≤ d
                  ·
                    have : d = 273680 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273679 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273678 ≤ d
                  ·
                    have : d = 273678 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 6412453) (by norm_num)
      right
      exact ⟨273678, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273677 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273675 ≤ d
                ·
                  by_cases h : 273676 ≤ d
                  ·
                    have : d = 273676 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273675 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273674 ≤ d
                  ·
                    have : d = 273674 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273673 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273669 ≤ d
              ·
                by_cases h : 273671 ≤ d
                ·
                  by_cases h : 273672 ≤ d
                  ·
                    have : d = 273672 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 181) (by norm_num)
      exact by decide
                  ·
                    have : d = 273671 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273670 ≤ d
                  ·
                    have : d = 273670 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 27367) (by norm_num)
      exact by decide
                  ·
                    have : d = 273669 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273667 ≤ d
                ·
                  by_cases h : 273668 ≤ d
                  ·
                    have : d = 273668 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273667 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273666 ≤ d
                  ·
                    have : d = 273666 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273665 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
  ·
    by_cases h : 273537 ≤ d
    ·
      by_cases h : 273601 ≤ d
      ·
        by_cases h : 273633 ≤ d
        ·
          by_cases h : 273649 ≤ d
          ·
            by_cases h : 273657 ≤ d
            ·
              by_cases h : 273661 ≤ d
              ·
                by_cases h : 273663 ≤ d
                ·
                  by_cases h : 273664 ≤ d
                  ·
                    have : d = 273664 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1069) (by norm_num)
      exact by decide
                  ·
                    have : d = 273663 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273662 ≤ d
                  ·
                    have : d = 273662 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273661 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273659 ≤ d
                ·
                  by_cases h : 273660 ≤ d
                  ·
                    have : d = 273660 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 4561) (by norm_num)
      exact by decide
                  ·
                    have : d = 273659 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273658 ≤ d
                  ·
                    have : d = 273658 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1777) (by norm_num)
      exact by decide
                  ·
                    have : d = 273657 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273653 ≤ d
              ·
                by_cases h : 273655 ≤ d
                ·
                  by_cases h : 273656 ≤ d
                  ·
                    have : d = 273656 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273655 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273654 ≤ d
                  ·
                    have : d = 273654 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23) (by norm_num)
      exact by decide
                  ·
                    have : d = 273653 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273651 ≤ d
                ·
                  by_cases h : 273652 ≤ d
                  ·
                    have : d = 273652 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273651 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273650 ≤ d
                  ·
                    have : d = 273650 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273649 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 273641 ≤ d
            ·
              by_cases h : 273645 ≤ d
              ·
                by_cases h : 273647 ≤ d
                ·
                  by_cases h : 273648 ≤ d
                  ·
                    have : d = 273648 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5701) (by norm_num)
      exact by decide
                  ·
                    have : d = 273647 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273646 ≤ d
                  ·
                    have : d = 273646 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273645 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273643 ≤ d
                ·
                  by_cases h : 273644 ≤ d
                  ·
                    have : d = 273644 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273643 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273642 ≤ d
                  ·
                    have : d = 273642 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 59) (by norm_num)
      exact by decide
                  ·
                    have : d = 273641 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273637 ≤ d
              ·
                by_cases h : 273639 ≤ d
                ·
                  by_cases h : 273640 ≤ d
                  ·
                    have : d = 273640 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273639 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273638 ≤ d
                  ·
                    have : d = 273638 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273637 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273635 ≤ d
                ·
                  by_cases h : 273636 ≤ d
                  ·
                    have : d = 273636 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273635 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273634 ≤ d
                  ·
                    have : d = 273634 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 41) (by norm_num)
      exact by decide
                  ·
                    have : d = 273633 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 273617 ≤ d
          ·
            by_cases h : 273625 ≤ d
            ·
              by_cases h : 273629 ≤ d
              ·
                by_cases h : 273631 ≤ d
                ·
                  by_cases h : 273632 ≤ d
                  ·
                    have : d = 273632 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273631 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273630 ≤ d
                  ·
                    have : d = 273630 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1303) (by norm_num)
      exact by decide
                  ·
                    have : d = 273629 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273627 ≤ d
                ·
                  by_cases h : 273628 ≤ d
                  ·
                    have : d = 273628 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 67) (by norm_num)
      exact by decide
                  ·
                    have : d = 273627 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273626 ≤ d
                  ·
                    have : d = 273626 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273625 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273621 ≤ d
              ·
                by_cases h : 273623 ≤ d
                ·
                  by_cases h : 273624 ≤ d
                  ·
                    have : d = 273624 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273623 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273622 ≤ d
                  ·
                    have : d = 273622 := by omega
                    subst d
      exact fullRecordGapTerm02214_not_prime
                  ·
                    have : d = 273621 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273619 ≤ d
                ·
                  by_cases h : 273620 ≤ d
                  ·
                    have : d = 273620 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273619 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273618 ≤ d
                  ·
                    have : d = 273618 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273617 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 273609 ≤ d
            ·
              by_cases h : 273613 ≤ d
              ·
                by_cases h : 273615 ≤ d
                ·
                  by_cases h : 273616 ≤ d
                  ·
                    have : d = 273616 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273615 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273614 ≤ d
                  ·
                    have : d = 273614 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273613 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273611 ≤ d
                ·
                  by_cases h : 273612 ≤ d
                  ·
                    have : d = 273612 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 151) (by norm_num)
      exact by decide
                  ·
                    have : d = 273611 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273610 ≤ d
                  ·
                    have : d = 273610 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273609 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273605 ≤ d
              ·
                by_cases h : 273607 ≤ d
                ·
                  by_cases h : 273608 ≤ d
                  ·
                    have : d = 273608 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273607 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273606 ≤ d
                  ·
                    have : d = 273606 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273605 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273603 ≤ d
                ·
                  by_cases h : 273604 ≤ d
                  ·
                    have : d = 273604 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 73) (by norm_num)
      exact by decide
                  ·
                    have : d = 273603 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273602 ≤ d
                  ·
                    have : d = 273602 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273601 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 273569 ≤ d
        ·
          by_cases h : 273585 ≤ d
          ·
            by_cases h : 273593 ≤ d
            ·
              by_cases h : 273597 ≤ d
              ·
                by_cases h : 273599 ≤ d
                ·
                  by_cases h : 273600 ≤ d
                  ·
                    have : d = 273600 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 273599 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273598 ≤ d
                  ·
                    have : d = 273598 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 273597 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273595 ≤ d
                ·
                  by_cases h : 273596 ≤ d
                  ·
                    have : d = 273596 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273595 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273594 ≤ d
                  ·
                    have : d = 273594 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3941083) (by norm_num)
      right
      exact ⟨273594, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273593 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273589 ≤ d
              ·
                by_cases h : 273591 ≤ d
                ·
                  by_cases h : 273592 ≤ d
                  ·
                    have : d = 273592 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3109) (by norm_num)
      exact by decide
                  ·
                    have : d = 273591 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273590 ≤ d
                  ·
                    have : d = 273590 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273589 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273587 ≤ d
                ·
                  by_cases h : 273588 ≤ d
                  ·
                    have : d = 273588 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3257) (by norm_num)
      exact by decide
                  ·
                    have : d = 273587 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273586 ≤ d
                  ·
                    have : d = 273586 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273585 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 273577 ≤ d
            ·
              by_cases h : 273581 ≤ d
              ·
                by_cases h : 273583 ≤ d
                ·
                  by_cases h : 273584 ≤ d
                  ·
                    have : d = 273584 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273583 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273582 ≤ d
                  ·
                    have : d = 273582 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273581 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273579 ≤ d
                ·
                  by_cases h : 273580 ≤ d
                  ·
                    have : d = 273580 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13679) (by norm_num)
      exact by decide
                  ·
                    have : d = 273579 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273578 ≤ d
                  ·
                    have : d = 273578 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273577 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273573 ≤ d
              ·
                by_cases h : 273575 ≤ d
                ·
                  by_cases h : 273576 ≤ d
                  ·
                    have : d = 273576 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273575 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273574 ≤ d
                  ·
                    have : d = 273574 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273573 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273571 ≤ d
                ·
                  by_cases h : 273572 ≤ d
                  ·
                    have : d = 273572 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273571 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273570 ≤ d
                  ·
                    have : d = 273570 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 829) (by norm_num)
      exact by decide
                  ·
                    have : d = 273569 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 273553 ≤ d
          ·
            by_cases h : 273561 ≤ d
            ·
              by_cases h : 273565 ≤ d
              ·
                by_cases h : 273567 ≤ d
                ·
                  by_cases h : 273568 ≤ d
                  ·
                    have : d = 273568 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273567 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273566 ≤ d
                  ·
                    have : d = 273566 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273565 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273563 ≤ d
                ·
                  by_cases h : 273564 ≤ d
                  ·
                    have : d = 273564 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 273563 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273562 ≤ d
                  ·
                    have : d = 273562 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 273561 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273557 ≤ d
              ·
                by_cases h : 273559 ≤ d
                ·
                  by_cases h : 273560 ≤ d
                  ·
                    have : d = 273560 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273559 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273558 ≤ d
                  ·
                    have : d = 273558 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 127) (by norm_num)
      exact by decide
                  ·
                    have : d = 273557 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273555 ≤ d
                ·
                  by_cases h : 273556 ≤ d
                  ·
                    have : d = 273556 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273555 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273554 ≤ d
                  ·
                    have : d = 273554 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273553 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 273545 ≤ d
            ·
              by_cases h : 273549 ≤ d
              ·
                by_cases h : 273551 ≤ d
                ·
                  by_cases h : 273552 ≤ d
                  ·
                    have : d = 273552 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273551 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273550 ≤ d
                  ·
                    have : d = 273550 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5471) (by norm_num)
      exact by decide
                  ·
                    have : d = 273549 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273547 ≤ d
                ·
                  by_cases h : 273548 ≤ d
                  ·
                    have : d = 273548 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273547 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273546 ≤ d
                  ·
                    have : d = 273546 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273545 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273541 ≤ d
              ·
                by_cases h : 273543 ≤ d
                ·
                  by_cases h : 273544 ≤ d
                  ·
                    have : d = 273544 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 31) (by norm_num)
      exact by decide
                  ·
                    have : d = 273543 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273542 ≤ d
                  ·
                    have : d = 273542 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273541 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273539 ≤ d
                ·
                  by_cases h : 273540 ≤ d
                  ·
                    have : d = 273540 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273539 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273538 ≤ d
                  ·
                    have : d = 273538 := by omega
                    subst d
      exact fullRecordGapTerm02215_not_prime
                  ·
                    have : d = 273537 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 273473 ≤ d
      ·
        by_cases h : 273505 ≤ d
        ·
          by_cases h : 273521 ≤ d
          ·
            by_cases h : 273529 ≤ d
            ·
              by_cases h : 273533 ≤ d
              ·
                by_cases h : 273535 ≤ d
                ·
                  by_cases h : 273536 ≤ d
                  ·
                    have : d = 273536 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273535 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273534 ≤ d
                  ·
                    have : d = 273534 := by omega
                    subst d
      exact fullRecordGapTerm02216_not_prime
                  ·
                    have : d = 273533 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273531 ≤ d
                ·
                  by_cases h : 273532 ≤ d
                  ·
                    have : d = 273532 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 9769) (by norm_num)
      exact by decide
                  ·
                    have : d = 273531 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273530 ≤ d
                  ·
                    have : d = 273530 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273529 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273525 ≤ d
              ·
                by_cases h : 273527 ≤ d
                ·
                  by_cases h : 273528 ≤ d
                  ·
                    have : d = 273528 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 29) (by norm_num)
      exact by decide
                  ·
                    have : d = 273527 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273526 ≤ d
                  ·
                    have : d = 273526 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273525 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273523 ≤ d
                ·
                  by_cases h : 273524 ≤ d
                  ·
                    have : d = 273524 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273523 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273522 ≤ d
                  ·
                    have : d = 273522 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7604939) (by norm_num)
      right
      exact ⟨273522, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273521 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 273513 ≤ d
            ·
              by_cases h : 273517 ≤ d
              ·
                by_cases h : 273519 ≤ d
                ·
                  by_cases h : 273520 ≤ d
                  ·
                    have : d = 273520 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 273519 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273518 ≤ d
                  ·
                    have : d = 273518 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273517 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273515 ≤ d
                ·
                  by_cases h : 273516 ≤ d
                  ·
                    have : d = 273516 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273515 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273514 ≤ d
                  ·
                    have : d = 273514 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 163) (by norm_num)
      exact by decide
                  ·
                    have : d = 273513 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273509 ≤ d
              ·
                by_cases h : 273511 ≤ d
                ·
                  by_cases h : 273512 ≤ d
                  ·
                    have : d = 273512 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273511 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273510 ≤ d
                  ·
                    have : d = 273510 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1013) (by norm_num)
      exact by decide
                  ·
                    have : d = 273509 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273507 ≤ d
                ·
                  by_cases h : 273508 ≤ d
                  ·
                    have : d = 273508 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273507 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273506 ≤ d
                  ·
                    have : d = 273506 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273505 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 273489 ≤ d
          ·
            by_cases h : 273497 ≤ d
            ·
              by_cases h : 273501 ≤ d
              ·
                by_cases h : 273503 ≤ d
                ·
                  by_cases h : 273504 ≤ d
                  ·
                    have : d = 273504 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 37) (by norm_num)
      exact by decide
                  ·
                    have : d = 273503 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273502 ≤ d
                  ·
                    have : d = 273502 := by omega
                    subst d
      exact fullRecordGapTerm02217_not_prime
                  ·
                    have : d = 273501 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273499 ≤ d
                ·
                  by_cases h : 273500 ≤ d
                  ·
                    have : d = 273500 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273499 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273498 ≤ d
                  ·
                    have : d = 273498 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273497 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273493 ≤ d
              ·
                by_cases h : 273495 ≤ d
                ·
                  by_cases h : 273496 ≤ d
                  ·
                    have : d = 273496 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273495 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273494 ≤ d
                  ·
                    have : d = 273494 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273493 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273491 ≤ d
                ·
                  by_cases h : 273492 ≤ d
                  ·
                    have : d = 273492 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 71) (by norm_num)
      exact by decide
                  ·
                    have : d = 273491 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273490 ≤ d
                  ·
                    have : d = 273490 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3907) (by norm_num)
      exact by decide
                  ·
                    have : d = 273489 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 273481 ≤ d
            ·
              by_cases h : 273485 ≤ d
              ·
                by_cases h : 273487 ≤ d
                ·
                  by_cases h : 273488 ≤ d
                  ·
                    have : d = 273488 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273487 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273486 ≤ d
                  ·
                    have : d = 273486 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273485 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273483 ≤ d
                ·
                  by_cases h : 273484 ≤ d
                  ·
                    have : d = 273484 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273483 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273482 ≤ d
                  ·
                    have : d = 273482 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273481 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273477 ≤ d
              ·
                by_cases h : 273479 ≤ d
                ·
                  by_cases h : 273480 ≤ d
                  ·
                    have : d = 273480 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 43) (by norm_num)
      exact by decide
                  ·
                    have : d = 273479 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273478 ≤ d
                  ·
                    have : d = 273478 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 52951) (by norm_num)
      right
      exact ⟨8723, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273477 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273475 ≤ d
                ·
                  by_cases h : 273476 ≤ d
                  ·
                    have : d = 273476 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273475 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273474 ≤ d
                  ·
                    have : d = 273474 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 15193) (by norm_num)
      exact by decide
                  ·
                    have : d = 273473 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 273441 ≤ d
        ·
          by_cases h : 273457 ≤ d
          ·
            by_cases h : 273465 ≤ d
            ·
              by_cases h : 273469 ≤ d
              ·
                by_cases h : 273471 ≤ d
                ·
                  by_cases h : 273472 ≤ d
                  ·
                    have : d = 273472 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 4273) (by norm_num)
      exact by decide
                  ·
                    have : d = 273471 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273470 ≤ d
                  ·
                    have : d = 273470 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273469 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273467 ≤ d
                ·
                  by_cases h : 273468 ≤ d
                  ·
                    have : d = 273468 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 273467 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273466 ≤ d
                  ·
                    have : d = 273466 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273465 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273461 ≤ d
              ·
                by_cases h : 273463 ≤ d
                ·
                  by_cases h : 273464 ≤ d
                  ·
                    have : d = 273464 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273463 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273462 ≤ d
                  ·
                    have : d = 273462 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 273461 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273459 ≤ d
                ·
                  by_cases h : 273460 ≤ d
                  ·
                    have : d = 273460 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 113) (by norm_num)
      exact by decide
                  ·
                    have : d = 273459 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273458 ≤ d
                  ·
                    have : d = 273458 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273457 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 273449 ≤ d
            ·
              by_cases h : 273453 ≤ d
              ·
                by_cases h : 273455 ≤ d
                ·
                  by_cases h : 273456 ≤ d
                  ·
                    have : d = 273456 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273455 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273454 ≤ d
                  ·
                    have : d = 273454 := by omega
                    subst d
      exact fullRecordGapTerm02218_not_prime
                  ·
                    have : d = 273453 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273451 ≤ d
                ·
                  by_cases h : 273452 ≤ d
                  ·
                    have : d = 273452 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273451 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273450 ≤ d
                  ·
                    have : d = 273450 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1823) (by norm_num)
      exact by decide
                  ·
                    have : d = 273449 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273445 ≤ d
              ·
                by_cases h : 273447 ≤ d
                ·
                  by_cases h : 273448 ≤ d
                  ·
                    have : d = 273448 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 273447 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273446 ≤ d
                  ·
                    have : d = 273446 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273445 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273443 ≤ d
                ·
                  by_cases h : 273444 ≤ d
                  ·
                    have : d = 273444 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 22787) (by norm_num)
      exact by decide
                  ·
                    have : d = 273443 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273442 ≤ d
                  ·
                    have : d = 273442 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273441 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 273425 ≤ d
          ·
            by_cases h : 273433 ≤ d
            ·
              by_cases h : 273437 ≤ d
              ·
                by_cases h : 273439 ≤ d
                ·
                  by_cases h : 273440 ≤ d
                  ·
                    have : d = 273440 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273439 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273438 ≤ d
                  ·
                    have : d = 273438 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1381) (by norm_num)
      exact by decide
                  ·
                    have : d = 273437 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273435 ≤ d
                ·
                  by_cases h : 273436 ≤ d
                  ·
                    have : d = 273436 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273435 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273434 ≤ d
                  ·
                    have : d = 273434 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273433 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273429 ≤ d
              ·
                by_cases h : 273431 ≤ d
                ·
                  by_cases h : 273432 ≤ d
                  ·
                    have : d = 273432 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11393) (by norm_num)
      exact by decide
                  ·
                    have : d = 273431 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273430 ≤ d
                  ·
                    have : d = 273430 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 37) (by norm_num)
      exact by decide
                  ·
                    have : d = 273429 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273427 ≤ d
                ·
                  by_cases h : 273428 ≤ d
                  ·
                    have : d = 273428 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273427 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273426 ≤ d
                  ·
                    have : d = 273426 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273425 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 273417 ≤ d
            ·
              by_cases h : 273421 ≤ d
              ·
                by_cases h : 273423 ≤ d
                ·
                  by_cases h : 273424 ≤ d
                  ·
                    have : d = 273424 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23) (by norm_num)
      exact by decide
                  ·
                    have : d = 273423 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273422 ≤ d
                  ·
                    have : d = 273422 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273421 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273419 ≤ d
                ·
                  by_cases h : 273420 ≤ d
                  ·
                    have : d = 273420 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273419 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273418 ≤ d
                  ·
                    have : d = 273418 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 46918679) (by norm_num)
      right
      exact ⟨273418, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273417 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 273413 ≤ d
              ·
                by_cases h : 273415 ≤ d
                ·
                  by_cases h : 273416 ≤ d
                  ·
                    have : d = 273416 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273415 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273414 ≤ d
                  ·
                    have : d = 273414 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273413 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 273411 ≤ d
                ·
                  by_cases h : 273412 ≤ d
                  ·
                    have : d = 273412 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 29) (by norm_num)
      exact by decide
                  ·
                    have : d = 273411 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 273410 ≤ d
                  ·
                    have : d = 273410 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 273409 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩

end PrimeFactorUnimodality
