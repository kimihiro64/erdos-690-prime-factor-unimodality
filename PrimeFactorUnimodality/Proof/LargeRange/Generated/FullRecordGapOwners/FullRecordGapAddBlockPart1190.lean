import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapFermat

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

theorem fullRecordGapAddBlock_part1190 (d : Nat) (152577 ≤ d) (d ≤ 153088) : ¬(recordGapCenter + d).Prime := by
  by_cases h : 152833 ≤ d
  ·
    by_cases h : 152961 ≤ d
    ·
      by_cases h : 153025 ≤ d
      ·
        by_cases h : 153057 ≤ d
        ·
          by_cases h : 153073 ≤ d
          ·
            by_cases h : 153081 ≤ d
            ·
              by_cases h : 153085 ≤ d
              ·
                by_cases h : 153087 ≤ d
                ·
                  by_cases h : 153088 ≤ d
                  ·
                    have : d = 153088 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 153087 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 153086 ≤ d
                  ·
                    have : d = 153086 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 201152051)
      right
      exact ⟨200998965, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 153085 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 153083 ≤ d
                ·
                  by_cases h : 153084 ≤ d
                  ·
                    have : d = 153084 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 153083 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 153082 ≤ d
                  ·
                    have : d = 153082 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 153081 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 153077 ≤ d
              ·
                by_cases h : 153079 ≤ d
                ·
                  by_cases h : 153080 ≤ d
                  ·
                    have : d = 153080 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 43)
      exact by decide
                  ·
                    have : d = 153079 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 153078 ≤ d
                  ·
                    have : d = 153078 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 153077 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 153075 ≤ d
                ·
                  by_cases h : 153076 ≤ d
                  ·
                    have : d = 153076 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 153075 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 153074 ≤ d
                  ·
                    have : d = 153074 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 153073 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 153065 ≤ d
            ·
              by_cases h : 153069 ≤ d
              ·
                by_cases h : 153071 ≤ d
                ·
                  by_cases h : 153072 ≤ d
                  ·
                    have : d = 153072 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 153071 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 153070 ≤ d
                  ·
                    have : d = 153070 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 153069 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 153067 ≤ d
                ·
                  by_cases h : 153068 ≤ d
                  ·
                    have : d = 153068 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 153067 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 153066 ≤ d
                  ·
                    have : d = 153066 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 97)
      exact by decide
                  ·
                    have : d = 153065 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 153061 ≤ d
              ·
                by_cases h : 153063 ≤ d
                ·
                  by_cases h : 153064 ≤ d
                  ·
                    have : d = 153064 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 153063 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 153062 ≤ d
                  ·
                    have : d = 153062 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 153061 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 153059 ≤ d
                ·
                  by_cases h : 153060 ≤ d
                  ·
                    have : d = 153060 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2551)
      exact by decide
                  ·
                    have : d = 153059 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 153058 ≤ d
                  ·
                    have : d = 153058 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 153057 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 153041 ≤ d
          ·
            by_cases h : 153049 ≤ d
            ·
              by_cases h : 153053 ≤ d
              ·
                by_cases h : 153055 ≤ d
                ·
                  by_cases h : 153056 ≤ d
                  ·
                    have : d = 153056 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 4783)
      exact by decide
                  ·
                    have : d = 153055 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 153054 ≤ d
                  ·
                    have : d = 153054 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 153053 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 153051 ≤ d
                ·
                  by_cases h : 153052 ≤ d
                  ·
                    have : d = 153052 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 153051 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 153050 ≤ d
                  ·
                    have : d = 153050 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 153049 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 153045 ≤ d
              ·
                by_cases h : 153047 ≤ d
                ·
                  by_cases h : 153048 ≤ d
                  ·
                    have : d = 153048 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 911)
      exact by decide
                  ·
                    have : d = 153047 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 153046 ≤ d
                  ·
                    have : d = 153046 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 153045 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 153043 ≤ d
                ·
                  by_cases h : 153044 ≤ d
                  ·
                    have : d = 153044 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 153043 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 153042 ≤ d
                  ·
                    have : d = 153042 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 153041 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 153033 ≤ d
            ·
              by_cases h : 153037 ≤ d
              ·
                by_cases h : 153039 ≤ d
                ·
                  by_cases h : 153040 ≤ d
                  ·
                    have : d = 153040 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 153039 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 153038 ≤ d
                  ·
                    have : d = 153038 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 6185429)
      right
      exact ⟨6032391, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 153037 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 153035 ≤ d
                ·
                  by_cases h : 153036 ≤ d
                  ·
                    have : d = 153036 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 153035 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 153034 ≤ d
                  ·
                    have : d = 153034 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 153033 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 153029 ≤ d
              ·
                by_cases h : 153031 ≤ d
                ·
                  by_cases h : 153032 ≤ d
                  ·
                    have : d = 153032 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 153031 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 153030 ≤ d
                  ·
                    have : d = 153030 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5101)
      exact by decide
                  ·
                    have : d = 153029 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 153027 ≤ d
                ·
                  by_cases h : 153028 ≤ d
                  ·
                    have : d = 153028 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 153027 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 153026 ≤ d
                  ·
                    have : d = 153026 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 153025 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 152993 ≤ d
        ·
          by_cases h : 153009 ≤ d
          ·
            by_cases h : 153017 ≤ d
            ·
              by_cases h : 153021 ≤ d
              ·
                by_cases h : 153023 ≤ d
                ·
                  by_cases h : 153024 ≤ d
                  ·
                    have : d = 153024 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 153023 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 153022 ≤ d
                  ·
                    have : d = 153022 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 153021 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 153019 ≤ d
                ·
                  by_cases h : 153020 ≤ d
                  ·
                    have : d = 153020 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1093)
      exact by decide
                  ·
                    have : d = 153019 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 153018 ≤ d
                  ·
                    have : d = 153018 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 8501)
      exact by decide
                  ·
                    have : d = 153017 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 153013 ≤ d
              ·
                by_cases h : 153015 ≤ d
                ·
                  by_cases h : 153016 ≤ d
                  ·
                    have : d = 153016 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 153015 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 153014 ≤ d
                  ·
                    have : d = 153014 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 153013 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 153011 ≤ d
                ·
                  by_cases h : 153012 ≤ d
                  ·
                    have : d = 153012 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 153011 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 153010 ≤ d
                  ·
                    have : d = 153010 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 153009 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 153001 ≤ d
            ·
              by_cases h : 153005 ≤ d
              ·
                by_cases h : 153007 ≤ d
                ·
                  by_cases h : 153008 ≤ d
                  ·
                    have : d = 153008 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 73)
      exact by decide
                  ·
                    have : d = 153007 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 153006 ≤ d
                  ·
                    have : d = 153006 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 153005 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 153003 ≤ d
                ·
                  by_cases h : 153004 ≤ d
                  ·
                    have : d = 153004 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 153003 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 153002 ≤ d
                  ·
                    have : d = 153002 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 113)
      exact by decide
                  ·
                    have : d = 153001 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 152997 ≤ d
              ·
                by_cases h : 152999 ≤ d
                ·
                  by_cases h : 153000 ≤ d
                  ·
                    have : d = 153000 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 152999 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152998 ≤ d
                  ·
                    have : d = 152998 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152997 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152995 ≤ d
                ·
                  by_cases h : 152996 ≤ d
                  ·
                    have : d = 152996 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 152995 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152994 ≤ d
                  ·
                    have : d = 152994 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152993 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 152977 ≤ d
          ·
            by_cases h : 152985 ≤ d
            ·
              by_cases h : 152989 ≤ d
              ·
                by_cases h : 152991 ≤ d
                ·
                  by_cases h : 152992 ≤ d
                  ·
                    have : d = 152992 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152991 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152990 ≤ d
                  ·
                    have : d = 152990 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 15299)
      exact by decide
                  ·
                    have : d = 152989 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152987 ≤ d
                ·
                  by_cases h : 152988 ≤ d
                  ·
                    have : d = 152988 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 152987 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152986 ≤ d
                  ·
                    have : d = 152986 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152985 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 152981 ≤ d
              ·
                by_cases h : 152983 ≤ d
                ·
                  by_cases h : 152984 ≤ d
                  ·
                    have : d = 152984 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152983 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152982 ≤ d
                  ·
                    have : d = 152982 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2833)
      exact by decide
                  ·
                    have : d = 152981 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152979 ≤ d
                ·
                  by_cases h : 152980 ≤ d
                  ·
                    have : d = 152980 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152979 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152978 ≤ d
                  ·
                    have : d = 152978 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 223)
      exact by decide
                  ·
                    have : d = 152977 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 152969 ≤ d
            ·
              by_cases h : 152973 ≤ d
              ·
                by_cases h : 152975 ≤ d
                ·
                  by_cases h : 152976 ≤ d
                  ·
                    have : d = 152976 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3187)
      exact by decide
                  ·
                    have : d = 152975 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152974 ≤ d
                  ·
                    have : d = 152974 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152973 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152971 ≤ d
                ·
                  by_cases h : 152972 ≤ d
                  ·
                    have : d = 152972 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 167)
      exact by decide
                  ·
                    have : d = 152971 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152970 ≤ d
                  ·
                    have : d = 152970 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152969 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 152965 ≤ d
              ·
                by_cases h : 152967 ≤ d
                ·
                  by_cases h : 152968 ≤ d
                  ·
                    have : d = 152968 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152967 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152966 ≤ d
                  ·
                    have : d = 152966 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 152965 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152963 ≤ d
                ·
                  by_cases h : 152964 ≤ d
                  ·
                    have : d = 152964 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152963 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152962 ≤ d
                  ·
                    have : d = 152962 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152961 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 152897 ≤ d
      ·
        by_cases h : 152929 ≤ d
        ·
          by_cases h : 152945 ≤ d
          ·
            by_cases h : 152953 ≤ d
            ·
              by_cases h : 152957 ≤ d
              ·
                by_cases h : 152959 ≤ d
                ·
                  by_cases h : 152960 ≤ d
                  ·
                    have : d = 152960 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 239)
      exact by decide
                  ·
                    have : d = 152959 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152958 ≤ d
                  ·
                    have : d = 152958 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 152957 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152955 ≤ d
                ·
                  by_cases h : 152956 ≤ d
                  ·
                    have : d = 152956 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152955 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152954 ≤ d
                  ·
                    have : d = 152954 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152953 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 152949 ≤ d
              ·
                by_cases h : 152951 ≤ d
                ·
                  by_cases h : 152952 ≤ d
                  ·
                    have : d = 152952 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 6373)
      exact by decide
                  ·
                    have : d = 152951 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152950 ≤ d
                  ·
                    have : d = 152950 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152949 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152947 ≤ d
                ·
                  by_cases h : 152948 ≤ d
                  ·
                    have : d = 152948 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 38237)
      exact by decide
                  ·
                    have : d = 152947 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152946 ≤ d
                  ·
                    have : d = 152946 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 152945 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 152937 ≤ d
            ·
              by_cases h : 152941 ≤ d
              ·
                by_cases h : 152943 ≤ d
                ·
                  by_cases h : 152944 ≤ d
                  ·
                    have : d = 152944 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152943 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152942 ≤ d
                  ·
                    have : d = 152942 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152941 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152939 ≤ d
                ·
                  by_cases h : 152940 ≤ d
                  ·
                    have : d = 152940 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152939 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152938 ≤ d
                  ·
                    have : d = 152938 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152937 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 152933 ≤ d
              ·
                by_cases h : 152935 ≤ d
                ·
                  by_cases h : 152936 ≤ d
                  ·
                    have : d = 152936 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2731)
      exact by decide
                  ·
                    have : d = 152935 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152934 ≤ d
                  ·
                    have : d = 152934 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152933 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152931 ≤ d
                ·
                  by_cases h : 152932 ≤ d
                  ·
                    have : d = 152932 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152931 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152930 ≤ d
                  ·
                    have : d = 152930 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 41)
      exact by decide
                  ·
                    have : d = 152929 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 152913 ≤ d
          ·
            by_cases h : 152921 ≤ d
            ·
              by_cases h : 152925 ≤ d
              ·
                by_cases h : 152927 ≤ d
                ·
                  by_cases h : 152928 ≤ d
                  ·
                    have : d = 152928 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152927 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152926 ≤ d
                  ·
                    have : d = 152926 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152925 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152923 ≤ d
                ·
                  by_cases h : 152924 ≤ d
                  ·
                    have : d = 152924 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152923 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152922 ≤ d
                  ·
                    have : d = 152922 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 331)
      exact by decide
                  ·
                    have : d = 152921 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 152917 ≤ d
              ·
                by_cases h : 152919 ≤ d
                ·
                  by_cases h : 152920 ≤ d
                  ·
                    have : d = 152920 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152919 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152918 ≤ d
                  ·
                    have : d = 152918 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152917 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152915 ≤ d
                ·
                  by_cases h : 152916 ≤ d
                  ·
                    have : d = 152916 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 12743)
      exact by decide
                  ·
                    have : d = 152915 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152914 ≤ d
                  ·
                    have : d = 152914 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152913 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 152905 ≤ d
            ·
              by_cases h : 152909 ≤ d
              ·
                by_cases h : 152911 ≤ d
                ·
                  by_cases h : 152912 ≤ d
                  ·
                    have : d = 152912 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 152911 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152910 ≤ d
                  ·
                    have : d = 152910 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1699)
      exact by decide
                  ·
                    have : d = 152909 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152907 ≤ d
                ·
                  by_cases h : 152908 ≤ d
                  ·
                    have : d = 152908 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152907 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152906 ≤ d
                  ·
                    have : d = 152906 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 152905 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 152901 ≤ d
              ·
                by_cases h : 152903 ≤ d
                ·
                  by_cases h : 152904 ≤ d
                  ·
                    have : d = 152904 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152903 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152902 ≤ d
                  ·
                    have : d = 152902 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152901 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152899 ≤ d
                ·
                  by_cases h : 152900 ≤ d
                  ·
                    have : d = 152900 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152899 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152898 ≤ d
                  ·
                    have : d = 152898 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 152897 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 152865 ≤ d
        ·
          by_cases h : 152881 ≤ d
          ·
            by_cases h : 152889 ≤ d
            ·
              by_cases h : 152893 ≤ d
              ·
                by_cases h : 152895 ≤ d
                ·
                  by_cases h : 152896 ≤ d
                  ·
                    have : d = 152896 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152895 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152894 ≤ d
                  ·
                    have : d = 152894 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152893 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152891 ≤ d
                ·
                  by_cases h : 152892 ≤ d
                  ·
                    have : d = 152892 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 152891 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152890 ≤ d
                  ·
                    have : d = 152890 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152889 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 152885 ≤ d
              ·
                by_cases h : 152887 ≤ d
                ·
                  by_cases h : 152888 ≤ d
                  ·
                    have : d = 152888 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 152887 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152886 ≤ d
                  ·
                    have : d = 152886 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152885 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152883 ≤ d
                ·
                  by_cases h : 152884 ≤ d
                  ·
                    have : d = 152884 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152883 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152882 ≤ d
                  ·
                    have : d = 152882 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 4958419969)
      right
      exact ⟨4958267087, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152881 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 152873 ≤ d
            ·
              by_cases h : 152877 ≤ d
              ·
                by_cases h : 152879 ≤ d
                ·
                  by_cases h : 152880 ≤ d
                  ·
                    have : d = 152880 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 152879 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152878 ≤ d
                  ·
                    have : d = 152878 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152877 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152875 ≤ d
                ·
                  by_cases h : 152876 ≤ d
                  ·
                    have : d = 152876 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 38219)
      exact by decide
                  ·
                    have : d = 152875 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152874 ≤ d
                  ·
                    have : d = 152874 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152873 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 152869 ≤ d
              ·
                by_cases h : 152871 ≤ d
                ·
                  by_cases h : 152872 ≤ d
                  ·
                    have : d = 152872 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152871 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152870 ≤ d
                  ·
                    have : d = 152870 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 15287)
      exact by decide
                  ·
                    have : d = 152869 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152867 ≤ d
                ·
                  by_cases h : 152868 ≤ d
                  ·
                    have : d = 152868 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 12739)
      exact by decide
                  ·
                    have : d = 152867 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152866 ≤ d
                  ·
                    have : d = 152866 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152865 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 152849 ≤ d
          ·
            by_cases h : 152857 ≤ d
            ·
              by_cases h : 152861 ≤ d
              ·
                by_cases h : 152863 ≤ d
                ·
                  by_cases h : 152864 ≤ d
                  ·
                    have : d = 152864 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152863 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152862 ≤ d
                  ·
                    have : d = 152862 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 73)
      exact by decide
                  ·
                    have : d = 152861 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152859 ≤ d
                ·
                  by_cases h : 152860 ≤ d
                  ·
                    have : d = 152860 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152859 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152858 ≤ d
                  ·
                    have : d = 152858 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152857 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 152853 ≤ d
              ·
                by_cases h : 152855 ≤ d
                ·
                  by_cases h : 152856 ≤ d
                  ·
                    have : d = 152856 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 193)
      exact by decide
                  ·
                    have : d = 152855 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152854 ≤ d
                  ·
                    have : d = 152854 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152853 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152851 ≤ d
                ·
                  by_cases h : 152852 ≤ d
                  ·
                    have : d = 152852 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152851 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152850 ≤ d
                  ·
                    have : d = 152850 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1019)
      exact by decide
                  ·
                    have : d = 152849 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 152841 ≤ d
            ·
              by_cases h : 152845 ≤ d
              ·
                by_cases h : 152847 ≤ d
                ·
                  by_cases h : 152848 ≤ d
                  ·
                    have : d = 152848 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152847 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152846 ≤ d
                  ·
                    have : d = 152846 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 115903)
      right
      exact ⟨78960, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152845 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152843 ≤ d
                ·
                  by_cases h : 152844 ≤ d
                  ·
                    have : d = 152844 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152843 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152842 ≤ d
                  ·
                    have : d = 152842 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152841 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 152837 ≤ d
              ·
                by_cases h : 152839 ≤ d
                ·
                  by_cases h : 152840 ≤ d
                  ·
                    have : d = 152840 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3821)
      exact by decide
                  ·
                    have : d = 152839 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152838 ≤ d
                  ·
                    have : d = 152838 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1213)
      exact by decide
                  ·
                    have : d = 152837 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152835 ≤ d
                ·
                  by_cases h : 152836 ≤ d
                  ·
                    have : d = 152836 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152835 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152834 ≤ d
                  ·
                    have : d = 152834 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152833 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
  ·
    by_cases h : 152705 ≤ d
    ·
      by_cases h : 152769 ≤ d
      ·
        by_cases h : 152801 ≤ d
        ·
          by_cases h : 152817 ≤ d
          ·
            by_cases h : 152825 ≤ d
            ·
              by_cases h : 152829 ≤ d
              ·
                by_cases h : 152831 ≤ d
                ·
                  by_cases h : 152832 ≤ d
                  ·
                    have : d = 152832 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 199)
      exact by decide
                  ·
                    have : d = 152831 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152830 ≤ d
                  ·
                    have : d = 152830 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152829 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152827 ≤ d
                ·
                  by_cases h : 152828 ≤ d
                  ·
                    have : d = 152828 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 152827 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152826 ≤ d
                  ·
                    have : d = 152826 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 25471)
      exact by decide
                  ·
                    have : d = 152825 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 152821 ≤ d
              ·
                by_cases h : 152823 ≤ d
                ·
                  by_cases h : 152824 ≤ d
                  ·
                    have : d = 152824 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152823 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152822 ≤ d
                  ·
                    have : d = 152822 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 43)
      exact by decide
                  ·
                    have : d = 152821 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152819 ≤ d
                ·
                  by_cases h : 152820 ≤ d
                  ·
                    have : d = 152820 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 283)
      exact by decide
                  ·
                    have : d = 152819 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152818 ≤ d
                  ·
                    have : d = 152818 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152817 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 152809 ≤ d
            ·
              by_cases h : 152813 ≤ d
              ·
                by_cases h : 152815 ≤ d
                ·
                  by_cases h : 152816 ≤ d
                  ·
                    have : d = 152816 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152815 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152814 ≤ d
                  ·
                    have : d = 152814 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152813 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152811 ≤ d
                ·
                  by_cases h : 152812 ≤ d
                  ·
                    have : d = 152812 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152811 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152810 ≤ d
                  ·
                    have : d = 152810 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 152809 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 152805 ≤ d
              ·
                by_cases h : 152807 ≤ d
                ·
                  by_cases h : 152808 ≤ d
                  ·
                    have : d = 152808 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152807 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152806 ≤ d
                  ·
                    have : d = 152806 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152805 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152803 ≤ d
                ·
                  by_cases h : 152804 ≤ d
                  ·
                    have : d = 152804 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152803 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152802 ≤ d
                  ·
                    have : d = 152802 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152801 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 152785 ≤ d
          ·
            by_cases h : 152793 ≤ d
            ·
              by_cases h : 152797 ≤ d
              ·
                by_cases h : 152799 ≤ d
                ·
                  by_cases h : 152800 ≤ d
                  ·
                    have : d = 152800 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152799 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152798 ≤ d
                  ·
                    have : d = 152798 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 152797 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152795 ≤ d
                ·
                  by_cases h : 152796 ≤ d
                  ·
                    have : d = 152796 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 152795 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152794 ≤ d
                  ·
                    have : d = 152794 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152793 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 152789 ≤ d
              ·
                by_cases h : 152791 ≤ d
                ·
                  by_cases h : 152792 ≤ d
                  ·
                    have : d = 152792 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 71)
      exact by decide
                  ·
                    have : d = 152791 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152790 ≤ d
                  ·
                    have : d = 152790 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 463)
      exact by decide
                  ·
                    have : d = 152789 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152787 ≤ d
                ·
                  by_cases h : 152788 ≤ d
                  ·
                    have : d = 152788 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152787 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152786 ≤ d
                  ·
                    have : d = 152786 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152785 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 152777 ≤ d
            ·
              by_cases h : 152781 ≤ d
              ·
                by_cases h : 152783 ≤ d
                ·
                  by_cases h : 152784 ≤ d
                  ·
                    have : d = 152784 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152783 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152782 ≤ d
                  ·
                    have : d = 152782 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152781 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152779 ≤ d
                ·
                  by_cases h : 152780 ≤ d
                  ·
                    have : d = 152780 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7639)
      exact by decide
                  ·
                    have : d = 152779 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152778 ≤ d
                  ·
                    have : d = 152778 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 25463)
      exact by decide
                  ·
                    have : d = 152777 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 152773 ≤ d
              ·
                by_cases h : 152775 ≤ d
                ·
                  by_cases h : 152776 ≤ d
                  ·
                    have : d = 152776 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152775 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152774 ≤ d
                  ·
                    have : d = 152774 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152773 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152771 ≤ d
                ·
                  by_cases h : 152772 ≤ d
                  ·
                    have : d = 152772 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 152771 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152770 ≤ d
                  ·
                    have : d = 152770 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152769 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 152737 ≤ d
        ·
          by_cases h : 152753 ≤ d
          ·
            by_cases h : 152761 ≤ d
            ·
              by_cases h : 152765 ≤ d
              ·
                by_cases h : 152767 ≤ d
                ·
                  by_cases h : 152768 ≤ d
                  ·
                    have : d = 152768 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 152767 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152766 ≤ d
                  ·
                    have : d = 152766 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 152765 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152763 ≤ d
                ·
                  by_cases h : 152764 ≤ d
                  ·
                    have : d = 152764 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152763 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152762 ≤ d
                  ·
                    have : d = 152762 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 152761 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 152757 ≤ d
              ·
                by_cases h : 152759 ≤ d
                ·
                  by_cases h : 152760 ≤ d
                  ·
                    have : d = 152760 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152759 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152758 ≤ d
                  ·
                    have : d = 152758 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152757 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152755 ≤ d
                ·
                  by_cases h : 152756 ≤ d
                  ·
                    have : d = 152756 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 38189)
      exact by decide
                  ·
                    have : d = 152755 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152754 ≤ d
                  ·
                    have : d = 152754 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152753 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 152745 ≤ d
            ·
              by_cases h : 152749 ≤ d
              ·
                by_cases h : 152751 ≤ d
                ·
                  by_cases h : 152752 ≤ d
                  ·
                    have : d = 152752 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152751 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152750 ≤ d
                  ·
                    have : d = 152750 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 152749 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152747 ≤ d
                ·
                  by_cases h : 152748 ≤ d
                  ·
                    have : d = 152748 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 4243)
      exact by decide
                  ·
                    have : d = 152747 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152746 ≤ d
                  ·
                    have : d = 152746 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152745 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 152741 ≤ d
              ·
                by_cases h : 152743 ≤ d
                ·
                  by_cases h : 152744 ≤ d
                  ·
                    have : d = 152744 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152743 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152742 ≤ d
                  ·
                    have : d = 152742 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152741 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152739 ≤ d
                ·
                  by_cases h : 152740 ≤ d
                  ·
                    have : d = 152740 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152739 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152738 ≤ d
                  ·
                    have : d = 152738 := by omega
                    subst d
      exact fullRecordGapTerm04464_not_prime
                  ·
                    have : d = 152737 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 152721 ≤ d
          ·
            by_cases h : 152729 ≤ d
            ·
              by_cases h : 152733 ≤ d
              ·
                by_cases h : 152735 ≤ d
                ·
                  by_cases h : 152736 ≤ d
                  ·
                    have : d = 152736 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 152735 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152734 ≤ d
                  ·
                    have : d = 152734 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152733 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152731 ≤ d
                ·
                  by_cases h : 152732 ≤ d
                  ·
                    have : d = 152732 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152731 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152730 ≤ d
                  ·
                    have : d = 152730 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1697)
      exact by decide
                  ·
                    have : d = 152729 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 152725 ≤ d
              ·
                by_cases h : 152727 ≤ d
                ·
                  by_cases h : 152728 ≤ d
                  ·
                    have : d = 152728 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152727 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152726 ≤ d
                  ·
                    have : d = 152726 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 10909)
      exact by decide
                  ·
                    have : d = 152725 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152723 ≤ d
                ·
                  by_cases h : 152724 ≤ d
                  ·
                    have : d = 152724 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152723 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152722 ≤ d
                  ·
                    have : d = 152722 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152721 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 152713 ≤ d
            ·
              by_cases h : 152717 ≤ d
              ·
                by_cases h : 152719 ≤ d
                ·
                  by_cases h : 152720 ≤ d
                  ·
                    have : d = 152720 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152719 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152718 ≤ d
                  ·
                    have : d = 152718 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152717 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152715 ≤ d
                ·
                  by_cases h : 152716 ≤ d
                  ·
                    have : d = 152716 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152715 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152714 ≤ d
                  ·
                    have : d = 152714 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152713 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 152709 ≤ d
              ·
                by_cases h : 152711 ≤ d
                ·
                  by_cases h : 152712 ≤ d
                  ·
                    have : d = 152712 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 101)
      exact by decide
                  ·
                    have : d = 152711 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152710 ≤ d
                  ·
                    have : d = 152710 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152709 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152707 ≤ d
                ·
                  by_cases h : 152708 ≤ d
                  ·
                    have : d = 152708 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 38177)
      exact by decide
                  ·
                    have : d = 152707 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152706 ≤ d
                  ·
                    have : d = 152706 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 152705 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 152641 ≤ d
      ·
        by_cases h : 152673 ≤ d
        ·
          by_cases h : 152689 ≤ d
          ·
            by_cases h : 152697 ≤ d
            ·
              by_cases h : 152701 ≤ d
              ·
                by_cases h : 152703 ≤ d
                ·
                  by_cases h : 152704 ≤ d
                  ·
                    have : d = 152704 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152703 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152702 ≤ d
                  ·
                    have : d = 152702 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 631)
      exact by decide
                  ·
                    have : d = 152701 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152699 ≤ d
                ·
                  by_cases h : 152700 ≤ d
                  ·
                    have : d = 152700 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 509)
      exact by decide
                  ·
                    have : d = 152699 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152698 ≤ d
                  ·
                    have : d = 152698 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152697 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 152693 ≤ d
              ·
                by_cases h : 152695 ≤ d
                ·
                  by_cases h : 152696 ≤ d
                  ·
                    have : d = 152696 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19087)
      exact by decide
                  ·
                    have : d = 152695 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152694 ≤ d
                  ·
                    have : d = 152694 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152693 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152691 ≤ d
                ·
                  by_cases h : 152692 ≤ d
                  ·
                    have : d = 152692 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152691 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152690 ≤ d
                  ·
                    have : d = 152690 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152689 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 152681 ≤ d
            ·
              by_cases h : 152685 ≤ d
              ·
                by_cases h : 152687 ≤ d
                ·
                  by_cases h : 152688 ≤ d
                  ·
                    have : d = 152688 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3181)
      exact by decide
                  ·
                    have : d = 152687 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152686 ≤ d
                  ·
                    have : d = 152686 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152685 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152683 ≤ d
                ·
                  by_cases h : 152684 ≤ d
                  ·
                    have : d = 152684 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152683 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152682 ≤ d
                  ·
                    have : d = 152682 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 25447)
      exact by decide
                  ·
                    have : d = 152681 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 152677 ≤ d
              ·
                by_cases h : 152679 ≤ d
                ·
                  by_cases h : 152680 ≤ d
                  ·
                    have : d = 152680 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152679 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152678 ≤ d
                  ·
                    have : d = 152678 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 97)
      exact by decide
                  ·
                    have : d = 152677 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152675 ≤ d
                ·
                  by_cases h : 152676 ≤ d
                  ·
                    have : d = 152676 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152675 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152674 ≤ d
                  ·
                    have : d = 152674 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152673 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 152657 ≤ d
          ·
            by_cases h : 152665 ≤ d
            ·
              by_cases h : 152669 ≤ d
              ·
                by_cases h : 152671 ≤ d
                ·
                  by_cases h : 152672 ≤ d
                  ·
                    have : d = 152672 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 152671 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152670 ≤ d
                  ·
                    have : d = 152670 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 727)
      exact by decide
                  ·
                    have : d = 152669 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152667 ≤ d
                ·
                  by_cases h : 152668 ≤ d
                  ·
                    have : d = 152668 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152667 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152666 ≤ d
                  ·
                    have : d = 152666 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 6826591)
      right
      exact ⟨6673925, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152665 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 152661 ≤ d
              ·
                by_cases h : 152663 ≤ d
                ·
                  by_cases h : 152664 ≤ d
                  ·
                    have : d = 152664 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152663 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152662 ≤ d
                  ·
                    have : d = 152662 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152661 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152659 ≤ d
                ·
                  by_cases h : 152660 ≤ d
                  ·
                    have : d = 152660 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 152659 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152658 ≤ d
                  ·
                    have : d = 152658 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 257)
      exact by decide
                  ·
                    have : d = 152657 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 152649 ≤ d
            ·
              by_cases h : 152653 ≤ d
              ·
                by_cases h : 152655 ≤ d
                ·
                  by_cases h : 152656 ≤ d
                  ·
                    have : d = 152656 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152655 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152654 ≤ d
                  ·
                    have : d = 152654 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152653 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152651 ≤ d
                ·
                  by_cases h : 152652 ≤ d
                  ·
                    have : d = 152652 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 12721)
      exact by decide
                  ·
                    have : d = 152651 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152650 ≤ d
                  ·
                    have : d = 152650 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152649 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 152645 ≤ d
              ·
                by_cases h : 152647 ≤ d
                ·
                  by_cases h : 152648 ≤ d
                  ·
                    have : d = 152648 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152647 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152646 ≤ d
                  ·
                    have : d = 152646 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 152645 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152643 ≤ d
                ·
                  by_cases h : 152644 ≤ d
                  ·
                    have : d = 152644 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152643 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152642 ≤ d
                  ·
                    have : d = 152642 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 10903)
      exact by decide
                  ·
                    have : d = 152641 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 152609 ≤ d
        ·
          by_cases h : 152625 ≤ d
          ·
            by_cases h : 152633 ≤ d
            ·
              by_cases h : 152637 ≤ d
              ·
                by_cases h : 152639 ≤ d
                ·
                  by_cases h : 152640 ≤ d
                  ·
                    have : d = 152640 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 53)
      exact by decide
                  ·
                    have : d = 152639 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152638 ≤ d
                  ·
                    have : d = 152638 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152637 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152635 ≤ d
                ·
                  by_cases h : 152636 ≤ d
                  ·
                    have : d = 152636 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3469)
      exact by decide
                  ·
                    have : d = 152635 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152634 ≤ d
                  ·
                    have : d = 152634 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152633 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 152629 ≤ d
              ·
                by_cases h : 152631 ≤ d
                ·
                  by_cases h : 152632 ≤ d
                  ·
                    have : d = 152632 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152631 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152630 ≤ d
                  ·
                    have : d = 152630 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 15263)
      exact by decide
                  ·
                    have : d = 152629 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152627 ≤ d
                ·
                  by_cases h : 152628 ≤ d
                  ·
                    have : d = 152628 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 152627 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152626 ≤ d
                  ·
                    have : d = 152626 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152625 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 152617 ≤ d
            ·
              by_cases h : 152621 ≤ d
              ·
                by_cases h : 152623 ≤ d
                ·
                  by_cases h : 152624 ≤ d
                  ·
                    have : d = 152624 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152623 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152622 ≤ d
                  ·
                    have : d = 152622 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 61)
      exact by decide
                  ·
                    have : d = 152621 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152619 ≤ d
                ·
                  by_cases h : 152620 ≤ d
                  ·
                    have : d = 152620 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152619 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152618 ≤ d
                  ·
                    have : d = 152618 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 137)
      exact by decide
                  ·
                    have : d = 152617 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 152613 ≤ d
              ·
                by_cases h : 152615 ≤ d
                ·
                  by_cases h : 152616 ≤ d
                  ·
                    have : d = 152616 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 6359)
      exact by decide
                  ·
                    have : d = 152615 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152614 ≤ d
                  ·
                    have : d = 152614 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152613 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152611 ≤ d
                ·
                  by_cases h : 152612 ≤ d
                  ·
                    have : d = 152612 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 38153)
      exact by decide
                  ·
                    have : d = 152611 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152610 ≤ d
                  ·
                    have : d = 152610 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152609 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 152593 ≤ d
          ·
            by_cases h : 152601 ≤ d
            ·
              by_cases h : 152605 ≤ d
              ·
                by_cases h : 152607 ≤ d
                ·
                  by_cases h : 152608 ≤ d
                  ·
                    have : d = 152608 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152607 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152606 ≤ d
                  ·
                    have : d = 152606 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152605 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152603 ≤ d
                ·
                  by_cases h : 152604 ≤ d
                  ·
                    have : d = 152604 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152603 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152602 ≤ d
                  ·
                    have : d = 152602 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152601 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 152597 ≤ d
              ·
                by_cases h : 152599 ≤ d
                ·
                  by_cases h : 152600 ≤ d
                  ·
                    have : d = 152600 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 109)
      exact by decide
                  ·
                    have : d = 152599 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152598 ≤ d
                  ·
                    have : d = 152598 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 152597 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152595 ≤ d
                ·
                  by_cases h : 152596 ≤ d
                  ·
                    have : d = 152596 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152595 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152594 ≤ d
                  ·
                    have : d = 152594 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152593 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 152585 ≤ d
            ·
              by_cases h : 152589 ≤ d
              ·
                by_cases h : 152591 ≤ d
                ·
                  by_cases h : 152592 ≤ d
                  ·
                    have : d = 152592 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152591 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152590 ≤ d
                  ·
                    have : d = 152590 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152589 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152587 ≤ d
                ·
                  by_cases h : 152588 ≤ d
                  ·
                    have : d = 152588 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152587 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152586 ≤ d
                  ·
                    have : d = 152586 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 173)
      exact by decide
                  ·
                    have : d = 152585 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 152581 ≤ d
              ·
                by_cases h : 152583 ≤ d
                ·
                  by_cases h : 152584 ≤ d
                  ·
                    have : d = 152584 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152583 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152582 ≤ d
                  ·
                    have : d = 152582 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 152581 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 152579 ≤ d
                ·
                  by_cases h : 152580 ≤ d
                  ·
                    have : d = 152580 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2543)
      exact by decide
                  ·
                    have : d = 152579 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 152578 ≤ d
                  ·
                    have : d = 152578 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 152577 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩

end PrimeFactorUnimodality
