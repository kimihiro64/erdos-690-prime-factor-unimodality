import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapFermat

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

theorem fullRecordGapSubBlock_part0348 (d : Nat) (177665 ≤ d) (d ≤ 178176) : ¬(recordGapCenter - d).Prime := by
  by_cases h : 177921 ≤ d
  ·
    by_cases h : 178049 ≤ d
    ·
      by_cases h : 178113 ≤ d
      ·
        by_cases h : 178145 ≤ d
        ·
          by_cases h : 178161 ≤ d
          ·
            by_cases h : 178169 ≤ d
            ·
              by_cases h : 178173 ≤ d
              ·
                by_cases h : 178175 ≤ d
                ·
                  by_cases h : 178176 ≤ d
                  ·
                    have : d = 178176 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178175 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178174 ≤ d
                  ·
                    have : d = 178174 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 34118302013) (by norm_num)
      right
      exact ⟨178174, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178173 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 178171 ≤ d
                ·
                  by_cases h : 178172 ≤ d
                  ·
                    have : d = 178172 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178171 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178170 ≤ d
                  ·
                    have : d = 178170 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5939) (by norm_num)
      exact by decide
                  ·
                    have : d = 178169 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 178165 ≤ d
              ·
                by_cases h : 178167 ≤ d
                ·
                  by_cases h : 178168 ≤ d
                  ·
                    have : d = 178168 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 22271) (by norm_num)
      exact by decide
                  ·
                    have : d = 178167 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178166 ≤ d
                  ·
                    have : d = 178166 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178165 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 178163 ≤ d
                ·
                  by_cases h : 178164 ≤ d
                  ·
                    have : d = 178164 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 101) (by norm_num)
      exact by decide
                  ·
                    have : d = 178163 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178162 ≤ d
                  ·
                    have : d = 178162 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 229) (by norm_num)
      exact by decide
                  ·
                    have : d = 178161 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 178153 ≤ d
            ·
              by_cases h : 178157 ≤ d
              ·
                by_cases h : 178159 ≤ d
                ·
                  by_cases h : 178160 ≤ d
                  ·
                    have : d = 178160 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178159 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178158 ≤ d
                  ·
                    have : d = 178158 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178157 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 178155 ≤ d
                ·
                  by_cases h : 178156 ≤ d
                  ·
                    have : d = 178156 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178155 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178154 ≤ d
                  ·
                    have : d = 178154 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178153 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 178149 ≤ d
              ·
                by_cases h : 178151 ≤ d
                ·
                  by_cases h : 178152 ≤ d
                  ·
                    have : d = 178152 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 178151 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178150 ≤ d
                  ·
                    have : d = 178150 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 509) (by norm_num)
      exact by decide
                  ·
                    have : d = 178149 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 178147 ≤ d
                ·
                  by_cases h : 178148 ≤ d
                  ·
                    have : d = 178148 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178147 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178146 ≤ d
                  ·
                    have : d = 178146 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178145 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 178129 ≤ d
          ·
            by_cases h : 178137 ≤ d
            ·
              by_cases h : 178141 ≤ d
              ·
                by_cases h : 178143 ≤ d
                ·
                  by_cases h : 178144 ≤ d
                  ·
                    have : d = 178144 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178143 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178142 ≤ d
                  ·
                    have : d = 178142 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178141 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 178139 ≤ d
                ·
                  by_cases h : 178140 ≤ d
                  ·
                    have : d = 178140 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2969) (by norm_num)
      exact by decide
                  ·
                    have : d = 178139 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178138 ≤ d
                  ·
                    have : d = 178138 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178137 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 178133 ≤ d
              ·
                by_cases h : 178135 ≤ d
                ·
                  by_cases h : 178136 ≤ d
                  ·
                    have : d = 178136 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178135 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178134 ≤ d
                  ·
                    have : d = 178134 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2699) (by norm_num)
      exact by decide
                  ·
                    have : d = 178133 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 178131 ≤ d
                ·
                  by_cases h : 178132 ≤ d
                  ·
                    have : d = 178132 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 72161) (by norm_num)
      right
      exact ⟨33810, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178131 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178130 ≤ d
                  ·
                    have : d = 178130 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178129 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 178121 ≤ d
            ·
              by_cases h : 178125 ≤ d
              ·
                by_cases h : 178127 ≤ d
                ·
                  by_cases h : 178128 ≤ d
                  ·
                    have : d = 178128 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1237) (by norm_num)
      exact by decide
                  ·
                    have : d = 178127 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178126 ≤ d
                  ·
                    have : d = 178126 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178125 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 178123 ≤ d
                ·
                  by_cases h : 178124 ≤ d
                  ·
                    have : d = 178124 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178123 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178122 ≤ d
                  ·
                    have : d = 178122 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 4241) (by norm_num)
      exact by decide
                  ·
                    have : d = 178121 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 178117 ≤ d
              ·
                by_cases h : 178119 ≤ d
                ·
                  by_cases h : 178120 ≤ d
                  ·
                    have : d = 178120 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 61) (by norm_num)
      exact by decide
                  ·
                    have : d = 178119 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178118 ≤ d
                  ·
                    have : d = 178118 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178117 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 178115 ≤ d
                ·
                  by_cases h : 178116 ≤ d
                  ·
                    have : d = 178116 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178115 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178114 ≤ d
                  ·
                    have : d = 178114 := by omega
                    subst d
      exact fullRecordGapTerm03039_not_prime
                  ·
                    have : d = 178113 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 178081 ≤ d
        ·
          by_cases h : 178097 ≤ d
          ·
            by_cases h : 178105 ≤ d
            ·
              by_cases h : 178109 ≤ d
              ·
                by_cases h : 178111 ≤ d
                ·
                  by_cases h : 178112 ≤ d
                  ·
                    have : d = 178112 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178111 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178110 ≤ d
                  ·
                    have : d = 178110 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1979) (by norm_num)
      exact by decide
                  ·
                    have : d = 178109 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 178107 ≤ d
                ·
                  by_cases h : 178108 ≤ d
                  ·
                    have : d = 178108 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 6361) (by norm_num)
      exact by decide
                  ·
                    have : d = 178107 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178106 ≤ d
                  ·
                    have : d = 178106 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178105 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 178101 ≤ d
              ·
                by_cases h : 178103 ≤ d
                ·
                  by_cases h : 178104 ≤ d
                  ·
                    have : d = 178104 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 41) (by norm_num)
      exact by decide
                  ·
                    have : d = 178103 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178102 ≤ d
                  ·
                    have : d = 178102 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178101 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 178099 ≤ d
                ·
                  by_cases h : 178100 ≤ d
                  ·
                    have : d = 178100 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178099 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178098 ≤ d
                  ·
                    have : d = 178098 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 29683) (by norm_num)
      exact by decide
                  ·
                    have : d = 178097 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 178089 ≤ d
            ·
              by_cases h : 178093 ≤ d
              ·
                by_cases h : 178095 ≤ d
                ·
                  by_cases h : 178096 ≤ d
                  ·
                    have : d = 178096 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178095 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178094 ≤ d
                  ·
                    have : d = 178094 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178093 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 178091 ≤ d
                ·
                  by_cases h : 178092 ≤ d
                  ·
                    have : d = 178092 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 178091 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178090 ≤ d
                  ·
                    have : d = 178090 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1619) (by norm_num)
      exact by decide
                  ·
                    have : d = 178089 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 178085 ≤ d
              ·
                by_cases h : 178087 ≤ d
                ·
                  by_cases h : 178088 ≤ d
                  ·
                    have : d = 178088 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178087 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178086 ≤ d
                  ·
                    have : d = 178086 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178085 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 178083 ≤ d
                ·
                  by_cases h : 178084 ≤ d
                  ·
                    have : d = 178084 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 211) (by norm_num)
      exact by decide
                  ·
                    have : d = 178083 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178082 ≤ d
                  ·
                    have : d = 178082 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178081 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 178065 ≤ d
          ·
            by_cases h : 178073 ≤ d
            ·
              by_cases h : 178077 ≤ d
              ·
                by_cases h : 178079 ≤ d
                ·
                  by_cases h : 178080 ≤ d
                  ·
                    have : d = 178080 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 53) (by norm_num)
      exact by decide
                  ·
                    have : d = 178079 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178078 ≤ d
                  ·
                    have : d = 178078 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 269) (by norm_num)
      exact by decide
                  ·
                    have : d = 178077 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 178075 ≤ d
                ·
                  by_cases h : 178076 ≤ d
                  ·
                    have : d = 178076 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178075 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178074 ≤ d
                  ·
                    have : d = 178074 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178073 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 178069 ≤ d
              ·
                by_cases h : 178071 ≤ d
                ·
                  by_cases h : 178072 ≤ d
                  ·
                    have : d = 178072 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178071 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178070 ≤ d
                  ·
                    have : d = 178070 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178069 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 178067 ≤ d
                ·
                  by_cases h : 178068 ≤ d
                  ·
                    have : d = 178068 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 178067 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178066 ≤ d
                  ·
                    have : d = 178066 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178065 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 178057 ≤ d
            ·
              by_cases h : 178061 ≤ d
              ·
                by_cases h : 178063 ≤ d
                ·
                  by_cases h : 178064 ≤ d
                  ·
                    have : d = 178064 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178063 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178062 ≤ d
                  ·
                    have : d = 178062 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 59) (by norm_num)
      exact by decide
                  ·
                    have : d = 178061 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 178059 ≤ d
                ·
                  by_cases h : 178060 ≤ d
                  ·
                    have : d = 178060 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178059 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178058 ≤ d
                  ·
                    have : d = 178058 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178057 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 178053 ≤ d
              ·
                by_cases h : 178055 ≤ d
                ·
                  by_cases h : 178056 ≤ d
                  ·
                    have : d = 178056 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178055 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178054 ≤ d
                  ·
                    have : d = 178054 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 127) (by norm_num)
      exact by decide
                  ·
                    have : d = 178053 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 178051 ≤ d
                ·
                  by_cases h : 178052 ≤ d
                  ·
                    have : d = 178052 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178051 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178050 ≤ d
                  ·
                    have : d = 178050 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178049 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 177985 ≤ d
      ·
        by_cases h : 178017 ≤ d
        ·
          by_cases h : 178033 ≤ d
          ·
            by_cases h : 178041 ≤ d
            ·
              by_cases h : 178045 ≤ d
              ·
                by_cases h : 178047 ≤ d
                ·
                  by_cases h : 178048 ≤ d
                  ·
                    have : d = 178048 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 178047 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178046 ≤ d
                  ·
                    have : d = 178046 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178045 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 178043 ≤ d
                ·
                  by_cases h : 178044 ≤ d
                  ·
                    have : d = 178044 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 37) (by norm_num)
      exact by decide
                  ·
                    have : d = 178043 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178042 ≤ d
                  ·
                    have : d = 178042 := by omega
                    subst d
      exact fullRecordGapTerm03040_not_prime
                  ·
                    have : d = 178041 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 178037 ≤ d
              ·
                by_cases h : 178039 ≤ d
                ·
                  by_cases h : 178040 ≤ d
                  ·
                    have : d = 178040 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178039 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178038 ≤ d
                  ·
                    have : d = 178038 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 157) (by norm_num)
      exact by decide
                  ·
                    have : d = 178037 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 178035 ≤ d
                ·
                  by_cases h : 178036 ≤ d
                  ·
                    have : d = 178036 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178035 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178034 ≤ d
                  ·
                    have : d = 178034 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178033 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 178025 ≤ d
            ·
              by_cases h : 178029 ≤ d
              ·
                by_cases h : 178031 ≤ d
                ·
                  by_cases h : 178032 ≤ d
                  ·
                    have : d = 178032 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178031 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178030 ≤ d
                  ·
                    have : d = 178030 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 178029 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 178027 ≤ d
                ·
                  by_cases h : 178028 ≤ d
                  ·
                    have : d = 178028 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178027 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178026 ≤ d
                  ·
                    have : d = 178026 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178025 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 178021 ≤ d
              ·
                by_cases h : 178023 ≤ d
                ·
                  by_cases h : 178024 ≤ d
                  ·
                    have : d = 178024 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 178023 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178022 ≤ d
                  ·
                    have : d = 178022 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178021 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 178019 ≤ d
                ·
                  by_cases h : 178020 ≤ d
                  ·
                    have : d = 178020 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23) (by norm_num)
      exact by decide
                  ·
                    have : d = 178019 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178018 ≤ d
                  ·
                    have : d = 178018 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178017 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 178001 ≤ d
          ·
            by_cases h : 178009 ≤ d
            ·
              by_cases h : 178013 ≤ d
              ·
                by_cases h : 178015 ≤ d
                ·
                  by_cases h : 178016 ≤ d
                  ·
                    have : d = 178016 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178015 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178014 ≤ d
                  ·
                    have : d = 178014 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 29669) (by norm_num)
      exact by decide
                  ·
                    have : d = 178013 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 178011 ≤ d
                ·
                  by_cases h : 178012 ≤ d
                  ·
                    have : d = 178012 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 191) (by norm_num)
      exact by decide
                  ·
                    have : d = 178011 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178010 ≤ d
                  ·
                    have : d = 178010 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178009 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 178005 ≤ d
              ·
                by_cases h : 178007 ≤ d
                ·
                  by_cases h : 178008 ≤ d
                  ·
                    have : d = 178008 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7417) (by norm_num)
      exact by decide
                  ·
                    have : d = 178007 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178006 ≤ d
                  ·
                    have : d = 178006 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178005 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 178003 ≤ d
                ·
                  by_cases h : 178004 ≤ d
                  ·
                    have : d = 178004 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 178003 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 178002 ≤ d
                  ·
                    have : d = 178002 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 29) (by norm_num)
      exact by decide
                  ·
                    have : d = 178001 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 177993 ≤ d
            ·
              by_cases h : 177997 ≤ d
              ·
                by_cases h : 177999 ≤ d
                ·
                  by_cases h : 178000 ≤ d
                  ·
                    have : d = 178000 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 89) (by norm_num)
      exact by decide
                  ·
                    have : d = 177999 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177998 ≤ d
                  ·
                    have : d = 177998 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177997 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177995 ≤ d
                ·
                  by_cases h : 177996 ≤ d
                  ·
                    have : d = 177996 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177995 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177994 ≤ d
                  ·
                    have : d = 177994 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 556267) (by norm_num)
      right
      exact ⟨177994, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177993 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 177989 ≤ d
              ·
                by_cases h : 177991 ≤ d
                ·
                  by_cases h : 177992 ≤ d
                  ·
                    have : d = 177992 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177991 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177990 ≤ d
                  ·
                    have : d = 177990 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177989 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177987 ≤ d
                ·
                  by_cases h : 177988 ≤ d
                  ·
                    have : d = 177988 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 338736311) (by norm_num)
      right
      exact ⟨177988, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177987 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177986 ≤ d
                  ·
                    have : d = 177986 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177985 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 177953 ≤ d
        ·
          by_cases h : 177969 ≤ d
          ·
            by_cases h : 177977 ≤ d
            ·
              by_cases h : 177981 ≤ d
              ·
                by_cases h : 177983 ≤ d
                ·
                  by_cases h : 177984 ≤ d
                  ·
                    have : d = 177984 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177983 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177982 ≤ d
                  ·
                    have : d = 177982 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 12713) (by norm_num)
      exact by decide
                  ·
                    have : d = 177981 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177979 ≤ d
                ·
                  by_cases h : 177980 ≤ d
                  ·
                    have : d = 177980 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177979 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177978 ≤ d
                  ·
                    have : d = 177978 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 29663) (by norm_num)
      exact by decide
                  ·
                    have : d = 177977 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 177973 ≤ d
              ·
                by_cases h : 177975 ≤ d
                ·
                  by_cases h : 177976 ≤ d
                  ·
                    have : d = 177976 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177975 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177974 ≤ d
                  ·
                    have : d = 177974 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177973 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177971 ≤ d
                ·
                  by_cases h : 177972 ≤ d
                  ·
                    have : d = 177972 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 14831) (by norm_num)
      exact by decide
                  ·
                    have : d = 177971 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177970 ≤ d
                  ·
                    have : d = 177970 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 177969 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 177961 ≤ d
            ·
              by_cases h : 177965 ≤ d
              ·
                by_cases h : 177967 ≤ d
                ·
                  by_cases h : 177968 ≤ d
                  ·
                    have : d = 177968 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177967 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177966 ≤ d
                  ·
                    have : d = 177966 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177965 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177963 ≤ d
                ·
                  by_cases h : 177964 ≤ d
                  ·
                    have : d = 177964 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 356737) (by norm_num)
      right
      exact ⟨177964, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177963 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177962 ≤ d
                  ·
                    have : d = 177962 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177961 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 177957 ≤ d
              ·
                by_cases h : 177959 ≤ d
                ·
                  by_cases h : 177960 ≤ d
                  ·
                    have : d = 177960 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1483) (by norm_num)
      exact by decide
                  ·
                    have : d = 177959 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177958 ≤ d
                  ·
                    have : d = 177958 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 8089) (by norm_num)
      exact by decide
                  ·
                    have : d = 177957 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177955 ≤ d
                ·
                  by_cases h : 177956 ≤ d
                  ·
                    have : d = 177956 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177955 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177954 ≤ d
                  ·
                    have : d = 177954 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 177953 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 177937 ≤ d
          ·
            by_cases h : 177945 ≤ d
            ·
              by_cases h : 177949 ≤ d
              ·
                by_cases h : 177951 ≤ d
                ·
                  by_cases h : 177952 ≤ d
                  ·
                    have : d = 177952 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 67) (by norm_num)
      exact by decide
                  ·
                    have : d = 177951 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177950 ≤ d
                  ·
                    have : d = 177950 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177949 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177947 ≤ d
                ·
                  by_cases h : 177948 ≤ d
                  ·
                    have : d = 177948 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177947 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177946 ≤ d
                  ·
                    have : d = 177946 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177945 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 177941 ≤ d
              ·
                by_cases h : 177943 ≤ d
                ·
                  by_cases h : 177944 ≤ d
                  ·
                    have : d = 177944 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177943 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177942 ≤ d
                  ·
                    have : d = 177942 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 47) (by norm_num)
      exact by decide
                  ·
                    have : d = 177941 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177939 ≤ d
                ·
                  by_cases h : 177940 ≤ d
                  ·
                    have : d = 177940 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177939 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177938 ≤ d
                  ·
                    have : d = 177938 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177937 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 177929 ≤ d
            ·
              by_cases h : 177933 ≤ d
              ·
                by_cases h : 177935 ≤ d
                ·
                  by_cases h : 177936 ≤ d
                  ·
                    have : d = 177936 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177935 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177934 ≤ d
                  ·
                    have : d = 177934 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177933 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177931 ≤ d
                ·
                  by_cases h : 177932 ≤ d
                  ·
                    have : d = 177932 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177931 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177930 ≤ d
                  ·
                    have : d = 177930 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 659) (by norm_num)
      exact by decide
                  ·
                    have : d = 177929 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 177925 ≤ d
              ·
                by_cases h : 177927 ≤ d
                ·
                  by_cases h : 177928 ≤ d
                  ·
                    have : d = 177928 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23) (by norm_num)
      exact by decide
                  ·
                    have : d = 177927 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177926 ≤ d
                  ·
                    have : d = 177926 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177925 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177923 ≤ d
                ·
                  by_cases h : 177924 ≤ d
                  ·
                    have : d = 177924 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 14827) (by norm_num)
      exact by decide
                  ·
                    have : d = 177923 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177922 ≤ d
                  ·
                    have : d = 177922 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 177921 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
  ·
    by_cases h : 177793 ≤ d
    ·
      by_cases h : 177857 ≤ d
      ·
        by_cases h : 177889 ≤ d
        ·
          by_cases h : 177905 ≤ d
          ·
            by_cases h : 177913 ≤ d
            ·
              by_cases h : 177917 ≤ d
              ·
                by_cases h : 177919 ≤ d
                ·
                  by_cases h : 177920 ≤ d
                  ·
                    have : d = 177920 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177919 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177918 ≤ d
                  ·
                    have : d = 177918 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177917 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177915 ≤ d
                ·
                  by_cases h : 177916 ≤ d
                  ·
                    have : d = 177916 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177915 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177914 ≤ d
                  ·
                    have : d = 177914 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177913 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 177909 ≤ d
              ·
                by_cases h : 177911 ≤ d
                ·
                  by_cases h : 177912 ≤ d
                  ·
                    have : d = 177912 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 353) (by norm_num)
      exact by decide
                  ·
                    have : d = 177911 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177910 ≤ d
                  ·
                    have : d = 177910 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17791) (by norm_num)
      exact by decide
                  ·
                    have : d = 177909 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177907 ≤ d
                ·
                  by_cases h : 177908 ≤ d
                  ·
                    have : d = 177908 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177907 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177906 ≤ d
                  ·
                    have : d = 177906 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177905 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 177897 ≤ d
            ·
              by_cases h : 177901 ≤ d
              ·
                by_cases h : 177903 ≤ d
                ·
                  by_cases h : 177904 ≤ d
                  ·
                    have : d = 177904 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11119) (by norm_num)
      exact by decide
                  ·
                    have : d = 177903 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177902 ≤ d
                  ·
                    have : d = 177902 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177901 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177899 ≤ d
                ·
                  by_cases h : 177900 ≤ d
                  ·
                    have : d = 177900 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 593) (by norm_num)
      exact by decide
                  ·
                    have : d = 177899 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177898 ≤ d
                  ·
                    have : d = 177898 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 97) (by norm_num)
      exact by decide
                  ·
                    have : d = 177897 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 177893 ≤ d
              ·
                by_cases h : 177895 ≤ d
                ·
                  by_cases h : 177896 ≤ d
                  ·
                    have : d = 177896 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177895 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177894 ≤ d
                  ·
                    have : d = 177894 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 9883) (by norm_num)
      exact by decide
                  ·
                    have : d = 177893 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177891 ≤ d
                ·
                  by_cases h : 177892 ≤ d
                  ·
                    have : d = 177892 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177891 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177890 ≤ d
                  ·
                    have : d = 177890 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177889 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 177873 ≤ d
          ·
            by_cases h : 177881 ≤ d
            ·
              by_cases h : 177885 ≤ d
              ·
                by_cases h : 177887 ≤ d
                ·
                  by_cases h : 177888 ≤ d
                  ·
                    have : d = 177888 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 177887 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177886 ≤ d
                  ·
                    have : d = 177886 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177885 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177883 ≤ d
                ·
                  by_cases h : 177884 ≤ d
                  ·
                    have : d = 177884 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177883 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177882 ≤ d
                  ·
                    have : d = 177882 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23) (by norm_num)
      exact by decide
                  ·
                    have : d = 177881 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 177877 ≤ d
              ·
                by_cases h : 177879 ≤ d
                ·
                  by_cases h : 177880 ≤ d
                  ·
                    have : d = 177880 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 4447) (by norm_num)
      exact by decide
                  ·
                    have : d = 177879 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177878 ≤ d
                  ·
                    have : d = 177878 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177877 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177875 ≤ d
                ·
                  by_cases h : 177876 ≤ d
                  ·
                    have : d = 177876 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177875 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177874 ≤ d
                  ·
                    have : d = 177874 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177873 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 177865 ≤ d
            ·
              by_cases h : 177869 ≤ d
              ·
                by_cases h : 177871 ≤ d
                ·
                  by_cases h : 177872 ≤ d
                  ·
                    have : d = 177872 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177871 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177870 ≤ d
                  ·
                    have : d = 177870 := by omega
                    subst d
      exact fullRecordGapTerm03041_not_prime
                  ·
                    have : d = 177869 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177867 ≤ d
                ·
                  by_cases h : 177868 ≤ d
                  ·
                    have : d = 177868 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 53) (by norm_num)
      exact by decide
                  ·
                    have : d = 177867 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177866 ≤ d
                  ·
                    have : d = 177866 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177865 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 177861 ≤ d
              ·
                by_cases h : 177863 ≤ d
                ·
                  by_cases h : 177864 ≤ d
                  ·
                    have : d = 177864 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177863 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177862 ≤ d
                  ·
                    have : d = 177862 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 113) (by norm_num)
      exact by decide
                  ·
                    have : d = 177861 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177859 ≤ d
                ·
                  by_cases h : 177860 ≤ d
                  ·
                    have : d = 177860 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177859 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177858 ≤ d
                  ·
                    have : d = 177858 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 41) (by norm_num)
      exact by decide
                  ·
                    have : d = 177857 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 177825 ≤ d
        ·
          by_cases h : 177841 ≤ d
          ·
            by_cases h : 177849 ≤ d
            ·
              by_cases h : 177853 ≤ d
              ·
                by_cases h : 177855 ≤ d
                ·
                  by_cases h : 177856 ≤ d
                  ·
                    have : d = 177856 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177855 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177854 ≤ d
                  ·
                    have : d = 177854 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177853 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177851 ≤ d
                ·
                  by_cases h : 177852 ≤ d
                  ·
                    have : d = 177852 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177851 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177850 ≤ d
                  ·
                    have : d = 177850 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177849 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 177845 ≤ d
              ·
                by_cases h : 177847 ≤ d
                ·
                  by_cases h : 177848 ≤ d
                  ·
                    have : d = 177848 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177847 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177846 ≤ d
                  ·
                    have : d = 177846 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177845 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177843 ≤ d
                ·
                  by_cases h : 177844 ≤ d
                  ·
                    have : d = 177844 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 173) (by norm_num)
      exact by decide
                  ·
                    have : d = 177843 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177842 ≤ d
                  ·
                    have : d = 177842 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177841 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 177833 ≤ d
            ·
              by_cases h : 177837 ≤ d
              ·
                by_cases h : 177839 ≤ d
                ·
                  by_cases h : 177840 ≤ d
                  ·
                    have : d = 177840 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 177839 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177838 ≤ d
                  ·
                    have : d = 177838 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 82763) (by norm_num)
      right
      exact ⟨12312, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177837 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177835 ≤ d
                ·
                  by_cases h : 177836 ≤ d
                  ·
                    have : d = 177836 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177835 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177834 ≤ d
                  ·
                    have : d = 177834 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 107) (by norm_num)
      exact by decide
                  ·
                    have : d = 177833 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 177829 ≤ d
              ·
                by_cases h : 177831 ≤ d
                ·
                  by_cases h : 177832 ≤ d
                  ·
                    have : d = 177832 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 22229) (by norm_num)
      exact by decide
                  ·
                    have : d = 177831 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177830 ≤ d
                  ·
                    have : d = 177830 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177829 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177827 ≤ d
                ·
                  by_cases h : 177828 ≤ d
                  ·
                    have : d = 177828 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 29) (by norm_num)
      exact by decide
                  ·
                    have : d = 177827 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177826 ≤ d
                  ·
                    have : d = 177826 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177825 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 177809 ≤ d
          ·
            by_cases h : 177817 ≤ d
            ·
              by_cases h : 177821 ≤ d
              ·
                by_cases h : 177823 ≤ d
                ·
                  by_cases h : 177824 ≤ d
                  ·
                    have : d = 177824 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177823 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177822 ≤ d
                  ·
                    have : d = 177822 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177821 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177819 ≤ d
                ·
                  by_cases h : 177820 ≤ d
                  ·
                    have : d = 177820 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 177819 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177818 ≤ d
                  ·
                    have : d = 177818 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177817 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 177813 ≤ d
              ·
                by_cases h : 177815 ≤ d
                ·
                  by_cases h : 177816 ≤ d
                  ·
                    have : d = 177816 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177815 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177814 ≤ d
                  ·
                    have : d = 177814 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 177813 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177811 ≤ d
                ·
                  by_cases h : 177812 ≤ d
                  ·
                    have : d = 177812 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177811 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177810 ≤ d
                  ·
                    have : d = 177810 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5927) (by norm_num)
      exact by decide
                  ·
                    have : d = 177809 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 177801 ≤ d
            ·
              by_cases h : 177805 ≤ d
              ·
                by_cases h : 177807 ≤ d
                ·
                  by_cases h : 177808 ≤ d
                  ·
                    have : d = 177808 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177807 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177806 ≤ d
                  ·
                    have : d = 177806 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177805 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177803 ≤ d
                ·
                  by_cases h : 177804 ≤ d
                  ·
                    have : d = 177804 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 449) (by norm_num)
      exact by decide
                  ·
                    have : d = 177803 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177802 ≤ d
                  ·
                    have : d = 177802 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 177801 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 177797 ≤ d
              ·
                by_cases h : 177799 ≤ d
                ·
                  by_cases h : 177800 ≤ d
                  ·
                    have : d = 177800 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177799 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177798 ≤ d
                  ·
                    have : d = 177798 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 29633) (by norm_num)
      exact by decide
                  ·
                    have : d = 177797 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177795 ≤ d
                ·
                  by_cases h : 177796 ≤ d
                  ·
                    have : d = 177796 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177795 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177794 ≤ d
                  ·
                    have : d = 177794 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177793 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 177729 ≤ d
      ·
        by_cases h : 177761 ≤ d
        ·
          by_cases h : 177777 ≤ d
          ·
            by_cases h : 177785 ≤ d
            ·
              by_cases h : 177789 ≤ d
              ·
                by_cases h : 177791 ≤ d
                ·
                  by_cases h : 177792 ≤ d
                  ·
                    have : d = 177792 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 463) (by norm_num)
      exact by decide
                  ·
                    have : d = 177791 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177790 ≤ d
                  ·
                    have : d = 177790 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23) (by norm_num)
      exact by decide
                  ·
                    have : d = 177789 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177787 ≤ d
                ·
                  by_cases h : 177788 ≤ d
                  ·
                    have : d = 177788 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177787 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177786 ≤ d
                  ·
                    have : d = 177786 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177785 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 177781 ≤ d
              ·
                by_cases h : 177783 ≤ d
                ·
                  by_cases h : 177784 ≤ d
                  ·
                    have : d = 177784 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 71) (by norm_num)
      exact by decide
                  ·
                    have : d = 177783 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177782 ≤ d
                  ·
                    have : d = 177782 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177781 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177779 ≤ d
                ·
                  by_cases h : 177780 ≤ d
                  ·
                    have : d = 177780 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177779 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177778 ≤ d
                  ·
                    have : d = 177778 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 103) (by norm_num)
      exact by decide
                  ·
                    have : d = 177777 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 177769 ≤ d
            ·
              by_cases h : 177773 ≤ d
              ·
                by_cases h : 177775 ≤ d
                ·
                  by_cases h : 177776 ≤ d
                  ·
                    have : d = 177776 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177775 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177774 ≤ d
                  ·
                    have : d = 177774 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 29629) (by norm_num)
      exact by decide
                  ·
                    have : d = 177773 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177771 ≤ d
                ·
                  by_cases h : 177772 ≤ d
                  ·
                    have : d = 177772 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 907) (by norm_num)
      exact by decide
                  ·
                    have : d = 177771 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177770 ≤ d
                  ·
                    have : d = 177770 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177769 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 177765 ≤ d
              ·
                by_cases h : 177767 ≤ d
                ·
                  by_cases h : 177768 ≤ d
                  ·
                    have : d = 177768 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 823) (by norm_num)
      exact by decide
                  ·
                    have : d = 177767 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177766 ≤ d
                  ·
                    have : d = 177766 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177765 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177763 ≤ d
                ·
                  by_cases h : 177764 ≤ d
                  ·
                    have : d = 177764 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177763 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177762 ≤ d
                  ·
                    have : d = 177762 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 177761 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 177745 ≤ d
          ·
            by_cases h : 177753 ≤ d
            ·
              by_cases h : 177757 ≤ d
              ·
                by_cases h : 177759 ≤ d
                ·
                  by_cases h : 177760 ≤ d
                  ·
                    have : d = 177760 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 101) (by norm_num)
      exact by decide
                  ·
                    have : d = 177759 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177758 ≤ d
                  ·
                    have : d = 177758 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177757 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177755 ≤ d
                ·
                  by_cases h : 177756 ≤ d
                  ·
                    have : d = 177756 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177755 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177754 ≤ d
                  ·
                    have : d = 177754 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 31) (by norm_num)
      exact by decide
                  ·
                    have : d = 177753 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 177749 ≤ d
              ·
                by_cases h : 177751 ≤ d
                ·
                  by_cases h : 177752 ≤ d
                  ·
                    have : d = 177752 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177751 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177750 ≤ d
                  ·
                    have : d = 177750 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 79) (by norm_num)
      exact by decide
                  ·
                    have : d = 177749 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177747 ≤ d
                ·
                  by_cases h : 177748 ≤ d
                  ·
                    have : d = 177748 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 37) (by norm_num)
      exact by decide
                  ·
                    have : d = 177747 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177746 ≤ d
                  ·
                    have : d = 177746 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177745 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 177737 ≤ d
            ·
              by_cases h : 177741 ≤ d
              ·
                by_cases h : 177743 ≤ d
                ·
                  by_cases h : 177744 ≤ d
                  ·
                    have : d = 177744 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23) (by norm_num)
      exact by decide
                  ·
                    have : d = 177743 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177742 ≤ d
                  ·
                    have : d = 177742 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177741 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177739 ≤ d
                ·
                  by_cases h : 177740 ≤ d
                  ·
                    have : d = 177740 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177739 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177738 ≤ d
                  ·
                    have : d = 177738 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177737 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 177733 ≤ d
              ·
                by_cases h : 177735 ≤ d
                ·
                  by_cases h : 177736 ≤ d
                  ·
                    have : d = 177736 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177735 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177734 ≤ d
                  ·
                    have : d = 177734 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177733 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177731 ≤ d
                ·
                  by_cases h : 177732 ≤ d
                  ·
                    have : d = 177732 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 4937) (by norm_num)
      exact by decide
                  ·
                    have : d = 177731 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177730 ≤ d
                  ·
                    have : d = 177730 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2539) (by norm_num)
      exact by decide
                  ·
                    have : d = 177729 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 177697 ≤ d
        ·
          by_cases h : 177713 ≤ d
          ·
            by_cases h : 177721 ≤ d
            ·
              by_cases h : 177725 ≤ d
              ·
                by_cases h : 177727 ≤ d
                ·
                  by_cases h : 177728 ≤ d
                  ·
                    have : d = 177728 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177727 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177726 ≤ d
                  ·
                    have : d = 177726 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177725 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177723 ≤ d
                ·
                  by_cases h : 177724 ≤ d
                  ·
                    have : d = 177724 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177723 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177722 ≤ d
                  ·
                    have : d = 177722 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177721 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 177717 ≤ d
              ·
                by_cases h : 177719 ≤ d
                ·
                  by_cases h : 177720 ≤ d
                  ·
                    have : d = 177720 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177719 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177718 ≤ d
                  ·
                    have : d = 177718 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 177717 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177715 ≤ d
                ·
                  by_cases h : 177716 ≤ d
                  ·
                    have : d = 177716 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177715 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177714 ≤ d
                  ·
                    have : d = 177714 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1097) (by norm_num)
      exact by decide
                  ·
                    have : d = 177713 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 177705 ≤ d
            ·
              by_cases h : 177709 ≤ d
              ·
                by_cases h : 177711 ≤ d
                ·
                  by_cases h : 177712 ≤ d
                  ·
                    have : d = 177712 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 29) (by norm_num)
      exact by decide
                  ·
                    have : d = 177711 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177710 ≤ d
                  ·
                    have : d = 177710 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177709 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177707 ≤ d
                ·
                  by_cases h : 177708 ≤ d
                  ·
                    have : d = 177708 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 59) (by norm_num)
      exact by decide
                  ·
                    have : d = 177707 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177706 ≤ d
                  ·
                    have : d = 177706 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177705 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 177701 ≤ d
              ·
                by_cases h : 177703 ≤ d
                ·
                  by_cases h : 177704 ≤ d
                  ·
                    have : d = 177704 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177703 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177702 ≤ d
                  ·
                    have : d = 177702 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 4231) (by norm_num)
      exact by decide
                  ·
                    have : d = 177701 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177699 ≤ d
                ·
                  by_cases h : 177700 ≤ d
                  ·
                    have : d = 177700 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1777) (by norm_num)
      exact by decide
                  ·
                    have : d = 177699 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177698 ≤ d
                  ·
                    have : d = 177698 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177697 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 177681 ≤ d
          ·
            by_cases h : 177689 ≤ d
            ·
              by_cases h : 177693 ≤ d
              ·
                by_cases h : 177695 ≤ d
                ·
                  by_cases h : 177696 ≤ d
                  ·
                    have : d = 177696 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177695 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177694 ≤ d
                  ·
                    have : d = 177694 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 41) (by norm_num)
      exact by decide
                  ·
                    have : d = 177693 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177691 ≤ d
                ·
                  by_cases h : 177692 ≤ d
                  ·
                    have : d = 177692 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177691 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177690 ≤ d
                  ·
                    have : d = 177690 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5923) (by norm_num)
      exact by decide
                  ·
                    have : d = 177689 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 177685 ≤ d
              ·
                by_cases h : 177687 ≤ d
                ·
                  by_cases h : 177688 ≤ d
                  ·
                    have : d = 177688 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 177687 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177686 ≤ d
                  ·
                    have : d = 177686 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177685 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177683 ≤ d
                ·
                  by_cases h : 177684 ≤ d
                  ·
                    have : d = 177684 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 177683 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177682 ≤ d
                  ·
                    have : d = 177682 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177681 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 177673 ≤ d
            ·
              by_cases h : 177677 ≤ d
              ·
                by_cases h : 177679 ≤ d
                ·
                  by_cases h : 177680 ≤ d
                  ·
                    have : d = 177680 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177679 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177678 ≤ d
                  ·
                    have : d = 177678 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 9871) (by norm_num)
      exact by decide
                  ·
                    have : d = 177677 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177675 ≤ d
                ·
                  by_cases h : 177676 ≤ d
                  ·
                    have : d = 177676 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177675 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177674 ≤ d
                  ·
                    have : d = 177674 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177673 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 177669 ≤ d
              ·
                by_cases h : 177671 ≤ d
                ·
                  by_cases h : 177672 ≤ d
                  ·
                    have : d = 177672 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 673) (by norm_num)
      exact by decide
                  ·
                    have : d = 177671 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177670 ≤ d
                  ·
                    have : d = 177670 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 109) (by norm_num)
      exact by decide
                  ·
                    have : d = 177669 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 177667 ≤ d
                ·
                  by_cases h : 177668 ≤ d
                  ·
                    have : d = 177668 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177667 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 177666 ≤ d
                  ·
                    have : d = 177666 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 177665 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩

end PrimeFactorUnimodality
