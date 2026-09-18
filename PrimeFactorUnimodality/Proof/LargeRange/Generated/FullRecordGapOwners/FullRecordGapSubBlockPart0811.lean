import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapFermat

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

theorem fullRecordGapSubBlock_part0811 (d : Nat) (414721 ≤ d) (d ≤ 415232) : ¬(recordGapCenter - d).Prime := by
  by_cases h : 414977 ≤ d
  ·
    by_cases h : 415105 ≤ d
    ·
      by_cases h : 415169 ≤ d
      ·
        by_cases h : 415201 ≤ d
        ·
          by_cases h : 415217 ≤ d
          ·
            by_cases h : 415225 ≤ d
            ·
              by_cases h : 415229 ≤ d
              ·
                by_cases h : 415231 ≤ d
                ·
                  by_cases h : 415232 ≤ d
                  ·
                    have : d = 415232 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415231 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415230 ≤ d
                  ·
                    have : d = 415230 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13841) (by norm_num)
      exact by decide
                  ·
                    have : d = 415229 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 415227 ≤ d
                ·
                  by_cases h : 415228 ≤ d
                  ·
                    have : d = 415228 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 9437) (by norm_num)
      exact by decide
                  ·
                    have : d = 415227 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415226 ≤ d
                  ·
                    have : d = 415226 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415225 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 415221 ≤ d
              ·
                by_cases h : 415223 ≤ d
                ·
                  by_cases h : 415224 ≤ d
                  ·
                    have : d = 415224 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 73) (by norm_num)
      exact by decide
                  ·
                    have : d = 415223 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415222 ≤ d
                  ·
                    have : d = 415222 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 29) (by norm_num)
      exact by decide
                  ·
                    have : d = 415221 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 415219 ≤ d
                ·
                  by_cases h : 415220 ≤ d
                  ·
                    have : d = 415220 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415219 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415218 ≤ d
                  ·
                    have : d = 415218 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 41833437409) (by norm_num)
      right
      exact ⟨415218, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415217 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 415209 ≤ d
            ·
              by_cases h : 415213 ≤ d
              ·
                by_cases h : 415215 ≤ d
                ·
                  by_cases h : 415216 ≤ d
                  ·
                    have : d = 415216 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415215 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415214 ≤ d
                  ·
                    have : d = 415214 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415213 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 415211 ≤ d
                ·
                  by_cases h : 415212 ≤ d
                  ·
                    have : d = 415212 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 4943) (by norm_num)
      exact by decide
                  ·
                    have : d = 415211 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415210 ≤ d
                  ·
                    have : d = 415210 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415209 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 415205 ≤ d
              ·
                by_cases h : 415207 ≤ d
                ·
                  by_cases h : 415208 ≤ d
                  ·
                    have : d = 415208 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415207 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415206 ≤ d
                  ·
                    have : d = 415206 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415205 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 415203 ≤ d
                ·
                  by_cases h : 415204 ≤ d
                  ·
                    have : d = 415204 := by omega
                    subst d
      exact fullRecordGapTerm00511_not_prime
                  ·
                    have : d = 415203 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415202 ≤ d
                  ·
                    have : d = 415202 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415201 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 415185 ≤ d
          ·
            by_cases h : 415193 ≤ d
            ·
              by_cases h : 415197 ≤ d
              ·
                by_cases h : 415199 ≤ d
                ·
                  by_cases h : 415200 ≤ d
                  ·
                    have : d = 415200 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 173) (by norm_num)
      exact by decide
                  ·
                    have : d = 415199 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415198 ≤ d
                  ·
                    have : d = 415198 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 47) (by norm_num)
      exact by decide
                  ·
                    have : d = 415197 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 415195 ≤ d
                ·
                  by_cases h : 415196 ≤ d
                  ·
                    have : d = 415196 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415195 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415194 ≤ d
                  ·
                    have : d = 415194 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 415193 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 415189 ≤ d
              ·
                by_cases h : 415191 ≤ d
                ·
                  by_cases h : 415192 ≤ d
                  ·
                    have : d = 415192 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415191 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415190 ≤ d
                  ·
                    have : d = 415190 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415189 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 415187 ≤ d
                ·
                  by_cases h : 415188 ≤ d
                  ·
                    have : d = 415188 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415187 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415186 ≤ d
                  ·
                    have : d = 415186 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415185 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 415177 ≤ d
            ·
              by_cases h : 415181 ≤ d
              ·
                by_cases h : 415183 ≤ d
                ·
                  by_cases h : 415184 ≤ d
                  ·
                    have : d = 415184 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415183 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415182 ≤ d
                  ·
                    have : d = 415182 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 43199983) (by norm_num)
      right
      exact ⟨415182, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415181 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 415179 ≤ d
                ·
                  by_cases h : 415180 ≤ d
                  ·
                    have : d = 415180 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 20759) (by norm_num)
      exact by decide
                  ·
                    have : d = 415179 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415178 ≤ d
                  ·
                    have : d = 415178 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415177 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 415173 ≤ d
              ·
                by_cases h : 415175 ≤ d
                ·
                  by_cases h : 415176 ≤ d
                  ·
                    have : d = 415176 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415175 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415174 ≤ d
                  ·
                    have : d = 415174 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 415173 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 415171 ≤ d
                ·
                  by_cases h : 415172 ≤ d
                  ·
                    have : d = 415172 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415171 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415170 ≤ d
                  ·
                    have : d = 415170 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 659) (by norm_num)
      exact by decide
                  ·
                    have : d = 415169 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 415137 ≤ d
        ·
          by_cases h : 415153 ≤ d
          ·
            by_cases h : 415161 ≤ d
            ·
              by_cases h : 415165 ≤ d
              ·
                by_cases h : 415167 ≤ d
                ·
                  by_cases h : 415168 ≤ d
                  ·
                    have : d = 415168 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 415167 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415166 ≤ d
                  ·
                    have : d = 415166 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415165 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 415163 ≤ d
                ·
                  by_cases h : 415164 ≤ d
                  ·
                    have : d = 415164 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415163 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415162 ≤ d
                  ·
                    have : d = 415162 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 113) (by norm_num)
      exact by decide
                  ·
                    have : d = 415161 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 415157 ≤ d
              ·
                by_cases h : 415159 ≤ d
                ·
                  by_cases h : 415160 ≤ d
                  ·
                    have : d = 415160 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415159 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415158 ≤ d
                  ·
                    have : d = 415158 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2916583) (by norm_num)
      right
      exact ⟨415158, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415157 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 415155 ≤ d
                ·
                  by_cases h : 415156 ≤ d
                  ·
                    have : d = 415156 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415155 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415154 ≤ d
                  ·
                    have : d = 415154 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415153 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 415145 ≤ d
            ·
              by_cases h : 415149 ≤ d
              ·
                by_cases h : 415151 ≤ d
                ·
                  by_cases h : 415152 ≤ d
                  ·
                    have : d = 415152 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 31) (by norm_num)
      exact by decide
                  ·
                    have : d = 415151 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415150 ≤ d
                  ·
                    have : d = 415150 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415149 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 415147 ≤ d
                ·
                  by_cases h : 415148 ≤ d
                  ·
                    have : d = 415148 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415147 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415146 ≤ d
                  ·
                    have : d = 415146 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415145 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 415141 ≤ d
              ·
                by_cases h : 415143 ≤ d
                ·
                  by_cases h : 415144 ≤ d
                  ·
                    have : d = 415144 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415143 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415142 ≤ d
                  ·
                    have : d = 415142 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415141 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 415139 ≤ d
                ·
                  by_cases h : 415140 ≤ d
                  ·
                    have : d = 415140 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 415139 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415138 ≤ d
                  ·
                    have : d = 415138 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23178371) (by norm_num)
      right
      exact ⟨415138, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415137 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 415121 ≤ d
          ·
            by_cases h : 415129 ≤ d
            ·
              by_cases h : 415133 ≤ d
              ·
                by_cases h : 415135 ≤ d
                ·
                  by_cases h : 415136 ≤ d
                  ·
                    have : d = 415136 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415135 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415134 ≤ d
                  ·
                    have : d = 415134 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23063) (by norm_num)
      exact by decide
                  ·
                    have : d = 415133 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 415131 ≤ d
                ·
                  by_cases h : 415132 ≤ d
                  ·
                    have : d = 415132 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 67) (by norm_num)
      exact by decide
                  ·
                    have : d = 415131 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415130 ≤ d
                  ·
                    have : d = 415130 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415129 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 415125 ≤ d
              ·
                by_cases h : 415127 ≤ d
                ·
                  by_cases h : 415128 ≤ d
                  ·
                    have : d = 415128 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 353) (by norm_num)
      exact by decide
                  ·
                    have : d = 415127 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415126 ≤ d
                  ·
                    have : d = 415126 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415125 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 415123 ≤ d
                ·
                  by_cases h : 415124 ≤ d
                  ·
                    have : d = 415124 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415123 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415122 ≤ d
                  ·
                    have : d = 415122 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415121 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 415113 ≤ d
            ·
              by_cases h : 415117 ≤ d
              ·
                by_cases h : 415119 ≤ d
                ·
                  by_cases h : 415120 ≤ d
                  ·
                    have : d = 415120 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5189) (by norm_num)
      exact by decide
                  ·
                    have : d = 415119 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415118 ≤ d
                  ·
                    have : d = 415118 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415117 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 415115 ≤ d
                ·
                  by_cases h : 415116 ≤ d
                  ·
                    have : d = 415116 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415115 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415114 ≤ d
                  ·
                    have : d = 415114 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 149) (by norm_num)
      exact by decide
                  ·
                    have : d = 415113 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 415109 ≤ d
              ·
                by_cases h : 415111 ≤ d
                ·
                  by_cases h : 415112 ≤ d
                  ·
                    have : d = 415112 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415111 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415110 ≤ d
                  ·
                    have : d = 415110 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 101) (by norm_num)
      exact by decide
                  ·
                    have : d = 415109 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 415107 ≤ d
                ·
                  by_cases h : 415108 ≤ d
                  ·
                    have : d = 415108 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415107 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415106 ≤ d
                  ·
                    have : d = 415106 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415105 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 415041 ≤ d
      ·
        by_cases h : 415073 ≤ d
        ·
          by_cases h : 415089 ≤ d
          ·
            by_cases h : 415097 ≤ d
            ·
              by_cases h : 415101 ≤ d
              ·
                by_cases h : 415103 ≤ d
                ·
                  by_cases h : 415104 ≤ d
                  ·
                    have : d = 415104 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23) (by norm_num)
      exact by decide
                  ·
                    have : d = 415103 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415102 ≤ d
                  ·
                    have : d = 415102 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 934229) (by norm_num)
      right
      exact ⟨415102, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415101 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 415099 ≤ d
                ·
                  by_cases h : 415100 ≤ d
                  ·
                    have : d = 415100 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415099 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415098 ≤ d
                  ·
                    have : d = 415098 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7687) (by norm_num)
      exact by decide
                  ·
                    have : d = 415097 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 415093 ≤ d
              ·
                by_cases h : 415095 ≤ d
                ·
                  by_cases h : 415096 ≤ d
                  ·
                    have : d = 415096 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415095 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415094 ≤ d
                  ·
                    have : d = 415094 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415093 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 415091 ≤ d
                ·
                  by_cases h : 415092 ≤ d
                  ·
                    have : d = 415092 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 34591) (by norm_num)
      exact by decide
                  ·
                    have : d = 415091 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415090 ≤ d
                  ·
                    have : d = 415090 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 415089 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 415081 ≤ d
            ·
              by_cases h : 415085 ≤ d
              ·
                by_cases h : 415087 ≤ d
                ·
                  by_cases h : 415088 ≤ d
                  ·
                    have : d = 415088 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415087 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415086 ≤ d
                  ·
                    have : d = 415086 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415085 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 415083 ≤ d
                ·
                  by_cases h : 415084 ≤ d
                  ·
                    have : d = 415084 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 41) (by norm_num)
      exact by decide
                  ·
                    have : d = 415083 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415082 ≤ d
                  ·
                    have : d = 415082 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415081 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 415077 ≤ d
              ·
                by_cases h : 415079 ≤ d
                ·
                  by_cases h : 415080 ≤ d
                  ·
                    have : d = 415080 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415079 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415078 ≤ d
                  ·
                    have : d = 415078 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415077 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 415075 ≤ d
                ·
                  by_cases h : 415076 ≤ d
                  ·
                    have : d = 415076 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415075 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415074 ≤ d
                  ·
                    have : d = 415074 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 415073 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 415057 ≤ d
          ·
            by_cases h : 415065 ≤ d
            ·
              by_cases h : 415069 ≤ d
              ·
                by_cases h : 415071 ≤ d
                ·
                  by_cases h : 415072 ≤ d
                  ·
                    have : d = 415072 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 415071 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415070 ≤ d
                  ·
                    have : d = 415070 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415069 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 415067 ≤ d
                ·
                  by_cases h : 415068 ≤ d
                  ·
                    have : d = 415068 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 34589) (by norm_num)
      exact by decide
                  ·
                    have : d = 415067 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415066 ≤ d
                  ·
                    have : d = 415066 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415065 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 415061 ≤ d
              ·
                by_cases h : 415063 ≤ d
                ·
                  by_cases h : 415064 ≤ d
                  ·
                    have : d = 415064 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415063 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415062 ≤ d
                  ·
                    have : d = 415062 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23059) (by norm_num)
      exact by decide
                  ·
                    have : d = 415061 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 415059 ≤ d
                ·
                  by_cases h : 415060 ≤ d
                  ·
                    have : d = 415060 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 20753) (by norm_num)
      exact by decide
                  ·
                    have : d = 415059 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415058 ≤ d
                  ·
                    have : d = 415058 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415057 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 415049 ≤ d
            ·
              by_cases h : 415053 ≤ d
              ·
                by_cases h : 415055 ≤ d
                ·
                  by_cases h : 415056 ≤ d
                  ·
                    have : d = 415056 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415055 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415054 ≤ d
                  ·
                    have : d = 415054 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 139) (by norm_num)
      exact by decide
                  ·
                    have : d = 415053 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 415051 ≤ d
                ·
                  by_cases h : 415052 ≤ d
                  ·
                    have : d = 415052 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415051 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415050 ≤ d
                  ·
                    have : d = 415050 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2767) (by norm_num)
      exact by decide
                  ·
                    have : d = 415049 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 415045 ≤ d
              ·
                by_cases h : 415047 ≤ d
                ·
                  by_cases h : 415048 ≤ d
                  ·
                    have : d = 415048 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 29) (by norm_num)
      exact by decide
                  ·
                    have : d = 415047 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415046 ≤ d
                  ·
                    have : d = 415046 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415045 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 415043 ≤ d
                ·
                  by_cases h : 415044 ≤ d
                  ·
                    have : d = 415044 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 61) (by norm_num)
      exact by decide
                  ·
                    have : d = 415043 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415042 ≤ d
                  ·
                    have : d = 415042 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3864397351) (by norm_num)
      right
      exact ⟨415042, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415041 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 415009 ≤ d
        ·
          by_cases h : 415025 ≤ d
          ·
            by_cases h : 415033 ≤ d
            ·
              by_cases h : 415037 ≤ d
              ·
                by_cases h : 415039 ≤ d
                ·
                  by_cases h : 415040 ≤ d
                  ·
                    have : d = 415040 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415039 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415038 ≤ d
                  ·
                    have : d = 415038 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415037 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 415035 ≤ d
                ·
                  by_cases h : 415036 ≤ d
                  ·
                    have : d = 415036 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415035 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415034 ≤ d
                  ·
                    have : d = 415034 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415033 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 415029 ≤ d
              ·
                by_cases h : 415031 ≤ d
                ·
                  by_cases h : 415032 ≤ d
                  ·
                    have : d = 415032 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17293) (by norm_num)
      exact by decide
                  ·
                    have : d = 415031 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415030 ≤ d
                  ·
                    have : d = 415030 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2006677) (by norm_num)
      right
      exact ⟨415030, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415029 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 415027 ≤ d
                ·
                  by_cases h : 415028 ≤ d
                  ·
                    have : d = 415028 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415027 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415026 ≤ d
                  ·
                    have : d = 415026 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415025 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 415017 ≤ d
            ·
              by_cases h : 415021 ≤ d
              ·
                by_cases h : 415023 ≤ d
                ·
                  by_cases h : 415024 ≤ d
                  ·
                    have : d = 415024 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415023 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415022 ≤ d
                  ·
                    have : d = 415022 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415021 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 415019 ≤ d
                ·
                  by_cases h : 415020 ≤ d
                  ·
                    have : d = 415020 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 6917) (by norm_num)
      exact by decide
                  ·
                    have : d = 415019 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415018 ≤ d
                  ·
                    have : d = 415018 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 155202623) (by norm_num)
      right
      exact ⟨415018, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415017 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 415013 ≤ d
              ·
                by_cases h : 415015 ≤ d
                ·
                  by_cases h : 415016 ≤ d
                  ·
                    have : d = 415016 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415015 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415014 ≤ d
                  ·
                    have : d = 415014 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 263) (by norm_num)
      exact by decide
                  ·
                    have : d = 415013 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 415011 ≤ d
                ·
                  by_cases h : 415012 ≤ d
                  ·
                    have : d = 415012 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415011 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415010 ≤ d
                  ·
                    have : d = 415010 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415009 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 414993 ≤ d
          ·
            by_cases h : 415001 ≤ d
            ·
              by_cases h : 415005 ≤ d
              ·
                by_cases h : 415007 ≤ d
                ·
                  by_cases h : 415008 ≤ d
                  ·
                    have : d = 415008 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 131) (by norm_num)
      exact by decide
                  ·
                    have : d = 415007 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415006 ≤ d
                  ·
                    have : d = 415006 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415005 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 415003 ≤ d
                ·
                  by_cases h : 415004 ≤ d
                  ·
                    have : d = 415004 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 415003 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 415002 ≤ d
                  ·
                    have : d = 415002 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 41) (by norm_num)
      exact by decide
                  ·
                    have : d = 415001 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 414997 ≤ d
              ·
                by_cases h : 414999 ≤ d
                ·
                  by_cases h : 415000 ≤ d
                  ·
                    have : d = 415000 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 83) (by norm_num)
      exact by decide
                  ·
                    have : d = 414999 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414998 ≤ d
                  ·
                    have : d = 414998 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414997 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414995 ≤ d
                ·
                  by_cases h : 414996 ≤ d
                  ·
                    have : d = 414996 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414995 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414994 ≤ d
                  ·
                    have : d = 414994 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 451039) (by norm_num)
      right
      exact ⟨414994, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414993 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 414985 ≤ d
            ·
              by_cases h : 414989 ≤ d
              ·
                by_cases h : 414991 ≤ d
                ·
                  by_cases h : 414992 ≤ d
                  ·
                    have : d = 414992 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414991 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414990 ≤ d
                  ·
                    have : d = 414990 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414989 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414987 ≤ d
                ·
                  by_cases h : 414988 ≤ d
                  ·
                    have : d = 414988 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 14821) (by norm_num)
      exact by decide
                  ·
                    have : d = 414987 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414986 ≤ d
                  ·
                    have : d = 414986 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414985 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 414981 ≤ d
              ·
                by_cases h : 414983 ≤ d
                ·
                  by_cases h : 414984 ≤ d
                  ·
                    have : d = 414984 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17291) (by norm_num)
      exact by decide
                  ·
                    have : d = 414983 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414982 ≤ d
                  ·
                    have : d = 414982 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414981 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414979 ≤ d
                ·
                  by_cases h : 414980 ≤ d
                  ·
                    have : d = 414980 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414979 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414978 ≤ d
                  ·
                    have : d = 414978 := by omega
                    subst d
      exact fullRecordGapTerm00512_not_prime
                  ·
                    have : d = 414977 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
  ·
    by_cases h : 414849 ≤ d
    ·
      by_cases h : 414913 ≤ d
      ·
        by_cases h : 414945 ≤ d
        ·
          by_cases h : 414961 ≤ d
          ·
            by_cases h : 414969 ≤ d
            ·
              by_cases h : 414973 ≤ d
              ·
                by_cases h : 414975 ≤ d
                ·
                  by_cases h : 414976 ≤ d
                  ·
                    have : d = 414976 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414975 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414974 ≤ d
                  ·
                    have : d = 414974 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414973 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414971 ≤ d
                ·
                  by_cases h : 414972 ≤ d
                  ·
                    have : d = 414972 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11527) (by norm_num)
      exact by decide
                  ·
                    have : d = 414971 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414970 ≤ d
                  ·
                    have : d = 414970 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 414969 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 414965 ≤ d
              ·
                by_cases h : 414967 ≤ d
                ·
                  by_cases h : 414968 ≤ d
                  ·
                    have : d = 414968 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414967 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414966 ≤ d
                  ·
                    have : d = 414966 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414965 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414963 ≤ d
                ·
                  by_cases h : 414964 ≤ d
                  ·
                    have : d = 414964 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 9431) (by norm_num)
      exact by decide
                  ·
                    have : d = 414963 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414962 ≤ d
                  ·
                    have : d = 414962 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414961 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 414953 ≤ d
            ·
              by_cases h : 414957 ≤ d
              ·
                by_cases h : 414959 ≤ d
                ·
                  by_cases h : 414960 ≤ d
                  ·
                    have : d = 414960 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 414959 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414958 ≤ d
                  ·
                    have : d = 414958 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 28568469283) (by norm_num)
      right
      exact ⟨414958, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414957 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414955 ≤ d
                ·
                  by_cases h : 414956 ≤ d
                  ·
                    have : d = 414956 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414955 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414954 ≤ d
                  ·
                    have : d = 414954 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414953 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 414949 ≤ d
              ·
                by_cases h : 414951 ≤ d
                ·
                  by_cases h : 414952 ≤ d
                  ·
                    have : d = 414952 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3911779) (by norm_num)
      right
      exact ⟨414952, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414951 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414950 ≤ d
                  ·
                    have : d = 414950 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414949 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414947 ≤ d
                ·
                  by_cases h : 414948 ≤ d
                  ·
                    have : d = 414948 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 151) (by norm_num)
      exact by decide
                  ·
                    have : d = 414947 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414946 ≤ d
                  ·
                    have : d = 414946 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414945 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 414929 ≤ d
          ·
            by_cases h : 414937 ≤ d
            ·
              by_cases h : 414941 ≤ d
              ·
                by_cases h : 414943 ≤ d
                ·
                  by_cases h : 414944 ≤ d
                  ·
                    have : d = 414944 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414943 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414942 ≤ d
                  ·
                    have : d = 414942 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 6287) (by norm_num)
      exact by decide
                  ·
                    have : d = 414941 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414939 ≤ d
                ·
                  by_cases h : 414940 ≤ d
                  ·
                    have : d = 414940 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414939 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414938 ≤ d
                  ·
                    have : d = 414938 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414937 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 414933 ≤ d
              ·
                by_cases h : 414935 ≤ d
                ·
                  by_cases h : 414936 ≤ d
                  ·
                    have : d = 414936 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414935 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414934 ≤ d
                  ·
                    have : d = 414934 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 414933 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414931 ≤ d
                ·
                  by_cases h : 414932 ≤ d
                  ·
                    have : d = 414932 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414931 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414930 ≤ d
                  ·
                    have : d = 414930 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13831) (by norm_num)
      exact by decide
                  ·
                    have : d = 414929 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 414921 ≤ d
            ·
              by_cases h : 414925 ≤ d
              ·
                by_cases h : 414927 ≤ d
                ·
                  by_cases h : 414928 ≤ d
                  ·
                    have : d = 414928 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 25933) (by norm_num)
      exact by decide
                  ·
                    have : d = 414927 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414926 ≤ d
                  ·
                    have : d = 414926 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414925 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414923 ≤ d
                ·
                  by_cases h : 414924 ≤ d
                  ·
                    have : d = 414924 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414923 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414922 ≤ d
                  ·
                    have : d = 414922 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 414921 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 414917 ≤ d
              ·
                by_cases h : 414919 ≤ d
                ·
                  by_cases h : 414920 ≤ d
                  ·
                    have : d = 414920 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414919 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414918 ≤ d
                  ·
                    have : d = 414918 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 37) (by norm_num)
      exact by decide
                  ·
                    have : d = 414917 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414915 ≤ d
                ·
                  by_cases h : 414916 ≤ d
                  ·
                    have : d = 414916 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414915 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414914 ≤ d
                  ·
                    have : d = 414914 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414913 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 414881 ≤ d
        ·
          by_cases h : 414897 ≤ d
          ·
            by_cases h : 414905 ≤ d
            ·
              by_cases h : 414909 ≤ d
              ·
                by_cases h : 414911 ≤ d
                ·
                  by_cases h : 414912 ≤ d
                  ·
                    have : d = 414912 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414911 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414910 ≤ d
                  ·
                    have : d = 414910 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 41491) (by norm_num)
      exact by decide
                  ·
                    have : d = 414909 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414907 ≤ d
                ·
                  by_cases h : 414908 ≤ d
                  ·
                    have : d = 414908 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414907 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414906 ≤ d
                  ·
                    have : d = 414906 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414905 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 414901 ≤ d
              ·
                by_cases h : 414903 ≤ d
                ·
                  by_cases h : 414904 ≤ d
                  ·
                    have : d = 414904 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 31) (by norm_num)
      exact by decide
                  ·
                    have : d = 414903 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414902 ≤ d
                  ·
                    have : d = 414902 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414901 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414899 ≤ d
                ·
                  by_cases h : 414900 ≤ d
                  ·
                    have : d = 414900 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 461) (by norm_num)
      exact by decide
                  ·
                    have : d = 414899 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414898 ≤ d
                  ·
                    have : d = 414898 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414897 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 414889 ≤ d
            ·
              by_cases h : 414893 ≤ d
              ·
                by_cases h : 414895 ≤ d
                ·
                  by_cases h : 414896 ≤ d
                  ·
                    have : d = 414896 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414895 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414894 ≤ d
                  ·
                    have : d = 414894 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 119724533) (by norm_num)
      right
      exact ⟨414894, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414893 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414891 ≤ d
                ·
                  by_cases h : 414892 ≤ d
                  ·
                    have : d = 414892 := by omega
                    subst d
      exact fullRecordGapTerm00513_not_prime
                  ·
                    have : d = 414891 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414890 ≤ d
                  ·
                    have : d = 414890 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414889 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 414885 ≤ d
              ·
                by_cases h : 414887 ≤ d
                ·
                  by_cases h : 414888 ≤ d
                  ·
                    have : d = 414888 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 59) (by norm_num)
      exact by decide
                  ·
                    have : d = 414887 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414886 ≤ d
                  ·
                    have : d = 414886 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414885 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414883 ≤ d
                ·
                  by_cases h : 414884 ≤ d
                  ·
                    have : d = 414884 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414883 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414882 ≤ d
                  ·
                    have : d = 414882 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 414881 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 414865 ≤ d
          ·
            by_cases h : 414873 ≤ d
            ·
              by_cases h : 414877 ≤ d
              ·
                by_cases h : 414879 ≤ d
                ·
                  by_cases h : 414880 ≤ d
                  ·
                    have : d = 414880 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414879 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414878 ≤ d
                  ·
                    have : d = 414878 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414877 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414875 ≤ d
                ·
                  by_cases h : 414876 ≤ d
                  ·
                    have : d = 414876 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414875 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414874 ≤ d
                  ·
                    have : d = 414874 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23) (by norm_num)
      exact by decide
                  ·
                    have : d = 414873 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 414869 ≤ d
              ·
                by_cases h : 414871 ≤ d
                ·
                  by_cases h : 414872 ≤ d
                  ·
                    have : d = 414872 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414871 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414870 ≤ d
                  ·
                    have : d = 414870 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414869 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414867 ≤ d
                ·
                  by_cases h : 414868 ≤ d
                  ·
                    have : d = 414868 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 414867 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414866 ≤ d
                  ·
                    have : d = 414866 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414865 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 414857 ≤ d
            ·
              by_cases h : 414861 ≤ d
              ·
                by_cases h : 414863 ≤ d
                ·
                  by_cases h : 414864 ≤ d
                  ·
                    have : d = 414864 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 43) (by norm_num)
      exact by decide
                  ·
                    have : d = 414863 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414862 ≤ d
                  ·
                    have : d = 414862 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 29633) (by norm_num)
      exact by decide
                  ·
                    have : d = 414861 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414859 ≤ d
                ·
                  by_cases h : 414860 ≤ d
                  ·
                    have : d = 414860 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414859 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414858 ≤ d
                  ·
                    have : d = 414858 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414857 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 414853 ≤ d
              ·
                by_cases h : 414855 ≤ d
                ·
                  by_cases h : 414856 ≤ d
                  ·
                    have : d = 414856 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414855 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414854 ≤ d
                  ·
                    have : d = 414854 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414853 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414851 ≤ d
                ·
                  by_cases h : 414852 ≤ d
                  ·
                    have : d = 414852 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 181) (by norm_num)
      exact by decide
                  ·
                    have : d = 414851 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414850 ≤ d
                  ·
                    have : d = 414850 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 8297) (by norm_num)
      exact by decide
                  ·
                    have : d = 414849 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 414785 ≤ d
      ·
        by_cases h : 414817 ≤ d
        ·
          by_cases h : 414833 ≤ d
          ·
            by_cases h : 414841 ≤ d
            ·
              by_cases h : 414845 ≤ d
              ·
                by_cases h : 414847 ≤ d
                ·
                  by_cases h : 414848 ≤ d
                  ·
                    have : d = 414848 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414847 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414846 ≤ d
                  ·
                    have : d = 414846 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414845 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414843 ≤ d
                ·
                  by_cases h : 414844 ≤ d
                  ·
                    have : d = 414844 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 37) (by norm_num)
      exact by decide
                  ·
                    have : d = 414843 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414842 ≤ d
                  ·
                    have : d = 414842 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414841 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 414837 ≤ d
              ·
                by_cases h : 414839 ≤ d
                ·
                  by_cases h : 414840 ≤ d
                  ·
                    have : d = 414840 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3457) (by norm_num)
      exact by decide
                  ·
                    have : d = 414839 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414838 ≤ d
                  ·
                    have : d = 414838 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 41) (by norm_num)
      exact by decide
                  ·
                    have : d = 414837 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414835 ≤ d
                ·
                  by_cases h : 414836 ≤ d
                  ·
                    have : d = 414836 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414835 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414834 ≤ d
                  ·
                    have : d = 414834 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 414833 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 414825 ≤ d
            ·
              by_cases h : 414829 ≤ d
              ·
                by_cases h : 414831 ≤ d
                ·
                  by_cases h : 414832 ≤ d
                  ·
                    have : d = 414832 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2357) (by norm_num)
      exact by decide
                  ·
                    have : d = 414831 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414830 ≤ d
                  ·
                    have : d = 414830 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414829 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414827 ≤ d
                ·
                  by_cases h : 414828 ≤ d
                  ·
                    have : d = 414828 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414827 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414826 ≤ d
                  ·
                    have : d = 414826 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414825 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 414821 ≤ d
              ·
                by_cases h : 414823 ≤ d
                ·
                  by_cases h : 414824 ≤ d
                  ·
                    have : d = 414824 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414823 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414822 ≤ d
                  ·
                    have : d = 414822 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 47) (by norm_num)
      exact by decide
                  ·
                    have : d = 414821 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414819 ≤ d
                ·
                  by_cases h : 414820 ≤ d
                  ·
                    have : d = 414820 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2963) (by norm_num)
      exact by decide
                  ·
                    have : d = 414819 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414818 ≤ d
                  ·
                    have : d = 414818 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414817 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 414801 ≤ d
          ·
            by_cases h : 414809 ≤ d
            ·
              by_cases h : 414813 ≤ d
              ·
                by_cases h : 414815 ≤ d
                ·
                  by_cases h : 414816 ≤ d
                  ·
                    have : d = 414816 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414815 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414814 ≤ d
                  ·
                    have : d = 414814 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414813 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414811 ≤ d
                ·
                  by_cases h : 414812 ≤ d
                  ·
                    have : d = 414812 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414811 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414810 ≤ d
                  ·
                    have : d = 414810 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 419) (by norm_num)
      exact by decide
                  ·
                    have : d = 414809 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 414805 ≤ d
              ·
                by_cases h : 414807 ≤ d
                ·
                  by_cases h : 414808 ≤ d
                  ·
                    have : d = 414808 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 414807 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414806 ≤ d
                  ·
                    have : d = 414806 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414805 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414803 ≤ d
                ·
                  by_cases h : 414804 ≤ d
                  ·
                    have : d = 414804 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 414803 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414802 ≤ d
                  ·
                    have : d = 414802 := by omega
                    subst d
      exact fullRecordGapTerm00514_not_prime
                  ·
                    have : d = 414801 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 414793 ≤ d
            ·
              by_cases h : 414797 ≤ d
              ·
                by_cases h : 414799 ≤ d
                ·
                  by_cases h : 414800 ≤ d
                  ·
                    have : d = 414800 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414799 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414798 ≤ d
                  ·
                    have : d = 414798 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 257) (by norm_num)
      exact by decide
                  ·
                    have : d = 414797 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414795 ≤ d
                ·
                  by_cases h : 414796 ≤ d
                  ·
                    have : d = 414796 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414795 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414794 ≤ d
                  ·
                    have : d = 414794 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414793 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 414789 ≤ d
              ·
                by_cases h : 414791 ≤ d
                ·
                  by_cases h : 414792 ≤ d
                  ·
                    have : d = 414792 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414791 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414790 ≤ d
                  ·
                    have : d = 414790 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 41479) (by norm_num)
      exact by decide
                  ·
                    have : d = 414789 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414787 ≤ d
                ·
                  by_cases h : 414788 ≤ d
                  ·
                    have : d = 414788 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414787 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414786 ≤ d
                  ·
                    have : d = 414786 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414785 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 414753 ≤ d
        ·
          by_cases h : 414769 ≤ d
          ·
            by_cases h : 414777 ≤ d
            ·
              by_cases h : 414781 ≤ d
              ·
                by_cases h : 414783 ≤ d
                ·
                  by_cases h : 414784 ≤ d
                  ·
                    have : d = 414784 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 6481) (by norm_num)
      exact by decide
                  ·
                    have : d = 414783 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414782 ≤ d
                  ·
                    have : d = 414782 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414781 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414779 ≤ d
                ·
                  by_cases h : 414780 ≤ d
                  ·
                    have : d = 414780 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 31) (by norm_num)
      exact by decide
                  ·
                    have : d = 414779 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414778 ≤ d
                  ·
                    have : d = 414778 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 414777 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 414773 ≤ d
              ·
                by_cases h : 414775 ≤ d
                ·
                  by_cases h : 414776 ≤ d
                  ·
                    have : d = 414776 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414775 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414774 ≤ d
                  ·
                    have : d = 414774 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7681) (by norm_num)
      exact by decide
                  ·
                    have : d = 414773 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414771 ≤ d
                ·
                  by_cases h : 414772 ≤ d
                  ·
                    have : d = 414772 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414771 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414770 ≤ d
                  ·
                    have : d = 414770 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414769 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 414761 ≤ d
            ·
              by_cases h : 414765 ≤ d
              ·
                by_cases h : 414767 ≤ d
                ·
                  by_cases h : 414768 ≤ d
                  ·
                    have : d = 414768 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 8641) (by norm_num)
      exact by decide
                  ·
                    have : d = 414767 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414766 ≤ d
                  ·
                    have : d = 414766 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414765 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414763 ≤ d
                ·
                  by_cases h : 414764 ≤ d
                  ·
                    have : d = 414764 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414763 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414762 ≤ d
                  ·
                    have : d = 414762 := by omega
                    subst d
      exact fullRecordGapTerm00515_not_prime
                  ·
                    have : d = 414761 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 414757 ≤ d
              ·
                by_cases h : 414759 ≤ d
                ·
                  by_cases h : 414760 ≤ d
                  ·
                    have : d = 414760 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 10369) (by norm_num)
      exact by decide
                  ·
                    have : d = 414759 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414758 ≤ d
                  ·
                    have : d = 414758 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414757 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414755 ≤ d
                ·
                  by_cases h : 414756 ≤ d
                  ·
                    have : d = 414756 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414755 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414754 ≤ d
                  ·
                    have : d = 414754 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 145121) (by norm_num)
      right
      exact ⟨124512, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414753 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 414737 ≤ d
          ·
            by_cases h : 414745 ≤ d
            ·
              by_cases h : 414749 ≤ d
              ·
                by_cases h : 414751 ≤ d
                ·
                  by_cases h : 414752 ≤ d
                  ·
                    have : d = 414752 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414751 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414750 ≤ d
                  ·
                    have : d = 414750 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 79) (by norm_num)
      exact by decide
                  ·
                    have : d = 414749 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414747 ≤ d
                ·
                  by_cases h : 414748 ≤ d
                  ·
                    have : d = 414748 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414747 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414746 ≤ d
                  ·
                    have : d = 414746 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414745 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 414741 ≤ d
              ·
                by_cases h : 414743 ≤ d
                ·
                  by_cases h : 414744 ≤ d
                  ·
                    have : d = 414744 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414743 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414742 ≤ d
                  ·
                    have : d = 414742 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 138337) (by norm_num)
      right
      exact ⟨138068, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414741 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414739 ≤ d
                ·
                  by_cases h : 414740 ≤ d
                  ·
                    have : d = 414740 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414739 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414738 ≤ d
                  ·
                    have : d = 414738 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23041) (by norm_num)
      exact by decide
                  ·
                    have : d = 414737 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 414729 ≤ d
            ·
              by_cases h : 414733 ≤ d
              ·
                by_cases h : 414735 ≤ d
                ·
                  by_cases h : 414736 ≤ d
                  ·
                    have : d = 414736 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414735 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414734 ≤ d
                  ·
                    have : d = 414734 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414733 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414731 ≤ d
                ·
                  by_cases h : 414732 ≤ d
                  ·
                    have : d = 414732 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 414731 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414730 ≤ d
                  ·
                    have : d = 414730 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414729 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 414725 ≤ d
              ·
                by_cases h : 414727 ≤ d
                ·
                  by_cases h : 414728 ≤ d
                  ·
                    have : d = 414728 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414727 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414726 ≤ d
                  ·
                    have : d = 414726 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414725 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 414723 ≤ d
                ·
                  by_cases h : 414724 ≤ d
                  ·
                    have : d = 414724 := by omega
                    subst d
      exact fullRecordGapTerm00516_not_prime
                  ·
                    have : d = 414723 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 414722 ≤ d
                  ·
                    have : d = 414722 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 414721 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩

end PrimeFactorUnimodality
