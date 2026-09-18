import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapFermat

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

theorem fullRecordGapSubBlock_part0149 (d : Nat) (75777 ≤ d) (d ≤ 76288) : ¬(recordGapCenter - d).Prime := by
  by_cases h : 76033 ≤ d
  ·
    by_cases h : 76161 ≤ d
    ·
      by_cases h : 76225 ≤ d
      ·
        by_cases h : 76257 ≤ d
        ·
          by_cases h : 76273 ≤ d
          ·
            by_cases h : 76281 ≤ d
            ·
              by_cases h : 76285 ≤ d
              ·
                by_cases h : 76287 ≤ d
                ·
                  by_cases h : 76288 ≤ d
                  ·
                    have : d = 76288 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 149) (by norm_num)
      exact by decide
                  ·
                    have : d = 76287 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76286 ≤ d
                  ·
                    have : d = 76286 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76285 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76283 ≤ d
                ·
                  by_cases h : 76284 ≤ d
                  ·
                    have : d = 76284 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 76283 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76282 ≤ d
                  ·
                    have : d = 76282 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 43) (by norm_num)
      exact by decide
                  ·
                    have : d = 76281 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 76277 ≤ d
              ·
                by_cases h : 76279 ≤ d
                ·
                  by_cases h : 76280 ≤ d
                  ·
                    have : d = 76280 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76279 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76278 ≤ d
                  ·
                    have : d = 76278 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76277 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76275 ≤ d
                ·
                  by_cases h : 76276 ≤ d
                  ·
                    have : d = 76276 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76275 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76274 ≤ d
                  ·
                    have : d = 76274 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76273 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 76265 ≤ d
            ·
              by_cases h : 76269 ≤ d
              ·
                by_cases h : 76271 ≤ d
                ·
                  by_cases h : 76272 ≤ d
                  ·
                    have : d = 76272 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 227) (by norm_num)
      exact by decide
                  ·
                    have : d = 76271 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76270 ≤ d
                  ·
                    have : d = 76270 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 29) (by norm_num)
      exact by decide
                  ·
                    have : d = 76269 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76267 ≤ d
                ·
                  by_cases h : 76268 ≤ d
                  ·
                    have : d = 76268 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76267 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76266 ≤ d
                  ·
                    have : d = 76266 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76265 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 76261 ≤ d
              ·
                by_cases h : 76263 ≤ d
                ·
                  by_cases h : 76264 ≤ d
                  ·
                    have : d = 76264 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 9533) (by norm_num)
      exact by decide
                  ·
                    have : d = 76263 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76262 ≤ d
                  ·
                    have : d = 76262 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76261 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76259 ≤ d
                ·
                  by_cases h : 76260 ≤ d
                  ·
                    have : d = 76260 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 31) (by norm_num)
      exact by decide
                  ·
                    have : d = 76259 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76258 ≤ d
                  ·
                    have : d = 76258 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 76257 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 76241 ≤ d
          ·
            by_cases h : 76249 ≤ d
            ·
              by_cases h : 76253 ≤ d
              ·
                by_cases h : 76255 ≤ d
                ·
                  by_cases h : 76256 ≤ d
                  ·
                    have : d = 76256 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76255 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76254 ≤ d
                  ·
                    have : d = 76254 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 71) (by norm_num)
      exact by decide
                  ·
                    have : d = 76253 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76251 ≤ d
                ·
                  by_cases h : 76252 ≤ d
                  ·
                    have : d = 76252 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76251 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76250 ≤ d
                  ·
                    have : d = 76250 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76249 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 76245 ≤ d
              ·
                by_cases h : 76247 ≤ d
                ·
                  by_cases h : 76248 ≤ d
                  ·
                    have : d = 76248 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 353) (by norm_num)
      exact by decide
                  ·
                    have : d = 76247 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76246 ≤ d
                  ·
                    have : d = 76246 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76245 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76243 ≤ d
                ·
                  by_cases h : 76244 ≤ d
                  ·
                    have : d = 76244 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76243 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76242 ≤ d
                  ·
                    have : d = 76242 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 97) (by norm_num)
      exact by decide
                  ·
                    have : d = 76241 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 76233 ≤ d
            ·
              by_cases h : 76237 ≤ d
              ·
                by_cases h : 76239 ≤ d
                ·
                  by_cases h : 76240 ≤ d
                  ·
                    have : d = 76240 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 953) (by norm_num)
      exact by decide
                  ·
                    have : d = 76239 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76238 ≤ d
                  ·
                    have : d = 76238 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76237 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76235 ≤ d
                ·
                  by_cases h : 76236 ≤ d
                  ·
                    have : d = 76236 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76235 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76234 ≤ d
                  ·
                    have : d = 76234 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76233 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 76229 ≤ d
              ·
                by_cases h : 76231 ≤ d
                ·
                  by_cases h : 76232 ≤ d
                  ·
                    have : d = 76232 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76231 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76230 ≤ d
                  ·
                    have : d = 76230 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 31884499) (by norm_num)
      right
      exact ⟨76230, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76229 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76227 ≤ d
                ·
                  by_cases h : 76228 ≤ d
                  ·
                    have : d = 76228 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 76227 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76226 ≤ d
                  ·
                    have : d = 76226 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76225 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 76193 ≤ d
        ·
          by_cases h : 76209 ≤ d
          ·
            by_cases h : 76217 ≤ d
            ·
              by_cases h : 76221 ≤ d
              ·
                by_cases h : 76223 ≤ d
                ·
                  by_cases h : 76224 ≤ d
                  ·
                    have : d = 76224 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76223 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76222 ≤ d
                  ·
                    have : d = 76222 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23) (by norm_num)
      exact by decide
                  ·
                    have : d = 76221 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76219 ≤ d
                ·
                  by_cases h : 76220 ≤ d
                  ·
                    have : d = 76220 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76219 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76218 ≤ d
                  ·
                    have : d = 76218 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 12703) (by norm_num)
      exact by decide
                  ·
                    have : d = 76217 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 76213 ≤ d
              ·
                by_cases h : 76215 ≤ d
                ·
                  by_cases h : 76216 ≤ d
                  ·
                    have : d = 76216 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76215 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76214 ≤ d
                  ·
                    have : d = 76214 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76213 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76211 ≤ d
                ·
                  by_cases h : 76212 ≤ d
                  ·
                    have : d = 76212 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76211 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76210 ≤ d
                  ·
                    have : d = 76210 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76209 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 76201 ≤ d
            ·
              by_cases h : 76205 ≤ d
              ·
                by_cases h : 76207 ≤ d
                ·
                  by_cases h : 76208 ≤ d
                  ·
                    have : d = 76208 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76207 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76206 ≤ d
                  ·
                    have : d = 76206 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76205 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76203 ≤ d
                ·
                  by_cases h : 76204 ≤ d
                  ·
                    have : d = 76204 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19051) (by norm_num)
      exact by decide
                  ·
                    have : d = 76203 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76202 ≤ d
                  ·
                    have : d = 76202 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76201 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 76197 ≤ d
              ·
                by_cases h : 76199 ≤ d
                ·
                  by_cases h : 76200 ≤ d
                  ·
                    have : d = 76200 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 127) (by norm_num)
      exact by decide
                  ·
                    have : d = 76199 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76198 ≤ d
                  ·
                    have : d = 76198 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 31) (by norm_num)
      exact by decide
                  ·
                    have : d = 76197 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76195 ≤ d
                ·
                  by_cases h : 76196 ≤ d
                  ·
                    have : d = 76196 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76195 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76194 ≤ d
                  ·
                    have : d = 76194 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 76193 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 76177 ≤ d
          ·
            by_cases h : 76185 ≤ d
            ·
              by_cases h : 76189 ≤ d
              ·
                by_cases h : 76191 ≤ d
                ·
                  by_cases h : 76192 ≤ d
                  ·
                    have : d = 76192 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2381) (by norm_num)
      exact by decide
                  ·
                    have : d = 76191 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76190 ≤ d
                  ·
                    have : d = 76190 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76189 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76187 ≤ d
                ·
                  by_cases h : 76188 ≤ d
                  ·
                    have : d = 76188 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 907) (by norm_num)
      exact by decide
                  ·
                    have : d = 76187 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76186 ≤ d
                  ·
                    have : d = 76186 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76185 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 76181 ≤ d
              ·
                by_cases h : 76183 ≤ d
                ·
                  by_cases h : 76184 ≤ d
                  ·
                    have : d = 76184 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76183 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76182 ≤ d
                  ·
                    have : d = 76182 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76181 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76179 ≤ d
                ·
                  by_cases h : 76180 ≤ d
                  ·
                    have : d = 76180 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 76179 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76178 ≤ d
                  ·
                    have : d = 76178 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76177 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 76169 ≤ d
            ·
              by_cases h : 76173 ≤ d
              ·
                by_cases h : 76175 ≤ d
                ·
                  by_cases h : 76176 ≤ d
                  ·
                    have : d = 76176 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76175 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76174 ≤ d
                  ·
                    have : d = 76174 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5441) (by norm_num)
      exact by decide
                  ·
                    have : d = 76173 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76171 ≤ d
                ·
                  by_cases h : 76172 ≤ d
                  ·
                    have : d = 76172 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76171 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76170 ≤ d
                  ·
                    have : d = 76170 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2539) (by norm_num)
      exact by decide
                  ·
                    have : d = 76169 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 76165 ≤ d
              ·
                by_cases h : 76167 ≤ d
                ·
                  by_cases h : 76168 ≤ d
                  ·
                    have : d = 76168 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76167 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76166 ≤ d
                  ·
                    have : d = 76166 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76165 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76163 ≤ d
                ·
                  by_cases h : 76164 ≤ d
                  ·
                    have : d = 76164 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 577) (by norm_num)
      exact by decide
                  ·
                    have : d = 76163 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76162 ≤ d
                  ·
                    have : d = 76162 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 113) (by norm_num)
      exact by decide
                  ·
                    have : d = 76161 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 76097 ≤ d
      ·
        by_cases h : 76129 ≤ d
        ·
          by_cases h : 76145 ≤ d
          ·
            by_cases h : 76153 ≤ d
            ·
              by_cases h : 76157 ≤ d
              ·
                by_cases h : 76159 ≤ d
                ·
                  by_cases h : 76160 ≤ d
                  ·
                    have : d = 76160 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76159 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76158 ≤ d
                  ·
                    have : d = 76158 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 4231) (by norm_num)
      exact by decide
                  ·
                    have : d = 76157 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76155 ≤ d
                ·
                  by_cases h : 76156 ≤ d
                  ·
                    have : d = 76156 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76155 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76154 ≤ d
                  ·
                    have : d = 76154 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76153 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 76149 ≤ d
              ·
                by_cases h : 76151 ≤ d
                ·
                  by_cases h : 76152 ≤ d
                  ·
                    have : d = 76152 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 76151 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76150 ≤ d
                  ·
                    have : d = 76150 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1523) (by norm_num)
      exact by decide
                  ·
                    have : d = 76149 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76147 ≤ d
                ·
                  by_cases h : 76148 ≤ d
                  ·
                    have : d = 76148 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76147 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76146 ≤ d
                  ·
                    have : d = 76146 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76145 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 76137 ≤ d
            ·
              by_cases h : 76141 ≤ d
              ·
                by_cases h : 76143 ≤ d
                ·
                  by_cases h : 76144 ≤ d
                  ·
                    have : d = 76144 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 4759) (by norm_num)
      exact by decide
                  ·
                    have : d = 76143 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76142 ≤ d
                  ·
                    have : d = 76142 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76141 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76139 ≤ d
                ·
                  by_cases h : 76140 ≤ d
                  ·
                    have : d = 76140 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76139 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76138 ≤ d
                  ·
                    have : d = 76138 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 38069) (by norm_num)
      exact by decide
                  ·
                    have : d = 76137 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 76133 ≤ d
              ·
                by_cases h : 76135 ≤ d
                ·
                  by_cases h : 76136 ≤ d
                  ·
                    have : d = 76136 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76135 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76134 ≤ d
                  ·
                    have : d = 76134 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 12689) (by norm_num)
      exact by decide
                  ·
                    have : d = 76133 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76131 ≤ d
                ·
                  by_cases h : 76132 ≤ d
                  ·
                    have : d = 76132 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2719) (by norm_num)
      exact by decide
                  ·
                    have : d = 76131 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76130 ≤ d
                  ·
                    have : d = 76130 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76129 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 76113 ≤ d
          ·
            by_cases h : 76121 ≤ d
            ·
              by_cases h : 76125 ≤ d
              ·
                by_cases h : 76127 ≤ d
                ·
                  by_cases h : 76128 ≤ d
                  ·
                    have : d = 76128 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 76127 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76126 ≤ d
                  ·
                    have : d = 76126 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76125 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76123 ≤ d
                ·
                  by_cases h : 76124 ≤ d
                  ·
                    have : d = 76124 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76123 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76122 ≤ d
                  ·
                    have : d = 76122 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 4229) (by norm_num)
      exact by decide
                  ·
                    have : d = 76121 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 76117 ≤ d
              ·
                by_cases h : 76119 ≤ d
                ·
                  by_cases h : 76120 ≤ d
                  ·
                    have : d = 76120 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 173) (by norm_num)
      exact by decide
                  ·
                    have : d = 76119 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76118 ≤ d
                  ·
                    have : d = 76118 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76117 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76115 ≤ d
                ·
                  by_cases h : 76116 ≤ d
                  ·
                    have : d = 76116 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76115 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76114 ≤ d
                  ·
                    have : d = 76114 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 76113 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 76105 ≤ d
            ·
              by_cases h : 76109 ≤ d
              ·
                by_cases h : 76111 ≤ d
                ·
                  by_cases h : 76112 ≤ d
                  ·
                    have : d = 76112 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76111 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76110 ≤ d
                  ·
                    have : d = 76110 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 43) (by norm_num)
      exact by decide
                  ·
                    have : d = 76109 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76107 ≤ d
                ·
                  by_cases h : 76108 ≤ d
                  ·
                    have : d = 76108 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 53) (by norm_num)
      exact by decide
                  ·
                    have : d = 76107 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76106 ≤ d
                  ·
                    have : d = 76106 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76105 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 76101 ≤ d
              ·
                by_cases h : 76103 ≤ d
                ·
                  by_cases h : 76104 ≤ d
                  ·
                    have : d = 76104 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 151) (by norm_num)
      exact by decide
                  ·
                    have : d = 76103 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76102 ≤ d
                  ·
                    have : d = 76102 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76101 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76099 ≤ d
                ·
                  by_cases h : 76100 ≤ d
                  ·
                    have : d = 76100 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76099 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76098 ≤ d
                  ·
                    have : d = 76098 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76097 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 76065 ≤ d
        ·
          by_cases h : 76081 ≤ d
          ·
            by_cases h : 76089 ≤ d
            ·
              by_cases h : 76093 ≤ d
              ·
                by_cases h : 76095 ≤ d
                ·
                  by_cases h : 76096 ≤ d
                  ·
                    have : d = 76096 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76095 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76094 ≤ d
                  ·
                    have : d = 76094 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76093 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76091 ≤ d
                ·
                  by_cases h : 76092 ≤ d
                  ·
                    have : d = 76092 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 76091 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76090 ≤ d
                  ·
                    have : d = 76090 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1087) (by norm_num)
      exact by decide
                  ·
                    have : d = 76089 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 76085 ≤ d
              ·
                by_cases h : 76087 ≤ d
                ·
                  by_cases h : 76088 ≤ d
                  ·
                    have : d = 76088 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76087 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76086 ≤ d
                  ·
                    have : d = 76086 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76085 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76083 ≤ d
                ·
                  by_cases h : 76084 ≤ d
                  ·
                    have : d = 76084 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76083 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76082 ≤ d
                  ·
                    have : d = 76082 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76081 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 76073 ≤ d
            ·
              by_cases h : 76077 ≤ d
              ·
                by_cases h : 76079 ≤ d
                ·
                  by_cases h : 76080 ≤ d
                  ·
                    have : d = 76080 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76079 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76078 ≤ d
                  ·
                    have : d = 76078 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 38039) (by norm_num)
      exact by decide
                  ·
                    have : d = 76077 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76075 ≤ d
                ·
                  by_cases h : 76076 ≤ d
                  ·
                    have : d = 76076 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76075 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76074 ≤ d
                  ·
                    have : d = 76074 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 31) (by norm_num)
      exact by decide
                  ·
                    have : d = 76073 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 76069 ≤ d
              ·
                by_cases h : 76071 ≤ d
                ·
                  by_cases h : 76072 ≤ d
                  ·
                    have : d = 76072 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 37) (by norm_num)
      exact by decide
                  ·
                    have : d = 76071 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76070 ≤ d
                  ·
                    have : d = 76070 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76069 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76067 ≤ d
                ·
                  by_cases h : 76068 ≤ d
                  ·
                    have : d = 76068 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2113) (by norm_num)
      exact by decide
                  ·
                    have : d = 76067 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76066 ≤ d
                  ·
                    have : d = 76066 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76065 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 76049 ≤ d
          ·
            by_cases h : 76057 ≤ d
            ·
              by_cases h : 76061 ≤ d
              ·
                by_cases h : 76063 ≤ d
                ·
                  by_cases h : 76064 ≤ d
                  ·
                    have : d = 76064 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76063 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76062 ≤ d
                  ·
                    have : d = 76062 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1811) (by norm_num)
      exact by decide
                  ·
                    have : d = 76061 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76059 ≤ d
                ·
                  by_cases h : 76060 ≤ d
                  ·
                    have : d = 76060 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3803) (by norm_num)
      exact by decide
                  ·
                    have : d = 76059 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76058 ≤ d
                  ·
                    have : d = 76058 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76057 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 76053 ≤ d
              ·
                by_cases h : 76055 ≤ d
                ·
                  by_cases h : 76056 ≤ d
                  ·
                    have : d = 76056 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76055 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76054 ≤ d
                  ·
                    have : d = 76054 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3457) (by norm_num)
      exact by decide
                  ·
                    have : d = 76053 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76051 ≤ d
                ·
                  by_cases h : 76052 ≤ d
                  ·
                    have : d = 76052 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76051 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76050 ≤ d
                  ·
                    have : d = 76050 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 76049 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 76041 ≤ d
            ·
              by_cases h : 76045 ≤ d
              ·
                by_cases h : 76047 ≤ d
                ·
                  by_cases h : 76048 ≤ d
                  ·
                    have : d = 76048 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 97) (by norm_num)
      exact by decide
                  ·
                    have : d = 76047 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76046 ≤ d
                  ·
                    have : d = 76046 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76045 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76043 ≤ d
                ·
                  by_cases h : 76044 ≤ d
                  ·
                    have : d = 76044 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 6337) (by norm_num)
      exact by decide
                  ·
                    have : d = 76043 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76042 ≤ d
                  ·
                    have : d = 76042 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76041 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 76037 ≤ d
              ·
                by_cases h : 76039 ≤ d
                ·
                  by_cases h : 76040 ≤ d
                  ·
                    have : d = 76040 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76039 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76038 ≤ d
                  ·
                    have : d = 76038 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 76037 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76035 ≤ d
                ·
                  by_cases h : 76036 ≤ d
                  ·
                    have : d = 76036 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76035 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76034 ≤ d
                  ·
                    have : d = 76034 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76033 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
  ·
    by_cases h : 75905 ≤ d
    ·
      by_cases h : 75969 ≤ d
      ·
        by_cases h : 76001 ≤ d
        ·
          by_cases h : 76017 ≤ d
          ·
            by_cases h : 76025 ≤ d
            ·
              by_cases h : 76029 ≤ d
              ·
                by_cases h : 76031 ≤ d
                ·
                  by_cases h : 76032 ≤ d
                  ·
                    have : d = 76032 := by omega
                    subst d
      exact fullRecordGapTerm03600_not_prime
                  ·
                    have : d = 76031 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76030 ≤ d
                  ·
                    have : d = 76030 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7603) (by norm_num)
      exact by decide
                  ·
                    have : d = 76029 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76027 ≤ d
                ·
                  by_cases h : 76028 ≤ d
                  ·
                    have : d = 76028 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76027 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76026 ≤ d
                  ·
                    have : d = 76026 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76025 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 76021 ≤ d
              ·
                by_cases h : 76023 ≤ d
                ·
                  by_cases h : 76024 ≤ d
                  ·
                    have : d = 76024 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 76023 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76022 ≤ d
                  ·
                    have : d = 76022 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76021 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76019 ≤ d
                ·
                  by_cases h : 76020 ≤ d
                  ·
                    have : d = 76020 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 181) (by norm_num)
      exact by decide
                  ·
                    have : d = 76019 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76018 ≤ d
                  ·
                    have : d = 76018 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 191) (by norm_num)
      exact by decide
                  ·
                    have : d = 76017 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 76009 ≤ d
            ·
              by_cases h : 76013 ≤ d
              ·
                by_cases h : 76015 ≤ d
                ·
                  by_cases h : 76016 ≤ d
                  ·
                    have : d = 76016 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76015 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76014 ≤ d
                  ·
                    have : d = 76014 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76013 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76011 ≤ d
                ·
                  by_cases h : 76012 ≤ d
                  ·
                    have : d = 76012 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 31) (by norm_num)
      exact by decide
                  ·
                    have : d = 76011 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76010 ≤ d
                  ·
                    have : d = 76010 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76009 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 76005 ≤ d
              ·
                by_cases h : 76007 ≤ d
                ·
                  by_cases h : 76008 ≤ d
                  ·
                    have : d = 76008 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3167) (by norm_num)
      exact by decide
                  ·
                    have : d = 76007 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76006 ≤ d
                  ·
                    have : d = 76006 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76005 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 76003 ≤ d
                ·
                  by_cases h : 76004 ≤ d
                  ·
                    have : d = 76004 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 76003 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 76002 ≤ d
                  ·
                    have : d = 76002 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 53) (by norm_num)
      exact by decide
                  ·
                    have : d = 76001 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 75985 ≤ d
          ·
            by_cases h : 75993 ≤ d
            ·
              by_cases h : 75997 ≤ d
              ·
                by_cases h : 75999 ≤ d
                ·
                  by_cases h : 76000 ≤ d
                  ·
                    have : d = 76000 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75999 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75998 ≤ d
                  ·
                    have : d = 75998 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75997 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 75995 ≤ d
                ·
                  by_cases h : 75996 ≤ d
                  ·
                    have : d = 75996 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75995 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75994 ≤ d
                  ·
                    have : d = 75994 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 37997) (by norm_num)
      exact by decide
                  ·
                    have : d = 75993 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 75989 ≤ d
              ·
                by_cases h : 75991 ≤ d
                ·
                  by_cases h : 75992 ≤ d
                  ·
                    have : d = 75992 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75991 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75990 ≤ d
                  ·
                    have : d = 75990 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 75989 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 75987 ≤ d
                ·
                  by_cases h : 75988 ≤ d
                  ·
                    have : d = 75988 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 157) (by norm_num)
      exact by decide
                  ·
                    have : d = 75987 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75986 ≤ d
                  ·
                    have : d = 75986 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75985 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 75977 ≤ d
            ·
              by_cases h : 75981 ≤ d
              ·
                by_cases h : 75983 ≤ d
                ·
                  by_cases h : 75984 ≤ d
                  ·
                    have : d = 75984 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1583) (by norm_num)
      exact by decide
                  ·
                    have : d = 75983 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75982 ≤ d
                  ·
                    have : d = 75982 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 37991) (by norm_num)
      exact by decide
                  ·
                    have : d = 75981 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 75979 ≤ d
                ·
                  by_cases h : 75980 ≤ d
                  ·
                    have : d = 75980 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75979 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75978 ≤ d
                  ·
                    have : d = 75978 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 67) (by norm_num)
      exact by decide
                  ·
                    have : d = 75977 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 75973 ≤ d
              ·
                by_cases h : 75975 ≤ d
                ·
                  by_cases h : 75976 ≤ d
                  ·
                    have : d = 75976 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75975 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75974 ≤ d
                  ·
                    have : d = 75974 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75973 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 75971 ≤ d
                ·
                  by_cases h : 75972 ≤ d
                  ·
                    have : d = 75972 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75971 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75970 ≤ d
                  ·
                    have : d = 75970 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75969 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 75937 ≤ d
        ·
          by_cases h : 75953 ≤ d
          ·
            by_cases h : 75961 ≤ d
            ·
              by_cases h : 75965 ≤ d
              ·
                by_cases h : 75967 ≤ d
                ·
                  by_cases h : 75968 ≤ d
                  ·
                    have : d = 75968 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75967 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75966 ≤ d
                  ·
                    have : d = 75966 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75965 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 75963 ≤ d
                ·
                  by_cases h : 75964 ≤ d
                  ·
                    have : d = 75964 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2713) (by norm_num)
      exact by decide
                  ·
                    have : d = 75963 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75962 ≤ d
                  ·
                    have : d = 75962 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75961 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 75957 ≤ d
              ·
                by_cases h : 75959 ≤ d
                ·
                  by_cases h : 75960 ≤ d
                  ·
                    have : d = 75960 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 211) (by norm_num)
      exact by decide
                  ·
                    have : d = 75959 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75958 ≤ d
                  ·
                    have : d = 75958 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75957 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 75955 ≤ d
                ·
                  by_cases h : 75956 ≤ d
                  ·
                    have : d = 75956 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75955 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75954 ≤ d
                  ·
                    have : d = 75954 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 12659) (by norm_num)
      exact by decide
                  ·
                    have : d = 75953 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 75945 ≤ d
            ·
              by_cases h : 75949 ≤ d
              ·
                by_cases h : 75951 ≤ d
                ·
                  by_cases h : 75952 ≤ d
                  ·
                    have : d = 75952 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 47) (by norm_num)
      exact by decide
                  ·
                    have : d = 75951 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75950 ≤ d
                  ·
                    have : d = 75950 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75949 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 75947 ≤ d
                ·
                  by_cases h : 75948 ≤ d
                  ·
                    have : d = 75948 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75947 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75946 ≤ d
                  ·
                    have : d = 75946 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75945 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 75941 ≤ d
              ·
                by_cases h : 75943 ≤ d
                ·
                  by_cases h : 75944 ≤ d
                  ·
                    have : d = 75944 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75943 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75942 ≤ d
                  ·
                    have : d = 75942 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 4219) (by norm_num)
      exact by decide
                  ·
                    have : d = 75941 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 75939 ≤ d
                ·
                  by_cases h : 75940 ≤ d
                  ·
                    have : d = 75940 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3797) (by norm_num)
      exact by decide
                  ·
                    have : d = 75939 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75938 ≤ d
                  ·
                    have : d = 75938 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75937 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 75921 ≤ d
          ·
            by_cases h : 75929 ≤ d
            ·
              by_cases h : 75933 ≤ d
              ·
                by_cases h : 75935 ≤ d
                ·
                  by_cases h : 75936 ≤ d
                  ·
                    have : d = 75936 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75935 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75934 ≤ d
                  ·
                    have : d = 75934 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 37967) (by norm_num)
      exact by decide
                  ·
                    have : d = 75933 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 75931 ≤ d
                ·
                  by_cases h : 75932 ≤ d
                  ·
                    have : d = 75932 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75931 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75930 ≤ d
                  ·
                    have : d = 75930 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75929 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 75925 ≤ d
              ·
                by_cases h : 75927 ≤ d
                ·
                  by_cases h : 75928 ≤ d
                  ·
                    have : d = 75928 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 9491) (by norm_num)
      exact by decide
                  ·
                    have : d = 75927 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75926 ≤ d
                  ·
                    have : d = 75926 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75925 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 75923 ≤ d
                ·
                  by_cases h : 75924 ≤ d
                  ·
                    have : d = 75924 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 75923 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75922 ≤ d
                  ·
                    have : d = 75922 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 75921 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 75913 ≤ d
            ·
              by_cases h : 75917 ≤ d
              ·
                by_cases h : 75919 ≤ d
                ·
                  by_cases h : 75920 ≤ d
                  ·
                    have : d = 75920 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75919 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75918 ≤ d
                  ·
                    have : d = 75918 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 12653) (by norm_num)
      exact by decide
                  ·
                    have : d = 75917 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 75915 ≤ d
                ·
                  by_cases h : 75916 ≤ d
                  ·
                    have : d = 75916 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75915 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75914 ≤ d
                  ·
                    have : d = 75914 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75913 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 75909 ≤ d
              ·
                by_cases h : 75911 ≤ d
                ·
                  by_cases h : 75912 ≤ d
                  ·
                    have : d = 75912 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3163) (by norm_num)
      exact by decide
                  ·
                    have : d = 75911 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75910 ≤ d
                  ·
                    have : d = 75910 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7591) (by norm_num)
      exact by decide
                  ·
                    have : d = 75909 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 75907 ≤ d
                ·
                  by_cases h : 75908 ≤ d
                  ·
                    have : d = 75908 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75907 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75906 ≤ d
                  ·
                    have : d = 75906 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75905 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 75841 ≤ d
      ·
        by_cases h : 75873 ≤ d
        ·
          by_cases h : 75889 ≤ d
          ·
            by_cases h : 75897 ≤ d
            ·
              by_cases h : 75901 ≤ d
              ·
                by_cases h : 75903 ≤ d
                ·
                  by_cases h : 75904 ≤ d
                  ·
                    have : d = 75904 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75903 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75902 ≤ d
                  ·
                    have : d = 75902 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75901 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 75899 ≤ d
                ·
                  by_cases h : 75900 ≤ d
                  ·
                    have : d = 75900 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23) (by norm_num)
      exact by decide
                  ·
                    have : d = 75899 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75898 ≤ d
                  ·
                    have : d = 75898 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 137) (by norm_num)
      exact by decide
                  ·
                    have : d = 75897 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 75893 ≤ d
              ·
                by_cases h : 75895 ≤ d
                ·
                  by_cases h : 75896 ≤ d
                  ·
                    have : d = 75896 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75895 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75894 ≤ d
                  ·
                    have : d = 75894 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 75893 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 75891 ≤ d
                ·
                  by_cases h : 75892 ≤ d
                  ·
                    have : d = 75892 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 18973) (by norm_num)
      exact by decide
                  ·
                    have : d = 75891 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75890 ≤ d
                  ·
                    have : d = 75890 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75889 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 75881 ≤ d
            ·
              by_cases h : 75885 ≤ d
              ·
                by_cases h : 75887 ≤ d
                ·
                  by_cases h : 75888 ≤ d
                  ·
                    have : d = 75888 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75887 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75886 ≤ d
                  ·
                    have : d = 75886 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75885 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 75883 ≤ d
                ·
                  by_cases h : 75884 ≤ d
                  ·
                    have : d = 75884 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75883 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75882 ≤ d
                  ·
                    have : d = 75882 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75881 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 75877 ≤ d
              ·
                by_cases h : 75879 ≤ d
                ·
                  by_cases h : 75880 ≤ d
                  ·
                    have : d = 75880 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 271) (by norm_num)
      exact by decide
                  ·
                    have : d = 75879 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75878 ≤ d
                  ·
                    have : d = 75878 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75877 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 75875 ≤ d
                ·
                  by_cases h : 75876 ≤ d
                  ·
                    have : d = 75876 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75875 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75874 ≤ d
                  ·
                    have : d = 75874 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75873 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 75857 ≤ d
          ·
            by_cases h : 75865 ≤ d
            ·
              by_cases h : 75869 ≤ d
              ·
                by_cases h : 75871 ≤ d
                ·
                  by_cases h : 75872 ≤ d
                  ·
                    have : d = 75872 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75871 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75870 ≤ d
                  ·
                    have : d = 75870 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 281) (by norm_num)
      exact by decide
                  ·
                    have : d = 75869 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 75867 ≤ d
                ·
                  by_cases h : 75868 ≤ d
                  ·
                    have : d = 75868 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 75867 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75866 ≤ d
                  ·
                    have : d = 75866 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75865 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 75861 ≤ d
              ·
                by_cases h : 75863 ≤ d
                ·
                  by_cases h : 75864 ≤ d
                  ·
                    have : d = 75864 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 29) (by norm_num)
      exact by decide
                  ·
                    have : d = 75863 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75862 ≤ d
                  ·
                    have : d = 75862 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 83) (by norm_num)
      exact by decide
                  ·
                    have : d = 75861 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 75859 ≤ d
                ·
                  by_cases h : 75860 ≤ d
                  ·
                    have : d = 75860 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75859 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75858 ≤ d
                  ·
                    have : d = 75858 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 47) (by norm_num)
      exact by decide
                  ·
                    have : d = 75857 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 75849 ≤ d
            ·
              by_cases h : 75853 ≤ d
              ·
                by_cases h : 75855 ≤ d
                ·
                  by_cases h : 75856 ≤ d
                  ·
                    have : d = 75856 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75855 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75854 ≤ d
                  ·
                    have : d = 75854 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75853 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 75851 ≤ d
                ·
                  by_cases h : 75852 ≤ d
                  ·
                    have : d = 75852 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 43) (by norm_num)
      exact by decide
                  ·
                    have : d = 75851 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75850 ≤ d
                  ·
                    have : d = 75850 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 37) (by norm_num)
      exact by decide
                  ·
                    have : d = 75849 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 75845 ≤ d
              ·
                by_cases h : 75847 ≤ d
                ·
                  by_cases h : 75848 ≤ d
                  ·
                    have : d = 75848 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75847 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75846 ≤ d
                  ·
                    have : d = 75846 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75845 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 75843 ≤ d
                ·
                  by_cases h : 75844 ≤ d
                  ·
                    have : d = 75844 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 67) (by norm_num)
      exact by decide
                  ·
                    have : d = 75843 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75842 ≤ d
                  ·
                    have : d = 75842 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75841 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 75809 ≤ d
        ·
          by_cases h : 75825 ≤ d
          ·
            by_cases h : 75833 ≤ d
            ·
              by_cases h : 75837 ≤ d
              ·
                by_cases h : 75839 ≤ d
                ·
                  by_cases h : 75840 ≤ d
                  ·
                    have : d = 75840 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 79) (by norm_num)
      exact by decide
                  ·
                    have : d = 75839 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75838 ≤ d
                  ·
                    have : d = 75838 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75837 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 75835 ≤ d
                ·
                  by_cases h : 75836 ≤ d
                  ·
                    have : d = 75836 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75835 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75834 ≤ d
                  ·
                    have : d = 75834 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 383) (by norm_num)
      exact by decide
                  ·
                    have : d = 75833 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 75829 ≤ d
              ·
                by_cases h : 75831 ≤ d
                ·
                  by_cases h : 75832 ≤ d
                  ·
                    have : d = 75832 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75831 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75830 ≤ d
                  ·
                    have : d = 75830 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75829 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 75827 ≤ d
                ·
                  by_cases h : 75828 ≤ d
                  ·
                    have : d = 75828 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 71) (by norm_num)
      exact by decide
                  ·
                    have : d = 75827 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75826 ≤ d
                  ·
                    have : d = 75826 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75825 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 75817 ≤ d
            ·
              by_cases h : 75821 ≤ d
              ·
                by_cases h : 75823 ≤ d
                ·
                  by_cases h : 75824 ≤ d
                  ·
                    have : d = 75824 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75823 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75822 ≤ d
                  ·
                    have : d = 75822 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 12637) (by norm_num)
      exact by decide
                  ·
                    have : d = 75821 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 75819 ≤ d
                ·
                  by_cases h : 75820 ≤ d
                  ·
                    have : d = 75820 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 75819 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75818 ≤ d
                  ·
                    have : d = 75818 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75817 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 75813 ≤ d
              ·
                by_cases h : 75815 ≤ d
                ·
                  by_cases h : 75816 ≤ d
                  ·
                    have : d = 75816 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75815 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75814 ≤ d
                  ·
                    have : d = 75814 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 37907) (by norm_num)
      exact by decide
                  ·
                    have : d = 75813 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 75811 ≤ d
                ·
                  by_cases h : 75812 ≤ d
                  ·
                    have : d = 75812 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75811 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75810 ≤ d
                  ·
                    have : d = 75810 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 75809 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 75793 ≤ d
          ·
            by_cases h : 75801 ≤ d
            ·
              by_cases h : 75805 ≤ d
              ·
                by_cases h : 75807 ≤ d
                ·
                  by_cases h : 75808 ≤ d
                  ·
                    have : d = 75808 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23) (by norm_num)
      exact by decide
                  ·
                    have : d = 75807 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75806 ≤ d
                  ·
                    have : d = 75806 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75805 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 75803 ≤ d
                ·
                  by_cases h : 75804 ≤ d
                  ·
                    have : d = 75804 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75803 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75802 ≤ d
                  ·
                    have : d = 75802 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 151) (by norm_num)
      exact by decide
                  ·
                    have : d = 75801 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 75797 ≤ d
              ·
                by_cases h : 75799 ≤ d
                ·
                  by_cases h : 75800 ≤ d
                  ·
                    have : d = 75800 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75799 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75798 ≤ d
                  ·
                    have : d = 75798 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 4211) (by norm_num)
      exact by decide
                  ·
                    have : d = 75797 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 75795 ≤ d
                ·
                  by_cases h : 75796 ≤ d
                  ·
                    have : d = 75796 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75795 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75794 ≤ d
                  ·
                    have : d = 75794 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75793 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 75785 ≤ d
            ·
              by_cases h : 75789 ≤ d
              ·
                by_cases h : 75791 ≤ d
                ·
                  by_cases h : 75792 ≤ d
                  ·
                    have : d = 75792 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1579) (by norm_num)
      exact by decide
                  ·
                    have : d = 75791 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75790 ≤ d
                  ·
                    have : d = 75790 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75789 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 75787 ≤ d
                ·
                  by_cases h : 75788 ≤ d
                  ·
                    have : d = 75788 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75787 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75786 ≤ d
                  ·
                    have : d = 75786 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75785 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 75781 ≤ d
              ·
                by_cases h : 75783 ≤ d
                ·
                  by_cases h : 75784 ≤ d
                  ·
                    have : d = 75784 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 9473) (by norm_num)
      exact by decide
                  ·
                    have : d = 75783 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75782 ≤ d
                  ·
                    have : d = 75782 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 75781 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 75779 ≤ d
                ·
                  by_cases h : 75780 ≤ d
                  ·
                    have : d = 75780 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 421) (by norm_num)
      exact by decide
                  ·
                    have : d = 75779 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 75778 ≤ d
                  ·
                    have : d = 75778 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 37889) (by norm_num)
      exact by decide
                  ·
                    have : d = 75777 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩

end PrimeFactorUnimodality
