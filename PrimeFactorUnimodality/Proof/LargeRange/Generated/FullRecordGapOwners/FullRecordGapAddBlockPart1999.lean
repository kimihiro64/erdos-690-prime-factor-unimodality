import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapFermat

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

theorem fullRecordGapAddBlock_part1999 (d : Nat) (566785 ≤ d) (d ≤ 567296) : ¬(recordGapCenter + d).Prime := by
  by_cases h : 567041 ≤ d
  ·
    by_cases h : 567169 ≤ d
    ·
      by_cases h : 567233 ≤ d
      ·
        by_cases h : 567265 ≤ d
        ·
          by_cases h : 567281 ≤ d
          ·
            by_cases h : 567289 ≤ d
            ·
              by_cases h : 567293 ≤ d
              ·
                by_cases h : 567295 ≤ d
                ·
                  by_cases h : 567296 ≤ d
                  ·
                    have : d = 567296 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 277)
      exact by decide
                  ·
                    have : d = 567295 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567294 ≤ d
                  ·
                    have : d = 567294 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567293 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567291 ≤ d
                ·
                  by_cases h : 567292 ≤ d
                  ·
                    have : d = 567292 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567291 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567290 ≤ d
                  ·
                    have : d = 567290 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 567289 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 567285 ≤ d
              ·
                by_cases h : 567287 ≤ d
                ·
                  by_cases h : 567288 ≤ d
                  ·
                    have : d = 567288 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567287 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567286 ≤ d
                  ·
                    have : d = 567286 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567285 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567283 ≤ d
                ·
                  by_cases h : 567284 ≤ d
                  ·
                    have : d = 567284 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567283 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567282 ≤ d
                  ·
                    have : d = 567282 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1932915443)
      right
      exact ⟨1932348161, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567281 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 567273 ≤ d
            ·
              by_cases h : 567277 ≤ d
              ·
                by_cases h : 567279 ≤ d
                ·
                  by_cases h : 567280 ≤ d
                  ·
                    have : d = 567280 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567279 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567278 ≤ d
                  ·
                    have : d = 567278 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 839327)
      right
      exact ⟨272049, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567277 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567275 ≤ d
                ·
                  by_cases h : 567276 ≤ d
                  ·
                    have : d = 567276 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 41)
      exact by decide
                  ·
                    have : d = 567275 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567274 ≤ d
                  ·
                    have : d = 567274 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567273 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 567269 ≤ d
              ·
                by_cases h : 567271 ≤ d
                ·
                  by_cases h : 567272 ≤ d
                  ·
                    have : d = 567272 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567271 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567270 ≤ d
                  ·
                    have : d = 567270 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 191)
      exact by decide
                  ·
                    have : d = 567269 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567267 ≤ d
                ·
                  by_cases h : 567268 ≤ d
                  ·
                    have : d = 567268 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567267 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567266 ≤ d
                  ·
                    have : d = 567266 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567265 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 567249 ≤ d
          ·
            by_cases h : 567257 ≤ d
            ·
              by_cases h : 567261 ≤ d
              ·
                by_cases h : 567263 ≤ d
                ·
                  by_cases h : 567264 ≤ d
                  ·
                    have : d = 567264 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567263 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567262 ≤ d
                  ·
                    have : d = 567262 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567261 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567259 ≤ d
                ·
                  by_cases h : 567260 ≤ d
                  ·
                    have : d = 567260 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 113)
      exact by decide
                  ·
                    have : d = 567259 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567258 ≤ d
                  ·
                    have : d = 567258 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567257 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 567253 ≤ d
              ·
                by_cases h : 567255 ≤ d
                ·
                  by_cases h : 567256 ≤ d
                  ·
                    have : d = 567256 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567255 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567254 ≤ d
                  ·
                    have : d = 567254 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567253 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567251 ≤ d
                ·
                  by_cases h : 567252 ≤ d
                  ·
                    have : d = 567252 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2251)
      exact by decide
                  ·
                    have : d = 567251 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567250 ≤ d
                  ·
                    have : d = 567250 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567249 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 567241 ≤ d
            ·
              by_cases h : 567245 ≤ d
              ·
                by_cases h : 567247 ≤ d
                ·
                  by_cases h : 567248 ≤ d
                  ·
                    have : d = 567248 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 293)
      exact by decide
                  ·
                    have : d = 567247 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567246 ≤ d
                  ·
                    have : d = 567246 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1727503)
      right
      exact ⟨1160257, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567245 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567243 ≤ d
                ·
                  by_cases h : 567244 ≤ d
                  ·
                    have : d = 567244 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567243 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567242 ≤ d
                  ·
                    have : d = 567242 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 567241 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 567237 ≤ d
              ·
                by_cases h : 567239 ≤ d
                ·
                  by_cases h : 567240 ≤ d
                  ·
                    have : d = 567240 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 567239 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567238 ≤ d
                  ·
                    have : d = 567238 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567237 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567235 ≤ d
                ·
                  by_cases h : 567236 ≤ d
                  ·
                    have : d = 567236 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 109)
      exact by decide
                  ·
                    have : d = 567235 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567234 ≤ d
                  ·
                    have : d = 567234 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567233 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 567201 ≤ d
        ·
          by_cases h : 567217 ≤ d
          ·
            by_cases h : 567225 ≤ d
            ·
              by_cases h : 567229 ≤ d
              ·
                by_cases h : 567231 ≤ d
                ·
                  by_cases h : 567232 ≤ d
                  ·
                    have : d = 567232 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567231 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567230 ≤ d
                  ·
                    have : d = 567230 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567229 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567227 ≤ d
                ·
                  by_cases h : 567228 ≤ d
                  ·
                    have : d = 567228 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 168223073)
      right
      exact ⟨167655845, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567227 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567226 ≤ d
                  ·
                    have : d = 567226 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567225 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 567221 ≤ d
              ·
                by_cases h : 567223 ≤ d
                ·
                  by_cases h : 567224 ≤ d
                  ·
                    have : d = 567224 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567223 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567222 ≤ d
                  ·
                    have : d = 567222 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567221 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567219 ≤ d
                ·
                  by_cases h : 567220 ≤ d
                  ·
                    have : d = 567220 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567219 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567218 ≤ d
                  ·
                    have : d = 567218 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 100237)
      right
      exact ⟨34204, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567217 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 567209 ≤ d
            ·
              by_cases h : 567213 ≤ d
              ·
                by_cases h : 567215 ≤ d
                ·
                  by_cases h : 567216 ≤ d
                  ·
                    have : d = 567216 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567215 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567214 ≤ d
                  ·
                    have : d = 567214 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567213 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567211 ≤ d
                ·
                  by_cases h : 567212 ≤ d
                  ·
                    have : d = 567212 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 44959)
      right
      exact ⟨17255, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567211 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567210 ≤ d
                  ·
                    have : d = 567210 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 567209 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 567205 ≤ d
              ·
                by_cases h : 567207 ≤ d
                ·
                  by_cases h : 567208 ≤ d
                  ·
                    have : d = 567208 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567207 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567206 ≤ d
                  ·
                    have : d = 567206 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 53)
      exact by decide
                  ·
                    have : d = 567205 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567203 ≤ d
                ·
                  by_cases h : 567204 ≤ d
                  ·
                    have : d = 567204 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567203 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567202 ≤ d
                  ·
                    have : d = 567202 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567201 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 567185 ≤ d
          ·
            by_cases h : 567193 ≤ d
            ·
              by_cases h : 567197 ≤ d
              ·
                by_cases h : 567199 ≤ d
                ·
                  by_cases h : 567200 ≤ d
                  ·
                    have : d = 567200 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567199 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567198 ≤ d
                  ·
                    have : d = 567198 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31511)
      exact by decide
                  ·
                    have : d = 567197 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567195 ≤ d
                ·
                  by_cases h : 567196 ≤ d
                  ·
                    have : d = 567196 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567195 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567194 ≤ d
                  ·
                    have : d = 567194 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567193 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 567189 ≤ d
              ·
                by_cases h : 567191 ≤ d
                ·
                  by_cases h : 567192 ≤ d
                  ·
                    have : d = 567192 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23633)
      exact by decide
                  ·
                    have : d = 567191 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567190 ≤ d
                  ·
                    have : d = 567190 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567189 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567187 ≤ d
                ·
                  by_cases h : 567188 ≤ d
                  ·
                    have : d = 567188 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567187 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567186 ≤ d
                  ·
                    have : d = 567186 := by omega
                    subst d
      exact fullRecordGapTerm09458_not_prime
                  ·
                    have : d = 567185 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 567177 ≤ d
            ·
              by_cases h : 567181 ≤ d
              ·
                by_cases h : 567183 ≤ d
                ·
                  by_cases h : 567184 ≤ d
                  ·
                    have : d = 567184 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567183 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567182 ≤ d
                  ·
                    have : d = 567182 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 567181 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567179 ≤ d
                ·
                  by_cases h : 567180 ≤ d
                  ·
                    have : d = 567180 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 567179 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567178 ≤ d
                  ·
                    have : d = 567178 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567177 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 567173 ≤ d
              ·
                by_cases h : 567175 ≤ d
                ·
                  by_cases h : 567176 ≤ d
                  ·
                    have : d = 567176 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 567175 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567174 ≤ d
                  ·
                    have : d = 567174 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567173 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567171 ≤ d
                ·
                  by_cases h : 567172 ≤ d
                  ·
                    have : d = 567172 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567171 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567170 ≤ d
                  ·
                    have : d = 567170 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 43)
      exact by decide
                  ·
                    have : d = 567169 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 567105 ≤ d
      ·
        by_cases h : 567137 ≤ d
        ·
          by_cases h : 567153 ≤ d
          ·
            by_cases h : 567161 ≤ d
            ·
              by_cases h : 567165 ≤ d
              ·
                by_cases h : 567167 ≤ d
                ·
                  by_cases h : 567168 ≤ d
                  ·
                    have : d = 567168 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 211)
      exact by decide
                  ·
                    have : d = 567167 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567166 ≤ d
                  ·
                    have : d = 567166 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567165 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567163 ≤ d
                ·
                  by_cases h : 567164 ≤ d
                  ·
                    have : d = 567164 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567163 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567162 ≤ d
                  ·
                    have : d = 567162 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 389)
      exact by decide
                  ·
                    have : d = 567161 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 567157 ≤ d
              ·
                by_cases h : 567159 ≤ d
                ·
                  by_cases h : 567160 ≤ d
                  ·
                    have : d = 567160 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567159 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567158 ≤ d
                  ·
                    have : d = 567158 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19409939)
      right
      exact ⟨18842781, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567157 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567155 ≤ d
                ·
                  by_cases h : 567156 ≤ d
                  ·
                    have : d = 567156 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567155 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567154 ≤ d
                  ·
                    have : d = 567154 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567153 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 567145 ≤ d
            ·
              by_cases h : 567149 ≤ d
              ·
                by_cases h : 567151 ≤ d
                ·
                  by_cases h : 567152 ≤ d
                  ·
                    have : d = 567152 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 35447)
      exact by decide
                  ·
                    have : d = 567151 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567150 ≤ d
                  ·
                    have : d = 567150 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 567149 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567147 ≤ d
                ·
                  by_cases h : 567148 ≤ d
                  ·
                    have : d = 567148 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567147 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567146 ≤ d
                  ·
                    have : d = 567146 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567145 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 567141 ≤ d
              ·
                by_cases h : 567143 ≤ d
                ·
                  by_cases h : 567144 ≤ d
                  ·
                    have : d = 567144 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567143 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567142 ≤ d
                  ·
                    have : d = 567142 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567141 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567139 ≤ d
                ·
                  by_cases h : 567140 ≤ d
                  ·
                    have : d = 567140 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 4051)
      exact by decide
                  ·
                    have : d = 567139 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567138 ≤ d
                  ·
                    have : d = 567138 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 567137 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 567121 ≤ d
          ·
            by_cases h : 567129 ≤ d
            ·
              by_cases h : 567133 ≤ d
              ·
                by_cases h : 567135 ≤ d
                ·
                  by_cases h : 567136 ≤ d
                  ·
                    have : d = 567136 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567135 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567134 ≤ d
                  ·
                    have : d = 567134 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567133 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567131 ≤ d
                ·
                  by_cases h : 567132 ≤ d
                  ·
                    have : d = 567132 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567131 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567130 ≤ d
                  ·
                    have : d = 567130 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567129 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 567125 ≤ d
              ·
                by_cases h : 567127 ≤ d
                ·
                  by_cases h : 567128 ≤ d
                  ·
                    have : d = 567128 := by omega
                    subst d
      exact fullRecordGapTerm09457_not_prime
                  ·
                    have : d = 567127 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567126 ≤ d
                  ·
                    have : d = 567126 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 643)
      exact by decide
                  ·
                    have : d = 567125 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567123 ≤ d
                ·
                  by_cases h : 567124 ≤ d
                  ·
                    have : d = 567124 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567123 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567122 ≤ d
                  ·
                    have : d = 567122 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 233)
      exact by decide
                  ·
                    have : d = 567121 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 567113 ≤ d
            ·
              by_cases h : 567117 ≤ d
              ·
                by_cases h : 567119 ≤ d
                ·
                  by_cases h : 567120 ≤ d
                  ·
                    have : d = 567120 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 567119 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567118 ≤ d
                  ·
                    have : d = 567118 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567117 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567115 ≤ d
                ·
                  by_cases h : 567116 ≤ d
                  ·
                    have : d = 567116 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 12889)
      exact by decide
                  ·
                    have : d = 567115 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567114 ≤ d
                  ·
                    have : d = 567114 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567113 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 567109 ≤ d
              ·
                by_cases h : 567111 ≤ d
                ·
                  by_cases h : 567112 ≤ d
                  ·
                    have : d = 567112 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567111 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567110 ≤ d
                  ·
                    have : d = 567110 := by omega
                    subst d
      exact fullRecordGapTerm09456_not_prime
                  ·
                    have : d = 567109 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567107 ≤ d
                ·
                  by_cases h : 567108 ≤ d
                  ·
                    have : d = 567108 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 59)
      exact by decide
                  ·
                    have : d = 567107 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567106 ≤ d
                  ·
                    have : d = 567106 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567105 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 567073 ≤ d
        ·
          by_cases h : 567089 ≤ d
          ·
            by_cases h : 567097 ≤ d
            ·
              by_cases h : 567101 ≤ d
              ·
                by_cases h : 567103 ≤ d
                ·
                  by_cases h : 567104 ≤ d
                  ·
                    have : d = 567104 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567103 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567102 ≤ d
                  ·
                    have : d = 567102 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 47)
      exact by decide
                  ·
                    have : d = 567101 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567099 ≤ d
                ·
                  by_cases h : 567100 ≤ d
                  ·
                    have : d = 567100 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567099 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567098 ≤ d
                  ·
                    have : d = 567098 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 40507)
      exact by decide
                  ·
                    have : d = 567097 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 567093 ≤ d
              ·
                by_cases h : 567095 ≤ d
                ·
                  by_cases h : 567096 ≤ d
                  ·
                    have : d = 567096 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23629)
      exact by decide
                  ·
                    have : d = 567095 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567094 ≤ d
                  ·
                    have : d = 567094 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567093 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567091 ≤ d
                ·
                  by_cases h : 567092 ≤ d
                  ·
                    have : d = 567092 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 78729191)
      right
      exact ⟨78162099, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567091 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567090 ≤ d
                  ·
                    have : d = 567090 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567089 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 567081 ≤ d
            ·
              by_cases h : 567085 ≤ d
              ·
                by_cases h : 567087 ≤ d
                ·
                  by_cases h : 567088 ≤ d
                  ·
                    have : d = 567088 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567087 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567086 ≤ d
                  ·
                    have : d = 567086 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 567085 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567083 ≤ d
                ·
                  by_cases h : 567084 ≤ d
                  ·
                    have : d = 567084 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567083 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567082 ≤ d
                  ·
                    have : d = 567082 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567081 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 567077 ≤ d
              ·
                by_cases h : 567079 ≤ d
                ·
                  by_cases h : 567080 ≤ d
                  ·
                    have : d = 567080 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 14177)
      exact by decide
                  ·
                    have : d = 567079 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567078 ≤ d
                  ·
                    have : d = 567078 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 44687)
      right
      exact ⟨13853, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567077 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567075 ≤ d
                ·
                  by_cases h : 567076 ≤ d
                  ·
                    have : d = 567076 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567075 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567074 ≤ d
                  ·
                    have : d = 567074 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567073 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 567057 ≤ d
          ·
            by_cases h : 567065 ≤ d
            ·
              by_cases h : 567069 ≤ d
              ·
                by_cases h : 567071 ≤ d
                ·
                  by_cases h : 567072 ≤ d
                  ·
                    have : d = 567072 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 179)
      exact by decide
                  ·
                    have : d = 567071 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567070 ≤ d
                  ·
                    have : d = 567070 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567069 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567067 ≤ d
                ·
                  by_cases h : 567068 ≤ d
                  ·
                    have : d = 567068 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567067 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567066 ≤ d
                  ·
                    have : d = 567066 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 567065 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 567061 ≤ d
              ·
                by_cases h : 567063 ≤ d
                ·
                  by_cases h : 567064 ≤ d
                  ·
                    have : d = 567064 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567063 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567062 ≤ d
                  ·
                    have : d = 567062 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567061 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567059 ≤ d
                ·
                  by_cases h : 567060 ≤ d
                  ·
                    have : d = 567060 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 567059 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567058 ≤ d
                  ·
                    have : d = 567058 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567057 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 567049 ≤ d
            ·
              by_cases h : 567053 ≤ d
              ·
                by_cases h : 567055 ≤ d
                ·
                  by_cases h : 567056 ≤ d
                  ·
                    have : d = 567056 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 61)
      exact by decide
                  ·
                    have : d = 567055 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567054 ≤ d
                  ·
                    have : d = 567054 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567053 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567051 ≤ d
                ·
                  by_cases h : 567052 ≤ d
                  ·
                    have : d = 567052 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567051 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567050 ≤ d
                  ·
                    have : d = 567050 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1031)
      exact by decide
                  ·
                    have : d = 567049 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 567045 ≤ d
              ·
                by_cases h : 567047 ≤ d
                ·
                  by_cases h : 567048 ≤ d
                  ·
                    have : d = 567048 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567047 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567046 ≤ d
                  ·
                    have : d = 567046 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567045 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567043 ≤ d
                ·
                  by_cases h : 567044 ≤ d
                  ·
                    have : d = 567044 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567043 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567042 ≤ d
                  ·
                    have : d = 567042 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 567041 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
  ·
    by_cases h : 566913 ≤ d
    ·
      by_cases h : 566977 ≤ d
      ·
        by_cases h : 567009 ≤ d
        ·
          by_cases h : 567025 ≤ d
          ·
            by_cases h : 567033 ≤ d
            ·
              by_cases h : 567037 ≤ d
              ·
                by_cases h : 567039 ≤ d
                ·
                  by_cases h : 567040 ≤ d
                  ·
                    have : d = 567040 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567039 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567038 ≤ d
                  ·
                    have : d = 567038 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 313896589)
      right
      exact ⟨313329551, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567037 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567035 ≤ d
                ·
                  by_cases h : 567036 ≤ d
                  ·
                    have : d = 567036 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 567035 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567034 ≤ d
                  ·
                    have : d = 567034 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567033 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 567029 ≤ d
              ·
                by_cases h : 567031 ≤ d
                ·
                  by_cases h : 567032 ≤ d
                  ·
                    have : d = 567032 := by omega
                    subst d
      exact fullRecordGapTerm09455_not_prime
                  ·
                    have : d = 567031 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567030 ≤ d
                  ·
                    have : d = 567030 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 41)
      exact by decide
                  ·
                    have : d = 567029 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567027 ≤ d
                ·
                  by_cases h : 567028 ≤ d
                  ·
                    have : d = 567028 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567027 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567026 ≤ d
                  ·
                    have : d = 567026 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 509)
      exact by decide
                  ·
                    have : d = 567025 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 567017 ≤ d
            ·
              by_cases h : 567021 ≤ d
              ·
                by_cases h : 567023 ≤ d
                ·
                  by_cases h : 567024 ≤ d
                  ·
                    have : d = 567024 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567023 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567022 ≤ d
                  ·
                    have : d = 567022 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567021 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567019 ≤ d
                ·
                  by_cases h : 567020 ≤ d
                  ·
                    have : d = 567020 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567019 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567018 ≤ d
                  ·
                    have : d = 567018 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 567017 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 567013 ≤ d
              ·
                by_cases h : 567015 ≤ d
                ·
                  by_cases h : 567016 ≤ d
                  ·
                    have : d = 567016 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567015 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567014 ≤ d
                  ·
                    have : d = 567014 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567013 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567011 ≤ d
                ·
                  by_cases h : 567012 ≤ d
                  ·
                    have : d = 567012 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 139921)
      right
      exact ⟨132593, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567011 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567010 ≤ d
                  ·
                    have : d = 567010 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567009 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 566993 ≤ d
          ·
            by_cases h : 567001 ≤ d
            ·
              by_cases h : 567005 ≤ d
              ·
                by_cases h : 567007 ≤ d
                ·
                  by_cases h : 567008 ≤ d
                  ·
                    have : d = 567008 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 567007 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567006 ≤ d
                  ·
                    have : d = 567006 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567005 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 567003 ≤ d
                ·
                  by_cases h : 567004 ≤ d
                  ·
                    have : d = 567004 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567003 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 567002 ≤ d
                  ·
                    have : d = 567002 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 567001 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 566997 ≤ d
              ·
                by_cases h : 566999 ≤ d
                ·
                  by_cases h : 567000 ≤ d
                  ·
                    have : d = 567000 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5167489)
      right
      exact ⟨4600489, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566999 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566998 ≤ d
                  ·
                    have : d = 566998 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566997 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 566995 ≤ d
                ·
                  by_cases h : 566996 ≤ d
                  ·
                    have : d = 566996 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 566995 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566994 ≤ d
                  ·
                    have : d = 566994 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566993 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 566985 ≤ d
            ·
              by_cases h : 566989 ≤ d
              ·
                by_cases h : 566991 ≤ d
                ·
                  by_cases h : 566992 ≤ d
                  ·
                    have : d = 566992 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566991 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566990 ≤ d
                  ·
                    have : d = 566990 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 566989 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 566987 ≤ d
                ·
                  by_cases h : 566988 ≤ d
                  ·
                    have : d = 566988 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 566987 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566986 ≤ d
                  ·
                    have : d = 566986 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566985 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 566981 ≤ d
              ·
                by_cases h : 566983 ≤ d
                ·
                  by_cases h : 566984 ≤ d
                  ·
                    have : d = 566984 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566983 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566982 ≤ d
                  ·
                    have : d = 566982 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 566981 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 566979 ≤ d
                ·
                  by_cases h : 566980 ≤ d
                  ·
                    have : d = 566980 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566979 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566978 ≤ d
                  ·
                    have : d = 566978 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566977 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 566945 ≤ d
        ·
          by_cases h : 566961 ≤ d
          ·
            by_cases h : 566969 ≤ d
            ·
              by_cases h : 566973 ≤ d
              ·
                by_cases h : 566975 ≤ d
                ·
                  by_cases h : 566976 ≤ d
                  ·
                    have : d = 566976 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2953)
      exact by decide
                  ·
                    have : d = 566975 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566974 ≤ d
                  ·
                    have : d = 566974 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566973 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 566971 ≤ d
                ·
                  by_cases h : 566972 ≤ d
                  ·
                    have : d = 566972 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 20249)
      exact by decide
                  ·
                    have : d = 566971 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566970 ≤ d
                  ·
                    have : d = 566970 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 18899)
      exact by decide
                  ·
                    have : d = 566969 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 566965 ≤ d
              ·
                by_cases h : 566967 ≤ d
                ·
                  by_cases h : 566968 ≤ d
                  ·
                    have : d = 566968 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566967 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566966 ≤ d
                  ·
                    have : d = 566966 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 197)
      exact by decide
                  ·
                    have : d = 566965 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 566963 ≤ d
                ·
                  by_cases h : 566964 ≤ d
                  ·
                    have : d = 566964 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566963 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566962 ≤ d
                  ·
                    have : d = 566962 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566961 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 566953 ≤ d
            ·
              by_cases h : 566957 ≤ d
              ·
                by_cases h : 566959 ≤ d
                ·
                  by_cases h : 566960 ≤ d
                  ·
                    have : d = 566960 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 566959 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566958 ≤ d
                  ·
                    have : d = 566958 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566957 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 566955 ≤ d
                ·
                  by_cases h : 566956 ≤ d
                  ·
                    have : d = 566956 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566955 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566954 ≤ d
                  ·
                    have : d = 566954 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566953 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 566949 ≤ d
              ·
                by_cases h : 566951 ≤ d
                ·
                  by_cases h : 566952 ≤ d
                  ·
                    have : d = 566952 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23623)
      exact by decide
                  ·
                    have : d = 566951 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566950 ≤ d
                  ·
                    have : d = 566950 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566949 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 566947 ≤ d
                ·
                  by_cases h : 566948 ≤ d
                  ·
                    have : d = 566948 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 41)
      exact by decide
                  ·
                    have : d = 566947 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566946 ≤ d
                  ·
                    have : d = 566946 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 10499)
      exact by decide
                  ·
                    have : d = 566945 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 566929 ≤ d
          ·
            by_cases h : 566937 ≤ d
            ·
              by_cases h : 566941 ≤ d
              ·
                by_cases h : 566943 ≤ d
                ·
                  by_cases h : 566944 ≤ d
                  ·
                    have : d = 566944 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566943 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566942 ≤ d
                  ·
                    have : d = 566942 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 257)
      exact by decide
                  ·
                    have : d = 566941 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 566939 ≤ d
                ·
                  by_cases h : 566940 ≤ d
                  ·
                    have : d = 566940 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 859)
      exact by decide
                  ·
                    have : d = 566939 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566938 ≤ d
                  ·
                    have : d = 566938 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566937 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 566933 ≤ d
              ·
                by_cases h : 566935 ≤ d
                ·
                  by_cases h : 566936 ≤ d
                  ·
                    have : d = 566936 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566935 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566934 ≤ d
                  ·
                    have : d = 566934 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566933 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 566931 ≤ d
                ·
                  by_cases h : 566932 ≤ d
                  ·
                    have : d = 566932 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566931 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566930 ≤ d
                  ·
                    have : d = 566930 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 566929 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 566921 ≤ d
            ·
              by_cases h : 566925 ≤ d
              ·
                by_cases h : 566927 ≤ d
                ·
                  by_cases h : 566928 ≤ d
                  ·
                    have : d = 566928 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 566927 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566926 ≤ d
                  ·
                    have : d = 566926 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566925 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 566923 ≤ d
                ·
                  by_cases h : 566924 ≤ d
                  ·
                    have : d = 566924 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566923 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566922 ≤ d
                  ·
                    have : d = 566922 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566921 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 566917 ≤ d
              ·
                by_cases h : 566919 ≤ d
                ·
                  by_cases h : 566920 ≤ d
                  ·
                    have : d = 566920 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566919 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566918 ≤ d
                  ·
                    have : d = 566918 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 73)
      exact by decide
                  ·
                    have : d = 566917 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 566915 ≤ d
                ·
                  by_cases h : 566916 ≤ d
                  ·
                    have : d = 566916 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 566915 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566914 ≤ d
                  ·
                    have : d = 566914 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566913 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 566849 ≤ d
      ·
        by_cases h : 566881 ≤ d
        ·
          by_cases h : 566897 ≤ d
          ·
            by_cases h : 566905 ≤ d
            ·
              by_cases h : 566909 ≤ d
              ·
                by_cases h : 566911 ≤ d
                ·
                  by_cases h : 566912 ≤ d
                  ·
                    have : d = 566912 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 43)
      exact by decide
                  ·
                    have : d = 566911 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566910 ≤ d
                  ·
                    have : d = 566910 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 6299)
      exact by decide
                  ·
                    have : d = 566909 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 566907 ≤ d
                ·
                  by_cases h : 566908 ≤ d
                  ·
                    have : d = 566908 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566907 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566906 ≤ d
                  ·
                    have : d = 566906 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 137)
      exact by decide
                  ·
                    have : d = 566905 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 566901 ≤ d
              ·
                by_cases h : 566903 ≤ d
                ·
                  by_cases h : 566904 ≤ d
                  ·
                    have : d = 566904 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566903 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566902 ≤ d
                  ·
                    have : d = 566902 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566901 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 566899 ≤ d
                ·
                  by_cases h : 566900 ≤ d
                  ·
                    have : d = 566900 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5669)
      exact by decide
                  ·
                    have : d = 566899 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566898 ≤ d
                  ·
                    have : d = 566898 := by omega
                    subst d
      exact fullRecordGapTerm09454_not_prime
                  ·
                    have : d = 566897 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 566889 ≤ d
            ·
              by_cases h : 566893 ≤ d
              ·
                by_cases h : 566895 ≤ d
                ·
                  by_cases h : 566896 ≤ d
                  ·
                    have : d = 566896 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566895 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566894 ≤ d
                  ·
                    have : d = 566894 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566893 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 566891 ≤ d
                ·
                  by_cases h : 566892 ≤ d
                  ·
                    have : d = 566892 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566891 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566890 ≤ d
                  ·
                    have : d = 566890 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566889 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 566885 ≤ d
              ·
                by_cases h : 566887 ≤ d
                ·
                  by_cases h : 566888 ≤ d
                  ·
                    have : d = 566888 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 53)
      exact by decide
                  ·
                    have : d = 566887 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566886 ≤ d
                  ·
                    have : d = 566886 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 107)
      exact by decide
                  ·
                    have : d = 566885 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 566883 ≤ d
                ·
                  by_cases h : 566884 ≤ d
                  ·
                    have : d = 566884 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566883 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566882 ≤ d
                  ·
                    have : d = 566882 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 566881 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 566865 ≤ d
          ·
            by_cases h : 566873 ≤ d
            ·
              by_cases h : 566877 ≤ d
              ·
                by_cases h : 566879 ≤ d
                ·
                  by_cases h : 566880 ≤ d
                  ·
                    have : d = 566880 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566879 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566878 ≤ d
                  ·
                    have : d = 566878 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566877 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 566875 ≤ d
                ·
                  by_cases h : 566876 ≤ d
                  ·
                    have : d = 566876 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1026197)
      right
      exact ⟨459321, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566875 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566874 ≤ d
                  ·
                    have : d = 566874 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566873 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 566869 ≤ d
              ·
                by_cases h : 566871 ≤ d
                ·
                  by_cases h : 566872 ≤ d
                  ·
                    have : d = 566872 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566871 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566870 ≤ d
                  ·
                    have : d = 566870 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566869 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 566867 ≤ d
                ·
                  by_cases h : 566868 ≤ d
                  ·
                    have : d = 566868 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 97)
      exact by decide
                  ·
                    have : d = 566867 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566866 ≤ d
                  ·
                    have : d = 566866 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566865 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 566857 ≤ d
            ·
              by_cases h : 566861 ≤ d
              ·
                by_cases h : 566863 ≤ d
                ·
                  by_cases h : 566864 ≤ d
                  ·
                    have : d = 566864 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566863 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566862 ≤ d
                  ·
                    have : d = 566862 := by omega
                    subst d
      exact fullRecordGapTerm09453_not_prime
                  ·
                    have : d = 566861 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 566859 ≤ d
                ·
                  by_cases h : 566860 ≤ d
                  ·
                    have : d = 566860 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566859 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566858 ≤ d
                  ·
                    have : d = 566858 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 566857 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 566853 ≤ d
              ·
                by_cases h : 566855 ≤ d
                ·
                  by_cases h : 566856 ≤ d
                  ·
                    have : d = 566856 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7873)
      exact by decide
                  ·
                    have : d = 566855 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566854 ≤ d
                  ·
                    have : d = 566854 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566853 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 566851 ≤ d
                ·
                  by_cases h : 566852 ≤ d
                  ·
                    have : d = 566852 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566851 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566850 ≤ d
                  ·
                    have : d = 566850 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3779)
      exact by decide
                  ·
                    have : d = 566849 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 566817 ≤ d
        ·
          by_cases h : 566833 ≤ d
          ·
            by_cases h : 566841 ≤ d
            ·
              by_cases h : 566845 ≤ d
              ·
                by_cases h : 566847 ≤ d
                ·
                  by_cases h : 566848 ≤ d
                  ·
                    have : d = 566848 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566847 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566846 ≤ d
                  ·
                    have : d = 566846 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 566845 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 566843 ≤ d
                ·
                  by_cases h : 566844 ≤ d
                  ·
                    have : d = 566844 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566843 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566842 ≤ d
                  ·
                    have : d = 566842 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566841 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 566837 ≤ d
              ·
                by_cases h : 566839 ≤ d
                ·
                  by_cases h : 566840 ≤ d
                  ·
                    have : d = 566840 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 566839 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566838 ≤ d
                  ·
                    have : d = 566838 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566837 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 566835 ≤ d
                ·
                  by_cases h : 566836 ≤ d
                  ·
                    have : d = 566836 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566835 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566834 ≤ d
                  ·
                    have : d = 566834 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566833 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 566825 ≤ d
            ·
              by_cases h : 566829 ≤ d
              ·
                by_cases h : 566831 ≤ d
                ·
                  by_cases h : 566832 ≤ d
                  ·
                    have : d = 566832 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 241)
      exact by decide
                  ·
                    have : d = 566831 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566830 ≤ d
                  ·
                    have : d = 566830 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566829 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 566827 ≤ d
                ·
                  by_cases h : 566828 ≤ d
                  ·
                    have : d = 566828 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 73914773)
      right
      exact ⟨73347945, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566827 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566826 ≤ d
                  ·
                    have : d = 566826 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566825 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 566821 ≤ d
              ·
                by_cases h : 566823 ≤ d
                ·
                  by_cases h : 566824 ≤ d
                  ·
                    have : d = 566824 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566823 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566822 ≤ d
                  ·
                    have : d = 566822 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 535573)
      right
      exact ⟨504324, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566821 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 566819 ≤ d
                ·
                  by_cases h : 566820 ≤ d
                  ·
                    have : d = 566820 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 47)
      exact by decide
                  ·
                    have : d = 566819 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566818 ≤ d
                  ·
                    have : d = 566818 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566817 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 566801 ≤ d
          ·
            by_cases h : 566809 ≤ d
            ·
              by_cases h : 566813 ≤ d
              ·
                by_cases h : 566815 ≤ d
                ·
                  by_cases h : 566816 ≤ d
                  ·
                    have : d = 566816 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17713)
      exact by decide
                  ·
                    have : d = 566815 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566814 ≤ d
                  ·
                    have : d = 566814 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566813 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 566811 ≤ d
                ·
                  by_cases h : 566812 ≤ d
                  ·
                    have : d = 566812 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566811 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566810 ≤ d
                  ·
                    have : d = 566810 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566809 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 566805 ≤ d
              ·
                by_cases h : 566807 ≤ d
                ·
                  by_cases h : 566808 ≤ d
                  ·
                    have : d = 566808 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 566807 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566806 ≤ d
                  ·
                    have : d = 566806 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566805 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 566803 ≤ d
                ·
                  by_cases h : 566804 ≤ d
                  ·
                    have : d = 566804 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566803 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566802 ≤ d
                  ·
                    have : d = 566802 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31489)
      exact by decide
                  ·
                    have : d = 566801 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 566793 ≤ d
            ·
              by_cases h : 566797 ≤ d
              ·
                by_cases h : 566799 ≤ d
                ·
                  by_cases h : 566800 ≤ d
                  ·
                    have : d = 566800 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566799 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566798 ≤ d
                  ·
                    have : d = 566798 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 167)
      exact by decide
                  ·
                    have : d = 566797 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 566795 ≤ d
                ·
                  by_cases h : 566796 ≤ d
                  ·
                    have : d = 566796 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566795 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566794 ≤ d
                  ·
                    have : d = 566794 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566793 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 566789 ≤ d
              ·
                by_cases h : 566791 ≤ d
                ·
                  by_cases h : 566792 ≤ d
                  ·
                    have : d = 566792 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 48757)
      right
      exact ⟨18292, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566791 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566790 ≤ d
                  ·
                    have : d = 566790 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2699)
      exact by decide
                  ·
                    have : d = 566789 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 566787 ≤ d
                ·
                  by_cases h : 566788 ≤ d
                  ·
                    have : d = 566788 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 566787 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 566786 ≤ d
                  ·
                    have : d = 566786 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 25763)
      exact by decide
                  ·
                    have : d = 566785 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩

end PrimeFactorUnimodality
