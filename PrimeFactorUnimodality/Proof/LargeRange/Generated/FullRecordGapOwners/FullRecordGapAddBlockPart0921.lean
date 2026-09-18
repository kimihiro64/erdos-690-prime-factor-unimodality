import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapFermat

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

theorem fullRecordGapAddBlock_part0921 (d : Nat) (14849 ≤ d) (d ≤ 15360) : ¬(recordGapCenter + d).Prime := by
  by_cases h : 15105 ≤ d
  ·
    by_cases h : 15233 ≤ d
    ·
      by_cases h : 15297 ≤ d
      ·
        by_cases h : 15329 ≤ d
        ·
          by_cases h : 15345 ≤ d
          ·
            by_cases h : 15353 ≤ d
            ·
              by_cases h : 15357 ≤ d
              ·
                by_cases h : 15359 ≤ d
                ·
                  by_cases h : 15360 ≤ d
                  ·
                    have : d = 15360 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2097857)
      right
      exact ⟨2082497, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15359 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15358 ≤ d
                  ·
                    have : d = 15358 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15357 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15355 ≤ d
                ·
                  by_cases h : 15356 ≤ d
                  ·
                    have : d = 15356 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 349)
      exact by decide
                  ·
                    have : d = 15355 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15354 ≤ d
                  ·
                    have : d = 15354 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15353 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 15349 ≤ d
              ·
                by_cases h : 15351 ≤ d
                ·
                  by_cases h : 15352 ≤ d
                  ·
                    have : d = 15352 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15351 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15350 ≤ d
                  ·
                    have : d = 15350 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15349 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15347 ≤ d
                ·
                  by_cases h : 15348 ≤ d
                  ·
                    have : d = 15348 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1279)
      exact by decide
                  ·
                    have : d = 15347 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15346 ≤ d
                  ·
                    have : d = 15346 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15345 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 15337 ≤ d
            ·
              by_cases h : 15341 ≤ d
              ·
                by_cases h : 15343 ≤ d
                ·
                  by_cases h : 15344 ≤ d
                  ·
                    have : d = 15344 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15343 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15342 ≤ d
                  ·
                    have : d = 15342 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2557)
      exact by decide
                  ·
                    have : d = 15341 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15339 ≤ d
                ·
                  by_cases h : 15340 ≤ d
                  ·
                    have : d = 15340 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15339 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15338 ≤ d
                  ·
                    have : d = 15338 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7669)
      exact by decide
                  ·
                    have : d = 15337 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 15333 ≤ d
              ·
                by_cases h : 15335 ≤ d
                ·
                  by_cases h : 15336 ≤ d
                  ·
                    have : d = 15336 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15335 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15334 ≤ d
                  ·
                    have : d = 15334 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15333 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15331 ≤ d
                ·
                  by_cases h : 15332 ≤ d
                  ·
                    have : d = 15332 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3833)
      exact by decide
                  ·
                    have : d = 15331 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15330 ≤ d
                  ·
                    have : d = 15330 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15329 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 15313 ≤ d
          ·
            by_cases h : 15321 ≤ d
            ·
              by_cases h : 15325 ≤ d
              ·
                by_cases h : 15327 ≤ d
                ·
                  by_cases h : 15328 ≤ d
                  ·
                    have : d = 15328 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15327 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15326 ≤ d
                  ·
                    have : d = 15326 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 79)
      exact by decide
                  ·
                    have : d = 15325 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15323 ≤ d
                ·
                  by_cases h : 15324 ≤ d
                  ·
                    have : d = 15324 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15323 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15322 ≤ d
                  ·
                    have : d = 15322 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15321 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 15317 ≤ d
              ·
                by_cases h : 15319 ≤ d
                ·
                  by_cases h : 15320 ≤ d
                  ·
                    have : d = 15320 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 383)
      exact by decide
                  ·
                    have : d = 15319 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15318 ≤ d
                  ·
                    have : d = 15318 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 15317 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15315 ≤ d
                ·
                  by_cases h : 15316 ≤ d
                  ·
                    have : d = 15316 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15315 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15314 ≤ d
                  ·
                    have : d = 15314 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15313 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 15305 ≤ d
            ·
              by_cases h : 15309 ≤ d
              ·
                by_cases h : 15311 ≤ d
                ·
                  by_cases h : 15312 ≤ d
                  ·
                    have : d = 15312 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 15311 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15310 ≤ d
                  ·
                    have : d = 15310 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15309 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15307 ≤ d
                ·
                  by_cases h : 15308 ≤ d
                  ·
                    have : d = 15308 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15307 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15306 ≤ d
                  ·
                    have : d = 15306 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2551)
      exact by decide
                  ·
                    have : d = 15305 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 15301 ≤ d
              ·
                by_cases h : 15303 ≤ d
                ·
                  by_cases h : 15304 ≤ d
                  ·
                    have : d = 15304 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15303 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15302 ≤ d
                  ·
                    have : d = 15302 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1093)
      exact by decide
                  ·
                    have : d = 15301 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15299 ≤ d
                ·
                  by_cases h : 15300 ≤ d
                  ·
                    have : d = 15300 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 15299 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15298 ≤ d
                  ·
                    have : d = 15298 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15297 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 15265 ≤ d
        ·
          by_cases h : 15281 ≤ d
          ·
            by_cases h : 15289 ≤ d
            ·
              by_cases h : 15293 ≤ d
              ·
                by_cases h : 15295 ≤ d
                ·
                  by_cases h : 15296 ≤ d
                  ·
                    have : d = 15296 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 239)
      exact by decide
                  ·
                    have : d = 15295 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15294 ≤ d
                  ·
                    have : d = 15294 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15293 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15291 ≤ d
                ·
                  by_cases h : 15292 ≤ d
                  ·
                    have : d = 15292 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15291 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15290 ≤ d
                  ·
                    have : d = 15290 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 139)
      exact by decide
                  ·
                    have : d = 15289 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 15285 ≤ d
              ·
                by_cases h : 15287 ≤ d
                ·
                  by_cases h : 15288 ≤ d
                  ·
                    have : d = 15288 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 15287 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15286 ≤ d
                  ·
                    have : d = 15286 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15285 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15283 ≤ d
                ·
                  by_cases h : 15284 ≤ d
                  ·
                    have : d = 15284 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15283 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15282 ≤ d
                  ·
                    have : d = 15282 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 283)
      exact by decide
                  ·
                    have : d = 15281 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 15273 ≤ d
            ·
              by_cases h : 15277 ≤ d
              ·
                by_cases h : 15279 ≤ d
                ·
                  by_cases h : 15280 ≤ d
                  ·
                    have : d = 15280 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15279 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15278 ≤ d
                  ·
                    have : d = 15278 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7639)
      exact by decide
                  ·
                    have : d = 15277 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15275 ≤ d
                ·
                  by_cases h : 15276 ≤ d
                  ·
                    have : d = 15276 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 15275 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15274 ≤ d
                  ·
                    have : d = 15274 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15273 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 15269 ≤ d
              ·
                by_cases h : 15271 ≤ d
                ·
                  by_cases h : 15272 ≤ d
                  ·
                    have : d = 15272 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 15271 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15270 ≤ d
                  ·
                    have : d = 15270 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 509)
      exact by decide
                  ·
                    have : d = 15269 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15267 ≤ d
                ·
                  by_cases h : 15268 ≤ d
                  ·
                    have : d = 15268 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15267 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15266 ≤ d
                  ·
                    have : d = 15266 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15265 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 15249 ≤ d
          ·
            by_cases h : 15257 ≤ d
            ·
              by_cases h : 15261 ≤ d
              ·
                by_cases h : 15263 ≤ d
                ·
                  by_cases h : 15264 ≤ d
                  ·
                    have : d = 15264 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15263 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15262 ≤ d
                  ·
                    have : d = 15262 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15261 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15259 ≤ d
                ·
                  by_cases h : 15260 ≤ d
                  ·
                    have : d = 15260 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 109)
      exact by decide
                  ·
                    have : d = 15259 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15258 ≤ d
                  ·
                    have : d = 15258 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2543)
      exact by decide
                  ·
                    have : d = 15257 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 15253 ≤ d
              ·
                by_cases h : 15255 ≤ d
                ·
                  by_cases h : 15256 ≤ d
                  ·
                    have : d = 15256 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15255 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15254 ≤ d
                  ·
                    have : d = 15254 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15253 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15251 ≤ d
                ·
                  by_cases h : 15252 ≤ d
                  ·
                    have : d = 15252 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15251 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15250 ≤ d
                  ·
                    have : d = 15250 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15249 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 15241 ≤ d
            ·
              by_cases h : 15245 ≤ d
              ·
                by_cases h : 15247 ≤ d
                ·
                  by_cases h : 15248 ≤ d
                  ·
                    have : d = 15248 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 953)
      exact by decide
                  ·
                    have : d = 15247 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15246 ≤ d
                  ·
                    have : d = 15246 := by omega
                    subst d
      exact fullRecordGapTerm03940_not_prime
                  ·
                    have : d = 15245 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15243 ≤ d
                ·
                  by_cases h : 15244 ≤ d
                  ·
                    have : d = 15244 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15243 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15242 ≤ d
                  ·
                    have : d = 15242 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15241 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 15237 ≤ d
              ·
                by_cases h : 15239 ≤ d
                ·
                  by_cases h : 15240 ≤ d
                  ·
                    have : d = 15240 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 127)
      exact by decide
                  ·
                    have : d = 15239 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15238 ≤ d
                  ·
                    have : d = 15238 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15237 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15235 ≤ d
                ·
                  by_cases h : 15236 ≤ d
                  ·
                    have : d = 15236 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 15235 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15234 ≤ d
                  ·
                    have : d = 15234 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15233 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 15169 ≤ d
      ·
        by_cases h : 15201 ≤ d
        ·
          by_cases h : 15217 ≤ d
          ·
            by_cases h : 15225 ≤ d
            ·
              by_cases h : 15229 ≤ d
              ·
                by_cases h : 15231 ≤ d
                ·
                  by_cases h : 15232 ≤ d
                  ·
                    have : d = 15232 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15231 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15230 ≤ d
                  ·
                    have : d = 15230 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1523)
      exact by decide
                  ·
                    have : d = 15229 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15227 ≤ d
                ·
                  by_cases h : 15228 ≤ d
                  ·
                    have : d = 15228 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 47)
      exact by decide
                  ·
                    have : d = 15227 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15226 ≤ d
                  ·
                    have : d = 15226 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15225 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 15221 ≤ d
              ·
                by_cases h : 15223 ≤ d
                ·
                  by_cases h : 15224 ≤ d
                  ·
                    have : d = 15224 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15223 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15222 ≤ d
                  ·
                    have : d = 15222 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 43)
      exact by decide
                  ·
                    have : d = 15221 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15219 ≤ d
                ·
                  by_cases h : 15220 ≤ d
                  ·
                    have : d = 15220 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15219 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15218 ≤ d
                  ·
                    have : d = 15218 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1087)
      exact by decide
                  ·
                    have : d = 15217 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 15209 ≤ d
            ·
              by_cases h : 15213 ≤ d
              ·
                by_cases h : 15215 ≤ d
                ·
                  by_cases h : 15216 ≤ d
                  ·
                    have : d = 15216 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 317)
      exact by decide
                  ·
                    have : d = 15215 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15214 ≤ d
                  ·
                    have : d = 15214 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15213 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15211 ≤ d
                ·
                  by_cases h : 15212 ≤ d
                  ·
                    have : d = 15212 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3803)
      exact by decide
                  ·
                    have : d = 15211 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15210 ≤ d
                  ·
                    have : d = 15210 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15209 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 15205 ≤ d
              ·
                by_cases h : 15207 ≤ d
                ·
                  by_cases h : 15208 ≤ d
                  ·
                    have : d = 15208 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15207 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15206 ≤ d
                  ·
                    have : d = 15206 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7603)
      exact by decide
                  ·
                    have : d = 15205 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15203 ≤ d
                ·
                  by_cases h : 15204 ≤ d
                  ·
                    have : d = 15204 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15203 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15202 ≤ d
                  ·
                    have : d = 15202 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15201 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 15185 ≤ d
          ·
            by_cases h : 15193 ≤ d
            ·
              by_cases h : 15197 ≤ d
              ·
                by_cases h : 15199 ≤ d
                ·
                  by_cases h : 15200 ≤ d
                  ·
                    have : d = 15200 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 15199 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15198 ≤ d
                  ·
                    have : d = 15198 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15197 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15195 ≤ d
                ·
                  by_cases h : 15196 ≤ d
                  ·
                    have : d = 15196 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15195 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15194 ≤ d
                  ·
                    have : d = 15194 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15193 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 15189 ≤ d
              ·
                by_cases h : 15191 ≤ d
                ·
                  by_cases h : 15192 ≤ d
                  ·
                    have : d = 15192 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 211)
      exact by decide
                  ·
                    have : d = 15191 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15190 ≤ d
                  ·
                    have : d = 15190 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15189 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15187 ≤ d
                ·
                  by_cases h : 15188 ≤ d
                  ·
                    have : d = 15188 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3797)
      exact by decide
                  ·
                    have : d = 15187 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15186 ≤ d
                  ·
                    have : d = 15186 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2531)
      exact by decide
                  ·
                    have : d = 15185 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 15177 ≤ d
            ·
              by_cases h : 15181 ≤ d
              ·
                by_cases h : 15183 ≤ d
                ·
                  by_cases h : 15184 ≤ d
                  ·
                    have : d = 15184 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15183 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15182 ≤ d
                  ·
                    have : d = 15182 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15181 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15179 ≤ d
                ·
                  by_cases h : 15180 ≤ d
                  ·
                    have : d = 15180 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 15179 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15178 ≤ d
                  ·
                    have : d = 15178 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15177 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 15173 ≤ d
              ·
                by_cases h : 15175 ≤ d
                ·
                  by_cases h : 15176 ≤ d
                  ·
                    have : d = 15176 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15175 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15174 ≤ d
                  ·
                    have : d = 15174 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15173 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15171 ≤ d
                ·
                  by_cases h : 15172 ≤ d
                  ·
                    have : d = 15172 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15171 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15170 ≤ d
                  ·
                    have : d = 15170 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 15169 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 15137 ≤ d
        ·
          by_cases h : 15153 ≤ d
          ·
            by_cases h : 15161 ≤ d
            ·
              by_cases h : 15165 ≤ d
              ·
                by_cases h : 15167 ≤ d
                ·
                  by_cases h : 15168 ≤ d
                  ·
                    have : d = 15168 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15167 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15166 ≤ d
                  ·
                    have : d = 15166 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15165 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15163 ≤ d
                ·
                  by_cases h : 15164 ≤ d
                  ·
                    have : d = 15164 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15163 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15162 ≤ d
                  ·
                    have : d = 15162 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 15161 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 15157 ≤ d
              ·
                by_cases h : 15159 ≤ d
                ·
                  by_cases h : 15160 ≤ d
                  ·
                    have : d = 15160 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15159 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15158 ≤ d
                  ·
                    have : d = 15158 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 15157 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15155 ≤ d
                ·
                  by_cases h : 15156 ≤ d
                  ·
                    have : d = 15156 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 421)
      exact by decide
                  ·
                    have : d = 15155 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15154 ≤ d
                  ·
                    have : d = 15154 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15153 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 15145 ≤ d
            ·
              by_cases h : 15149 ≤ d
              ·
                by_cases h : 15151 ≤ d
                ·
                  by_cases h : 15152 ≤ d
                  ·
                    have : d = 15152 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 947)
      exact by decide
                  ·
                    have : d = 15151 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15150 ≤ d
                  ·
                    have : d = 15150 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 101)
      exact by decide
                  ·
                    have : d = 15149 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15147 ≤ d
                ·
                  by_cases h : 15148 ≤ d
                  ·
                    have : d = 15148 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15147 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15146 ≤ d
                  ·
                    have : d = 15146 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7573)
      exact by decide
                  ·
                    have : d = 15145 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 15141 ≤ d
              ·
                by_cases h : 15143 ≤ d
                ·
                  by_cases h : 15144 ≤ d
                  ·
                    have : d = 15144 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15143 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15142 ≤ d
                  ·
                    have : d = 15142 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15141 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15139 ≤ d
                ·
                  by_cases h : 15140 ≤ d
                  ·
                    have : d = 15140 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15139 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15138 ≤ d
                  ·
                    have : d = 15138 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 15137 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 15121 ≤ d
          ·
            by_cases h : 15129 ≤ d
            ·
              by_cases h : 15133 ≤ d
              ·
                by_cases h : 15135 ≤ d
                ·
                  by_cases h : 15136 ≤ d
                  ·
                    have : d = 15136 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15135 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15134 ≤ d
                  ·
                    have : d = 15134 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15133 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15131 ≤ d
                ·
                  by_cases h : 15132 ≤ d
                  ·
                    have : d = 15132 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15131 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15130 ≤ d
                  ·
                    have : d = 15130 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15129 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 15125 ≤ d
              ·
                by_cases h : 15127 ≤ d
                ·
                  by_cases h : 15128 ≤ d
                  ·
                    have : d = 15128 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 15127 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15126 ≤ d
                  ·
                    have : d = 15126 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15125 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15123 ≤ d
                ·
                  by_cases h : 15124 ≤ d
                  ·
                    have : d = 15124 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15123 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15122 ≤ d
                  ·
                    have : d = 15122 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7561)
      exact by decide
                  ·
                    have : d = 15121 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 15113 ≤ d
            ·
              by_cases h : 15117 ≤ d
              ·
                by_cases h : 15119 ≤ d
                ·
                  by_cases h : 15120 ≤ d
                  ·
                    have : d = 15120 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 690997)
      right
      exact ⟨675877, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15119 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15118 ≤ d
                  ·
                    have : d = 15118 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15117 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15115 ≤ d
                ·
                  by_cases h : 15116 ≤ d
                  ·
                    have : d = 15116 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3779)
      exact by decide
                  ·
                    have : d = 15115 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15114 ≤ d
                  ·
                    have : d = 15114 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15113 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 15109 ≤ d
              ·
                by_cases h : 15111 ≤ d
                ·
                  by_cases h : 15112 ≤ d
                  ·
                    have : d = 15112 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15111 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15110 ≤ d
                  ·
                    have : d = 15110 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15109 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15107 ≤ d
                ·
                  by_cases h : 15108 ≤ d
                  ·
                    have : d = 15108 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1259)
      exact by decide
                  ·
                    have : d = 15107 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15106 ≤ d
                  ·
                    have : d = 15106 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15105 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
  ·
    by_cases h : 14977 ≤ d
    ·
      by_cases h : 15041 ≤ d
      ·
        by_cases h : 15073 ≤ d
        ·
          by_cases h : 15089 ≤ d
          ·
            by_cases h : 15097 ≤ d
            ·
              by_cases h : 15101 ≤ d
              ·
                by_cases h : 15103 ≤ d
                ·
                  by_cases h : 15104 ≤ d
                  ·
                    have : d = 15104 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15103 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15102 ≤ d
                  ·
                    have : d = 15102 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 839)
      exact by decide
                  ·
                    have : d = 15101 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15099 ≤ d
                ·
                  by_cases h : 15100 ≤ d
                  ·
                    have : d = 15100 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15099 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15098 ≤ d
                  ·
                    have : d = 15098 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15097 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 15093 ≤ d
              ·
                by_cases h : 15095 ≤ d
                ·
                  by_cases h : 15096 ≤ d
                  ·
                    have : d = 15096 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 15095 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15094 ≤ d
                  ·
                    have : d = 15094 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15093 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15091 ≤ d
                ·
                  by_cases h : 15092 ≤ d
                  ·
                    have : d = 15092 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5946593)
      right
      exact ⟨5931501, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15091 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15090 ≤ d
                  ·
                    have : d = 15090 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 503)
      exact by decide
                  ·
                    have : d = 15089 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 15081 ≤ d
            ·
              by_cases h : 15085 ≤ d
              ·
                by_cases h : 15087 ≤ d
                ·
                  by_cases h : 15088 ≤ d
                  ·
                    have : d = 15088 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15087 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15086 ≤ d
                  ·
                    have : d = 15086 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 15085 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15083 ≤ d
                ·
                  by_cases h : 15084 ≤ d
                  ·
                    have : d = 15084 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15083 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15082 ≤ d
                  ·
                    have : d = 15082 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15081 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 15077 ≤ d
              ·
                by_cases h : 15079 ≤ d
                ·
                  by_cases h : 15080 ≤ d
                  ·
                    have : d = 15080 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 15079 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15078 ≤ d
                  ·
                    have : d = 15078 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 359)
      exact by decide
                  ·
                    have : d = 15077 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15075 ≤ d
                ·
                  by_cases h : 15076 ≤ d
                  ·
                    have : d = 15076 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15075 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15074 ≤ d
                  ·
                    have : d = 15074 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15073 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 15057 ≤ d
          ·
            by_cases h : 15065 ≤ d
            ·
              by_cases h : 15069 ≤ d
              ·
                by_cases h : 15071 ≤ d
                ·
                  by_cases h : 15072 ≤ d
                  ·
                    have : d = 15072 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 157)
      exact by decide
                  ·
                    have : d = 15071 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15070 ≤ d
                  ·
                    have : d = 15070 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15069 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15067 ≤ d
                ·
                  by_cases h : 15068 ≤ d
                  ·
                    have : d = 15068 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3767)
      exact by decide
                  ·
                    have : d = 15067 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15066 ≤ d
                  ·
                    have : d = 15066 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15065 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 15061 ≤ d
              ·
                by_cases h : 15063 ≤ d
                ·
                  by_cases h : 15064 ≤ d
                  ·
                    have : d = 15064 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15063 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15062 ≤ d
                  ·
                    have : d = 15062 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 15061 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15059 ≤ d
                ·
                  by_cases h : 15060 ≤ d
                  ·
                    have : d = 15060 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 251)
      exact by decide
                  ·
                    have : d = 15059 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15058 ≤ d
                  ·
                    have : d = 15058 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15057 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 15049 ≤ d
            ·
              by_cases h : 15053 ≤ d
              ·
                by_cases h : 15055 ≤ d
                ·
                  by_cases h : 15056 ≤ d
                  ·
                    have : d = 15056 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15055 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15054 ≤ d
                  ·
                    have : d = 15054 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15053 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15051 ≤ d
                ·
                  by_cases h : 15052 ≤ d
                  ·
                    have : d = 15052 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15051 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15050 ≤ d
                  ·
                    have : d = 15050 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 43)
      exact by decide
                  ·
                    have : d = 15049 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 15045 ≤ d
              ·
                by_cases h : 15047 ≤ d
                ·
                  by_cases h : 15048 ≤ d
                  ·
                    have : d = 15048 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 15047 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15046 ≤ d
                  ·
                    have : d = 15046 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15045 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15043 ≤ d
                ·
                  by_cases h : 15044 ≤ d
                  ·
                    have : d = 15044 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15043 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15042 ≤ d
                  ·
                    have : d = 15042 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15041 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 15009 ≤ d
        ·
          by_cases h : 15025 ≤ d
          ·
            by_cases h : 15033 ≤ d
            ·
              by_cases h : 15037 ≤ d
              ·
                by_cases h : 15039 ≤ d
                ·
                  by_cases h : 15040 ≤ d
                  ·
                    have : d = 15040 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15039 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15038 ≤ d
                  ·
                    have : d = 15038 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 73)
      exact by decide
                  ·
                    have : d = 15037 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15035 ≤ d
                ·
                  by_cases h : 15036 ≤ d
                  ·
                    have : d = 15036 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 179)
      exact by decide
                  ·
                    have : d = 15035 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15034 ≤ d
                  ·
                    have : d = 15034 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15033 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 15029 ≤ d
              ·
                by_cases h : 15031 ≤ d
                ·
                  by_cases h : 15032 ≤ d
                  ·
                    have : d = 15032 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1879)
      exact by decide
                  ·
                    have : d = 15031 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15030 ≤ d
                  ·
                    have : d = 15030 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 167)
      exact by decide
                  ·
                    have : d = 15029 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15027 ≤ d
                ·
                  by_cases h : 15028 ≤ d
                  ·
                    have : d = 15028 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15027 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15026 ≤ d
                  ·
                    have : d = 15026 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 683)
      exact by decide
                  ·
                    have : d = 15025 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 15017 ≤ d
            ·
              by_cases h : 15021 ≤ d
              ·
                by_cases h : 15023 ≤ d
                ·
                  by_cases h : 15024 ≤ d
                  ·
                    have : d = 15024 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15023 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15022 ≤ d
                  ·
                    have : d = 15022 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15021 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15019 ≤ d
                ·
                  by_cases h : 15020 ≤ d
                  ·
                    have : d = 15020 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 751)
      exact by decide
                  ·
                    have : d = 15019 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15018 ≤ d
                  ·
                    have : d = 15018 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2503)
      exact by decide
                  ·
                    have : d = 15017 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 15013 ≤ d
              ·
                by_cases h : 15015 ≤ d
                ·
                  by_cases h : 15016 ≤ d
                  ·
                    have : d = 15016 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15015 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15014 ≤ d
                  ·
                    have : d = 15014 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15013 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15011 ≤ d
                ·
                  by_cases h : 15012 ≤ d
                  ·
                    have : d = 15012 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 139)
      exact by decide
                  ·
                    have : d = 15011 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15010 ≤ d
                  ·
                    have : d = 15010 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15009 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 14993 ≤ d
          ·
            by_cases h : 15001 ≤ d
            ·
              by_cases h : 15005 ≤ d
              ·
                by_cases h : 15007 ≤ d
                ·
                  by_cases h : 15008 ≤ d
                  ·
                    have : d = 15008 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 67)
      exact by decide
                  ·
                    have : d = 15007 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15006 ≤ d
                  ·
                    have : d = 15006 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 41)
      exact by decide
                  ·
                    have : d = 15005 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 15003 ≤ d
                ·
                  by_cases h : 15004 ≤ d
                  ·
                    have : d = 15004 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 15003 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 15002 ≤ d
                  ·
                    have : d = 15002 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 15001 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 14997 ≤ d
              ·
                by_cases h : 14999 ≤ d
                ·
                  by_cases h : 15000 ≤ d
                  ·
                    have : d = 15000 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14999 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14998 ≤ d
                  ·
                    have : d = 14998 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14997 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 14995 ≤ d
                ·
                  by_cases h : 14996 ≤ d
                  ·
                    have : d = 14996 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 14995 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14994 ≤ d
                  ·
                    have : d = 14994 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14993 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 14985 ≤ d
            ·
              by_cases h : 14989 ≤ d
              ·
                by_cases h : 14991 ≤ d
                ·
                  by_cases h : 14992 ≤ d
                  ·
                    have : d = 14992 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14991 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14990 ≤ d
                  ·
                    have : d = 14990 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1499)
      exact by decide
                  ·
                    have : d = 14989 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 14987 ≤ d
                ·
                  by_cases h : 14988 ≤ d
                  ·
                    have : d = 14988 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1249)
      exact by decide
                  ·
                    have : d = 14987 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14986 ≤ d
                  ·
                    have : d = 14986 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14985 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 14981 ≤ d
              ·
                by_cases h : 14983 ≤ d
                ·
                  by_cases h : 14984 ≤ d
                  ·
                    have : d = 14984 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14983 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14982 ≤ d
                  ·
                    have : d = 14982 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 227)
      exact by decide
                  ·
                    have : d = 14981 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 14979 ≤ d
                ·
                  by_cases h : 14980 ≤ d
                  ·
                    have : d = 14980 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14979 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14978 ≤ d
                  ·
                    have : d = 14978 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14977 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 14913 ≤ d
      ·
        by_cases h : 14945 ≤ d
        ·
          by_cases h : 14961 ≤ d
          ·
            by_cases h : 14969 ≤ d
            ·
              by_cases h : 14973 ≤ d
              ·
                by_cases h : 14975 ≤ d
                ·
                  by_cases h : 14976 ≤ d
                  ·
                    have : d = 14976 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 14975 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14974 ≤ d
                  ·
                    have : d = 14974 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14973 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 14971 ≤ d
                ·
                  by_cases h : 14972 ≤ d
                  ·
                    have : d = 14972 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14971 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14970 ≤ d
                  ·
                    have : d = 14970 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 499)
      exact by decide
                  ·
                    have : d = 14969 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 14965 ≤ d
              ·
                by_cases h : 14967 ≤ d
                ·
                  by_cases h : 14968 ≤ d
                  ·
                    have : d = 14968 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14967 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14966 ≤ d
                  ·
                    have : d = 14966 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1069)
      exact by decide
                  ·
                    have : d = 14965 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 14963 ≤ d
                ·
                  by_cases h : 14964 ≤ d
                  ·
                    have : d = 14964 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14963 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14962 ≤ d
                  ·
                    have : d = 14962 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14961 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 14953 ≤ d
            ·
              by_cases h : 14957 ≤ d
              ·
                by_cases h : 14959 ≤ d
                ·
                  by_cases h : 14960 ≤ d
                  ·
                    have : d = 14960 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 14959 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14958 ≤ d
                  ·
                    have : d = 14958 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14957 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 14955 ≤ d
                ·
                  by_cases h : 14956 ≤ d
                  ·
                    have : d = 14956 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14955 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14954 ≤ d
                  ·
                    have : d = 14954 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14953 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 14949 ≤ d
              ·
                by_cases h : 14951 ≤ d
                ·
                  by_cases h : 14952 ≤ d
                  ·
                    have : d = 14952 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 89)
      exact by decide
                  ·
                    have : d = 14951 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14950 ≤ d
                  ·
                    have : d = 14950 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14949 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 14947 ≤ d
                ·
                  by_cases h : 14948 ≤ d
                  ·
                    have : d = 14948 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 14947 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14946 ≤ d
                  ·
                    have : d = 14946 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 47)
      exact by decide
                  ·
                    have : d = 14945 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 14929 ≤ d
          ·
            by_cases h : 14937 ≤ d
            ·
              by_cases h : 14941 ≤ d
              ·
                by_cases h : 14943 ≤ d
                ·
                  by_cases h : 14944 ≤ d
                  ·
                    have : d = 14944 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14943 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14942 ≤ d
                  ·
                    have : d = 14942 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 14941 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 14939 ≤ d
                ·
                  by_cases h : 14940 ≤ d
                  ·
                    have : d = 14940 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 83)
      exact by decide
                  ·
                    have : d = 14939 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14938 ≤ d
                  ·
                    have : d = 14938 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14937 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 14933 ≤ d
              ·
                by_cases h : 14935 ≤ d
                ·
                  by_cases h : 14936 ≤ d
                  ·
                    have : d = 14936 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1867)
      exact by decide
                  ·
                    have : d = 14935 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14934 ≤ d
                  ·
                    have : d = 14934 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14933 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 14931 ≤ d
                ·
                  by_cases h : 14932 ≤ d
                  ·
                    have : d = 14932 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14931 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14930 ≤ d
                  ·
                    have : d = 14930 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14929 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 14921 ≤ d
            ·
              by_cases h : 14925 ≤ d
              ·
                by_cases h : 14927 ≤ d
                ·
                  by_cases h : 14928 ≤ d
                  ·
                    have : d = 14928 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 311)
      exact by decide
                  ·
                    have : d = 14927 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14926 ≤ d
                  ·
                    have : d = 14926 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14925 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 14923 ≤ d
                ·
                  by_cases h : 14924 ≤ d
                  ·
                    have : d = 14924 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14923 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14922 ≤ d
                  ·
                    have : d = 14922 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 829)
      exact by decide
                  ·
                    have : d = 14921 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 14917 ≤ d
              ·
                by_cases h : 14919 ≤ d
                ·
                  by_cases h : 14920 ≤ d
                  ·
                    have : d = 14920 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14919 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14918 ≤ d
                  ·
                    have : d = 14918 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7459)
      exact by decide
                  ·
                    have : d = 14917 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 14915 ≤ d
                ·
                  by_cases h : 14916 ≤ d
                  ·
                    have : d = 14916 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14915 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14914 ≤ d
                  ·
                    have : d = 14914 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14913 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 14881 ≤ d
        ·
          by_cases h : 14897 ≤ d
          ·
            by_cases h : 14905 ≤ d
            ·
              by_cases h : 14909 ≤ d
              ·
                by_cases h : 14911 ≤ d
                ·
                  by_cases h : 14912 ≤ d
                  ·
                    have : d = 14912 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14911 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14910 ≤ d
                  ·
                    have : d = 14910 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 71)
      exact by decide
                  ·
                    have : d = 14909 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 14907 ≤ d
                ·
                  by_cases h : 14908 ≤ d
                  ·
                    have : d = 14908 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14907 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14906 ≤ d
                  ·
                    have : d = 14906 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 14905 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 14901 ≤ d
              ·
                by_cases h : 14903 ≤ d
                ·
                  by_cases h : 14904 ≤ d
                  ·
                    have : d = 14904 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14903 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14902 ≤ d
                  ·
                    have : d = 14902 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14901 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 14899 ≤ d
                ·
                  by_cases h : 14900 ≤ d
                  ·
                    have : d = 14900 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 149)
      exact by decide
                  ·
                    have : d = 14899 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14898 ≤ d
                  ·
                    have : d = 14898 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 14897 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 14889 ≤ d
            ·
              by_cases h : 14893 ≤ d
              ·
                by_cases h : 14895 ≤ d
                ·
                  by_cases h : 14896 ≤ d
                  ·
                    have : d = 14896 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14895 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14894 ≤ d
                  ·
                    have : d = 14894 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14893 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 14891 ≤ d
                ·
                  by_cases h : 14892 ≤ d
                  ·
                    have : d = 14892 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 14891 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14890 ≤ d
                  ·
                    have : d = 14890 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14889 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 14885 ≤ d
              ·
                by_cases h : 14887 ≤ d
                ·
                  by_cases h : 14888 ≤ d
                  ·
                    have : d = 14888 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14887 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14886 ≤ d
                  ·
                    have : d = 14886 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 827)
      exact by decide
                  ·
                    have : d = 14885 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 14883 ≤ d
                ·
                  by_cases h : 14884 ≤ d
                  ·
                    have : d = 14884 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14883 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14882 ≤ d
                  ·
                    have : d = 14882 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1063)
      exact by decide
                  ·
                    have : d = 14881 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 14865 ≤ d
          ·
            by_cases h : 14873 ≤ d
            ·
              by_cases h : 14877 ≤ d
              ·
                by_cases h : 14879 ≤ d
                ·
                  by_cases h : 14880 ≤ d
                  ·
                    have : d = 14880 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 14879 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14878 ≤ d
                  ·
                    have : d = 14878 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14877 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 14875 ≤ d
                ·
                  by_cases h : 14876 ≤ d
                  ·
                    have : d = 14876 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3719)
      exact by decide
                  ·
                    have : d = 14875 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14874 ≤ d
                  ·
                    have : d = 14874 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14873 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 14869 ≤ d
              ·
                by_cases h : 14871 ≤ d
                ·
                  by_cases h : 14872 ≤ d
                  ·
                    have : d = 14872 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14871 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14870 ≤ d
                  ·
                    have : d = 14870 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1487)
      exact by decide
                  ·
                    have : d = 14869 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 14867 ≤ d
                ·
                  by_cases h : 14868 ≤ d
                  ·
                    have : d = 14868 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14867 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14866 ≤ d
                  ·
                    have : d = 14866 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14865 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 14857 ≤ d
            ·
              by_cases h : 14861 ≤ d
              ·
                by_cases h : 14863 ≤ d
                ·
                  by_cases h : 14864 ≤ d
                  ·
                    have : d = 14864 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14863 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14862 ≤ d
                  ·
                    have : d = 14862 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2477)
      exact by decide
                  ·
                    have : d = 14861 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 14859 ≤ d
                ·
                  by_cases h : 14860 ≤ d
                  ·
                    have : d = 14860 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14859 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14858 ≤ d
                  ·
                    have : d = 14858 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 14857 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 14853 ≤ d
              ·
                by_cases h : 14855 ≤ d
                ·
                  by_cases h : 14856 ≤ d
                  ·
                    have : d = 14856 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 619)
      exact by decide
                  ·
                    have : d = 14855 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14854 ≤ d
                  ·
                    have : d = 14854 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 14853 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 14851 ≤ d
                ·
                  by_cases h : 14852 ≤ d
                  ·
                    have : d = 14852 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 47)
      exact by decide
                  ·
                    have : d = 14851 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 14850 ≤ d
                  ·
                    have : d = 14850 := by omega
                    subst d
      exact fullRecordGapTerm03939_not_prime
                  ·
                    have : d = 14849 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩

end PrimeFactorUnimodality
