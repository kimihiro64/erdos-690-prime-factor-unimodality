import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapFermat

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

theorem fullRecordGapAddBlock_part1923 (d : Nat) (527873 ≤ d) (d ≤ 528384) : ¬(recordGapCenter + d).Prime := by
  by_cases h : 528129 ≤ d
  ·
    by_cases h : 528257 ≤ d
    ·
      by_cases h : 528321 ≤ d
      ·
        by_cases h : 528353 ≤ d
        ·
          by_cases h : 528369 ≤ d
          ·
            by_cases h : 528377 ≤ d
            ·
              by_cases h : 528381 ≤ d
              ·
                by_cases h : 528383 ≤ d
                ·
                  by_cases h : 528384 ≤ d
                  ·
                    have : d = 528384 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528383 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528382 ≤ d
                  ·
                    have : d = 528382 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528381 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528379 ≤ d
                ·
                  by_cases h : 528380 ≤ d
                  ·
                    have : d = 528380 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528379 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528378 ≤ d
                  ·
                    have : d = 528378 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 83)
      exact by decide
                  ·
                    have : d = 528377 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 528373 ≤ d
              ·
                by_cases h : 528375 ≤ d
                ·
                  by_cases h : 528376 ≤ d
                  ·
                    have : d = 528376 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528375 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528374 ≤ d
                  ·
                    have : d = 528374 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528373 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528371 ≤ d
                ·
                  by_cases h : 528372 ≤ d
                  ·
                    have : d = 528372 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 528371 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528370 ≤ d
                  ·
                    have : d = 528370 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528369 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 528361 ≤ d
            ·
              by_cases h : 528365 ≤ d
              ·
                by_cases h : 528367 ≤ d
                ·
                  by_cases h : 528368 ≤ d
                  ·
                    have : d = 528368 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 33023)
      exact by decide
                  ·
                    have : d = 528367 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528366 ≤ d
                  ·
                    have : d = 528366 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528365 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528363 ≤ d
                ·
                  by_cases h : 528364 ≤ d
                  ·
                    have : d = 528364 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528363 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528362 ≤ d
                  ·
                    have : d = 528362 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 67)
      exact by decide
                  ·
                    have : d = 528361 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 528357 ≤ d
              ·
                by_cases h : 528359 ≤ d
                ·
                  by_cases h : 528360 ≤ d
                  ·
                    have : d = 528360 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 528359 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528358 ≤ d
                  ·
                    have : d = 528358 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528357 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528355 ≤ d
                ·
                  by_cases h : 528356 ≤ d
                  ·
                    have : d = 528356 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 528355 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528354 ≤ d
                  ·
                    have : d = 528354 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528353 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 528337 ≤ d
          ·
            by_cases h : 528345 ≤ d
            ·
              by_cases h : 528349 ≤ d
              ·
                by_cases h : 528351 ≤ d
                ·
                  by_cases h : 528352 ≤ d
                  ·
                    have : d = 528352 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528351 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528350 ≤ d
                  ·
                    have : d = 528350 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 10567)
      exact by decide
                  ·
                    have : d = 528349 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528347 ≤ d
                ·
                  by_cases h : 528348 ≤ d
                  ·
                    have : d = 528348 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528347 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528346 ≤ d
                  ·
                    have : d = 528346 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528345 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 528341 ≤ d
              ·
                by_cases h : 528343 ≤ d
                ·
                  by_cases h : 528344 ≤ d
                  ·
                    have : d = 528344 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528343 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528342 ≤ d
                  ·
                    have : d = 528342 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 173)
      exact by decide
                  ·
                    have : d = 528341 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528339 ≤ d
                ·
                  by_cases h : 528340 ≤ d
                  ·
                    have : d = 528340 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528339 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528338 ≤ d
                  ·
                    have : d = 528338 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528337 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 528329 ≤ d
            ·
              by_cases h : 528333 ≤ d
              ·
                by_cases h : 528335 ≤ d
                ·
                  by_cases h : 528336 ≤ d
                  ·
                    have : d = 528336 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1223)
      exact by decide
                  ·
                    have : d = 528335 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528334 ≤ d
                  ·
                    have : d = 528334 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528333 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528331 ≤ d
                ·
                  by_cases h : 528332 ≤ d
                  ·
                    have : d = 528332 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 18869)
      exact by decide
                  ·
                    have : d = 528331 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528330 ≤ d
                  ·
                    have : d = 528330 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1601)
      exact by decide
                  ·
                    have : d = 528329 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 528325 ≤ d
              ·
                by_cases h : 528327 ≤ d
                ·
                  by_cases h : 528328 ≤ d
                  ·
                    have : d = 528328 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528327 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528326 ≤ d
                  ·
                    have : d = 528326 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528325 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528323 ≤ d
                ·
                  by_cases h : 528324 ≤ d
                  ·
                    have : d = 528324 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528323 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528322 ≤ d
                  ·
                    have : d = 528322 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528321 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 528289 ≤ d
        ·
          by_cases h : 528305 ≤ d
          ·
            by_cases h : 528313 ≤ d
            ·
              by_cases h : 528317 ≤ d
              ·
                by_cases h : 528319 ≤ d
                ·
                  by_cases h : 528320 ≤ d
                  ·
                    have : d = 528320 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 528319 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528318 ≤ d
                  ·
                    have : d = 528318 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 599)
      exact by decide
                  ·
                    have : d = 528317 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528315 ≤ d
                ·
                  by_cases h : 528316 ≤ d
                  ·
                    have : d = 528316 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528315 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528314 ≤ d
                  ·
                    have : d = 528314 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528313 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 528309 ≤ d
              ·
                by_cases h : 528311 ≤ d
                ·
                  by_cases h : 528312 ≤ d
                  ·
                    have : d = 528312 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 22013)
      exact by decide
                  ·
                    have : d = 528311 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528310 ≤ d
                  ·
                    have : d = 528310 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528309 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528307 ≤ d
                ·
                  by_cases h : 528308 ≤ d
                  ·
                    have : d = 528308 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 12007)
      exact by decide
                  ·
                    have : d = 528307 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528306 ≤ d
                  ·
                    have : d = 528306 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 191)
      exact by decide
                  ·
                    have : d = 528305 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 528297 ≤ d
            ·
              by_cases h : 528301 ≤ d
              ·
                by_cases h : 528303 ≤ d
                ·
                  by_cases h : 528304 ≤ d
                  ·
                    have : d = 528304 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528303 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528302 ≤ d
                  ·
                    have : d = 528302 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 528301 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528299 ≤ d
                ·
                  by_cases h : 528300 ≤ d
                  ·
                    have : d = 528300 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 587)
      exact by decide
                  ·
                    have : d = 528299 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528298 ≤ d
                  ·
                    have : d = 528298 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528297 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 528293 ≤ d
              ·
                by_cases h : 528295 ≤ d
                ·
                  by_cases h : 528296 ≤ d
                  ·
                    have : d = 528296 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528295 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528294 ≤ d
                  ·
                    have : d = 528294 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528293 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528291 ≤ d
                ·
                  by_cases h : 528292 ≤ d
                  ·
                    have : d = 528292 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528291 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528290 ≤ d
                  ·
                    have : d = 528290 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7547)
      exact by decide
                  ·
                    have : d = 528289 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 528273 ≤ d
          ·
            by_cases h : 528281 ≤ d
            ·
              by_cases h : 528285 ≤ d
              ·
                by_cases h : 528287 ≤ d
                ·
                  by_cases h : 528288 ≤ d
                  ·
                    have : d = 528288 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5503)
      exact by decide
                  ·
                    have : d = 528287 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528286 ≤ d
                  ·
                    have : d = 528286 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528285 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528283 ≤ d
                ·
                  by_cases h : 528284 ≤ d
                  ·
                    have : d = 528284 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528283 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528282 ≤ d
                  ·
                    have : d = 528282 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528281 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 528277 ≤ d
              ·
                by_cases h : 528279 ≤ d
                ·
                  by_cases h : 528280 ≤ d
                  ·
                    have : d = 528280 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528279 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528278 ≤ d
                  ·
                    have : d = 528278 := by omega
                    subst d
      exact fullRecordGapTerm08833_not_prime
                  ·
                    have : d = 528277 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528275 ≤ d
                ·
                  by_cases h : 528276 ≤ d
                  ·
                    have : d = 528276 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 528275 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528274 ≤ d
                  ·
                    have : d = 528274 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528273 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 528265 ≤ d
            ·
              by_cases h : 528269 ≤ d
              ·
                by_cases h : 528271 ≤ d
                ·
                  by_cases h : 528272 ≤ d
                  ·
                    have : d = 528272 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 137)
      exact by decide
                  ·
                    have : d = 528271 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528270 ≤ d
                  ·
                    have : d = 528270 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17609)
      exact by decide
                  ·
                    have : d = 528269 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528267 ≤ d
                ·
                  by_cases h : 528268 ≤ d
                  ·
                    have : d = 528268 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528267 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528266 ≤ d
                  ·
                    have : d = 528266 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5693327)
      right
      exact ⟨5165061, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528265 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 528261 ≤ d
              ·
                by_cases h : 528263 ≤ d
                ·
                  by_cases h : 528264 ≤ d
                  ·
                    have : d = 528264 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528263 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528262 ≤ d
                  ·
                    have : d = 528262 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528261 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528259 ≤ d
                ·
                  by_cases h : 528260 ≤ d
                  ·
                    have : d = 528260 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528259 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528258 ≤ d
                  ·
                    have : d = 528258 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 528257 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 528193 ≤ d
      ·
        by_cases h : 528225 ≤ d
        ·
          by_cases h : 528241 ≤ d
          ·
            by_cases h : 528249 ≤ d
            ·
              by_cases h : 528253 ≤ d
              ·
                by_cases h : 528255 ≤ d
                ·
                  by_cases h : 528256 ≤ d
                  ·
                    have : d = 528256 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528255 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528254 ≤ d
                  ·
                    have : d = 528254 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528253 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528251 ≤ d
                ·
                  by_cases h : 528252 ≤ d
                  ·
                    have : d = 528252 := by omega
                    subst d
      exact fullRecordGapTerm08832_not_prime
                  ·
                    have : d = 528251 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528250 ≤ d
                  ·
                    have : d = 528250 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528249 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 528245 ≤ d
              ·
                by_cases h : 528247 ≤ d
                ·
                  by_cases h : 528248 ≤ d
                  ·
                    have : d = 528248 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 9433)
      exact by decide
                  ·
                    have : d = 528247 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528246 ≤ d
                  ·
                    have : d = 528246 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29347)
      exact by decide
                  ·
                    have : d = 528245 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528243 ≤ d
                ·
                  by_cases h : 528244 ≤ d
                  ·
                    have : d = 528244 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528243 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528242 ≤ d
                  ·
                    have : d = 528242 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 528241 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 528233 ≤ d
            ·
              by_cases h : 528237 ≤ d
              ·
                by_cases h : 528239 ≤ d
                ·
                  by_cases h : 528240 ≤ d
                  ·
                    have : d = 528240 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528239 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528238 ≤ d
                  ·
                    have : d = 528238 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528237 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528235 ≤ d
                ·
                  by_cases h : 528236 ≤ d
                  ·
                    have : d = 528236 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 974161)
      right
      exact ⟨445925, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528235 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528234 ≤ d
                  ·
                    have : d = 528234 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528233 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 528229 ≤ d
              ·
                by_cases h : 528231 ≤ d
                ·
                  by_cases h : 528232 ≤ d
                  ·
                    have : d = 528232 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528231 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528230 ≤ d
                  ·
                    have : d = 528230 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 101)
      exact by decide
                  ·
                    have : d = 528229 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528227 ≤ d
                ·
                  by_cases h : 528228 ≤ d
                  ·
                    have : d = 528228 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 67)
      exact by decide
                  ·
                    have : d = 528227 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528226 ≤ d
                  ·
                    have : d = 528226 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528225 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 528209 ≤ d
          ·
            by_cases h : 528217 ≤ d
            ·
              by_cases h : 528221 ≤ d
              ·
                by_cases h : 528223 ≤ d
                ·
                  by_cases h : 528224 ≤ d
                  ·
                    have : d = 528224 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528223 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528222 ≤ d
                  ·
                    have : d = 528222 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 4917109)
      right
      exact ⟨4388887, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528221 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528219 ≤ d
                ·
                  by_cases h : 528220 ≤ d
                  ·
                    have : d = 528220 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528219 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528218 ≤ d
                  ·
                    have : d = 528218 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 528217 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 528213 ≤ d
              ·
                by_cases h : 528215 ≤ d
                ·
                  by_cases h : 528216 ≤ d
                  ·
                    have : d = 528216 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528215 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528214 ≤ d
                  ·
                    have : d = 528214 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528213 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528211 ≤ d
                ·
                  by_cases h : 528212 ≤ d
                  ·
                    have : d = 528212 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528211 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528210 ≤ d
                  ·
                    have : d = 528210 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5869)
      exact by decide
                  ·
                    have : d = 528209 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 528201 ≤ d
            ·
              by_cases h : 528205 ≤ d
              ·
                by_cases h : 528207 ≤ d
                ·
                  by_cases h : 528208 ≤ d
                  ·
                    have : d = 528208 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528207 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528206 ≤ d
                  ·
                    have : d = 528206 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 528205 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528203 ≤ d
                ·
                  by_cases h : 528204 ≤ d
                  ·
                    have : d = 528204 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528203 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528202 ≤ d
                  ·
                    have : d = 528202 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528201 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 528197 ≤ d
              ·
                by_cases h : 528199 ≤ d
                ·
                  by_cases h : 528200 ≤ d
                  ·
                    have : d = 528200 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 528199 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528198 ≤ d
                  ·
                    have : d = 528198 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528197 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528195 ≤ d
                ·
                  by_cases h : 528196 ≤ d
                  ·
                    have : d = 528196 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528195 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528194 ≤ d
                  ·
                    have : d = 528194 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528193 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 528161 ≤ d
        ·
          by_cases h : 528177 ≤ d
          ·
            by_cases h : 528185 ≤ d
            ·
              by_cases h : 528189 ≤ d
              ·
                by_cases h : 528191 ≤ d
                ·
                  by_cases h : 528192 ≤ d
                  ·
                    have : d = 528192 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 131)
      exact by decide
                  ·
                    have : d = 528191 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528190 ≤ d
                  ·
                    have : d = 528190 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528189 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528187 ≤ d
                ·
                  by_cases h : 528188 ≤ d
                  ·
                    have : d = 528188 := by omega
                    subst d
      exact fullRecordGapTerm08831_not_prime
                  ·
                    have : d = 528187 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528186 ≤ d
                  ·
                    have : d = 528186 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 47)
      exact by decide
                  ·
                    have : d = 528185 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 528181 ≤ d
              ·
                by_cases h : 528183 ≤ d
                ·
                  by_cases h : 528184 ≤ d
                  ·
                    have : d = 528184 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528183 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528182 ≤ d
                  ·
                    have : d = 528182 := by omega
                    subst d
      exact fullRecordGapTerm08830_not_prime
                  ·
                    have : d = 528181 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528179 ≤ d
                ·
                  by_cases h : 528180 ≤ d
                  ·
                    have : d = 528180 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 8803)
      exact by decide
                  ·
                    have : d = 528179 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528178 ≤ d
                  ·
                    have : d = 528178 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528177 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 528169 ≤ d
            ·
              by_cases h : 528173 ≤ d
              ·
                by_cases h : 528175 ≤ d
                ·
                  by_cases h : 528176 ≤ d
                  ·
                    have : d = 528176 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3001)
      exact by decide
                  ·
                    have : d = 528175 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528174 ≤ d
                  ·
                    have : d = 528174 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528173 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528171 ≤ d
                ·
                  by_cases h : 528172 ≤ d
                  ·
                    have : d = 528172 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528171 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528170 ≤ d
                  ·
                    have : d = 528170 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528169 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 528165 ≤ d
              ·
                by_cases h : 528167 ≤ d
                ·
                  by_cases h : 528168 ≤ d
                  ·
                    have : d = 528168 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 59)
      exact by decide
                  ·
                    have : d = 528167 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528166 ≤ d
                  ·
                    have : d = 528166 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528165 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528163 ≤ d
                ·
                  by_cases h : 528164 ≤ d
                  ·
                    have : d = 528164 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528163 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528162 ≤ d
                  ·
                    have : d = 528162 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 528161 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 528145 ≤ d
          ·
            by_cases h : 528153 ≤ d
            ·
              by_cases h : 528157 ≤ d
              ·
                by_cases h : 528159 ≤ d
                ·
                  by_cases h : 528160 ≤ d
                  ·
                    have : d = 528160 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528159 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528158 ≤ d
                  ·
                    have : d = 528158 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 181)
      exact by decide
                  ·
                    have : d = 528157 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528155 ≤ d
                ·
                  by_cases h : 528156 ≤ d
                  ·
                    have : d = 528156 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528155 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528154 ≤ d
                  ·
                    have : d = 528154 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528153 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 528149 ≤ d
              ·
                by_cases h : 528151 ≤ d
                ·
                  by_cases h : 528152 ≤ d
                  ·
                    have : d = 528152 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 107)
      exact by decide
                  ·
                    have : d = 528151 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528150 ≤ d
                  ·
                    have : d = 528150 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528149 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528147 ≤ d
                ·
                  by_cases h : 528148 ≤ d
                  ·
                    have : d = 528148 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528147 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528146 ≤ d
                  ·
                    have : d = 528146 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 199)
      exact by decide
                  ·
                    have : d = 528145 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 528137 ≤ d
            ·
              by_cases h : 528141 ≤ d
              ·
                by_cases h : 528143 ≤ d
                ·
                  by_cases h : 528144 ≤ d
                  ·
                    have : d = 528144 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528143 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528142 ≤ d
                  ·
                    have : d = 528142 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528141 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528139 ≤ d
                ·
                  by_cases h : 528140 ≤ d
                  ·
                    have : d = 528140 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 26407)
      exact by decide
                  ·
                    have : d = 528139 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528138 ≤ d
                  ·
                    have : d = 528138 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 528137 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 528133 ≤ d
              ·
                by_cases h : 528135 ≤ d
                ·
                  by_cases h : 528136 ≤ d
                  ·
                    have : d = 528136 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528135 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528134 ≤ d
                  ·
                    have : d = 528134 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528133 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528131 ≤ d
                ·
                  by_cases h : 528132 ≤ d
                  ·
                    have : d = 528132 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 4001)
      exact by decide
                  ·
                    have : d = 528131 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528130 ≤ d
                  ·
                    have : d = 528130 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528129 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
  ·
    by_cases h : 528001 ≤ d
    ·
      by_cases h : 528065 ≤ d
      ·
        by_cases h : 528097 ≤ d
        ·
          by_cases h : 528113 ≤ d
          ·
            by_cases h : 528121 ≤ d
            ·
              by_cases h : 528125 ≤ d
              ·
                by_cases h : 528127 ≤ d
                ·
                  by_cases h : 528128 ≤ d
                  ·
                    have : d = 528128 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528127 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528126 ≤ d
                  ·
                    have : d = 528126 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 528125 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528123 ≤ d
                ·
                  by_cases h : 528124 ≤ d
                  ·
                    have : d = 528124 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528123 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528122 ≤ d
                  ·
                    have : d = 528122 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 528121 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 528117 ≤ d
              ·
                by_cases h : 528119 ≤ d
                ·
                  by_cases h : 528120 ≤ d
                  ·
                    have : d = 528120 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 163)
      exact by decide
                  ·
                    have : d = 528119 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528118 ≤ d
                  ·
                    have : d = 528118 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528117 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528115 ≤ d
                ·
                  by_cases h : 528116 ≤ d
                  ·
                    have : d = 528116 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 528115 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528114 ≤ d
                  ·
                    have : d = 528114 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528113 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 528105 ≤ d
            ·
              by_cases h : 528109 ≤ d
              ·
                by_cases h : 528111 ≤ d
                ·
                  by_cases h : 528112 ≤ d
                  ·
                    have : d = 528112 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528111 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528110 ≤ d
                  ·
                    have : d = 528110 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 4801)
      exact by decide
                  ·
                    have : d = 528109 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528107 ≤ d
                ·
                  by_cases h : 528108 ≤ d
                  ·
                    have : d = 528108 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 6287)
      exact by decide
                  ·
                    have : d = 528107 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528106 ≤ d
                  ·
                    have : d = 528106 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528105 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 528101 ≤ d
              ·
                by_cases h : 528103 ≤ d
                ·
                  by_cases h : 528104 ≤ d
                  ·
                    have : d = 528104 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528103 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528102 ≤ d
                  ·
                    have : d = 528102 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29339)
      exact by decide
                  ·
                    have : d = 528101 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528099 ≤ d
                ·
                  by_cases h : 528100 ≤ d
                  ·
                    have : d = 528100 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528099 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528098 ≤ d
                  ·
                    have : d = 528098 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 71)
      exact by decide
                  ·
                    have : d = 528097 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 528081 ≤ d
          ·
            by_cases h : 528089 ≤ d
            ·
              by_cases h : 528093 ≤ d
              ·
                by_cases h : 528095 ≤ d
                ·
                  by_cases h : 528096 ≤ d
                  ·
                    have : d = 528096 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5501)
      exact by decide
                  ·
                    have : d = 528095 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528094 ≤ d
                  ·
                    have : d = 528094 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528093 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528091 ≤ d
                ·
                  by_cases h : 528092 ≤ d
                  ·
                    have : d = 528092 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 47)
      exact by decide
                  ·
                    have : d = 528091 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528090 ≤ d
                  ·
                    have : d = 528090 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 528089 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 528085 ≤ d
              ·
                by_cases h : 528087 ≤ d
                ·
                  by_cases h : 528088 ≤ d
                  ·
                    have : d = 528088 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528087 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528086 ≤ d
                  ·
                    have : d = 528086 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528085 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528083 ≤ d
                ·
                  by_cases h : 528084 ≤ d
                  ·
                    have : d = 528084 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528083 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528082 ≤ d
                  ·
                    have : d = 528082 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528081 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 528073 ≤ d
            ·
              by_cases h : 528077 ≤ d
              ·
                by_cases h : 528079 ≤ d
                ·
                  by_cases h : 528080 ≤ d
                  ·
                    have : d = 528080 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 528079 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528078 ≤ d
                  ·
                    have : d = 528078 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 283)
      exact by decide
                  ·
                    have : d = 528077 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528075 ≤ d
                ·
                  by_cases h : 528076 ≤ d
                  ·
                    have : d = 528076 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528075 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528074 ≤ d
                  ·
                    have : d = 528074 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528073 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 528069 ≤ d
              ·
                by_cases h : 528071 ≤ d
                ·
                  by_cases h : 528072 ≤ d
                  ·
                    have : d = 528072 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528071 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528070 ≤ d
                  ·
                    have : d = 528070 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528069 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528067 ≤ d
                ·
                  by_cases h : 528068 ≤ d
                  ·
                    have : d = 528068 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 97)
      exact by decide
                  ·
                    have : d = 528067 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528066 ≤ d
                  ·
                    have : d = 528066 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 127)
      exact by decide
                  ·
                    have : d = 528065 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 528033 ≤ d
        ·
          by_cases h : 528049 ≤ d
          ·
            by_cases h : 528057 ≤ d
            ·
              by_cases h : 528061 ≤ d
              ·
                by_cases h : 528063 ≤ d
                ·
                  by_cases h : 528064 ≤ d
                  ·
                    have : d = 528064 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528063 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528062 ≤ d
                  ·
                    have : d = 528062 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528061 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528059 ≤ d
                ·
                  by_cases h : 528060 ≤ d
                  ·
                    have : d = 528060 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 528059 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528058 ≤ d
                  ·
                    have : d = 528058 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528057 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 528053 ≤ d
              ·
                by_cases h : 528055 ≤ d
                ·
                  by_cases h : 528056 ≤ d
                  ·
                    have : d = 528056 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 149)
      exact by decide
                  ·
                    have : d = 528055 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528054 ≤ d
                  ·
                    have : d = 528054 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528053 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528051 ≤ d
                ·
                  by_cases h : 528052 ≤ d
                  ·
                    have : d = 528052 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528051 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528050 ≤ d
                  ·
                    have : d = 528050 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 59)
      exact by decide
                  ·
                    have : d = 528049 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 528041 ≤ d
            ·
              by_cases h : 528045 ≤ d
              ·
                by_cases h : 528047 ≤ d
                ·
                  by_cases h : 528048 ≤ d
                  ·
                    have : d = 528048 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 528047 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528046 ≤ d
                  ·
                    have : d = 528046 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528045 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528043 ≤ d
                ·
                  by_cases h : 528044 ≤ d
                  ·
                    have : d = 528044 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528043 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528042 ≤ d
                  ·
                    have : d = 528042 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1155919)
      right
      exact ⟨627877, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528041 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 528037 ≤ d
              ·
                by_cases h : 528039 ≤ d
                ·
                  by_cases h : 528040 ≤ d
                  ·
                    have : d = 528040 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528039 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528038 ≤ d
                  ·
                    have : d = 528038 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37717)
      exact by decide
                  ·
                    have : d = 528037 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528035 ≤ d
                ·
                  by_cases h : 528036 ≤ d
                  ·
                    have : d = 528036 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 79)
      exact by decide
                  ·
                    have : d = 528035 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528034 ≤ d
                  ·
                    have : d = 528034 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528033 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 528017 ≤ d
          ·
            by_cases h : 528025 ≤ d
            ·
              by_cases h : 528029 ≤ d
              ·
                by_cases h : 528031 ≤ d
                ·
                  by_cases h : 528032 ≤ d
                  ·
                    have : d = 528032 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 528031 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528030 ≤ d
                  ·
                    have : d = 528030 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528029 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528027 ≤ d
                ·
                  by_cases h : 528028 ≤ d
                  ·
                    have : d = 528028 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528027 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528026 ≤ d
                  ·
                    have : d = 528026 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7721191)
      right
      exact ⟨7193165, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528025 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 528021 ≤ d
              ·
                by_cases h : 528023 ≤ d
                ·
                  by_cases h : 528024 ≤ d
                  ·
                    have : d = 528024 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528023 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528022 ≤ d
                  ·
                    have : d = 528022 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528021 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528019 ≤ d
                ·
                  by_cases h : 528020 ≤ d
                  ·
                    have : d = 528020 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 528019 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528018 ≤ d
                  ·
                    have : d = 528018 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528017 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 528009 ≤ d
            ·
              by_cases h : 528013 ≤ d
              ·
                by_cases h : 528015 ≤ d
                ·
                  by_cases h : 528016 ≤ d
                  ·
                    have : d = 528016 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528015 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528014 ≤ d
                  ·
                    have : d = 528014 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528013 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528011 ≤ d
                ·
                  by_cases h : 528012 ≤ d
                  ·
                    have : d = 528012 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 4889)
      exact by decide
                  ·
                    have : d = 528011 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528010 ≤ d
                  ·
                    have : d = 528010 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528009 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 528005 ≤ d
              ·
                by_cases h : 528007 ≤ d
                ·
                  by_cases h : 528008 ≤ d
                  ·
                    have : d = 528008 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 528007 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528006 ≤ d
                  ·
                    have : d = 528006 := by omega
                    subst d
      exact fullRecordGapTerm08829_not_prime
                  ·
                    have : d = 528005 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 528003 ≤ d
                ·
                  by_cases h : 528004 ≤ d
                  ·
                    have : d = 528004 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528003 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 528002 ≤ d
                  ·
                    have : d = 528002 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 528001 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 527937 ≤ d
      ·
        by_cases h : 527969 ≤ d
        ·
          by_cases h : 527985 ≤ d
          ·
            by_cases h : 527993 ≤ d
            ·
              by_cases h : 527997 ≤ d
              ·
                by_cases h : 527999 ≤ d
                ·
                  by_cases h : 528000 ≤ d
                  ·
                    have : d = 528000 := by omega
                    subst d
      exact fullRecordGapTerm08828_not_prime
                  ·
                    have : d = 527999 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527998 ≤ d
                  ·
                    have : d = 527998 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527997 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 527995 ≤ d
                ·
                  by_cases h : 527996 ≤ d
                  ·
                    have : d = 527996 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527995 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527994 ≤ d
                  ·
                    have : d = 527994 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527993 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 527989 ≤ d
              ·
                by_cases h : 527991 ≤ d
                ·
                  by_cases h : 527992 ≤ d
                  ·
                    have : d = 527992 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527991 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527990 ≤ d
                  ·
                    have : d = 527990 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 527989 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 527987 ≤ d
                ·
                  by_cases h : 527988 ≤ d
                  ·
                    have : d = 527988 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527987 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527986 ≤ d
                  ·
                    have : d = 527986 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527985 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 527977 ≤ d
            ·
              by_cases h : 527981 ≤ d
              ·
                by_cases h : 527983 ≤ d
                ·
                  by_cases h : 527984 ≤ d
                  ·
                    have : d = 527984 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527983 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527982 ≤ d
                  ·
                    have : d = 527982 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 527981 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 527979 ≤ d
                ·
                  by_cases h : 527980 ≤ d
                  ·
                    have : d = 527980 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527979 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527978 ≤ d
                  ·
                    have : d = 527978 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 103)
      exact by decide
                  ·
                    have : d = 527977 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 527973 ≤ d
              ·
                by_cases h : 527975 ≤ d
                ·
                  by_cases h : 527976 ≤ d
                  ·
                    have : d = 527976 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7333)
      exact by decide
                  ·
                    have : d = 527975 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527974 ≤ d
                  ·
                    have : d = 527974 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527973 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 527971 ≤ d
                ·
                  by_cases h : 527972 ≤ d
                  ·
                    have : d = 527972 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 527971 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527970 ≤ d
                  ·
                    have : d = 527970 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17599)
      exact by decide
                  ·
                    have : d = 527969 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 527953 ≤ d
          ·
            by_cases h : 527961 ≤ d
            ·
              by_cases h : 527965 ≤ d
              ·
                by_cases h : 527967 ≤ d
                ·
                  by_cases h : 527968 ≤ d
                  ·
                    have : d = 527968 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527967 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527966 ≤ d
                  ·
                    have : d = 527966 := by omega
                    subst d
      exact fullRecordGapTerm08827_not_prime
                  ·
                    have : d = 527965 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 527963 ≤ d
                ·
                  by_cases h : 527964 ≤ d
                  ·
                    have : d = 527964 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527963 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527962 ≤ d
                  ·
                    have : d = 527962 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527961 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 527957 ≤ d
              ·
                by_cases h : 527959 ≤ d
                ·
                  by_cases h : 527960 ≤ d
                  ·
                    have : d = 527960 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527959 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527958 ≤ d
                  ·
                    have : d = 527958 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3259)
      exact by decide
                  ·
                    have : d = 527957 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 527955 ≤ d
                ·
                  by_cases h : 527956 ≤ d
                  ·
                    have : d = 527956 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527955 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527954 ≤ d
                  ·
                    have : d = 527954 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527953 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 527945 ≤ d
            ·
              by_cases h : 527949 ≤ d
              ·
                by_cases h : 527951 ≤ d
                ·
                  by_cases h : 527952 ≤ d
                  ·
                    have : d = 527952 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527951 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527950 ≤ d
                  ·
                    have : d = 527950 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527949 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 527947 ≤ d
                ·
                  by_cases h : 527948 ≤ d
                  ·
                    have : d = 527948 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 89)
      exact by decide
                  ·
                    have : d = 527947 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527946 ≤ d
                  ·
                    have : d = 527946 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527945 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 527941 ≤ d
              ·
                by_cases h : 527943 ≤ d
                ·
                  by_cases h : 527944 ≤ d
                  ·
                    have : d = 527944 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527943 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527942 ≤ d
                  ·
                    have : d = 527942 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 527941 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 527939 ≤ d
                ·
                  by_cases h : 527940 ≤ d
                  ·
                    have : d = 527940 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 419)
      exact by decide
                  ·
                    have : d = 527939 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527938 ≤ d
                  ·
                    have : d = 527938 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527937 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 527905 ≤ d
        ·
          by_cases h : 527921 ≤ d
          ·
            by_cases h : 527929 ≤ d
            ·
              by_cases h : 527933 ≤ d
              ·
                by_cases h : 527935 ≤ d
                ·
                  by_cases h : 527936 ≤ d
                  ·
                    have : d = 527936 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 73)
      exact by decide
                  ·
                    have : d = 527935 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527934 ≤ d
                  ·
                    have : d = 527934 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527933 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 527931 ≤ d
                ·
                  by_cases h : 527932 ≤ d
                  ·
                    have : d = 527932 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527931 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527930 ≤ d
                  ·
                    have : d = 527930 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527929 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 527925 ≤ d
              ·
                by_cases h : 527927 ≤ d
                ·
                  by_cases h : 527928 ≤ d
                  ·
                    have : d = 527928 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 21997)
      exact by decide
                  ·
                    have : d = 527927 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527926 ≤ d
                  ·
                    have : d = 527926 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527925 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 527923 ≤ d
                ·
                  by_cases h : 527924 ≤ d
                  ·
                    have : d = 527924 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527923 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527922 ≤ d
                  ·
                    have : d = 527922 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 139)
      exact by decide
                  ·
                    have : d = 527921 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 527913 ≤ d
            ·
              by_cases h : 527917 ≤ d
              ·
                by_cases h : 527919 ≤ d
                ·
                  by_cases h : 527920 ≤ d
                  ·
                    have : d = 527920 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527919 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527918 ≤ d
                  ·
                    have : d = 527918 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527917 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 527915 ≤ d
                ·
                  by_cases h : 527916 ≤ d
                  ·
                    have : d = 527916 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 527915 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527914 ≤ d
                  ·
                    have : d = 527914 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527913 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 527909 ≤ d
              ·
                by_cases h : 527911 ≤ d
                ·
                  by_cases h : 527912 ≤ d
                  ·
                    have : d = 527912 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 857)
      exact by decide
                  ·
                    have : d = 527911 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527910 ≤ d
                  ·
                    have : d = 527910 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17597)
      exact by decide
                  ·
                    have : d = 527909 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 527907 ≤ d
                ·
                  by_cases h : 527908 ≤ d
                  ·
                    have : d = 527908 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527907 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527906 ≤ d
                  ·
                    have : d = 527906 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 144271)
      right
      exact ⟨49178, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527905 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 527889 ≤ d
          ·
            by_cases h : 527897 ≤ d
            ·
              by_cases h : 527901 ≤ d
              ·
                by_cases h : 527903 ≤ d
                ·
                  by_cases h : 527904 ≤ d
                  ·
                    have : d = 527904 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527903 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527902 ≤ d
                  ·
                    have : d = 527902 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527901 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 527899 ≤ d
                ·
                  by_cases h : 527900 ≤ d
                  ·
                    have : d = 527900 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5279)
      exact by decide
                  ·
                    have : d = 527899 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527898 ≤ d
                  ·
                    have : d = 527898 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 12569)
      exact by decide
                  ·
                    have : d = 527897 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 527893 ≤ d
              ·
                by_cases h : 527895 ≤ d
                ·
                  by_cases h : 527896 ≤ d
                  ·
                    have : d = 527896 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527895 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527894 ≤ d
                  ·
                    have : d = 527894 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527893 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 527891 ≤ d
                ·
                  by_cases h : 527892 ≤ d
                  ·
                    have : d = 527892 := by omega
                    subst d
      exact fullRecordGapTerm08826_not_prime
                  ·
                    have : d = 527891 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527890 ≤ d
                  ·
                    have : d = 527890 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527889 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 527881 ≤ d
            ·
              by_cases h : 527885 ≤ d
              ·
                by_cases h : 527887 ≤ d
                ·
                  by_cases h : 527888 ≤ d
                  ·
                    have : d = 527888 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 32993)
      exact by decide
                  ·
                    have : d = 527887 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527886 ≤ d
                  ·
                    have : d = 527886 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527885 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 527883 ≤ d
                ·
                  by_cases h : 527884 ≤ d
                  ·
                    have : d = 527884 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527883 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527882 ≤ d
                  ·
                    have : d = 527882 := by omega
                    subst d
      exact fullRecordGapTerm08825_not_prime
                  ·
                    have : d = 527881 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 527877 ≤ d
              ·
                by_cases h : 527879 ≤ d
                ·
                  by_cases h : 527880 ≤ d
                  ·
                    have : d = 527880 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 53)
      exact by decide
                  ·
                    have : d = 527879 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527878 ≤ d
                  ·
                    have : d = 527878 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527877 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 527875 ≤ d
                ·
                  by_cases h : 527876 ≤ d
                  ·
                    have : d = 527876 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527875 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 527874 ≤ d
                  ·
                    have : d = 527874 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 527873 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩

end PrimeFactorUnimodality
