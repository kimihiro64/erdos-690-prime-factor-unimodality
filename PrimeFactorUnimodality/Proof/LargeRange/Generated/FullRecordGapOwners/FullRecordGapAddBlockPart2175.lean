import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapFermat

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

theorem fullRecordGapAddBlock_part2175 (d : Nat) (656897 ≤ d) (d ≤ 657401) : ¬(recordGapCenter + d).Prime := by
  by_cases h : 657150 ≤ d
  ·
    by_cases h : 657276 ≤ d
    ·
      by_cases h : 657339 ≤ d
      ·
        by_cases h : 657371 ≤ d
        ·
          by_cases h : 657387 ≤ d
          ·
            by_cases h : 657395 ≤ d
            ·
              by_cases h : 657399 ≤ d
              ·
                by_cases h : 657401 ≤ d
                ·
                  have : d = 657401 := by omega
                  subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657400 ≤ d
                  ·
                    have : d = 657400 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657399 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657397 ≤ d
                ·
                  by_cases h : 657398 ≤ d
                  ·
                    have : d = 657398 := by omega
                    subst d
      exact fullRecordGapTerm10918_not_prime
                  ·
                    have : d = 657397 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657396 ≤ d
                  ·
                    have : d = 657396 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2029)
      exact by decide
                  ·
                    have : d = 657395 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 657391 ≤ d
              ·
                by_cases h : 657393 ≤ d
                ·
                  by_cases h : 657394 ≤ d
                  ·
                    have : d = 657394 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657393 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657392 ≤ d
                  ·
                    have : d = 657392 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 181)
      exact by decide
                  ·
                    have : d = 657391 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657389 ≤ d
                ·
                  by_cases h : 657390 ≤ d
                  ·
                    have : d = 657390 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657389 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657388 ≤ d
                  ·
                    have : d = 657388 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657387 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 657379 ≤ d
            ·
              by_cases h : 657383 ≤ d
              ·
                by_cases h : 657385 ≤ d
                ·
                  by_cases h : 657386 ≤ d
                  ·
                    have : d = 657386 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 657385 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657384 ≤ d
                  ·
                    have : d = 657384 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657383 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657381 ≤ d
                ·
                  by_cases h : 657382 ≤ d
                  ·
                    have : d = 657382 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657381 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657380 ≤ d
                  ·
                    have : d = 657380 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 32869)
      exact by decide
                  ·
                    have : d = 657379 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 657375 ≤ d
              ·
                by_cases h : 657377 ≤ d
                ·
                  by_cases h : 657378 ≤ d
                  ·
                    have : d = 657378 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657377 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657376 ≤ d
                  ·
                    have : d = 657376 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657375 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657373 ≤ d
                ·
                  by_cases h : 657374 ≤ d
                  ·
                    have : d = 657374 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657373 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657372 ≤ d
                  ·
                    have : d = 657372 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 657371 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 657355 ≤ d
          ·
            by_cases h : 657363 ≤ d
            ·
              by_cases h : 657367 ≤ d
              ·
                by_cases h : 657369 ≤ d
                ·
                  by_cases h : 657370 ≤ d
                  ·
                    have : d = 657370 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657369 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657368 ≤ d
                  ·
                    have : d = 657368 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 464483)
      right
      exact ⟨271598, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657367 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657365 ≤ d
                ·
                  by_cases h : 657366 ≤ d
                  ·
                    have : d = 657366 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 331)
      exact by decide
                  ·
                    have : d = 657365 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657364 ≤ d
                  ·
                    have : d = 657364 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657363 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 657359 ≤ d
              ·
                by_cases h : 657361 ≤ d
                ·
                  by_cases h : 657362 ≤ d
                  ·
                    have : d = 657362 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657361 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657360 ≤ d
                  ·
                    have : d = 657360 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 83)
      exact by decide
                  ·
                    have : d = 657359 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657357 ≤ d
                ·
                  by_cases h : 657358 ≤ d
                  ·
                    have : d = 657358 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657357 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657356 ≤ d
                  ·
                    have : d = 657356 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657355 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 657347 ≤ d
            ·
              by_cases h : 657351 ≤ d
              ·
                by_cases h : 657353 ≤ d
                ·
                  by_cases h : 657354 ≤ d
                  ·
                    have : d = 657354 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657353 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657352 ≤ d
                  ·
                    have : d = 657352 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657351 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657349 ≤ d
                ·
                  by_cases h : 657350 ≤ d
                  ·
                    have : d = 657350 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13147)
      exact by decide
                  ·
                    have : d = 657349 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657348 ≤ d
                  ·
                    have : d = 657348 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657347 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 657343 ≤ d
              ·
                by_cases h : 657345 ≤ d
                ·
                  by_cases h : 657346 ≤ d
                  ·
                    have : d = 657346 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657345 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657344 ≤ d
                  ·
                    have : d = 657344 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657343 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657341 ≤ d
                ·
                  by_cases h : 657342 ≤ d
                  ·
                    have : d = 657342 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 657341 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657340 ≤ d
                  ·
                    have : d = 657340 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657339 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 657308 ≤ d
        ·
          by_cases h : 657324 ≤ d
          ·
            by_cases h : 657332 ≤ d
            ·
              by_cases h : 657336 ≤ d
              ·
                by_cases h : 657338 ≤ d
                ·
                  have : d = 657338 := by omega
                  subst d
      apply fullRecordGap_add_not_prime (q := 29879)
      exact by decide
                ·
                  by_cases h : 657337 ≤ d
                  ·
                    have : d = 657337 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657336 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 61)
      exact by decide
              ·
                by_cases h : 657334 ≤ d
                ·
                  by_cases h : 657335 ≤ d
                  ·
                    have : d = 657335 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657334 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657333 ≤ d
                  ·
                    have : d = 657333 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657332 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
            ·
              by_cases h : 657328 ≤ d
              ·
                by_cases h : 657330 ≤ d
                ·
                  by_cases h : 657331 ≤ d
                  ·
                    have : d = 657331 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657330 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 21911)
      exact by decide
                ·
                  by_cases h : 657329 ≤ d
                  ·
                    have : d = 657329 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657328 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657326 ≤ d
                ·
                  by_cases h : 657327 ≤ d
                  ·
                    have : d = 657327 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657326 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 137)
      exact by decide
                ·
                  by_cases h : 657325 ≤ d
                  ·
                    have : d = 657325 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657324 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 657316 ≤ d
            ·
              by_cases h : 657320 ≤ d
              ·
                by_cases h : 657322 ≤ d
                ·
                  by_cases h : 657323 ≤ d
                  ·
                    have : d = 657323 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657322 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657321 ≤ d
                  ·
                    have : d = 657321 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657320 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657318 ≤ d
                ·
                  by_cases h : 657319 ≤ d
                  ·
                    have : d = 657319 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657318 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 71)
      exact by decide
                ·
                  by_cases h : 657317 ≤ d
                  ·
                    have : d = 657317 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657316 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 657312 ≤ d
              ·
                by_cases h : 657314 ≤ d
                ·
                  by_cases h : 657315 ≤ d
                  ·
                    have : d = 657315 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657314 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657313 ≤ d
                  ·
                    have : d = 657313 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657312 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657310 ≤ d
                ·
                  by_cases h : 657311 ≤ d
                  ·
                    have : d = 657311 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657310 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657309 ≤ d
                  ·
                    have : d = 657309 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657308 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 101)
      exact by decide
        ·
          by_cases h : 657292 ≤ d
          ·
            by_cases h : 657300 ≤ d
            ·
              by_cases h : 657304 ≤ d
              ·
                by_cases h : 657306 ≤ d
                ·
                  by_cases h : 657307 ≤ d
                  ·
                    have : d = 657307 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657306 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657305 ≤ d
                  ·
                    have : d = 657305 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657304 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657302 ≤ d
                ·
                  by_cases h : 657303 ≤ d
                  ·
                    have : d = 657303 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657302 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1229521)
      right
      exact ⟨572219, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657301 ≤ d
                  ·
                    have : d = 657301 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657300 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 313)
      exact by decide
            ·
              by_cases h : 657296 ≤ d
              ·
                by_cases h : 657298 ≤ d
                ·
                  by_cases h : 657299 ≤ d
                  ·
                    have : d = 657299 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657298 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657297 ≤ d
                  ·
                    have : d = 657297 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657296 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 41081)
      exact by decide
              ·
                by_cases h : 657294 ≤ d
                ·
                  by_cases h : 657295 ≤ d
                  ·
                    have : d = 657295 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657294 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657293 ≤ d
                  ·
                    have : d = 657293 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657292 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 657284 ≤ d
            ·
              by_cases h : 657288 ≤ d
              ·
                by_cases h : 657290 ≤ d
                ·
                  by_cases h : 657291 ≤ d
                  ·
                    have : d = 657291 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657290 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657289 ≤ d
                  ·
                    have : d = 657289 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657288 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
              ·
                by_cases h : 657286 ≤ d
                ·
                  by_cases h : 657287 ≤ d
                  ·
                    have : d = 657287 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657286 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657285 ≤ d
                  ·
                    have : d = 657285 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657284 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 657280 ≤ d
              ·
                by_cases h : 657282 ≤ d
                ·
                  by_cases h : 657283 ≤ d
                  ·
                    have : d = 657283 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657282 := by omega
                    subst d
      exact fullRecordGapTerm10917_not_prime
                ·
                  by_cases h : 657281 ≤ d
                  ·
                    have : d = 657281 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657280 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657278 ≤ d
                ·
                  by_cases h : 657279 ≤ d
                  ·
                    have : d = 657279 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657278 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657277 ≤ d
                  ·
                    have : d = 657277 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657276 := by omega
                    subst d
      exact fullRecordGapTerm10916_not_prime
    ·
      by_cases h : 657213 ≤ d
      ·
        by_cases h : 657245 ≤ d
        ·
          by_cases h : 657261 ≤ d
          ·
            by_cases h : 657269 ≤ d
            ·
              by_cases h : 657273 ≤ d
              ·
                by_cases h : 657275 ≤ d
                ·
                  have : d = 657275 := by omega
                  subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657274 ≤ d
                  ·
                    have : d = 657274 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657273 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657271 ≤ d
                ·
                  by_cases h : 657272 ≤ d
                  ·
                    have : d = 657272 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 97)
      exact by decide
                  ·
                    have : d = 657271 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657270 ≤ d
                  ·
                    have : d = 657270 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 67)
      exact by decide
                  ·
                    have : d = 657269 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 657265 ≤ d
              ·
                by_cases h : 657267 ≤ d
                ·
                  by_cases h : 657268 ≤ d
                  ·
                    have : d = 657268 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657267 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657266 ≤ d
                  ·
                    have : d = 657266 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 413551)
      right
      exact ⟨169836, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657265 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657263 ≤ d
                ·
                  by_cases h : 657264 ≤ d
                  ·
                    have : d = 657264 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657263 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657262 ≤ d
                  ·
                    have : d = 657262 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657261 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 657253 ≤ d
            ·
              by_cases h : 657257 ≤ d
              ·
                by_cases h : 657259 ≤ d
                ·
                  by_cases h : 657260 ≤ d
                  ·
                    have : d = 657260 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 59)
      exact by decide
                  ·
                    have : d = 657259 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657258 ≤ d
                  ·
                    have : d = 657258 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 15649)
      exact by decide
                  ·
                    have : d = 657257 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657255 ≤ d
                ·
                  by_cases h : 657256 ≤ d
                  ·
                    have : d = 657256 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657255 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657254 ≤ d
                  ·
                    have : d = 657254 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657253 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 657249 ≤ d
              ·
                by_cases h : 657251 ≤ d
                ·
                  by_cases h : 657252 ≤ d
                  ·
                    have : d = 657252 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 18257)
      exact by decide
                  ·
                    have : d = 657251 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657250 ≤ d
                  ·
                    have : d = 657250 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657249 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657247 ≤ d
                ·
                  by_cases h : 657248 ≤ d
                  ·
                    have : d = 657248 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 657247 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657246 ≤ d
                  ·
                    have : d = 657246 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657245 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 657229 ≤ d
          ·
            by_cases h : 657237 ≤ d
            ·
              by_cases h : 657241 ≤ d
              ·
                by_cases h : 657243 ≤ d
                ·
                  by_cases h : 657244 ≤ d
                  ·
                    have : d = 657244 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657243 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657242 ≤ d
                  ·
                    have : d = 657242 := by omega
                    subst d
      exact fullRecordGapTerm10915_not_prime
                  ·
                    have : d = 657241 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657239 ≤ d
                ·
                  by_cases h : 657240 ≤ d
                  ·
                    have : d = 657240 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5477)
      exact by decide
                  ·
                    have : d = 657239 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657238 ≤ d
                  ·
                    have : d = 657238 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657237 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 657233 ≤ d
              ·
                by_cases h : 657235 ≤ d
                ·
                  by_cases h : 657236 ≤ d
                  ·
                    have : d = 657236 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657235 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657234 ≤ d
                  ·
                    have : d = 657234 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657233 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657231 ≤ d
                ·
                  by_cases h : 657232 ≤ d
                  ·
                    have : d = 657232 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657231 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657230 ≤ d
                  ·
                    have : d = 657230 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 41)
      exact by decide
                  ·
                    have : d = 657229 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 657221 ≤ d
            ·
              by_cases h : 657225 ≤ d
              ·
                by_cases h : 657227 ≤ d
                ·
                  by_cases h : 657228 ≤ d
                  ·
                    have : d = 657228 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 657227 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657226 ≤ d
                  ·
                    have : d = 657226 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657225 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657223 ≤ d
                ·
                  by_cases h : 657224 ≤ d
                  ·
                    have : d = 657224 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657223 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657222 ≤ d
                  ·
                    have : d = 657222 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657221 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 657217 ≤ d
              ·
                by_cases h : 657219 ≤ d
                ·
                  by_cases h : 657220 ≤ d
                  ·
                    have : d = 657220 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657219 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657218 ≤ d
                  ·
                    have : d = 657218 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 347)
      exact by decide
                  ·
                    have : d = 657217 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657215 ≤ d
                ·
                  by_cases h : 657216 ≤ d
                  ·
                    have : d = 657216 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 163)
      exact by decide
                  ·
                    have : d = 657215 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657214 ≤ d
                  ·
                    have : d = 657214 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657213 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 657182 ≤ d
        ·
          by_cases h : 657198 ≤ d
          ·
            by_cases h : 657206 ≤ d
            ·
              by_cases h : 657210 ≤ d
              ·
                by_cases h : 657212 ≤ d
                ·
                  have : d = 657212 := by omega
                  subst d
      apply fullRecordGap_add_not_prime (q := 43)
      exact by decide
                ·
                  by_cases h : 657211 ≤ d
                  ·
                    have : d = 657211 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657210 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
              ·
                by_cases h : 657208 ≤ d
                ·
                  by_cases h : 657209 ≤ d
                  ·
                    have : d = 657209 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657208 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657207 ≤ d
                  ·
                    have : d = 657207 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657206 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29873)
      exact by decide
            ·
              by_cases h : 657202 ≤ d
              ·
                by_cases h : 657204 ≤ d
                ·
                  by_cases h : 657205 ≤ d
                  ·
                    have : d = 657205 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657204 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657203 ≤ d
                  ·
                    have : d = 657203 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657202 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657200 ≤ d
                ·
                  by_cases h : 657201 ≤ d
                  ·
                    have : d = 657201 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657200 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                ·
                  by_cases h : 657199 ≤ d
                  ·
                    have : d = 657199 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657198 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
          ·
            by_cases h : 657190 ≤ d
            ·
              by_cases h : 657194 ≤ d
              ·
                by_cases h : 657196 ≤ d
                ·
                  by_cases h : 657197 ≤ d
                  ·
                    have : d = 657197 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657196 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657195 ≤ d
                  ·
                    have : d = 657195 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657194 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657192 ≤ d
                ·
                  by_cases h : 657193 ≤ d
                  ·
                    have : d = 657193 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657192 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 139)
      exact by decide
                ·
                  by_cases h : 657191 ≤ d
                  ·
                    have : d = 657191 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657190 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 657186 ≤ d
              ·
                by_cases h : 657188 ≤ d
                ·
                  by_cases h : 657189 ≤ d
                  ·
                    have : d = 657189 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657188 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 479)
      exact by decide
                ·
                  by_cases h : 657187 ≤ d
                  ·
                    have : d = 657187 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657186 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
              ·
                by_cases h : 657184 ≤ d
                ·
                  by_cases h : 657185 ≤ d
                  ·
                    have : d = 657185 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657184 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657183 ≤ d
                  ·
                    have : d = 657183 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657182 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7669890421)
      right
      exact ⟨7669233239, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 657166 ≤ d
          ·
            by_cases h : 657174 ≤ d
            ·
              by_cases h : 657178 ≤ d
              ·
                by_cases h : 657180 ≤ d
                ·
                  by_cases h : 657181 ≤ d
                  ·
                    have : d = 657181 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657180 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657179 ≤ d
                  ·
                    have : d = 657179 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657178 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657176 ≤ d
                ·
                  by_cases h : 657177 ≤ d
                  ·
                    have : d = 657177 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657176 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                ·
                  by_cases h : 657175 ≤ d
                  ·
                    have : d = 657175 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657174 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 657170 ≤ d
              ·
                by_cases h : 657172 ≤ d
                ·
                  by_cases h : 657173 ≤ d
                  ·
                    have : d = 657173 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657172 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657171 ≤ d
                  ·
                    have : d = 657171 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657170 := by omega
                    subst d
      exact fullRecordGapTerm10914_not_prime
              ·
                by_cases h : 657168 ≤ d
                ·
                  by_cases h : 657169 ≤ d
                  ·
                    have : d = 657169 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657168 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13691)
      exact by decide
                ·
                  by_cases h : 657167 ≤ d
                  ·
                    have : d = 657167 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657166 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 657158 ≤ d
            ·
              by_cases h : 657162 ≤ d
              ·
                by_cases h : 657164 ≤ d
                ·
                  by_cases h : 657165 ≤ d
                  ·
                    have : d = 657165 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657164 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657163 ≤ d
                  ·
                    have : d = 657163 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657162 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3319)
      exact by decide
              ·
                by_cases h : 657160 ≤ d
                ·
                  by_cases h : 657161 ≤ d
                  ·
                    have : d = 657161 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657160 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657159 ≤ d
                  ·
                    have : d = 657159 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657158 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 657154 ≤ d
              ·
                by_cases h : 657156 ≤ d
                ·
                  by_cases h : 657157 ≤ d
                  ·
                    have : d = 657157 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657156 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                ·
                  by_cases h : 657155 ≤ d
                  ·
                    have : d = 657155 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657154 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657152 ≤ d
                ·
                  by_cases h : 657153 ≤ d
                  ·
                    have : d = 657153 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657152 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657151 ≤ d
                  ·
                    have : d = 657151 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657150 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
  ·
    by_cases h : 657024 ≤ d
    ·
      by_cases h : 657087 ≤ d
      ·
        by_cases h : 657119 ≤ d
        ·
          by_cases h : 657135 ≤ d
          ·
            by_cases h : 657143 ≤ d
            ·
              by_cases h : 657147 ≤ d
              ·
                by_cases h : 657149 ≤ d
                ·
                  have : d = 657149 := by omega
                  subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657148 ≤ d
                  ·
                    have : d = 657148 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657147 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657145 ≤ d
                ·
                  by_cases h : 657146 ≤ d
                  ·
                    have : d = 657146 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 73)
      exact by decide
                  ·
                    have : d = 657145 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657144 ≤ d
                  ·
                    have : d = 657144 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657143 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 657139 ≤ d
              ·
                by_cases h : 657141 ≤ d
                ·
                  by_cases h : 657142 ≤ d
                  ·
                    have : d = 657142 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657141 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657140 ≤ d
                  ·
                    have : d = 657140 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 657139 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657137 ≤ d
                ·
                  by_cases h : 657138 ≤ d
                  ·
                    have : d = 657138 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657137 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657136 ≤ d
                  ·
                    have : d = 657136 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657135 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 657127 ≤ d
            ·
              by_cases h : 657131 ≤ d
              ·
                by_cases h : 657133 ≤ d
                ·
                  by_cases h : 657134 ≤ d
                  ·
                    have : d = 657134 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657133 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657132 ≤ d
                  ·
                    have : d = 657132 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7823)
      exact by decide
                  ·
                    have : d = 657131 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657129 ≤ d
                ·
                  by_cases h : 657130 ≤ d
                  ·
                    have : d = 657130 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657129 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657128 ≤ d
                  ·
                    have : d = 657128 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 77621)
      right
      exact ⟨41461, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657127 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 657123 ≤ d
              ·
                by_cases h : 657125 ≤ d
                ·
                  by_cases h : 657126 ≤ d
                  ·
                    have : d = 657126 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 43)
      exact by decide
                  ·
                    have : d = 657125 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657124 ≤ d
                  ·
                    have : d = 657124 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657123 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657121 ≤ d
                ·
                  by_cases h : 657122 ≤ d
                  ·
                    have : d = 657122 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 79)
      exact by decide
                  ·
                    have : d = 657121 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657120 ≤ d
                  ·
                    have : d = 657120 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 657119 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 657103 ≤ d
          ·
            by_cases h : 657111 ≤ d
            ·
              by_cases h : 657115 ≤ d
              ·
                by_cases h : 657117 ≤ d
                ·
                  by_cases h : 657118 ≤ d
                  ·
                    have : d = 657118 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657117 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657116 ≤ d
                  ·
                    have : d = 657116 := by omega
                    subst d
      exact fullRecordGapTerm10913_not_prime
                  ·
                    have : d = 657115 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657113 ≤ d
                ·
                  by_cases h : 657114 ≤ d
                  ·
                    have : d = 657114 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657113 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657112 ≤ d
                  ·
                    have : d = 657112 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657111 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 657107 ≤ d
              ·
                by_cases h : 657109 ≤ d
                ·
                  by_cases h : 657110 ≤ d
                  ·
                    have : d = 657110 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657109 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657108 ≤ d
                  ·
                    have : d = 657108 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 18253)
      exact by decide
                  ·
                    have : d = 657107 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657105 ≤ d
                ·
                  by_cases h : 657106 ≤ d
                  ·
                    have : d = 657106 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657105 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657104 ≤ d
                  ·
                    have : d = 657104 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657103 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 657095 ≤ d
            ·
              by_cases h : 657099 ≤ d
              ·
                by_cases h : 657101 ≤ d
                ·
                  by_cases h : 657102 ≤ d
                  ·
                    have : d = 657102 := by omega
                    subst d
      exact fullRecordGapTerm10912_not_prime
                  ·
                    have : d = 657101 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657100 ≤ d
                  ·
                    have : d = 657100 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657099 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657097 ≤ d
                ·
                  by_cases h : 657098 ≤ d
                  ·
                    have : d = 657098 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 657097 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657096 ≤ d
                  ·
                    have : d = 657096 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657095 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 657091 ≤ d
              ·
                by_cases h : 657093 ≤ d
                ·
                  by_cases h : 657094 ≤ d
                  ·
                    have : d = 657094 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657093 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657092 ≤ d
                  ·
                    have : d = 657092 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657091 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657089 ≤ d
                ·
                  by_cases h : 657090 ≤ d
                  ·
                    have : d = 657090 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 149)
      exact by decide
                  ·
                    have : d = 657089 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657088 ≤ d
                  ·
                    have : d = 657088 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657087 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 657056 ≤ d
        ·
          by_cases h : 657072 ≤ d
          ·
            by_cases h : 657080 ≤ d
            ·
              by_cases h : 657084 ≤ d
              ·
                by_cases h : 657086 ≤ d
                ·
                  have : d = 657086 := by omega
                  subst d
      exact fullRecordGapTerm10911_not_prime
                ·
                  by_cases h : 657085 ≤ d
                  ·
                    have : d = 657085 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657084 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657082 ≤ d
                ·
                  by_cases h : 657083 ≤ d
                  ·
                    have : d = 657083 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657082 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657081 ≤ d
                  ·
                    have : d = 657081 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657080 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 16427)
      exact by decide
            ·
              by_cases h : 657076 ≤ d
              ·
                by_cases h : 657078 ≤ d
                ·
                  by_cases h : 657079 ≤ d
                  ·
                    have : d = 657079 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657078 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 97)
      exact by decide
                ·
                  by_cases h : 657077 ≤ d
                  ·
                    have : d = 657077 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657076 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657074 ≤ d
                ·
                  by_cases h : 657075 ≤ d
                  ·
                    have : d = 657075 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657074 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657073 ≤ d
                  ·
                    have : d = 657073 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657072 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
          ·
            by_cases h : 657064 ≤ d
            ·
              by_cases h : 657068 ≤ d
              ·
                by_cases h : 657070 ≤ d
                ·
                  by_cases h : 657071 ≤ d
                  ·
                    have : d = 657071 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657070 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657069 ≤ d
                  ·
                    have : d = 657069 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657068 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657066 ≤ d
                ·
                  by_cases h : 657067 ≤ d
                  ·
                    have : d = 657067 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657066 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 41)
      exact by decide
                ·
                  by_cases h : 657065 ≤ d
                  ·
                    have : d = 657065 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657064 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 657060 ≤ d
              ·
                by_cases h : 657062 ≤ d
                ·
                  by_cases h : 657063 ≤ d
                  ·
                    have : d = 657063 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657062 := by omega
                    subst d
      exact fullRecordGapTerm10910_not_prime
                ·
                  by_cases h : 657061 ≤ d
                  ·
                    have : d = 657061 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657060 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 47)
      exact by decide
              ·
                by_cases h : 657058 ≤ d
                ·
                  by_cases h : 657059 ≤ d
                  ·
                    have : d = 657059 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657058 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657057 ≤ d
                  ·
                    have : d = 657057 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657056 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 20533)
      exact by decide
        ·
          by_cases h : 657040 ≤ d
          ·
            by_cases h : 657048 ≤ d
            ·
              by_cases h : 657052 ≤ d
              ·
                by_cases h : 657054 ≤ d
                ·
                  by_cases h : 657055 ≤ d
                  ·
                    have : d = 657055 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657054 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657053 ≤ d
                  ·
                    have : d = 657053 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657052 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657050 ≤ d
                ·
                  by_cases h : 657051 ≤ d
                  ·
                    have : d = 657051 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657050 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                ·
                  by_cases h : 657049 ≤ d
                  ·
                    have : d = 657049 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657048 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 657044 ≤ d
              ·
                by_cases h : 657046 ≤ d
                ·
                  by_cases h : 657047 ≤ d
                  ·
                    have : d = 657047 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657046 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657045 ≤ d
                  ·
                    have : d = 657045 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657044 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657042 ≤ d
                ·
                  by_cases h : 657043 ≤ d
                  ·
                    have : d = 657043 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657042 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 66603479)
      right
      exact ⟨65946437, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657041 ≤ d
                  ·
                    have : d = 657041 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657040 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 657032 ≤ d
            ·
              by_cases h : 657036 ≤ d
              ·
                by_cases h : 657038 ≤ d
                ·
                  by_cases h : 657039 ≤ d
                  ·
                    have : d = 657039 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657038 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 8871882403)
      right
      exact ⟨8871225365, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657037 ≤ d
                  ·
                    have : d = 657037 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657036 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 18251)
      exact by decide
              ·
                by_cases h : 657034 ≤ d
                ·
                  by_cases h : 657035 ≤ d
                  ·
                    have : d = 657035 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657034 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657033 ≤ d
                  ·
                    have : d = 657033 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657032 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 85745368441)
      right
      exact ⟨85744711409, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 657028 ≤ d
              ·
                by_cases h : 657030 ≤ d
                ·
                  by_cases h : 657031 ≤ d
                  ·
                    have : d = 657031 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657030 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 181)
      exact by decide
                ·
                  by_cases h : 657029 ≤ d
                  ·
                    have : d = 657029 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657028 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657026 ≤ d
                ·
                  by_cases h : 657027 ≤ d
                  ·
                    have : d = 657027 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657026 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657025 ≤ d
                  ·
                    have : d = 657025 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657024 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 656961 ≤ d
      ·
        by_cases h : 656993 ≤ d
        ·
          by_cases h : 657009 ≤ d
          ·
            by_cases h : 657017 ≤ d
            ·
              by_cases h : 657021 ≤ d
              ·
                by_cases h : 657023 ≤ d
                ·
                  have : d = 657023 := by omega
                  subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657022 ≤ d
                  ·
                    have : d = 657022 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657021 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657019 ≤ d
                ·
                  by_cases h : 657020 ≤ d
                  ·
                    have : d = 657020 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 657019 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657018 ≤ d
                  ·
                    have : d = 657018 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 657017 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 657013 ≤ d
              ·
                by_cases h : 657015 ≤ d
                ·
                  by_cases h : 657016 ≤ d
                  ·
                    have : d = 657016 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657015 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657014 ≤ d
                  ·
                    have : d = 657014 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657013 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657011 ≤ d
                ·
                  by_cases h : 657012 ≤ d
                  ·
                    have : d = 657012 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657011 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657010 ≤ d
                  ·
                    have : d = 657010 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657009 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 657001 ≤ d
            ·
              by_cases h : 657005 ≤ d
              ·
                by_cases h : 657007 ≤ d
                ·
                  by_cases h : 657008 ≤ d
                  ·
                    have : d = 657008 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3733)
      exact by decide
                  ·
                    have : d = 657007 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657006 ≤ d
                  ·
                    have : d = 657006 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 15643)
      exact by decide
                  ·
                    have : d = 657005 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 657003 ≤ d
                ·
                  by_cases h : 657004 ≤ d
                  ·
                    have : d = 657004 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 657003 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 657002 ≤ d
                  ·
                    have : d = 657002 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 67)
      exact by decide
                  ·
                    have : d = 657001 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 656997 ≤ d
              ·
                by_cases h : 656999 ≤ d
                ·
                  by_cases h : 657000 ≤ d
                  ·
                    have : d = 657000 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 73)
      exact by decide
                  ·
                    have : d = 656999 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 656998 ≤ d
                  ·
                    have : d = 656998 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656997 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 656995 ≤ d
                ·
                  by_cases h : 656996 ≤ d
                  ·
                    have : d = 656996 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 86323)
      right
      exact ⟨33588, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656995 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 656994 ≤ d
                  ·
                    have : d = 656994 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656993 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 656977 ≤ d
          ·
            by_cases h : 656985 ≤ d
            ·
              by_cases h : 656989 ≤ d
              ·
                by_cases h : 656991 ≤ d
                ·
                  by_cases h : 656992 ≤ d
                  ·
                    have : d = 656992 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656991 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 656990 ≤ d
                  ·
                    have : d = 656990 := by omega
                    subst d
      exact fullRecordGapTerm10909_not_prime
                  ·
                    have : d = 656989 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 656987 ≤ d
                ·
                  by_cases h : 656988 ≤ d
                  ·
                    have : d = 656988 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 53)
      exact by decide
                  ·
                    have : d = 656987 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 656986 ≤ d
                  ·
                    have : d = 656986 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656985 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 656981 ≤ d
              ·
                by_cases h : 656983 ≤ d
                ·
                  by_cases h : 656984 ≤ d
                  ·
                    have : d = 656984 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656983 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 656982 ≤ d
                  ·
                    have : d = 656982 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656981 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 656979 ≤ d
                ·
                  by_cases h : 656980 ≤ d
                  ·
                    have : d = 656980 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656979 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 656978 ≤ d
                  ·
                    have : d = 656978 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 167)
      exact by decide
                  ·
                    have : d = 656977 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 656969 ≤ d
            ·
              by_cases h : 656973 ≤ d
              ·
                by_cases h : 656975 ≤ d
                ·
                  by_cases h : 656976 ≤ d
                  ·
                    have : d = 656976 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13687)
      exact by decide
                  ·
                    have : d = 656975 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 656974 ≤ d
                  ·
                    have : d = 656974 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656973 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 656971 ≤ d
                ·
                  by_cases h : 656972 ≤ d
                  ·
                    have : d = 656972 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 656971 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 656970 ≤ d
                  ·
                    have : d = 656970 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656969 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 656965 ≤ d
              ·
                by_cases h : 656967 ≤ d
                ·
                  by_cases h : 656968 ≤ d
                  ·
                    have : d = 656968 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656967 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 656966 ≤ d
                  ·
                    have : d = 656966 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 656965 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 656963 ≤ d
                ·
                  by_cases h : 656964 ≤ d
                  ·
                    have : d = 656964 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656963 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 656962 ≤ d
                  ·
                    have : d = 656962 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656961 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 656929 ≤ d
        ·
          by_cases h : 656945 ≤ d
          ·
            by_cases h : 656953 ≤ d
            ·
              by_cases h : 656957 ≤ d
              ·
                by_cases h : 656959 ≤ d
                ·
                  by_cases h : 656960 ≤ d
                  ·
                    have : d = 656960 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656959 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 656958 ≤ d
                  ·
                    have : d = 656958 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 223)
      exact by decide
                  ·
                    have : d = 656957 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 656955 ≤ d
                ·
                  by_cases h : 656956 ≤ d
                  ·
                    have : d = 656956 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656955 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 656954 ≤ d
                  ·
                    have : d = 656954 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656953 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 656949 ≤ d
              ·
                by_cases h : 656951 ≤ d
                ·
                  by_cases h : 656952 ≤ d
                  ·
                    have : d = 656952 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 656951 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 656950 ≤ d
                  ·
                    have : d = 656950 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656949 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 656947 ≤ d
                ·
                  by_cases h : 656948 ≤ d
                  ·
                    have : d = 656948 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 656947 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 656946 ≤ d
                  ·
                    have : d = 656946 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 36497)
      exact by decide
                  ·
                    have : d = 656945 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 656937 ≤ d
            ·
              by_cases h : 656941 ≤ d
              ·
                by_cases h : 656943 ≤ d
                ·
                  by_cases h : 656944 ≤ d
                  ·
                    have : d = 656944 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656943 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 656942 ≤ d
                  ·
                    have : d = 656942 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656941 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 656939 ≤ d
                ·
                  by_cases h : 656940 ≤ d
                  ·
                    have : d = 656940 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 10949)
      exact by decide
                  ·
                    have : d = 656939 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 656938 ≤ d
                  ·
                    have : d = 656938 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656937 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 656933 ≤ d
              ·
                by_cases h : 656935 ≤ d
                ·
                  by_cases h : 656936 ≤ d
                  ·
                    have : d = 656936 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11731)
      exact by decide
                  ·
                    have : d = 656935 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 656934 ≤ d
                  ·
                    have : d = 656934 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656933 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 656931 ≤ d
                ·
                  by_cases h : 656932 ≤ d
                  ·
                    have : d = 656932 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656931 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 656930 ≤ d
                  ·
                    have : d = 656930 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 179)
      exact by decide
                  ·
                    have : d = 656929 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 656913 ≤ d
          ·
            by_cases h : 656921 ≤ d
            ·
              by_cases h : 656925 ≤ d
              ·
                by_cases h : 656927 ≤ d
                ·
                  by_cases h : 656928 ≤ d
                  ·
                    have : d = 656928 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656927 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 656926 ≤ d
                  ·
                    have : d = 656926 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656925 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 656923 ≤ d
                ·
                  by_cases h : 656924 ≤ d
                  ·
                    have : d = 656924 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656923 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 656922 ≤ d
                  ·
                    have : d = 656922 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 15641)
      exact by decide
                  ·
                    have : d = 656921 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 656917 ≤ d
              ·
                by_cases h : 656919 ≤ d
                ·
                  by_cases h : 656920 ≤ d
                  ·
                    have : d = 656920 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656919 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 656918 ≤ d
                  ·
                    have : d = 656918 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 503)
      exact by decide
                  ·
                    have : d = 656917 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 656915 ≤ d
                ·
                  by_cases h : 656916 ≤ d
                  ·
                    have : d = 656916 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656915 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 656914 ≤ d
                  ·
                    have : d = 656914 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656913 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 656905 ≤ d
            ·
              by_cases h : 656909 ≤ d
              ·
                by_cases h : 656911 ≤ d
                ·
                  by_cases h : 656912 ≤ d
                  ·
                    have : d = 656912 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 41057)
      exact by decide
                  ·
                    have : d = 656911 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 656910 ≤ d
                  ·
                    have : d = 656910 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 811)
      exact by decide
                  ·
                    have : d = 656909 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 656907 ≤ d
                ·
                  by_cases h : 656908 ≤ d
                  ·
                    have : d = 656908 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656907 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 656906 ≤ d
                  ·
                    have : d = 656906 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 656905 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 656901 ≤ d
              ·
                by_cases h : 656903 ≤ d
                ·
                  by_cases h : 656904 ≤ d
                  ·
                    have : d = 656904 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656903 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 656902 ≤ d
                  ·
                    have : d = 656902 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656901 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 656899 ≤ d
                ·
                  by_cases h : 656900 ≤ d
                  ·
                    have : d = 656900 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 656899 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 656898 ≤ d
                  ·
                    have : d = 656898 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 656897 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩

end PrimeFactorUnimodality
