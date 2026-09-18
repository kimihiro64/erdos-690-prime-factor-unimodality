import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapFermat

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

theorem fullRecordGapSubBlock_part0579 (d : Nat) (295937 ≤ d) (d ≤ 296448) : ¬(recordGapCenter - d).Prime := by
  by_cases h : 296193 ≤ d
  ·
    by_cases h : 296321 ≤ d
    ·
      by_cases h : 296385 ≤ d
      ·
        by_cases h : 296417 ≤ d
        ·
          by_cases h : 296433 ≤ d
          ·
            by_cases h : 296441 ≤ d
            ·
              by_cases h : 296445 ≤ d
              ·
                by_cases h : 296447 ≤ d
                ·
                  by_cases h : 296448 ≤ d
                  ·
                    have : d = 296448 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 193) (by norm_num)
      exact by decide
                  ·
                    have : d = 296447 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296446 ≤ d
                  ·
                    have : d = 296446 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296445 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296443 ≤ d
                ·
                  by_cases h : 296444 ≤ d
                  ·
                    have : d = 296444 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296443 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296442 ≤ d
                  ·
                    have : d = 296442 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 43) (by norm_num)
      exact by decide
                  ·
                    have : d = 296441 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 296437 ≤ d
              ·
                by_cases h : 296439 ≤ d
                ·
                  by_cases h : 296440 ≤ d
                  ·
                    have : d = 296440 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7411) (by norm_num)
      exact by decide
                  ·
                    have : d = 296439 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296438 ≤ d
                  ·
                    have : d = 296438 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296437 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296435 ≤ d
                ·
                  by_cases h : 296436 ≤ d
                  ·
                    have : d = 296436 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296435 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296434 ≤ d
                  ·
                    have : d = 296434 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 103) (by norm_num)
      exact by decide
                  ·
                    have : d = 296433 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 296425 ≤ d
            ·
              by_cases h : 296429 ≤ d
              ·
                by_cases h : 296431 ≤ d
                ·
                  by_cases h : 296432 ≤ d
                  ·
                    have : d = 296432 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296431 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296430 ≤ d
                  ·
                    have : d = 296430 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296429 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296427 ≤ d
                ·
                  by_cases h : 296428 ≤ d
                  ·
                    have : d = 296428 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 6737) (by norm_num)
      exact by decide
                  ·
                    have : d = 296427 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296426 ≤ d
                  ·
                    have : d = 296426 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296425 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 296421 ≤ d
              ·
                by_cases h : 296423 ≤ d
                ·
                  by_cases h : 296424 ≤ d
                  ·
                    have : d = 296424 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23) (by norm_num)
      exact by decide
                  ·
                    have : d = 296423 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296422 ≤ d
                  ·
                    have : d = 296422 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 31) (by norm_num)
      exact by decide
                  ·
                    have : d = 296421 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296419 ≤ d
                ·
                  by_cases h : 296420 ≤ d
                  ·
                    have : d = 296420 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296419 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296418 ≤ d
                  ·
                    have : d = 296418 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 127) (by norm_num)
      exact by decide
                  ·
                    have : d = 296417 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 296401 ≤ d
          ·
            by_cases h : 296409 ≤ d
            ·
              by_cases h : 296413 ≤ d
              ·
                by_cases h : 296415 ≤ d
                ·
                  by_cases h : 296416 ≤ d
                  ·
                    have : d = 296416 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296415 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296414 ≤ d
                  ·
                    have : d = 296414 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296413 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296411 ≤ d
                ·
                  by_cases h : 296412 ≤ d
                  ·
                    have : d = 296412 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 296411 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296410 ≤ d
                  ·
                    have : d = 296410 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296409 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 296405 ≤ d
              ·
                by_cases h : 296407 ≤ d
                ·
                  by_cases h : 296408 ≤ d
                  ·
                    have : d = 296408 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296407 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296406 ≤ d
                  ·
                    have : d = 296406 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296405 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296403 ≤ d
                ·
                  by_cases h : 296404 ≤ d
                  ·
                    have : d = 296404 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13578343) (by norm_num)
      right
      exact ⟨296404, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296403 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296402 ≤ d
                  ·
                    have : d = 296402 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296401 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 296393 ≤ d
            ·
              by_cases h : 296397 ≤ d
              ·
                by_cases h : 296399 ≤ d
                ·
                  by_cases h : 296400 ≤ d
                  ·
                    have : d = 296400 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 296399 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296398 ≤ d
                  ·
                    have : d = 296398 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 25923311) (by norm_num)
      right
      exact ⟨296398, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296397 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296395 ≤ d
                ·
                  by_cases h : 296396 ≤ d
                  ·
                    have : d = 296396 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296395 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296394 ≤ d
                  ·
                    have : d = 296394 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7057) (by norm_num)
      exact by decide
                  ·
                    have : d = 296393 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 296389 ≤ d
              ·
                by_cases h : 296391 ≤ d
                ·
                  by_cases h : 296392 ≤ d
                  ·
                    have : d = 296392 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 37049) (by norm_num)
      exact by decide
                  ·
                    have : d = 296391 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296390 ≤ d
                  ·
                    have : d = 296390 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296389 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296387 ≤ d
                ·
                  by_cases h : 296388 ≤ d
                  ·
                    have : d = 296388 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296387 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296386 ≤ d
                  ·
                    have : d = 296386 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296385 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 296353 ≤ d
        ·
          by_cases h : 296369 ≤ d
          ·
            by_cases h : 296377 ≤ d
            ·
              by_cases h : 296381 ≤ d
              ·
                by_cases h : 296383 ≤ d
                ·
                  by_cases h : 296384 ≤ d
                  ·
                    have : d = 296384 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296383 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296382 ≤ d
                  ·
                    have : d = 296382 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 47) (by norm_num)
      exact by decide
                  ·
                    have : d = 296381 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296379 ≤ d
                ·
                  by_cases h : 296380 ≤ d
                  ·
                    have : d = 296380 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 29) (by norm_num)
      exact by decide
                  ·
                    have : d = 296379 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296378 ≤ d
                  ·
                    have : d = 296378 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296377 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 296373 ≤ d
              ·
                by_cases h : 296375 ≤ d
                ·
                  by_cases h : 296376 ≤ d
                  ·
                    have : d = 296376 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296375 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296374 ≤ d
                  ·
                    have : d = 296374 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296373 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296371 ≤ d
                ·
                  by_cases h : 296372 ≤ d
                  ·
                    have : d = 296372 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296371 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296370 ≤ d
                  ·
                    have : d = 296370 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 37) (by norm_num)
      exact by decide
                  ·
                    have : d = 296369 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 296361 ≤ d
            ·
              by_cases h : 296365 ≤ d
              ·
                by_cases h : 296367 ≤ d
                ·
                  by_cases h : 296368 ≤ d
                  ·
                    have : d = 296368 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 18523) (by norm_num)
      exact by decide
                  ·
                    have : d = 296367 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296366 ≤ d
                  ·
                    have : d = 296366 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296365 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296363 ≤ d
                ·
                  by_cases h : 296364 ≤ d
                  ·
                    have : d = 296364 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 24697) (by norm_num)
      exact by decide
                  ·
                    have : d = 296363 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296362 ≤ d
                  ·
                    have : d = 296362 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 296361 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 296357 ≤ d
              ·
                by_cases h : 296359 ≤ d
                ·
                  by_cases h : 296360 ≤ d
                  ·
                    have : d = 296360 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296359 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296358 ≤ d
                  ·
                    have : d = 296358 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 33176041) (by norm_num)
      right
      exact ⟨296358, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296357 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296355 ≤ d
                ·
                  by_cases h : 296356 ≤ d
                  ·
                    have : d = 296356 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296355 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296354 ≤ d
                  ·
                    have : d = 296354 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296353 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 296337 ≤ d
          ·
            by_cases h : 296345 ≤ d
            ·
              by_cases h : 296349 ≤ d
              ·
                by_cases h : 296351 ≤ d
                ·
                  by_cases h : 296352 ≤ d
                  ·
                    have : d = 296352 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 241117) (by norm_num)
      right
      exact ⟨55235, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296351 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296350 ≤ d
                  ·
                    have : d = 296350 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5927) (by norm_num)
      exact by decide
                  ·
                    have : d = 296349 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296347 ≤ d
                ·
                  by_cases h : 296348 ≤ d
                  ·
                    have : d = 296348 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296347 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296346 ≤ d
                  ·
                    have : d = 296346 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296345 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 296341 ≤ d
              ·
                by_cases h : 296343 ≤ d
                ·
                  by_cases h : 296344 ≤ d
                  ·
                    have : d = 296344 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296343 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296342 ≤ d
                  ·
                    have : d = 296342 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296341 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296339 ≤ d
                ·
                  by_cases h : 296340 ≤ d
                  ·
                    have : d = 296340 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 449) (by norm_num)
      exact by decide
                  ·
                    have : d = 296339 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296338 ≤ d
                  ·
                    have : d = 296338 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 61) (by norm_num)
      exact by decide
                  ·
                    have : d = 296337 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 296329 ≤ d
            ·
              by_cases h : 296333 ≤ d
              ·
                by_cases h : 296335 ≤ d
                ·
                  by_cases h : 296336 ≤ d
                  ·
                    have : d = 296336 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296335 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296334 ≤ d
                  ·
                    have : d = 296334 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 101) (by norm_num)
      exact by decide
                  ·
                    have : d = 296333 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296331 ≤ d
                ·
                  by_cases h : 296332 ≤ d
                  ·
                    have : d = 296332 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296331 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296330 ≤ d
                  ·
                    have : d = 296330 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296329 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 296325 ≤ d
              ·
                by_cases h : 296327 ≤ d
                ·
                  by_cases h : 296328 ≤ d
                  ·
                    have : d = 296328 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 12347) (by norm_num)
      exact by decide
                  ·
                    have : d = 296327 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296326 ≤ d
                  ·
                    have : d = 296326 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296325 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296323 ≤ d
                ·
                  by_cases h : 296324 ≤ d
                  ·
                    have : d = 296324 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296323 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296322 ≤ d
                  ·
                    have : d = 296322 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296321 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 296257 ≤ d
      ·
        by_cases h : 296289 ≤ d
        ·
          by_cases h : 296305 ≤ d
          ·
            by_cases h : 296313 ≤ d
            ·
              by_cases h : 296317 ≤ d
              ·
                by_cases h : 296319 ≤ d
                ·
                  by_cases h : 296320 ≤ d
                  ·
                    have : d = 296320 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 463) (by norm_num)
      exact by decide
                  ·
                    have : d = 296319 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296318 ≤ d
                  ·
                    have : d = 296318 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296317 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296315 ≤ d
                ·
                  by_cases h : 296316 ≤ d
                  ·
                    have : d = 296316 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296315 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296314 ≤ d
                  ·
                    have : d = 296314 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 271097) (by norm_num)
      right
      exact ⟨25217, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296313 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 296309 ≤ d
              ·
                by_cases h : 296311 ≤ d
                ·
                  by_cases h : 296312 ≤ d
                  ·
                    have : d = 296312 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296311 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296310 ≤ d
                  ·
                    have : d = 296310 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 296309 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296307 ≤ d
                ·
                  by_cases h : 296308 ≤ d
                  ·
                    have : d = 296308 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 60611) (by norm_num)
      right
      exact ⟨53864, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296307 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296306 ≤ d
                  ·
                    have : d = 296306 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296305 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 296297 ≤ d
            ·
              by_cases h : 296301 ≤ d
              ·
                by_cases h : 296303 ≤ d
                ·
                  by_cases h : 296304 ≤ d
                  ·
                    have : d = 296304 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296303 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296302 ≤ d
                  ·
                    have : d = 296302 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 204553529) (by norm_num)
      right
      exact ⟨296302, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296301 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296299 ≤ d
                ·
                  by_cases h : 296300 ≤ d
                  ·
                    have : d = 296300 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296299 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296298 ≤ d
                  ·
                    have : d = 296298 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 31) (by norm_num)
      exact by decide
                  ·
                    have : d = 296297 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 296293 ≤ d
              ·
                by_cases h : 296295 ≤ d
                ·
                  by_cases h : 296296 ≤ d
                  ·
                    have : d = 296296 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296295 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296294 ≤ d
                  ·
                    have : d = 296294 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296293 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296291 ≤ d
                ·
                  by_cases h : 296292 ≤ d
                  ·
                    have : d = 296292 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 24691) (by norm_num)
      exact by decide
                  ·
                    have : d = 296291 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296290 ≤ d
                  ·
                    have : d = 296290 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296289 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 296273 ≤ d
          ·
            by_cases h : 296281 ≤ d
            ·
              by_cases h : 296285 ≤ d
              ·
                by_cases h : 296287 ≤ d
                ·
                  by_cases h : 296288 ≤ d
                  ·
                    have : d = 296288 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296287 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296286 ≤ d
                  ·
                    have : d = 296286 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296285 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296283 ≤ d
                ·
                  by_cases h : 296284 ≤ d
                  ·
                    have : d = 296284 := by omega
                    subst d
      exact fullRecordGapTerm01955_not_prime
                  ·
                    have : d = 296283 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296282 ≤ d
                  ·
                    have : d = 296282 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296281 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 296277 ≤ d
              ·
                by_cases h : 296279 ≤ d
                ·
                  by_cases h : 296280 ≤ d
                  ·
                    have : d = 296280 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 823) (by norm_num)
      exact by decide
                  ·
                    have : d = 296279 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296278 ≤ d
                  ·
                    have : d = 296278 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296277 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296275 ≤ d
                ·
                  by_cases h : 296276 ≤ d
                  ·
                    have : d = 296276 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296275 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296274 ≤ d
                  ·
                    have : d = 296274 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 67) (by norm_num)
      exact by decide
                  ·
                    have : d = 296273 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 296265 ≤ d
            ·
              by_cases h : 296269 ≤ d
              ·
                by_cases h : 296271 ≤ d
                ·
                  by_cases h : 296272 ≤ d
                  ·
                    have : d = 296272 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 18517) (by norm_num)
      exact by decide
                  ·
                    have : d = 296271 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296270 ≤ d
                  ·
                    have : d = 296270 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296269 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296267 ≤ d
                ·
                  by_cases h : 296268 ≤ d
                  ·
                    have : d = 296268 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3527) (by norm_num)
      exact by decide
                  ·
                    have : d = 296267 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296266 ≤ d
                  ·
                    have : d = 296266 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296265 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 296261 ≤ d
              ·
                by_cases h : 296263 ≤ d
                ·
                  by_cases h : 296264 ≤ d
                  ·
                    have : d = 296264 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296263 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296262 ≤ d
                  ·
                    have : d = 296262 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296261 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296259 ≤ d
                ·
                  by_cases h : 296260 ≤ d
                  ·
                    have : d = 296260 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 14813) (by norm_num)
      exact by decide
                  ·
                    have : d = 296259 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296258 ≤ d
                  ·
                    have : d = 296258 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296257 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 296225 ≤ d
        ·
          by_cases h : 296241 ≤ d
          ·
            by_cases h : 296249 ≤ d
            ·
              by_cases h : 296253 ≤ d
              ·
                by_cases h : 296255 ≤ d
                ·
                  by_cases h : 296256 ≤ d
                  ·
                    have : d = 296256 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296255 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296254 ≤ d
                  ·
                    have : d = 296254 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3023) (by norm_num)
      exact by decide
                  ·
                    have : d = 296253 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296251 ≤ d
                ·
                  by_cases h : 296252 ≤ d
                  ·
                    have : d = 296252 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296251 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296250 ≤ d
                  ·
                    have : d = 296250 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 79) (by norm_num)
      exact by decide
                  ·
                    have : d = 296249 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 296245 ≤ d
              ·
                by_cases h : 296247 ≤ d
                ·
                  by_cases h : 296248 ≤ d
                  ·
                    have : d = 296248 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296247 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296246 ≤ d
                  ·
                    have : d = 296246 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296245 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296243 ≤ d
                ·
                  by_cases h : 296244 ≤ d
                  ·
                    have : d = 296244 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 296243 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296242 ≤ d
                  ·
                    have : d = 296242 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 296241 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 296233 ≤ d
            ·
              by_cases h : 296237 ≤ d
              ·
                by_cases h : 296239 ≤ d
                ·
                  by_cases h : 296240 ≤ d
                  ·
                    have : d = 296240 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296239 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296238 ≤ d
                  ·
                    have : d = 296238 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 97) (by norm_num)
      exact by decide
                  ·
                    have : d = 296237 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296235 ≤ d
                ·
                  by_cases h : 296236 ≤ d
                  ·
                    have : d = 296236 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296235 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296234 ≤ d
                  ·
                    have : d = 296234 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296233 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 296229 ≤ d
              ·
                by_cases h : 296231 ≤ d
                ·
                  by_cases h : 296232 ≤ d
                  ·
                    have : d = 296232 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 12343) (by norm_num)
      exact by decide
                  ·
                    have : d = 296231 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296230 ≤ d
                  ·
                    have : d = 296230 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2693) (by norm_num)
      exact by decide
                  ·
                    have : d = 296229 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296227 ≤ d
                ·
                  by_cases h : 296228 ≤ d
                  ·
                    have : d = 296228 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296227 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296226 ≤ d
                  ·
                    have : d = 296226 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296225 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 296209 ≤ d
          ·
            by_cases h : 296217 ≤ d
            ·
              by_cases h : 296221 ≤ d
              ·
                by_cases h : 296223 ≤ d
                ·
                  by_cases h : 296224 ≤ d
                  ·
                    have : d = 296224 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 9257) (by norm_num)
      exact by decide
                  ·
                    have : d = 296223 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296222 ≤ d
                  ·
                    have : d = 296222 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296221 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296219 ≤ d
                ·
                  by_cases h : 296220 ≤ d
                  ·
                    have : d = 296220 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296219 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296218 ≤ d
                  ·
                    have : d = 296218 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 296217 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 296213 ≤ d
              ·
                by_cases h : 296215 ≤ d
                ·
                  by_cases h : 296216 ≤ d
                  ·
                    have : d = 296216 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296215 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296214 ≤ d
                  ·
                    have : d = 296214 := by omega
                    subst d
      exact fullRecordGapTerm01956_not_prime
                  ·
                    have : d = 296213 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296211 ≤ d
                ·
                  by_cases h : 296212 ≤ d
                  ·
                    have : d = 296212 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296211 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296210 ≤ d
                  ·
                    have : d = 296210 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296209 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 296201 ≤ d
            ·
              by_cases h : 296205 ≤ d
              ·
                by_cases h : 296207 ≤ d
                ·
                  by_cases h : 296208 ≤ d
                  ·
                    have : d = 296208 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 296207 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296206 ≤ d
                  ·
                    have : d = 296206 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296205 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296203 ≤ d
                ·
                  by_cases h : 296204 ≤ d
                  ·
                    have : d = 296204 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296203 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296202 ≤ d
                  ·
                    have : d = 296202 := by omega
                    subst d
      exact fullRecordGapTerm01957_not_prime
                  ·
                    have : d = 296201 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 296197 ≤ d
              ·
                by_cases h : 296199 ≤ d
                ·
                  by_cases h : 296200 ≤ d
                  ·
                    have : d = 296200 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1481) (by norm_num)
      exact by decide
                  ·
                    have : d = 296199 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296198 ≤ d
                  ·
                    have : d = 296198 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296197 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296195 ≤ d
                ·
                  by_cases h : 296196 ≤ d
                  ·
                    have : d = 296196 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296195 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296194 ≤ d
                  ·
                    have : d = 296194 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23) (by norm_num)
      exact by decide
                  ·
                    have : d = 296193 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
  ·
    by_cases h : 296065 ≤ d
    ·
      by_cases h : 296129 ≤ d
      ·
        by_cases h : 296161 ≤ d
        ·
          by_cases h : 296177 ≤ d
          ·
            by_cases h : 296185 ≤ d
            ·
              by_cases h : 296189 ≤ d
              ·
                by_cases h : 296191 ≤ d
                ·
                  by_cases h : 296192 ≤ d
                  ·
                    have : d = 296192 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296191 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296190 ≤ d
                  ·
                    have : d = 296190 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296189 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296187 ≤ d
                ·
                  by_cases h : 296188 ≤ d
                  ·
                    have : d = 296188 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2519899) (by norm_num)
      right
      exact ⟨296188, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296187 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296186 ≤ d
                  ·
                    have : d = 296186 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296185 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 296181 ≤ d
              ·
                by_cases h : 296183 ≤ d
                ·
                  by_cases h : 296184 ≤ d
                  ·
                    have : d = 296184 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 41) (by norm_num)
      exact by decide
                  ·
                    have : d = 296183 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296182 ≤ d
                  ·
                    have : d = 296182 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 27104039) (by norm_num)
      right
      exact ⟨296182, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296181 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296179 ≤ d
                ·
                  by_cases h : 296180 ≤ d
                  ·
                    have : d = 296180 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296179 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296178 ≤ d
                  ·
                    have : d = 296178 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296177 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 296169 ≤ d
            ·
              by_cases h : 296173 ≤ d
              ·
                by_cases h : 296175 ≤ d
                ·
                  by_cases h : 296176 ≤ d
                  ·
                    have : d = 296176 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296175 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296174 ≤ d
                  ·
                    have : d = 296174 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296173 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296171 ≤ d
                ·
                  by_cases h : 296172 ≤ d
                  ·
                    have : d = 296172 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 296171 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296170 ≤ d
                  ·
                    have : d = 296170 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 4231) (by norm_num)
      exact by decide
                  ·
                    have : d = 296169 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 296165 ≤ d
              ·
                by_cases h : 296167 ≤ d
                ·
                  by_cases h : 296168 ≤ d
                  ·
                    have : d = 296168 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296167 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296166 ≤ d
                  ·
                    have : d = 296166 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296165 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296163 ≤ d
                ·
                  by_cases h : 296164 ≤ d
                  ·
                    have : d = 296164 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296163 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296162 ≤ d
                  ·
                    have : d = 296162 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296161 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 296145 ≤ d
          ·
            by_cases h : 296153 ≤ d
            ·
              by_cases h : 296157 ≤ d
              ·
                by_cases h : 296159 ≤ d
                ·
                  by_cases h : 296160 ≤ d
                  ·
                    have : d = 296160 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 617) (by norm_num)
      exact by decide
                  ·
                    have : d = 296159 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296158 ≤ d
                  ·
                    have : d = 296158 := by omega
                    subst d
      exact fullRecordGapTerm01958_not_prime
                  ·
                    have : d = 296157 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296155 ≤ d
                ·
                  by_cases h : 296156 ≤ d
                  ·
                    have : d = 296156 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296155 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296154 ≤ d
                  ·
                    have : d = 296154 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 16453) (by norm_num)
      exact by decide
                  ·
                    have : d = 296153 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 296149 ≤ d
              ·
                by_cases h : 296151 ≤ d
                ·
                  by_cases h : 296152 ≤ d
                  ·
                    have : d = 296152 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 37019) (by norm_num)
      exact by decide
                  ·
                    have : d = 296151 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296150 ≤ d
                  ·
                    have : d = 296150 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296149 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296147 ≤ d
                ·
                  by_cases h : 296148 ≤ d
                  ·
                    have : d = 296148 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23) (by norm_num)
      exact by decide
                  ·
                    have : d = 296147 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296146 ≤ d
                  ·
                    have : d = 296146 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296145 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 296137 ≤ d
            ·
              by_cases h : 296141 ≤ d
              ·
                by_cases h : 296143 ≤ d
                ·
                  by_cases h : 296144 ≤ d
                  ·
                    have : d = 296144 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296143 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296142 ≤ d
                  ·
                    have : d = 296142 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 641) (by norm_num)
      exact by decide
                  ·
                    have : d = 296141 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296139 ≤ d
                ·
                  by_cases h : 296140 ≤ d
                  ·
                    have : d = 296140 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 296139 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296138 ≤ d
                  ·
                    have : d = 296138 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296137 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 296133 ≤ d
              ·
                by_cases h : 296135 ≤ d
                ·
                  by_cases h : 296136 ≤ d
                  ·
                    have : d = 296136 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296135 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296134 ≤ d
                  ·
                    have : d = 296134 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 296133 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296131 ≤ d
                ·
                  by_cases h : 296132 ≤ d
                  ·
                    have : d = 296132 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296131 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296130 ≤ d
                  ·
                    have : d = 296130 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 9871) (by norm_num)
      exact by decide
                  ·
                    have : d = 296129 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 296097 ≤ d
        ·
          by_cases h : 296113 ≤ d
          ·
            by_cases h : 296121 ≤ d
            ·
              by_cases h : 296125 ≤ d
              ·
                by_cases h : 296127 ≤ d
                ·
                  by_cases h : 296128 ≤ d
                  ·
                    have : d = 296128 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 661) (by norm_num)
      exact by decide
                  ·
                    have : d = 296127 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296126 ≤ d
                  ·
                    have : d = 296126 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296125 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296123 ≤ d
                ·
                  by_cases h : 296124 ≤ d
                  ·
                    have : d = 296124 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296123 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296122 ≤ d
                  ·
                    have : d = 296122 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296121 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 296117 ≤ d
              ·
                by_cases h : 296119 ≤ d
                ·
                  by_cases h : 296120 ≤ d
                  ·
                    have : d = 296120 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296119 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296118 ≤ d
                  ·
                    have : d = 296118 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 16451) (by norm_num)
      exact by decide
                  ·
                    have : d = 296117 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296115 ≤ d
                ·
                  by_cases h : 296116 ≤ d
                  ·
                    have : d = 296116 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296115 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296114 ≤ d
                  ·
                    have : d = 296114 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296113 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 296105 ≤ d
            ·
              by_cases h : 296109 ≤ d
              ·
                by_cases h : 296111 ≤ d
                ·
                  by_cases h : 296112 ≤ d
                  ·
                    have : d = 296112 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 31) (by norm_num)
      exact by decide
                  ·
                    have : d = 296111 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296110 ≤ d
                  ·
                    have : d = 296110 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 29611) (by norm_num)
      exact by decide
                  ·
                    have : d = 296109 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296107 ≤ d
                ·
                  by_cases h : 296108 ≤ d
                  ·
                    have : d = 296108 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296107 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296106 ≤ d
                  ·
                    have : d = 296106 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296105 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 296101 ≤ d
              ·
                by_cases h : 296103 ≤ d
                ·
                  by_cases h : 296104 ≤ d
                  ·
                    have : d = 296104 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 37013) (by norm_num)
      exact by decide
                  ·
                    have : d = 296103 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296102 ≤ d
                  ·
                    have : d = 296102 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296101 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296099 ≤ d
                ·
                  by_cases h : 296100 ≤ d
                  ·
                    have : d = 296100 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 47) (by norm_num)
      exact by decide
                  ·
                    have : d = 296099 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296098 ≤ d
                  ·
                    have : d = 296098 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 43) (by norm_num)
      exact by decide
                  ·
                    have : d = 296097 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 296081 ≤ d
          ·
            by_cases h : 296089 ≤ d
            ·
              by_cases h : 296093 ≤ d
              ·
                by_cases h : 296095 ≤ d
                ·
                  by_cases h : 296096 ≤ d
                  ·
                    have : d = 296096 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296095 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296094 ≤ d
                  ·
                    have : d = 296094 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296093 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296091 ≤ d
                ·
                  by_cases h : 296092 ≤ d
                  ·
                    have : d = 296092 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 79) (by norm_num)
      exact by decide
                  ·
                    have : d = 296091 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296090 ≤ d
                  ·
                    have : d = 296090 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296089 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 296085 ≤ d
              ·
                by_cases h : 296087 ≤ d
                ·
                  by_cases h : 296088 ≤ d
                  ·
                    have : d = 296088 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 296087 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296086 ≤ d
                  ·
                    have : d = 296086 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296085 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296083 ≤ d
                ·
                  by_cases h : 296084 ≤ d
                  ·
                    have : d = 296084 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296083 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296082 ≤ d
                  ·
                    have : d = 296082 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5483) (by norm_num)
      exact by decide
                  ·
                    have : d = 296081 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 296073 ≤ d
            ·
              by_cases h : 296077 ≤ d
              ·
                by_cases h : 296079 ≤ d
                ·
                  by_cases h : 296080 ≤ d
                  ·
                    have : d = 296080 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296079 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296078 ≤ d
                  ·
                    have : d = 296078 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296077 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296075 ≤ d
                ·
                  by_cases h : 296076 ≤ d
                  ·
                    have : d = 296076 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296075 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296074 ≤ d
                  ·
                    have : d = 296074 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 37) (by norm_num)
      exact by decide
                  ·
                    have : d = 296073 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 296069 ≤ d
              ·
                by_cases h : 296071 ≤ d
                ·
                  by_cases h : 296072 ≤ d
                  ·
                    have : d = 296072 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296071 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296070 ≤ d
                  ·
                    have : d = 296070 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 71) (by norm_num)
      exact by decide
                  ·
                    have : d = 296069 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296067 ≤ d
                ·
                  by_cases h : 296068 ≤ d
                  ·
                    have : d = 296068 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1098787) (by norm_num)
      right
      exact ⟨296068, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296067 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296066 ≤ d
                  ·
                    have : d = 296066 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296065 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 296001 ≤ d
      ·
        by_cases h : 296033 ≤ d
        ·
          by_cases h : 296049 ≤ d
          ·
            by_cases h : 296057 ≤ d
            ·
              by_cases h : 296061 ≤ d
              ·
                by_cases h : 296063 ≤ d
                ·
                  by_cases h : 296064 ≤ d
                  ·
                    have : d = 296064 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 257) (by norm_num)
      exact by decide
                  ·
                    have : d = 296063 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296062 ≤ d
                  ·
                    have : d = 296062 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 296061 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296059 ≤ d
                ·
                  by_cases h : 296060 ≤ d
                  ·
                    have : d = 296060 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296059 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296058 ≤ d
                  ·
                    have : d = 296058 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296057 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 296053 ≤ d
              ·
                by_cases h : 296055 ≤ d
                ·
                  by_cases h : 296056 ≤ d
                  ·
                    have : d = 296056 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296055 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296054 ≤ d
                  ·
                    have : d = 296054 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296053 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296051 ≤ d
                ·
                  by_cases h : 296052 ≤ d
                  ·
                    have : d = 296052 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296051 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296050 ≤ d
                  ·
                    have : d = 296050 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 31) (by norm_num)
      exact by decide
                  ·
                    have : d = 296049 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 296041 ≤ d
            ·
              by_cases h : 296045 ≤ d
              ·
                by_cases h : 296047 ≤ d
                ·
                  by_cases h : 296048 ≤ d
                  ·
                    have : d = 296048 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296047 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296046 ≤ d
                  ·
                    have : d = 296046 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296045 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296043 ≤ d
                ·
                  by_cases h : 296044 ≤ d
                  ·
                    have : d = 296044 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 97) (by norm_num)
      exact by decide
                  ·
                    have : d = 296043 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296042 ≤ d
                  ·
                    have : d = 296042 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296041 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 296037 ≤ d
              ·
                by_cases h : 296039 ≤ d
                ·
                  by_cases h : 296040 ≤ d
                  ·
                    have : d = 296040 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2467) (by norm_num)
      exact by decide
                  ·
                    have : d = 296039 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296038 ≤ d
                  ·
                    have : d = 296038 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296037 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296035 ≤ d
                ·
                  by_cases h : 296036 ≤ d
                  ·
                    have : d = 296036 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296035 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296034 ≤ d
                  ·
                    have : d = 296034 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 28234209953) (by norm_num)
      right
      exact ⟨296034, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296033 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 296017 ≤ d
          ·
            by_cases h : 296025 ≤ d
            ·
              by_cases h : 296029 ≤ d
              ·
                by_cases h : 296031 ≤ d
                ·
                  by_cases h : 296032 ≤ d
                  ·
                    have : d = 296032 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 29) (by norm_num)
      exact by decide
                  ·
                    have : d = 296031 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296030 ≤ d
                  ·
                    have : d = 296030 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296029 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296027 ≤ d
                ·
                  by_cases h : 296028 ≤ d
                  ·
                    have : d = 296028 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2741) (by norm_num)
      exact by decide
                  ·
                    have : d = 296027 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296026 ≤ d
                  ·
                    have : d = 296026 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296025 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 296021 ≤ d
              ·
                by_cases h : 296023 ≤ d
                ·
                  by_cases h : 296024 ≤ d
                  ·
                    have : d = 296024 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296023 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296022 ≤ d
                  ·
                    have : d = 296022 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 103) (by norm_num)
      exact by decide
                  ·
                    have : d = 296021 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296019 ≤ d
                ·
                  by_cases h : 296020 ≤ d
                  ·
                    have : d = 296020 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 296019 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296018 ≤ d
                  ·
                    have : d = 296018 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296017 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 296009 ≤ d
            ·
              by_cases h : 296013 ≤ d
              ·
                by_cases h : 296015 ≤ d
                ·
                  by_cases h : 296016 ≤ d
                  ·
                    have : d = 296016 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296015 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296014 ≤ d
                  ·
                    have : d = 296014 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296013 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296011 ≤ d
                ·
                  by_cases h : 296012 ≤ d
                  ·
                    have : d = 296012 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296011 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296010 ≤ d
                  ·
                    have : d = 296010 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296009 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 296005 ≤ d
              ·
                by_cases h : 296007 ≤ d
                ·
                  by_cases h : 296008 ≤ d
                  ·
                    have : d = 296008 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 163) (by norm_num)
      exact by decide
                  ·
                    have : d = 296007 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296006 ≤ d
                  ·
                    have : d = 296006 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 296005 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 296003 ≤ d
                ·
                  by_cases h : 296004 ≤ d
                  ·
                    have : d = 296004 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 296003 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 296002 ≤ d
                  ·
                    have : d = 296002 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 21143) (by norm_num)
      exact by decide
                  ·
                    have : d = 296001 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 295969 ≤ d
        ·
          by_cases h : 295985 ≤ d
          ·
            by_cases h : 295993 ≤ d
            ·
              by_cases h : 295997 ≤ d
              ·
                by_cases h : 295999 ≤ d
                ·
                  by_cases h : 296000 ≤ d
                  ·
                    have : d = 296000 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 295999 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 295998 ≤ d
                  ·
                    have : d = 295998 := by omega
                    subst d
      exact fullRecordGapTerm01959_not_prime
                  ·
                    have : d = 295997 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 295995 ≤ d
                ·
                  by_cases h : 295996 ≤ d
                  ·
                    have : d = 295996 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 295995 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 295994 ≤ d
                  ·
                    have : d = 295994 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 295993 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 295989 ≤ d
              ·
                by_cases h : 295991 ≤ d
                ·
                  by_cases h : 295992 ≤ d
                  ·
                    have : d = 295992 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 295991 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 295990 ≤ d
                  ·
                    have : d = 295990 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 29599) (by norm_num)
      exact by decide
                  ·
                    have : d = 295989 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 295987 ≤ d
                ·
                  by_cases h : 295988 ≤ d
                  ·
                    have : d = 295988 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 295987 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 295986 ≤ d
                  ·
                    have : d = 295986 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 295985 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 295977 ≤ d
            ·
              by_cases h : 295981 ≤ d
              ·
                by_cases h : 295983 ≤ d
                ·
                  by_cases h : 295984 ≤ d
                  ·
                    have : d = 295984 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 295983 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 295982 ≤ d
                  ·
                    have : d = 295982 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 295981 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 295979 ≤ d
                ·
                  by_cases h : 295980 ≤ d
                  ·
                    have : d = 295980 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 4933) (by norm_num)
      exact by decide
                  ·
                    have : d = 295979 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 295978 ≤ d
                  ·
                    have : d = 295978 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 83) (by norm_num)
      exact by decide
                  ·
                    have : d = 295977 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 295973 ≤ d
              ·
                by_cases h : 295975 ≤ d
                ·
                  by_cases h : 295976 ≤ d
                  ·
                    have : d = 295976 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 295975 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 295974 ≤ d
                  ·
                    have : d = 295974 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 29) (by norm_num)
      exact by decide
                  ·
                    have : d = 295973 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 295971 ≤ d
                ·
                  by_cases h : 295972 ≤ d
                  ·
                    have : d = 295972 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 61) (by norm_num)
      exact by decide
                  ·
                    have : d = 295971 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 295970 ≤ d
                  ·
                    have : d = 295970 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 295969 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 295953 ≤ d
          ·
            by_cases h : 295961 ≤ d
            ·
              by_cases h : 295965 ≤ d
              ·
                by_cases h : 295967 ≤ d
                ·
                  by_cases h : 295968 ≤ d
                  ·
                    have : d = 295968 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 295967 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 295966 ≤ d
                  ·
                    have : d = 295966 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 295965 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 295963 ≤ d
                ·
                  by_cases h : 295964 ≤ d
                  ·
                    have : d = 295964 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 295963 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 295962 ≤ d
                  ·
                    have : d = 295962 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 107) (by norm_num)
      exact by decide
                  ·
                    have : d = 295961 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 295957 ≤ d
              ·
                by_cases h : 295959 ≤ d
                ·
                  by_cases h : 295960 ≤ d
                  ·
                    have : d = 295960 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 151) (by norm_num)
      exact by decide
                  ·
                    have : d = 295959 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 295958 ≤ d
                  ·
                    have : d = 295958 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 295957 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 295955 ≤ d
                ·
                  by_cases h : 295956 ≤ d
                  ·
                    have : d = 295956 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 295955 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 295954 ≤ d
                  ·
                    have : d = 295954 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 295953 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 295945 ≤ d
            ·
              by_cases h : 295949 ≤ d
              ·
                by_cases h : 295951 ≤ d
                ·
                  by_cases h : 295952 ≤ d
                  ·
                    have : d = 295952 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 295951 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 295950 ≤ d
                  ·
                    have : d = 295950 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1973) (by norm_num)
      exact by decide
                  ·
                    have : d = 295949 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 295947 ≤ d
                ·
                  by_cases h : 295948 ≤ d
                  ·
                    have : d = 295948 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 295947 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 295946 ≤ d
                  ·
                    have : d = 295946 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 295945 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 295941 ≤ d
              ·
                by_cases h : 295943 ≤ d
                ·
                  by_cases h : 295944 ≤ d
                  ·
                    have : d = 295944 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 295943 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 295942 ≤ d
                  ·
                    have : d = 295942 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 73) (by norm_num)
      exact by decide
                  ·
                    have : d = 295941 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 295939 ≤ d
                ·
                  by_cases h : 295940 ≤ d
                  ·
                    have : d = 295940 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 295939 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 295938 ≤ d
                  ·
                    have : d = 295938 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 41) (by norm_num)
      exact by decide
                  ·
                    have : d = 295937 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩

end PrimeFactorUnimodality
