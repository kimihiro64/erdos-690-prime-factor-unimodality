import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapFermat

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

theorem fullRecordGapAddBlock_part1972 (d : Nat) (552961 ≤ d) (d ≤ 553472) : ¬(recordGapCenter + d).Prime := by
  by_cases h : 553217 ≤ d
  ·
    by_cases h : 553345 ≤ d
    ·
      by_cases h : 553409 ≤ d
      ·
        by_cases h : 553441 ≤ d
        ·
          by_cases h : 553457 ≤ d
          ·
            by_cases h : 553465 ≤ d
            ·
              by_cases h : 553469 ≤ d
              ·
                by_cases h : 553471 ≤ d
                ·
                  by_cases h : 553472 ≤ d
                  ·
                    have : d = 553472 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553471 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553470 ≤ d
                  ·
                    have : d = 553470 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 553469 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553467 ≤ d
                ·
                  by_cases h : 553468 ≤ d
                  ·
                    have : d = 553468 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553467 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553466 ≤ d
                  ·
                    have : d = 553466 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 127)
      exact by decide
                  ·
                    have : d = 553465 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 553461 ≤ d
              ·
                by_cases h : 553463 ≤ d
                ·
                  by_cases h : 553464 ≤ d
                  ·
                    have : d = 553464 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553463 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553462 ≤ d
                  ·
                    have : d = 553462 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553461 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553459 ≤ d
                ·
                  by_cases h : 553460 ≤ d
                  ·
                    have : d = 553460 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 27673)
      exact by decide
                  ·
                    have : d = 553459 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553458 ≤ d
                  ·
                    have : d = 553458 := by omega
                    subst d
      exact fullRecordGapTerm09241_not_prime
                  ·
                    have : d = 553457 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 553449 ≤ d
            ·
              by_cases h : 553453 ≤ d
              ·
                by_cases h : 553455 ≤ d
                ·
                  by_cases h : 553456 ≤ d
                  ·
                    have : d = 553456 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553455 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553454 ≤ d
                  ·
                    have : d = 553454 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553453 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553451 ≤ d
                ·
                  by_cases h : 553452 ≤ d
                  ·
                    have : d = 553452 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 553451 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553450 ≤ d
                  ·
                    have : d = 553450 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553449 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 553445 ≤ d
              ·
                by_cases h : 553447 ≤ d
                ·
                  by_cases h : 553448 ≤ d
                  ·
                    have : d = 553448 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 9883)
      exact by decide
                  ·
                    have : d = 553447 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553446 ≤ d
                  ·
                    have : d = 553446 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 553445 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553443 ≤ d
                ·
                  by_cases h : 553444 ≤ d
                  ·
                    have : d = 553444 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553443 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553442 ≤ d
                  ·
                    have : d = 553442 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 340014361)
      right
      exact ⟨339460919, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553441 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 553425 ≤ d
          ·
            by_cases h : 553433 ≤ d
            ·
              by_cases h : 553437 ≤ d
              ·
                by_cases h : 553439 ≤ d
                ·
                  by_cases h : 553440 ≤ d
                  ·
                    have : d = 553440 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553439 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553438 ≤ d
                  ·
                    have : d = 553438 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553437 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553435 ≤ d
                ·
                  by_cases h : 553436 ≤ d
                  ·
                    have : d = 553436 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 553435 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553434 ≤ d
                  ·
                    have : d = 553434 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553433 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 553429 ≤ d
              ·
                by_cases h : 553431 ≤ d
                ·
                  by_cases h : 553432 ≤ d
                  ·
                    have : d = 553432 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553431 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553430 ≤ d
                  ·
                    have : d = 553430 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 991429)
      right
      exact ⟨437999, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553429 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553427 ≤ d
                ·
                  by_cases h : 553428 ≤ d
                  ·
                    have : d = 553428 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553427 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553426 ≤ d
                  ·
                    have : d = 553426 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553425 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 553417 ≤ d
            ·
              by_cases h : 553421 ≤ d
              ·
                by_cases h : 553423 ≤ d
                ·
                  by_cases h : 553424 ≤ d
                  ·
                    have : d = 553424 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553423 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553422 ≤ d
                  ·
                    have : d = 553422 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1860001001)
      right
      exact ⟨1859447579, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553421 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553419 ≤ d
                ·
                  by_cases h : 553420 ≤ d
                  ·
                    have : d = 553420 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553419 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553418 ≤ d
                  ·
                    have : d = 553418 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 553417 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 553413 ≤ d
              ·
                by_cases h : 553415 ≤ d
                ·
                  by_cases h : 553416 ≤ d
                  ·
                    have : d = 553416 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23059)
      exact by decide
                  ·
                    have : d = 553415 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553414 ≤ d
                  ·
                    have : d = 553414 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553413 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553411 ≤ d
                ·
                  by_cases h : 553412 ≤ d
                  ·
                    have : d = 553412 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553411 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553410 ≤ d
                  ·
                    have : d = 553410 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 553409 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 553377 ≤ d
        ·
          by_cases h : 553393 ≤ d
          ·
            by_cases h : 553401 ≤ d
            ·
              by_cases h : 553405 ≤ d
              ·
                by_cases h : 553407 ≤ d
                ·
                  by_cases h : 553408 ≤ d
                  ·
                    have : d = 553408 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553407 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553406 ≤ d
                  ·
                    have : d = 553406 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553405 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553403 ≤ d
                ·
                  by_cases h : 553404 ≤ d
                  ·
                    have : d = 553404 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553403 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553402 ≤ d
                  ·
                    have : d = 553402 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553401 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 553397 ≤ d
              ·
                by_cases h : 553399 ≤ d
                ·
                  by_cases h : 553400 ≤ d
                  ·
                    have : d = 553400 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2767)
      exact by decide
                  ·
                    have : d = 553399 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553398 ≤ d
                  ·
                    have : d = 553398 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553397 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553395 ≤ d
                ·
                  by_cases h : 553396 ≤ d
                  ·
                    have : d = 553396 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553395 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553394 ≤ d
                  ·
                    have : d = 553394 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553393 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 553385 ≤ d
            ·
              by_cases h : 553389 ≤ d
              ·
                by_cases h : 553391 ≤ d
                ·
                  by_cases h : 553392 ≤ d
                  ·
                    have : d = 553392 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 61)
      exact by decide
                  ·
                    have : d = 553391 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553390 ≤ d
                  ·
                    have : d = 553390 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553389 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553387 ≤ d
                ·
                  by_cases h : 553388 ≤ d
                  ·
                    have : d = 553388 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 12577)
      exact by decide
                  ·
                    have : d = 553387 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553386 ≤ d
                  ·
                    have : d = 553386 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 149)
      exact by decide
                  ·
                    have : d = 553385 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 553381 ≤ d
              ·
                by_cases h : 553383 ≤ d
                ·
                  by_cases h : 553384 ≤ d
                  ·
                    have : d = 553384 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553383 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553382 ≤ d
                  ·
                    have : d = 553382 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 271)
      exact by decide
                  ·
                    have : d = 553381 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553379 ≤ d
                ·
                  by_cases h : 553380 ≤ d
                  ·
                    have : d = 553380 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 553379 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553378 ≤ d
                  ·
                    have : d = 553378 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553377 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 553361 ≤ d
          ·
            by_cases h : 553369 ≤ d
            ·
              by_cases h : 553373 ≤ d
              ·
                by_cases h : 553375 ≤ d
                ·
                  by_cases h : 553376 ≤ d
                  ·
                    have : d = 553376 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17293)
      exact by decide
                  ·
                    have : d = 553375 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553374 ≤ d
                  ·
                    have : d = 553374 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553373 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553371 ≤ d
                ·
                  by_cases h : 553372 ≤ d
                  ·
                    have : d = 553372 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553371 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553370 ≤ d
                  ·
                    have : d = 553370 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553369 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 553365 ≤ d
              ·
                by_cases h : 553367 ≤ d
                ·
                  by_cases h : 553368 ≤ d
                  ·
                    have : d = 553368 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23057)
      exact by decide
                  ·
                    have : d = 553367 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553366 ≤ d
                  ·
                    have : d = 553366 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553365 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553363 ≤ d
                ·
                  by_cases h : 553364 ≤ d
                  ·
                    have : d = 553364 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553363 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553362 ≤ d
                  ·
                    have : d = 553362 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553361 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 553353 ≤ d
            ·
              by_cases h : 553357 ≤ d
              ·
                by_cases h : 553359 ≤ d
                ·
                  by_cases h : 553360 ≤ d
                  ·
                    have : d = 553360 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553359 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553358 ≤ d
                  ·
                    have : d = 553358 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 553357 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553355 ≤ d
                ·
                  by_cases h : 553356 ≤ d
                  ·
                    have : d = 553356 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553355 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553354 ≤ d
                  ·
                    have : d = 553354 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553353 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 553349 ≤ d
              ·
                by_cases h : 553351 ≤ d
                ·
                  by_cases h : 553352 ≤ d
                  ·
                    have : d = 553352 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 263)
      exact by decide
                  ·
                    have : d = 553351 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553350 ≤ d
                  ·
                    have : d = 553350 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 553349 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553347 ≤ d
                ·
                  by_cases h : 553348 ≤ d
                  ·
                    have : d = 553348 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553347 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553346 ≤ d
                  ·
                    have : d = 553346 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 26790587)
      right
      exact ⟨26237241, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553345 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 553281 ≤ d
      ·
        by_cases h : 553313 ≤ d
        ·
          by_cases h : 553329 ≤ d
          ·
            by_cases h : 553337 ≤ d
            ·
              by_cases h : 553341 ≤ d
              ·
                by_cases h : 553343 ≤ d
                ·
                  by_cases h : 553344 ≤ d
                  ·
                    have : d = 553344 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553343 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553342 ≤ d
                  ·
                    have : d = 553342 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553341 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553339 ≤ d
                ·
                  by_cases h : 553340 ≤ d
                  ·
                    have : d = 553340 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553339 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553338 ≤ d
                  ·
                    have : d = 553338 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 10247)
      exact by decide
                  ·
                    have : d = 553337 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 553333 ≤ d
              ·
                by_cases h : 553335 ≤ d
                ·
                  by_cases h : 553336 ≤ d
                  ·
                    have : d = 553336 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553335 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553334 ≤ d
                  ·
                    have : d = 553334 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553333 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553331 ≤ d
                ·
                  by_cases h : 553332 ≤ d
                  ·
                    have : d = 553332 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 553331 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553330 ≤ d
                  ·
                    have : d = 553330 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553329 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 553321 ≤ d
            ·
              by_cases h : 553325 ≤ d
              ·
                by_cases h : 553327 ≤ d
                ·
                  by_cases h : 553328 ≤ d
                  ·
                    have : d = 553328 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553327 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553326 ≤ d
                  ·
                    have : d = 553326 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 579263)
      right
      exact ⟨25937, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553325 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553323 ≤ d
                ·
                  by_cases h : 553324 ≤ d
                  ·
                    have : d = 553324 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553323 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553322 ≤ d
                  ·
                    have : d = 553322 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3593)
      exact by decide
                  ·
                    have : d = 553321 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 553317 ≤ d
              ·
                by_cases h : 553319 ≤ d
                ·
                  by_cases h : 553320 ≤ d
                  ·
                    have : d = 553320 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 553319 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553318 ≤ d
                  ·
                    have : d = 553318 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553317 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553315 ≤ d
                ·
                  by_cases h : 553316 ≤ d
                  ·
                    have : d = 553316 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 553315 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553314 ≤ d
                  ·
                    have : d = 553314 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553313 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 553297 ≤ d
          ·
            by_cases h : 553305 ≤ d
            ·
              by_cases h : 553309 ≤ d
              ·
                by_cases h : 553311 ≤ d
                ·
                  by_cases h : 553312 ≤ d
                  ·
                    have : d = 553312 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553311 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553310 ≤ d
                  ·
                    have : d = 553310 := by omega
                    subst d
      exact fullRecordGapTerm09240_not_prime
                  ·
                    have : d = 553309 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553307 ≤ d
                ·
                  by_cases h : 553308 ≤ d
                  ·
                    have : d = 553308 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 941)
      exact by decide
                  ·
                    have : d = 553307 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553306 ≤ d
                  ·
                    have : d = 553306 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553305 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 553301 ≤ d
              ·
                by_cases h : 553303 ≤ d
                ·
                  by_cases h : 553304 ≤ d
                  ·
                    have : d = 553304 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553303 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553302 ≤ d
                  ·
                    have : d = 553302 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 59)
      exact by decide
                  ·
                    have : d = 553301 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553299 ≤ d
                ·
                  by_cases h : 553300 ≤ d
                  ·
                    have : d = 553300 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553299 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553298 ≤ d
                  ·
                    have : d = 553298 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 553297 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 553289 ≤ d
            ·
              by_cases h : 553293 ≤ d
              ·
                by_cases h : 553295 ≤ d
                ·
                  by_cases h : 553296 ≤ d
                  ·
                    have : d = 553296 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553295 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553294 ≤ d
                  ·
                    have : d = 553294 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553293 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553291 ≤ d
                ·
                  by_cases h : 553292 ≤ d
                  ·
                    have : d = 553292 := by omega
                    subst d
      exact fullRecordGapTerm09239_not_prime
                  ·
                    have : d = 553291 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553290 ≤ d
                  ·
                    have : d = 553290 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 18443)
      exact by decide
                  ·
                    have : d = 553289 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 553285 ≤ d
              ·
                by_cases h : 553287 ≤ d
                ·
                  by_cases h : 553288 ≤ d
                  ·
                    have : d = 553288 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553287 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553286 ≤ d
                  ·
                    have : d = 553286 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553285 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553283 ≤ d
                ·
                  by_cases h : 553284 ≤ d
                  ·
                    have : d = 553284 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553283 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553282 ≤ d
                  ·
                    have : d = 553282 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553281 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 553249 ≤ d
        ·
          by_cases h : 553265 ≤ d
          ·
            by_cases h : 553273 ≤ d
            ·
              by_cases h : 553277 ≤ d
              ·
                by_cases h : 553279 ≤ d
                ·
                  by_cases h : 553280 ≤ d
                  ·
                    have : d = 553280 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 553279 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553278 ≤ d
                  ·
                    have : d = 553278 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 83)
      exact by decide
                  ·
                    have : d = 553277 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553275 ≤ d
                ·
                  by_cases h : 553276 ≤ d
                  ·
                    have : d = 553276 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553275 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553274 ≤ d
                  ·
                    have : d = 553274 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553273 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 553269 ≤ d
              ·
                by_cases h : 553271 ≤ d
                ·
                  by_cases h : 553272 ≤ d
                  ·
                    have : d = 553272 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553271 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553270 ≤ d
                  ·
                    have : d = 553270 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553269 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553267 ≤ d
                ·
                  by_cases h : 553268 ≤ d
                  ·
                    have : d = 553268 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 157)
      exact by decide
                  ·
                    have : d = 553267 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553266 ≤ d
                  ·
                    have : d = 553266 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 4391)
      exact by decide
                  ·
                    have : d = 553265 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 553257 ≤ d
            ·
              by_cases h : 553261 ≤ d
              ·
                by_cases h : 553263 ≤ d
                ·
                  by_cases h : 553264 ≤ d
                  ·
                    have : d = 553264 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553263 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553262 ≤ d
                  ·
                    have : d = 553262 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 553261 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553259 ≤ d
                ·
                  by_cases h : 553260 ≤ d
                  ·
                    have : d = 553260 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 9221)
      exact by decide
                  ·
                    have : d = 553259 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553258 ≤ d
                  ·
                    have : d = 553258 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553257 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 553253 ≤ d
              ·
                by_cases h : 553255 ≤ d
                ·
                  by_cases h : 553256 ≤ d
                  ·
                    have : d = 553256 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 6287)
      exact by decide
                  ·
                    have : d = 553255 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553254 ≤ d
                  ·
                    have : d = 553254 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553253 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553251 ≤ d
                ·
                  by_cases h : 553252 ≤ d
                  ·
                    have : d = 553252 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553251 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553250 ≤ d
                  ·
                    have : d = 553250 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2213)
      exact by decide
                  ·
                    have : d = 553249 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 553233 ≤ d
          ·
            by_cases h : 553241 ≤ d
            ·
              by_cases h : 553245 ≤ d
              ·
                by_cases h : 553247 ≤ d
                ·
                  by_cases h : 553248 ≤ d
                  ·
                    have : d = 553248 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 553247 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553246 ≤ d
                  ·
                    have : d = 553246 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553245 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553243 ≤ d
                ·
                  by_cases h : 553244 ≤ d
                  ·
                    have : d = 553244 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553243 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553242 ≤ d
                  ·
                    have : d = 553242 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 553241 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 553237 ≤ d
              ·
                by_cases h : 553239 ≤ d
                ·
                  by_cases h : 553240 ≤ d
                  ·
                    have : d = 553240 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553239 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553238 ≤ d
                  ·
                    have : d = 553238 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 43)
      exact by decide
                  ·
                    have : d = 553237 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553235 ≤ d
                ·
                  by_cases h : 553236 ≤ d
                  ·
                    have : d = 553236 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 230861)
      right
      exact ⟨139347, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553235 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553234 ≤ d
                  ·
                    have : d = 553234 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553233 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 553225 ≤ d
            ·
              by_cases h : 553229 ≤ d
              ·
                by_cases h : 553231 ≤ d
                ·
                  by_cases h : 553232 ≤ d
                  ·
                    have : d = 553232 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 71)
      exact by decide
                  ·
                    have : d = 553231 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553230 ≤ d
                  ·
                    have : d = 553230 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553229 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553227 ≤ d
                ·
                  by_cases h : 553228 ≤ d
                  ·
                    have : d = 553228 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553227 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553226 ≤ d
                  ·
                    have : d = 553226 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 553225 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 553221 ≤ d
              ·
                by_cases h : 553223 ≤ d
                ·
                  by_cases h : 553224 ≤ d
                  ·
                    have : d = 553224 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553223 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553222 ≤ d
                  ·
                    have : d = 553222 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553221 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553219 ≤ d
                ·
                  by_cases h : 553220 ≤ d
                  ·
                    have : d = 553220 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 139)
      exact by decide
                  ·
                    have : d = 553219 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553218 ≤ d
                  ·
                    have : d = 553218 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 383917)
      right
      exact ⟨214616, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553217 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
  ·
    by_cases h : 553089 ≤ d
    ·
      by_cases h : 553153 ≤ d
      ·
        by_cases h : 553185 ≤ d
        ·
          by_cases h : 553201 ≤ d
          ·
            by_cases h : 553209 ≤ d
            ·
              by_cases h : 553213 ≤ d
              ·
                by_cases h : 553215 ≤ d
                ·
                  by_cases h : 553216 ≤ d
                  ·
                    have : d = 553216 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553215 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553214 ≤ d
                  ·
                    have : d = 553214 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553213 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553211 ≤ d
                ·
                  by_cases h : 553212 ≤ d
                  ·
                    have : d = 553212 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 127)
      exact by decide
                  ·
                    have : d = 553211 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553210 ≤ d
                  ·
                    have : d = 553210 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553209 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 553205 ≤ d
              ·
                by_cases h : 553207 ≤ d
                ·
                  by_cases h : 553208 ≤ d
                  ·
                    have : d = 553208 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553207 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553206 ≤ d
                  ·
                    have : d = 553206 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 137)
      exact by decide
                  ·
                    have : d = 553205 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553203 ≤ d
                ·
                  by_cases h : 553204 ≤ d
                  ·
                    have : d = 553204 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553203 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553202 ≤ d
                  ·
                    have : d = 553202 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553201 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 553193 ≤ d
            ·
              by_cases h : 553197 ≤ d
              ·
                by_cases h : 553199 ≤ d
                ·
                  by_cases h : 553200 ≤ d
                  ·
                    have : d = 553200 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 461)
      exact by decide
                  ·
                    have : d = 553199 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553198 ≤ d
                  ·
                    have : d = 553198 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553197 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553195 ≤ d
                ·
                  by_cases h : 553196 ≤ d
                  ·
                    have : d = 553196 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 553195 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553194 ≤ d
                  ·
                    have : d = 553194 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553193 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 553189 ≤ d
              ·
                by_cases h : 553191 ≤ d
                ·
                  by_cases h : 553192 ≤ d
                  ·
                    have : d = 553192 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553191 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553190 ≤ d
                  ·
                    have : d = 553190 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 47)
      exact by decide
                  ·
                    have : d = 553189 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553187 ≤ d
                ·
                  by_cases h : 553188 ≤ d
                  ·
                    have : d = 553188 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553187 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553186 ≤ d
                  ·
                    have : d = 553186 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553185 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 553169 ≤ d
          ·
            by_cases h : 553177 ≤ d
            ·
              by_cases h : 553181 ≤ d
              ·
                by_cases h : 553183 ≤ d
                ·
                  by_cases h : 553184 ≤ d
                  ·
                    have : d = 553184 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553183 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553182 ≤ d
                  ·
                    have : d = 553182 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13171)
      exact by decide
                  ·
                    have : d = 553181 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553179 ≤ d
                ·
                  by_cases h : 553180 ≤ d
                  ·
                    have : d = 553180 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553179 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553178 ≤ d
                  ·
                    have : d = 553178 := by omega
                    subst d
      exact fullRecordGapTerm09238_not_prime
                  ·
                    have : d = 553177 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 553173 ≤ d
              ·
                by_cases h : 553175 ≤ d
                ·
                  by_cases h : 553176 ≤ d
                  ·
                    have : d = 553176 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 553175 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553174 ≤ d
                  ·
                    have : d = 553174 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553173 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553171 ≤ d
                ·
                  by_cases h : 553172 ≤ d
                  ·
                    have : d = 553172 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 41)
      exact by decide
                  ·
                    have : d = 553171 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553170 ≤ d
                  ·
                    have : d = 553170 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 18439)
      exact by decide
                  ·
                    have : d = 553169 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 553161 ≤ d
            ·
              by_cases h : 553165 ≤ d
              ·
                by_cases h : 553167 ≤ d
                ·
                  by_cases h : 553168 ≤ d
                  ·
                    have : d = 553168 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553167 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553166 ≤ d
                  ·
                    have : d = 553166 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 553165 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553163 ≤ d
                ·
                  by_cases h : 553164 ≤ d
                  ·
                    have : d = 553164 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553163 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553162 ≤ d
                  ·
                    have : d = 553162 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553161 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 553157 ≤ d
              ·
                by_cases h : 553159 ≤ d
                ·
                  by_cases h : 553160 ≤ d
                  ·
                    have : d = 553160 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553159 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553158 ≤ d
                  ·
                    have : d = 553158 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 79)
      exact by decide
                  ·
                    have : d = 553157 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553155 ≤ d
                ·
                  by_cases h : 553156 ≤ d
                  ·
                    have : d = 553156 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553155 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553154 ≤ d
                  ·
                    have : d = 553154 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553153 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 553121 ≤ d
        ·
          by_cases h : 553137 ≤ d
          ·
            by_cases h : 553145 ≤ d
            ·
              by_cases h : 553149 ≤ d
              ·
                by_cases h : 553151 ≤ d
                ·
                  by_cases h : 553152 ≤ d
                  ·
                    have : d = 553152 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 43)
      exact by decide
                  ·
                    have : d = 553151 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553150 ≤ d
                  ·
                    have : d = 553150 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553149 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553147 ≤ d
                ·
                  by_cases h : 553148 ≤ d
                  ·
                    have : d = 553148 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 61)
      exact by decide
                  ·
                    have : d = 553147 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553146 ≤ d
                  ·
                    have : d = 553146 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553145 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 553141 ≤ d
              ·
                by_cases h : 553143 ≤ d
                ·
                  by_cases h : 553144 ≤ d
                  ·
                    have : d = 553144 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553143 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553142 ≤ d
                  ·
                    have : d = 553142 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553141 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553139 ≤ d
                ·
                  by_cases h : 553140 ≤ d
                  ·
                    have : d = 553140 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 439)
      exact by decide
                  ·
                    have : d = 553139 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553138 ≤ d
                  ·
                    have : d = 553138 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553137 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 553129 ≤ d
            ·
              by_cases h : 553133 ≤ d
              ·
                by_cases h : 553135 ≤ d
                ·
                  by_cases h : 553136 ≤ d
                  ·
                    have : d = 553136 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 181)
      exact by decide
                  ·
                    have : d = 553135 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553134 ≤ d
                  ·
                    have : d = 553134 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553133 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553131 ≤ d
                ·
                  by_cases h : 553132 ≤ d
                  ·
                    have : d = 553132 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553131 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553130 ≤ d
                  ·
                    have : d = 553130 := by omega
                    subst d
      exact fullRecordGapTerm09237_not_prime
                  ·
                    have : d = 553129 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 553125 ≤ d
              ·
                by_cases h : 553127 ≤ d
                ·
                  by_cases h : 553128 ≤ d
                  ·
                    have : d = 553128 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 553127 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553126 ≤ d
                  ·
                    have : d = 553126 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553125 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553123 ≤ d
                ·
                  by_cases h : 553124 ≤ d
                  ·
                    have : d = 553124 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553123 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553122 ≤ d
                  ·
                    have : d = 553122 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 10243)
      exact by decide
                  ·
                    have : d = 553121 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 553105 ≤ d
          ·
            by_cases h : 553113 ≤ d
            ·
              by_cases h : 553117 ≤ d
              ·
                by_cases h : 553119 ≤ d
                ·
                  by_cases h : 553120 ≤ d
                  ·
                    have : d = 553120 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553119 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553118 ≤ d
                  ·
                    have : d = 553118 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553117 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553115 ≤ d
                ·
                  by_cases h : 553116 ≤ d
                  ·
                    have : d = 553116 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1789003)
      right
      exact ⟨1235887, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553115 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553114 ≤ d
                  ·
                    have : d = 553114 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553113 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 553109 ≤ d
              ·
                by_cases h : 553111 ≤ d
                ·
                  by_cases h : 553112 ≤ d
                  ·
                    have : d = 553112 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 553111 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553110 ≤ d
                  ·
                    have : d = 553110 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 103)
      exact by decide
                  ·
                    have : d = 553109 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553107 ≤ d
                ·
                  by_cases h : 553108 ≤ d
                  ·
                    have : d = 553108 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553107 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553106 ≤ d
                  ·
                    have : d = 553106 := by omega
                    subst d
      exact fullRecordGapTerm09236_not_prime
                  ·
                    have : d = 553105 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 553097 ≤ d
            ·
              by_cases h : 553101 ≤ d
              ·
                by_cases h : 553103 ≤ d
                ·
                  by_cases h : 553104 ≤ d
                  ·
                    have : d = 553104 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553103 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553102 ≤ d
                  ·
                    have : d = 553102 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553101 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553099 ≤ d
                ·
                  by_cases h : 553100 ≤ d
                  ·
                    have : d = 553100 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5531)
      exact by decide
                  ·
                    have : d = 553099 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553098 ≤ d
                  ·
                    have : d = 553098 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553097 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 553093 ≤ d
              ·
                by_cases h : 553095 ≤ d
                ·
                  by_cases h : 553096 ≤ d
                  ·
                    have : d = 553096 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553095 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553094 ≤ d
                  ·
                    have : d = 553094 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553093 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553091 ≤ d
                ·
                  by_cases h : 553092 ≤ d
                  ·
                    have : d = 553092 := by omega
                    subst d
      exact fullRecordGapTerm09235_not_prime
                  ·
                    have : d = 553091 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553090 ≤ d
                  ·
                    have : d = 553090 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553089 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 553025 ≤ d
      ·
        by_cases h : 553057 ≤ d
        ·
          by_cases h : 553073 ≤ d
          ·
            by_cases h : 553081 ≤ d
            ·
              by_cases h : 553085 ≤ d
              ·
                by_cases h : 553087 ≤ d
                ·
                  by_cases h : 553088 ≤ d
                  ·
                    have : d = 553088 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 553087 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553086 ≤ d
                  ·
                    have : d = 553086 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 30727)
      exact by decide
                  ·
                    have : d = 553085 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553083 ≤ d
                ·
                  by_cases h : 553084 ≤ d
                  ·
                    have : d = 553084 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553083 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553082 ≤ d
                  ·
                    have : d = 553082 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 131)
      exact by decide
                  ·
                    have : d = 553081 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 553077 ≤ d
              ·
                by_cases h : 553079 ≤ d
                ·
                  by_cases h : 553080 ≤ d
                  ·
                    have : d = 553080 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 419)
      exact by decide
                  ·
                    have : d = 553079 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553078 ≤ d
                  ·
                    have : d = 553078 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553077 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553075 ≤ d
                ·
                  by_cases h : 553076 ≤ d
                  ·
                    have : d = 553076 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553075 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553074 ≤ d
                  ·
                    have : d = 553074 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553073 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 553065 ≤ d
            ·
              by_cases h : 553069 ≤ d
              ·
                by_cases h : 553071 ≤ d
                ·
                  by_cases h : 553072 ≤ d
                  ·
                    have : d = 553072 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553071 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553070 ≤ d
                  ·
                    have : d = 553070 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7901)
      exact by decide
                  ·
                    have : d = 553069 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553067 ≤ d
                ·
                  by_cases h : 553068 ≤ d
                  ·
                    have : d = 553068 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 569)
      exact by decide
                  ·
                    have : d = 553067 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553066 ≤ d
                  ·
                    have : d = 553066 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553065 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 553061 ≤ d
              ·
                by_cases h : 553063 ≤ d
                ·
                  by_cases h : 553064 ≤ d
                  ·
                    have : d = 553064 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553063 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553062 ≤ d
                  ·
                    have : d = 553062 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553061 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553059 ≤ d
                ·
                  by_cases h : 553060 ≤ d
                  ·
                    have : d = 553060 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553059 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553058 ≤ d
                  ·
                    have : d = 553058 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 553057 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 553041 ≤ d
          ·
            by_cases h : 553049 ≤ d
            ·
              by_cases h : 553053 ≤ d
              ·
                by_cases h : 553055 ≤ d
                ·
                  by_cases h : 553056 ≤ d
                  ·
                    have : d = 553056 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 823)
      exact by decide
                  ·
                    have : d = 553055 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553054 ≤ d
                  ·
                    have : d = 553054 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553053 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553051 ≤ d
                ·
                  by_cases h : 553052 ≤ d
                  ·
                    have : d = 553052 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 553051 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553050 ≤ d
                  ·
                    have : d = 553050 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1229)
      exact by decide
                  ·
                    have : d = 553049 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 553045 ≤ d
              ·
                by_cases h : 553047 ≤ d
                ·
                  by_cases h : 553048 ≤ d
                  ·
                    have : d = 553048 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553047 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553046 ≤ d
                  ·
                    have : d = 553046 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 553045 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553043 ≤ d
                ·
                  by_cases h : 553044 ≤ d
                  ·
                    have : d = 553044 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553043 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553042 ≤ d
                  ·
                    have : d = 553042 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553041 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 553033 ≤ d
            ·
              by_cases h : 553037 ≤ d
              ·
                by_cases h : 553039 ≤ d
                ·
                  by_cases h : 553040 ≤ d
                  ·
                    have : d = 553040 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 553039 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553038 ≤ d
                  ·
                    have : d = 553038 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5472619531)
      right
      exact ⟨5472066493, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553037 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553035 ≤ d
                ·
                  by_cases h : 553036 ≤ d
                  ·
                    have : d = 553036 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553035 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553034 ≤ d
                  ·
                    have : d = 553034 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553033 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 553029 ≤ d
              ·
                by_cases h : 553031 ≤ d
                ·
                  by_cases h : 553032 ≤ d
                  ·
                    have : d = 553032 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553031 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553030 ≤ d
                  ·
                    have : d = 553030 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553029 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553027 ≤ d
                ·
                  by_cases h : 553028 ≤ d
                  ·
                    have : d = 553028 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19751)
      exact by decide
                  ·
                    have : d = 553027 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553026 ≤ d
                  ·
                    have : d = 553026 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 61)
      exact by decide
                  ·
                    have : d = 553025 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 552993 ≤ d
        ·
          by_cases h : 553009 ≤ d
          ·
            by_cases h : 553017 ≤ d
            ·
              by_cases h : 553021 ≤ d
              ·
                by_cases h : 553023 ≤ d
                ·
                  by_cases h : 553024 ≤ d
                  ·
                    have : d = 553024 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553023 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553022 ≤ d
                  ·
                    have : d = 553022 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 113)
      exact by decide
                  ·
                    have : d = 553021 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553019 ≤ d
                ·
                  by_cases h : 553020 ≤ d
                  ·
                    have : d = 553020 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553019 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553018 ≤ d
                  ·
                    have : d = 553018 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553017 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 553013 ≤ d
              ·
                by_cases h : 553015 ≤ d
                ·
                  by_cases h : 553016 ≤ d
                  ·
                    have : d = 553016 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 84121)
      right
      exact ⟨35831, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553015 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553014 ≤ d
                  ·
                    have : d = 553014 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553013 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553011 ≤ d
                ·
                  by_cases h : 553012 ≤ d
                  ·
                    have : d = 553012 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553011 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553010 ≤ d
                  ·
                    have : d = 553010 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553009 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 553001 ≤ d
            ·
              by_cases h : 553005 ≤ d
              ·
                by_cases h : 553007 ≤ d
                ·
                  by_cases h : 553008 ≤ d
                  ·
                    have : d = 553008 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 41)
      exact by decide
                  ·
                    have : d = 553007 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553006 ≤ d
                  ·
                    have : d = 553006 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553005 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 553003 ≤ d
                ·
                  by_cases h : 553004 ≤ d
                  ·
                    have : d = 553004 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 553003 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 553002 ≤ d
                  ·
                    have : d = 553002 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 553001 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 552997 ≤ d
              ·
                by_cases h : 552999 ≤ d
                ·
                  by_cases h : 553000 ≤ d
                  ·
                    have : d = 553000 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 552999 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 552998 ≤ d
                  ·
                    have : d = 552998 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 126190543)
      right
      exact ⟨125637545, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 552997 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 552995 ≤ d
                ·
                  by_cases h : 552996 ≤ d
                  ·
                    have : d = 552996 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 15361)
      exact by decide
                  ·
                    have : d = 552995 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 552994 ≤ d
                  ·
                    have : d = 552994 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 552993 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 552977 ≤ d
          ·
            by_cases h : 552985 ≤ d
            ·
              by_cases h : 552989 ≤ d
              ·
                by_cases h : 552991 ≤ d
                ·
                  by_cases h : 552992 ≤ d
                  ·
                    have : d = 552992 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 552991 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 552990 ≤ d
                  ·
                    have : d = 552990 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 18433)
      exact by decide
                  ·
                    have : d = 552989 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 552987 ≤ d
                ·
                  by_cases h : 552988 ≤ d
                  ·
                    have : d = 552988 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 552987 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 552986 ≤ d
                  ·
                    have : d = 552986 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 39499)
      exact by decide
                  ·
                    have : d = 552985 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 552981 ≤ d
              ·
                by_cases h : 552983 ≤ d
                ·
                  by_cases h : 552984 ≤ d
                  ·
                    have : d = 552984 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 552983 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 552982 ≤ d
                  ·
                    have : d = 552982 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 552981 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 552979 ≤ d
                ·
                  by_cases h : 552980 ≤ d
                  ·
                    have : d = 552980 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 43)
      exact by decide
                  ·
                    have : d = 552979 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 552978 ≤ d
                  ·
                    have : d = 552978 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 552977 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 552969 ≤ d
            ·
              by_cases h : 552973 ≤ d
              ·
                by_cases h : 552975 ≤ d
                ·
                  by_cases h : 552976 ≤ d
                  ·
                    have : d = 552976 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 552975 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 552974 ≤ d
                  ·
                    have : d = 552974 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 552973 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 552971 ≤ d
                ·
                  by_cases h : 552972 ≤ d
                  ·
                    have : d = 552972 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 552971 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 552970 ≤ d
                  ·
                    have : d = 552970 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 552969 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 552965 ≤ d
              ·
                by_cases h : 552967 ≤ d
                ·
                  by_cases h : 552968 ≤ d
                  ·
                    have : d = 552968 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 552967 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 552966 ≤ d
                  ·
                    have : d = 552966 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 552965 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 552963 ≤ d
                ·
                  by_cases h : 552964 ≤ d
                  ·
                    have : d = 552964 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 552963 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 552962 ≤ d
                  ·
                    have : d = 552962 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 151)
      exact by decide
                  ·
                    have : d = 552961 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩

end PrimeFactorUnimodality
