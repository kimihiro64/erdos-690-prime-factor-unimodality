import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapFermat

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

theorem fullRecordGapSubBlock_part0503 (d : Nat) (257025 ≤ d) (d ≤ 257536) : ¬(recordGapCenter - d).Prime := by
  by_cases h : 257281 ≤ d
  ·
    by_cases h : 257409 ≤ d
    ·
      by_cases h : 257473 ≤ d
      ·
        by_cases h : 257505 ≤ d
        ·
          by_cases h : 257521 ≤ d
          ·
            by_cases h : 257529 ≤ d
            ·
              by_cases h : 257533 ≤ d
              ·
                by_cases h : 257535 ≤ d
                ·
                  by_cases h : 257536 ≤ d
                  ·
                    have : d = 257536 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257535 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257534 ≤ d
                  ·
                    have : d = 257534 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257533 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257531 ≤ d
                ·
                  by_cases h : 257532 ≤ d
                  ·
                    have : d = 257532 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1951) (by norm_num)
      exact by decide
                  ·
                    have : d = 257531 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257530 ≤ d
                  ·
                    have : d = 257530 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 257529 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257525 ≤ d
              ·
                by_cases h : 257527 ≤ d
                ·
                  by_cases h : 257528 ≤ d
                  ·
                    have : d = 257528 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257527 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257526 ≤ d
                  ·
                    have : d = 257526 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257525 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257523 ≤ d
                ·
                  by_cases h : 257524 ≤ d
                  ·
                    have : d = 257524 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257523 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257522 ≤ d
                  ·
                    have : d = 257522 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257521 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 257513 ≤ d
            ·
              by_cases h : 257517 ≤ d
              ·
                by_cases h : 257519 ≤ d
                ·
                  by_cases h : 257520 ≤ d
                  ·
                    have : d = 257520 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 29) (by norm_num)
      exact by decide
                  ·
                    have : d = 257519 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257518 ≤ d
                  ·
                    have : d = 257518 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 331) (by norm_num)
      exact by decide
                  ·
                    have : d = 257517 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257515 ≤ d
                ·
                  by_cases h : 257516 ≤ d
                  ·
                    have : d = 257516 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257515 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257514 ≤ d
                  ·
                    have : d = 257514 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257513 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257509 ≤ d
              ·
                by_cases h : 257511 ≤ d
                ·
                  by_cases h : 257512 ≤ d
                  ·
                    have : d = 257512 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 32189) (by norm_num)
      exact by decide
                  ·
                    have : d = 257511 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257510 ≤ d
                  ·
                    have : d = 257510 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257509 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257507 ≤ d
                ·
                  by_cases h : 257508 ≤ d
                  ·
                    have : d = 257508 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23) (by norm_num)
      exact by decide
                  ·
                    have : d = 257507 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257506 ≤ d
                  ·
                    have : d = 257506 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257505 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 257489 ≤ d
          ·
            by_cases h : 257497 ≤ d
            ·
              by_cases h : 257501 ≤ d
              ·
                by_cases h : 257503 ≤ d
                ·
                  by_cases h : 257504 ≤ d
                  ·
                    have : d = 257504 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257503 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257502 ≤ d
                  ·
                    have : d = 257502 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 6131) (by norm_num)
      exact by decide
                  ·
                    have : d = 257501 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257499 ≤ d
                ·
                  by_cases h : 257500 ≤ d
                  ·
                    have : d = 257500 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 103) (by norm_num)
      exact by decide
                  ·
                    have : d = 257499 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257498 ≤ d
                  ·
                    have : d = 257498 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257497 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257493 ≤ d
              ·
                by_cases h : 257495 ≤ d
                ·
                  by_cases h : 257496 ≤ d
                  ·
                    have : d = 257496 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257495 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257494 ≤ d
                  ·
                    have : d = 257494 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 536933) (by norm_num)
      right
      exact ⟨257494, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257493 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257491 ≤ d
                ·
                  by_cases h : 257492 ≤ d
                  ·
                    have : d = 257492 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257491 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257490 ≤ d
                  ·
                    have : d = 257490 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2861) (by norm_num)
      exact by decide
                  ·
                    have : d = 257489 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 257481 ≤ d
            ·
              by_cases h : 257485 ≤ d
              ·
                by_cases h : 257487 ≤ d
                ·
                  by_cases h : 257488 ≤ d
                  ·
                    have : d = 257488 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 257487 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257486 ≤ d
                  ·
                    have : d = 257486 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257485 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257483 ≤ d
                ·
                  by_cases h : 257484 ≤ d
                  ·
                    have : d = 257484 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 43) (by norm_num)
      exact by decide
                  ·
                    have : d = 257483 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257482 ≤ d
                  ·
                    have : d = 257482 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257481 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257477 ≤ d
              ·
                by_cases h : 257479 ≤ d
                ·
                  by_cases h : 257480 ≤ d
                  ·
                    have : d = 257480 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257479 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257478 ≤ d
                  ·
                    have : d = 257478 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 257477 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257475 ≤ d
                ·
                  by_cases h : 257476 ≤ d
                  ·
                    have : d = 257476 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257475 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257474 ≤ d
                  ·
                    have : d = 257474 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257473 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 257441 ≤ d
        ·
          by_cases h : 257457 ≤ d
          ·
            by_cases h : 257465 ≤ d
            ·
              by_cases h : 257469 ≤ d
              ·
                by_cases h : 257471 ≤ d
                ·
                  by_cases h : 257472 ≤ d
                  ·
                    have : d = 257472 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 149) (by norm_num)
      exact by decide
                  ·
                    have : d = 257471 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257470 ≤ d
                  ·
                    have : d = 257470 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257469 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257467 ≤ d
                ·
                  by_cases h : 257468 ≤ d
                  ·
                    have : d = 257468 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257467 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257466 ≤ d
                  ·
                    have : d = 257466 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257465 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257461 ≤ d
              ·
                by_cases h : 257463 ≤ d
                ·
                  by_cases h : 257464 ≤ d
                  ·
                    have : d = 257464 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 32183) (by norm_num)
      exact by decide
                  ·
                    have : d = 257463 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257462 ≤ d
                  ·
                    have : d = 257462 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257461 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257459 ≤ d
                ·
                  by_cases h : 257460 ≤ d
                  ·
                    have : d = 257460 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 613) (by norm_num)
      exact by decide
                  ·
                    have : d = 257459 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257458 ≤ d
                  ·
                    have : d = 257458 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 109) (by norm_num)
      exact by decide
                  ·
                    have : d = 257457 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 257449 ≤ d
            ·
              by_cases h : 257453 ≤ d
              ·
                by_cases h : 257455 ≤ d
                ·
                  by_cases h : 257456 ≤ d
                  ·
                    have : d = 257456 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257455 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257454 ≤ d
                  ·
                    have : d = 257454 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257453 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257451 ≤ d
                ·
                  by_cases h : 257452 ≤ d
                  ·
                    have : d = 257452 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 257451 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257450 ≤ d
                  ·
                    have : d = 257450 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257449 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257445 ≤ d
              ·
                by_cases h : 257447 ≤ d
                ·
                  by_cases h : 257448 ≤ d
                  ·
                    have : d = 257448 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257447 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257446 ≤ d
                  ·
                    have : d = 257446 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257445 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257443 ≤ d
                ·
                  by_cases h : 257444 ≤ d
                  ·
                    have : d = 257444 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257443 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257442 ≤ d
                  ·
                    have : d = 257442 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 107) (by norm_num)
      exact by decide
                  ·
                    have : d = 257441 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 257425 ≤ d
          ·
            by_cases h : 257433 ≤ d
            ·
              by_cases h : 257437 ≤ d
              ·
                by_cases h : 257439 ≤ d
                ·
                  by_cases h : 257440 ≤ d
                  ·
                    have : d = 257440 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257439 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257438 ≤ d
                  ·
                    have : d = 257438 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257437 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257435 ≤ d
                ·
                  by_cases h : 257436 ≤ d
                  ·
                    have : d = 257436 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257435 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257434 ≤ d
                  ·
                    have : d = 257434 := by omega
                    subst d
      exact fullRecordGapTerm02392_not_prime
                  ·
                    have : d = 257433 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257429 ≤ d
              ·
                by_cases h : 257431 ≤ d
                ·
                  by_cases h : 257432 ≤ d
                  ·
                    have : d = 257432 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257431 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257430 ≤ d
                  ·
                    have : d = 257430 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 8581) (by norm_num)
      exact by decide
                  ·
                    have : d = 257429 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257427 ≤ d
                ·
                  by_cases h : 257428 ≤ d
                  ·
                    have : d = 257428 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 139) (by norm_num)
      exact by decide
                  ·
                    have : d = 257427 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257426 ≤ d
                  ·
                    have : d = 257426 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257425 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 257417 ≤ d
            ·
              by_cases h : 257421 ≤ d
              ·
                by_cases h : 257423 ≤ d
                ·
                  by_cases h : 257424 ≤ d
                  ·
                    have : d = 257424 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 31) (by norm_num)
      exact by decide
                  ·
                    have : d = 257423 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257422 ≤ d
                  ·
                    have : d = 257422 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11701) (by norm_num)
      exact by decide
                  ·
                    have : d = 257421 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257419 ≤ d
                ·
                  by_cases h : 257420 ≤ d
                  ·
                    have : d = 257420 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257419 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257418 ≤ d
                  ·
                    have : d = 257418 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 227) (by norm_num)
      exact by decide
                  ·
                    have : d = 257417 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257413 ≤ d
              ·
                by_cases h : 257415 ≤ d
                ·
                  by_cases h : 257416 ≤ d
                  ·
                    have : d = 257416 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257415 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257414 ≤ d
                  ·
                    have : d = 257414 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257413 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257411 ≤ d
                ·
                  by_cases h : 257412 ≤ d
                  ·
                    have : d = 257412 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257411 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257410 ≤ d
                  ·
                    have : d = 257410 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 25741) (by norm_num)
      exact by decide
                  ·
                    have : d = 257409 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 257345 ≤ d
      ·
        by_cases h : 257377 ≤ d
        ·
          by_cases h : 257393 ≤ d
          ·
            by_cases h : 257401 ≤ d
            ·
              by_cases h : 257405 ≤ d
              ·
                by_cases h : 257407 ≤ d
                ·
                  by_cases h : 257408 ≤ d
                  ·
                    have : d = 257408 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257407 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257406 ≤ d
                  ·
                    have : d = 257406 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257405 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257403 ≤ d
                ·
                  by_cases h : 257404 ≤ d
                  ·
                    have : d = 257404 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257403 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257402 ≤ d
                  ·
                    have : d = 257402 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257401 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257397 ≤ d
              ·
                by_cases h : 257399 ≤ d
                ·
                  by_cases h : 257400 ≤ d
                  ·
                    have : d = 257400 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 257399 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257398 ≤ d
                  ·
                    have : d = 257398 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257397 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257395 ≤ d
                ·
                  by_cases h : 257396 ≤ d
                  ·
                    have : d = 257396 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257395 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257394 ≤ d
                  ·
                    have : d = 257394 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 42899) (by norm_num)
      exact by decide
                  ·
                    have : d = 257393 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 257385 ≤ d
            ·
              by_cases h : 257389 ≤ d
              ·
                by_cases h : 257391 ≤ d
                ·
                  by_cases h : 257392 ≤ d
                  ·
                    have : d = 257392 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 16087) (by norm_num)
      exact by decide
                  ·
                    have : d = 257391 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257390 ≤ d
                  ·
                    have : d = 257390 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257389 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257387 ≤ d
                ·
                  by_cases h : 257388 ≤ d
                  ·
                    have : d = 257388 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 89) (by norm_num)
      exact by decide
                  ·
                    have : d = 257387 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257386 ≤ d
                  ·
                    have : d = 257386 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257385 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257381 ≤ d
              ·
                by_cases h : 257383 ≤ d
                ·
                  by_cases h : 257384 ≤ d
                  ·
                    have : d = 257384 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257383 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257382 ≤ d
                  ·
                    have : d = 257382 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257381 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257379 ≤ d
                ·
                  by_cases h : 257380 ≤ d
                  ·
                    have : d = 257380 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 257379 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257378 ≤ d
                  ·
                    have : d = 257378 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257377 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 257361 ≤ d
          ·
            by_cases h : 257369 ≤ d
            ·
              by_cases h : 257373 ≤ d
              ·
                by_cases h : 257375 ≤ d
                ·
                  by_cases h : 257376 ≤ d
                  ·
                    have : d = 257376 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257375 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257374 ≤ d
                  ·
                    have : d = 257374 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 257373 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257371 ≤ d
                ·
                  by_cases h : 257372 ≤ d
                  ·
                    have : d = 257372 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257371 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257370 ≤ d
                  ·
                    have : d = 257370 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257369 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257365 ≤ d
              ·
                by_cases h : 257367 ≤ d
                ·
                  by_cases h : 257368 ≤ d
                  ·
                    have : d = 257368 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 53) (by norm_num)
      exact by decide
                  ·
                    have : d = 257367 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257366 ≤ d
                  ·
                    have : d = 257366 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257365 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257363 ≤ d
                ·
                  by_cases h : 257364 ≤ d
                  ·
                    have : d = 257364 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2383) (by norm_num)
      exact by decide
                  ·
                    have : d = 257363 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257362 ≤ d
                  ·
                    have : d = 257362 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 31) (by norm_num)
      exact by decide
                  ·
                    have : d = 257361 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 257353 ≤ d
            ·
              by_cases h : 257357 ≤ d
              ·
                by_cases h : 257359 ≤ d
                ·
                  by_cases h : 257360 ≤ d
                  ·
                    have : d = 257360 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257359 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257358 ≤ d
                  ·
                    have : d = 257358 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 59) (by norm_num)
      exact by decide
                  ·
                    have : d = 257357 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257355 ≤ d
                ·
                  by_cases h : 257356 ≤ d
                  ·
                    have : d = 257356 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257355 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257354 ≤ d
                  ·
                    have : d = 257354 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257353 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257349 ≤ d
              ·
                by_cases h : 257351 ≤ d
                ·
                  by_cases h : 257352 ≤ d
                  ·
                    have : d = 257352 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 10723) (by norm_num)
      exact by decide
                  ·
                    have : d = 257351 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257350 ≤ d
                  ·
                    have : d = 257350 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5147) (by norm_num)
      exact by decide
                  ·
                    have : d = 257349 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257347 ≤ d
                ·
                  by_cases h : 257348 ≤ d
                  ·
                    have : d = 257348 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257347 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257346 ≤ d
                  ·
                    have : d = 257346 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257345 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 257313 ≤ d
        ·
          by_cases h : 257329 ≤ d
          ·
            by_cases h : 257337 ≤ d
            ·
              by_cases h : 257341 ≤ d
              ·
                by_cases h : 257343 ≤ d
                ·
                  by_cases h : 257344 ≤ d
                  ·
                    have : d = 257344 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 4021) (by norm_num)
      exact by decide
                  ·
                    have : d = 257343 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257342 ≤ d
                  ·
                    have : d = 257342 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257341 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257339 ≤ d
                ·
                  by_cases h : 257340 ≤ d
                  ·
                    have : d = 257340 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 4289) (by norm_num)
      exact by decide
                  ·
                    have : d = 257339 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257338 ≤ d
                  ·
                    have : d = 257338 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257337 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257333 ≤ d
              ·
                by_cases h : 257335 ≤ d
                ·
                  by_cases h : 257336 ≤ d
                  ·
                    have : d = 257336 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257335 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257334 ≤ d
                  ·
                    have : d = 257334 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 557) (by norm_num)
      exact by decide
                  ·
                    have : d = 257333 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257331 ≤ d
                ·
                  by_cases h : 257332 ≤ d
                  ·
                    have : d = 257332 := by omega
                    subst d
      exact fullRecordGapTerm02393_not_prime
                  ·
                    have : d = 257331 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257330 ≤ d
                  ·
                    have : d = 257330 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257329 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 257321 ≤ d
            ·
              by_cases h : 257325 ≤ d
              ·
                by_cases h : 257327 ≤ d
                ·
                  by_cases h : 257328 ≤ d
                  ·
                    have : d = 257328 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257327 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257326 ≤ d
                  ·
                    have : d = 257326 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257325 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257323 ≤ d
                ·
                  by_cases h : 257324 ≤ d
                  ·
                    have : d = 257324 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257323 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257322 ≤ d
                  ·
                    have : d = 257322 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 257321 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257317 ≤ d
              ·
                by_cases h : 257319 ≤ d
                ·
                  by_cases h : 257320 ≤ d
                  ·
                    have : d = 257320 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 919) (by norm_num)
      exact by decide
                  ·
                    have : d = 257319 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257318 ≤ d
                  ·
                    have : d = 257318 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257317 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257315 ≤ d
                ·
                  by_cases h : 257316 ≤ d
                  ·
                    have : d = 257316 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257315 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257314 ≤ d
                  ·
                    have : d = 257314 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257313 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 257297 ≤ d
          ·
            by_cases h : 257305 ≤ d
            ·
              by_cases h : 257309 ≤ d
              ·
                by_cases h : 257311 ≤ d
                ·
                  by_cases h : 257312 ≤ d
                  ·
                    have : d = 257312 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257311 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257310 ≤ d
                  ·
                    have : d = 257310 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 953) (by norm_num)
      exact by decide
                  ·
                    have : d = 257309 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257307 ≤ d
                ·
                  by_cases h : 257308 ≤ d
                  ·
                    have : d = 257308 := by omega
                    subst d
      exact fullRecordGapTerm02394_not_prime
                  ·
                    have : d = 257307 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257306 ≤ d
                  ·
                    have : d = 257306 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257305 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257301 ≤ d
              ·
                by_cases h : 257303 ≤ d
                ·
                  by_cases h : 257304 ≤ d
                  ·
                    have : d = 257304 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 71) (by norm_num)
      exact by decide
                  ·
                    have : d = 257303 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257302 ≤ d
                  ·
                    have : d = 257302 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 127) (by norm_num)
      exact by decide
                  ·
                    have : d = 257301 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257299 ≤ d
                ·
                  by_cases h : 257300 ≤ d
                  ·
                    have : d = 257300 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257299 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257298 ≤ d
                  ·
                    have : d = 257298 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 257297 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 257289 ≤ d
            ·
              by_cases h : 257293 ≤ d
              ·
                by_cases h : 257295 ≤ d
                ·
                  by_cases h : 257296 ≤ d
                  ·
                    have : d = 257296 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257295 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257294 ≤ d
                  ·
                    have : d = 257294 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257293 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257291 ≤ d
                ·
                  by_cases h : 257292 ≤ d
                  ·
                    have : d = 257292 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1021) (by norm_num)
      exact by decide
                  ·
                    have : d = 257291 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257290 ≤ d
                  ·
                    have : d = 257290 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2339) (by norm_num)
      exact by decide
                  ·
                    have : d = 257289 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257285 ≤ d
              ·
                by_cases h : 257287 ≤ d
                ·
                  by_cases h : 257288 ≤ d
                  ·
                    have : d = 257288 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257287 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257286 ≤ d
                  ·
                    have : d = 257286 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257285 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257283 ≤ d
                ·
                  by_cases h : 257284 ≤ d
                  ·
                    have : d = 257284 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 131) (by norm_num)
      exact by decide
                  ·
                    have : d = 257283 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257282 ≤ d
                  ·
                    have : d = 257282 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257281 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
  ·
    by_cases h : 257153 ≤ d
    ·
      by_cases h : 257217 ≤ d
      ·
        by_cases h : 257249 ≤ d
        ·
          by_cases h : 257265 ≤ d
          ·
            by_cases h : 257273 ≤ d
            ·
              by_cases h : 257277 ≤ d
              ·
                by_cases h : 257279 ≤ d
                ·
                  by_cases h : 257280 ≤ d
                  ·
                    have : d = 257280 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 67) (by norm_num)
      exact by decide
                  ·
                    have : d = 257279 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257278 ≤ d
                  ·
                    have : d = 257278 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 257277 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257275 ≤ d
                ·
                  by_cases h : 257276 ≤ d
                  ·
                    have : d = 257276 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257275 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257274 ≤ d
                  ·
                    have : d = 257274 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 14293) (by norm_num)
      exact by decide
                  ·
                    have : d = 257273 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257269 ≤ d
              ·
                by_cases h : 257271 ≤ d
                ·
                  by_cases h : 257272 ≤ d
                  ·
                    have : d = 257272 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257271 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257270 ≤ d
                  ·
                    have : d = 257270 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257269 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257267 ≤ d
                ·
                  by_cases h : 257268 ≤ d
                  ·
                    have : d = 257268 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1949) (by norm_num)
      exact by decide
                  ·
                    have : d = 257267 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257266 ≤ d
                  ·
                    have : d = 257266 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257265 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 257257 ≤ d
            ·
              by_cases h : 257261 ≤ d
              ·
                by_cases h : 257263 ≤ d
                ·
                  by_cases h : 257264 ≤ d
                  ·
                    have : d = 257264 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257263 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257262 ≤ d
                  ·
                    have : d = 257262 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 53) (by norm_num)
      exact by decide
                  ·
                    have : d = 257261 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257259 ≤ d
                ·
                  by_cases h : 257260 ≤ d
                  ·
                    have : d = 257260 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 257259 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257258 ≤ d
                  ·
                    have : d = 257258 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257257 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257253 ≤ d
              ·
                by_cases h : 257255 ≤ d
                ·
                  by_cases h : 257256 ≤ d
                  ·
                    have : d = 257256 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257255 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257254 ≤ d
                  ·
                    have : d = 257254 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 293) (by norm_num)
      exact by decide
                  ·
                    have : d = 257253 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257251 ≤ d
                ·
                  by_cases h : 257252 ≤ d
                  ·
                    have : d = 257252 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257251 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257250 ≤ d
                  ·
                    have : d = 257250 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257249 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 257233 ≤ d
          ·
            by_cases h : 257241 ≤ d
            ·
              by_cases h : 257245 ≤ d
              ·
                by_cases h : 257247 ≤ d
                ·
                  by_cases h : 257248 ≤ d
                  ·
                    have : d = 257248 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 8039) (by norm_num)
      exact by decide
                  ·
                    have : d = 257247 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257246 ≤ d
                  ·
                    have : d = 257246 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257245 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257243 ≤ d
                ·
                  by_cases h : 257244 ≤ d
                  ·
                    have : d = 257244 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257243 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257242 ≤ d
                  ·
                    have : d = 257242 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2843704373) (by norm_num)
      right
      exact ⟨257242, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257241 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257237 ≤ d
              ·
                by_cases h : 257239 ≤ d
                ·
                  by_cases h : 257240 ≤ d
                  ·
                    have : d = 257240 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257239 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257238 ≤ d
                  ·
                    have : d = 257238 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 31) (by norm_num)
      exact by decide
                  ·
                    have : d = 257237 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257235 ≤ d
                ·
                  by_cases h : 257236 ≤ d
                  ·
                    have : d = 257236 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257235 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257234 ≤ d
                  ·
                    have : d = 257234 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257233 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 257225 ≤ d
            ·
              by_cases h : 257229 ≤ d
              ·
                by_cases h : 257231 ≤ d
                ·
                  by_cases h : 257232 ≤ d
                  ·
                    have : d = 257232 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23) (by norm_num)
      exact by decide
                  ·
                    have : d = 257231 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257230 ≤ d
                  ·
                    have : d = 257230 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257229 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257227 ≤ d
                ·
                  by_cases h : 257228 ≤ d
                  ·
                    have : d = 257228 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257227 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257226 ≤ d
                  ·
                    have : d = 257226 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257225 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257221 ≤ d
              ·
                by_cases h : 257223 ≤ d
                ·
                  by_cases h : 257224 ≤ d
                  ·
                    have : d = 257224 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 37) (by norm_num)
      exact by decide
                  ·
                    have : d = 257223 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257222 ≤ d
                  ·
                    have : d = 257222 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257221 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257219 ≤ d
                ·
                  by_cases h : 257220 ≤ d
                  ·
                    have : d = 257220 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1429) (by norm_num)
      exact by decide
                  ·
                    have : d = 257219 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257218 ≤ d
                  ·
                    have : d = 257218 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 257217 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 257185 ≤ d
        ·
          by_cases h : 257201 ≤ d
          ·
            by_cases h : 257209 ≤ d
            ·
              by_cases h : 257213 ≤ d
              ·
                by_cases h : 257215 ≤ d
                ·
                  by_cases h : 257216 ≤ d
                  ·
                    have : d = 257216 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257215 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257214 ≤ d
                  ·
                    have : d = 257214 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 163) (by norm_num)
      exact by decide
                  ·
                    have : d = 257213 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257211 ≤ d
                ·
                  by_cases h : 257212 ≤ d
                  ·
                    have : d = 257212 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 643039) (by norm_num)
      right
      exact ⟨257212, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257211 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257210 ≤ d
                  ·
                    have : d = 257210 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257209 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257205 ≤ d
              ·
                by_cases h : 257207 ≤ d
                ·
                  by_cases h : 257208 ≤ d
                  ·
                    have : d = 257208 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1531) (by norm_num)
      exact by decide
                  ·
                    have : d = 257207 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257206 ≤ d
                  ·
                    have : d = 257206 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257205 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257203 ≤ d
                ·
                  by_cases h : 257204 ≤ d
                  ·
                    have : d = 257204 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257203 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257202 ≤ d
                  ·
                    have : d = 257202 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257201 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 257193 ≤ d
            ·
              by_cases h : 257197 ≤ d
              ·
                by_cases h : 257199 ≤ d
                ·
                  by_cases h : 257200 ≤ d
                  ·
                    have : d = 257200 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 643) (by norm_num)
      exact by decide
                  ·
                    have : d = 257199 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257198 ≤ d
                  ·
                    have : d = 257198 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257197 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257195 ≤ d
                ·
                  by_cases h : 257196 ≤ d
                  ·
                    have : d = 257196 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257195 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257194 ≤ d
                  ·
                    have : d = 257194 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 18371) (by norm_num)
      exact by decide
                  ·
                    have : d = 257193 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257189 ≤ d
              ·
                by_cases h : 257191 ≤ d
                ·
                  by_cases h : 257192 ≤ d
                  ·
                    have : d = 257192 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257191 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257190 ≤ d
                  ·
                    have : d = 257190 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 8573) (by norm_num)
      exact by decide
                  ·
                    have : d = 257189 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257187 ≤ d
                ·
                  by_cases h : 257188 ≤ d
                  ·
                    have : d = 257188 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257187 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257186 ≤ d
                  ·
                    have : d = 257186 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257185 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 257169 ≤ d
          ·
            by_cases h : 257177 ≤ d
            ·
              by_cases h : 257181 ≤ d
              ·
                by_cases h : 257183 ≤ d
                ·
                  by_cases h : 257184 ≤ d
                  ·
                    have : d = 257184 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257183 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257182 ≤ d
                  ·
                    have : d = 257182 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 409517) (by norm_num)
      right
      exact ⟨257182, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257181 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257179 ≤ d
                ·
                  by_cases h : 257180 ≤ d
                  ·
                    have : d = 257180 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257179 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257178 ≤ d
                  ·
                    have : d = 257178 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 42863) (by norm_num)
      exact by decide
                  ·
                    have : d = 257177 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257173 ≤ d
              ·
                by_cases h : 257175 ≤ d
                ·
                  by_cases h : 257176 ≤ d
                  ·
                    have : d = 257176 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257175 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257174 ≤ d
                  ·
                    have : d = 257174 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257173 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257171 ≤ d
                ·
                  by_cases h : 257172 ≤ d
                  ·
                    have : d = 257172 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 29) (by norm_num)
      exact by decide
                  ·
                    have : d = 257171 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257170 ≤ d
                  ·
                    have : d = 257170 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 25717) (by norm_num)
      exact by decide
                  ·
                    have : d = 257169 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 257161 ≤ d
            ·
              by_cases h : 257165 ≤ d
              ·
                by_cases h : 257167 ≤ d
                ·
                  by_cases h : 257168 ≤ d
                  ·
                    have : d = 257168 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257167 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257166 ≤ d
                  ·
                    have : d = 257166 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257165 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257163 ≤ d
                ·
                  by_cases h : 257164 ≤ d
                  ·
                    have : d = 257164 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 239) (by norm_num)
      exact by decide
                  ·
                    have : d = 257163 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257162 ≤ d
                  ·
                    have : d = 257162 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257161 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257157 ≤ d
              ·
                by_cases h : 257159 ≤ d
                ·
                  by_cases h : 257160 ≤ d
                  ·
                    have : d = 257160 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257159 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257158 ≤ d
                  ·
                    have : d = 257158 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11689) (by norm_num)
      exact by decide
                  ·
                    have : d = 257157 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257155 ≤ d
                ·
                  by_cases h : 257156 ≤ d
                  ·
                    have : d = 257156 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257155 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257154 ≤ d
                  ·
                    have : d = 257154 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 42859) (by norm_num)
      exact by decide
                  ·
                    have : d = 257153 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 257089 ≤ d
      ·
        by_cases h : 257121 ≤ d
        ·
          by_cases h : 257137 ≤ d
          ·
            by_cases h : 257145 ≤ d
            ·
              by_cases h : 257149 ≤ d
              ·
                by_cases h : 257151 ≤ d
                ·
                  by_cases h : 257152 ≤ d
                  ·
                    have : d = 257152 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 41) (by norm_num)
      exact by decide
                  ·
                    have : d = 257151 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257150 ≤ d
                  ·
                    have : d = 257150 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257149 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257147 ≤ d
                ·
                  by_cases h : 257148 ≤ d
                  ·
                    have : d = 257148 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2381) (by norm_num)
      exact by decide
                  ·
                    have : d = 257147 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257146 ≤ d
                  ·
                    have : d = 257146 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257145 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257141 ≤ d
              ·
                by_cases h : 257143 ≤ d
                ·
                  by_cases h : 257144 ≤ d
                  ·
                    have : d = 257144 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257143 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257142 ≤ d
                  ·
                    have : d = 257142 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 257141 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257139 ≤ d
                ·
                  by_cases h : 257140 ≤ d
                  ·
                    have : d = 257140 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257139 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257138 ≤ d
                  ·
                    have : d = 257138 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257137 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 257129 ≤ d
            ·
              by_cases h : 257133 ≤ d
              ·
                by_cases h : 257135 ≤ d
                ·
                  by_cases h : 257136 ≤ d
                  ·
                    have : d = 257136 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257135 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257134 ≤ d
                  ·
                    have : d = 257134 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 83) (by norm_num)
      exact by decide
                  ·
                    have : d = 257133 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257131 ≤ d
                ·
                  by_cases h : 257132 ≤ d
                  ·
                    have : d = 257132 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257131 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257130 ≤ d
                  ·
                    have : d = 257130 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2857) (by norm_num)
      exact by decide
                  ·
                    have : d = 257129 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257125 ≤ d
              ·
                by_cases h : 257127 ≤ d
                ·
                  by_cases h : 257128 ≤ d
                  ·
                    have : d = 257128 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 32141) (by norm_num)
      exact by decide
                  ·
                    have : d = 257127 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257126 ≤ d
                  ·
                    have : d = 257126 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257125 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257123 ≤ d
                ·
                  by_cases h : 257124 ≤ d
                  ·
                    have : d = 257124 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3061) (by norm_num)
      exact by decide
                  ·
                    have : d = 257123 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257122 ≤ d
                  ·
                    have : d = 257122 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 59) (by norm_num)
      exact by decide
                  ·
                    have : d = 257121 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 257105 ≤ d
          ·
            by_cases h : 257113 ≤ d
            ·
              by_cases h : 257117 ≤ d
              ·
                by_cases h : 257119 ≤ d
                ·
                  by_cases h : 257120 ≤ d
                  ·
                    have : d = 257120 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257119 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257118 ≤ d
                  ·
                    have : d = 257118 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257117 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257115 ≤ d
                ·
                  by_cases h : 257116 ≤ d
                  ·
                    have : d = 257116 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257115 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257114 ≤ d
                  ·
                    have : d = 257114 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257113 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257109 ≤ d
              ·
                by_cases h : 257111 ≤ d
                ·
                  by_cases h : 257112 ≤ d
                  ·
                    have : d = 257112 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3571) (by norm_num)
      exact by decide
                  ·
                    have : d = 257111 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257110 ≤ d
                  ·
                    have : d = 257110 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3673) (by norm_num)
      exact by decide
                  ·
                    have : d = 257109 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257107 ≤ d
                ·
                  by_cases h : 257108 ≤ d
                  ·
                    have : d = 257108 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257107 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257106 ≤ d
                  ·
                    have : d = 257106 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257105 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 257097 ≤ d
            ·
              by_cases h : 257101 ≤ d
              ·
                by_cases h : 257103 ≤ d
                ·
                  by_cases h : 257104 ≤ d
                  ·
                    have : d = 257104 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257103 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257102 ≤ d
                  ·
                    have : d = 257102 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257101 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257099 ≤ d
                ·
                  by_cases h : 257100 ≤ d
                  ·
                    have : d = 257100 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 857) (by norm_num)
      exact by decide
                  ·
                    have : d = 257099 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257098 ≤ d
                  ·
                    have : d = 257098 := by omega
                    subst d
      exact fullRecordGapTerm02395_not_prime
                  ·
                    have : d = 257097 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257093 ≤ d
              ·
                by_cases h : 257095 ≤ d
                ·
                  by_cases h : 257096 ≤ d
                  ·
                    have : d = 257096 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257095 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257094 ≤ d
                  ·
                    have : d = 257094 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23) (by norm_num)
      exact by decide
                  ·
                    have : d = 257093 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257091 ≤ d
                ·
                  by_cases h : 257092 ≤ d
                  ·
                    have : d = 257092 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5843) (by norm_num)
      exact by decide
                  ·
                    have : d = 257091 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257090 ≤ d
                  ·
                    have : d = 257090 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257089 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 257057 ≤ d
        ·
          by_cases h : 257073 ≤ d
          ·
            by_cases h : 257081 ≤ d
            ·
              by_cases h : 257085 ≤ d
              ·
                by_cases h : 257087 ≤ d
                ·
                  by_cases h : 257088 ≤ d
                  ·
                    have : d = 257088 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 257087 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257086 ≤ d
                  ·
                    have : d = 257086 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257085 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257083 ≤ d
                ·
                  by_cases h : 257084 ≤ d
                  ·
                    have : d = 257084 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257083 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257082 ≤ d
                  ·
                    have : d = 257082 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 6121) (by norm_num)
      exact by decide
                  ·
                    have : d = 257081 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257077 ≤ d
              ·
                by_cases h : 257079 ≤ d
                ·
                  by_cases h : 257080 ≤ d
                  ·
                    have : d = 257080 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 6427) (by norm_num)
      exact by decide
                  ·
                    have : d = 257079 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257078 ≤ d
                  ·
                    have : d = 257078 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257077 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257075 ≤ d
                ·
                  by_cases h : 257076 ≤ d
                  ·
                    have : d = 257076 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257075 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257074 ≤ d
                  ·
                    have : d = 257074 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257073 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 257065 ≤ d
            ·
              by_cases h : 257069 ≤ d
              ·
                by_cases h : 257071 ≤ d
                ·
                  by_cases h : 257072 ≤ d
                  ·
                    have : d = 257072 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257071 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257070 ≤ d
                  ·
                    have : d = 257070 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 257069 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257067 ≤ d
                ·
                  by_cases h : 257068 ≤ d
                  ·
                    have : d = 257068 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 9181) (by norm_num)
      exact by decide
                  ·
                    have : d = 257067 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257066 ≤ d
                  ·
                    have : d = 257066 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257065 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257061 ≤ d
              ·
                by_cases h : 257063 ≤ d
                ·
                  by_cases h : 257064 ≤ d
                  ·
                    have : d = 257064 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 10711) (by norm_num)
      exact by decide
                  ·
                    have : d = 257063 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257062 ≤ d
                  ·
                    have : d = 257062 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257061 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257059 ≤ d
                ·
                  by_cases h : 257060 ≤ d
                  ·
                    have : d = 257060 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257059 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257058 ≤ d
                  ·
                    have : d = 257058 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 14281) (by norm_num)
      exact by decide
                  ·
                    have : d = 257057 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 257041 ≤ d
          ·
            by_cases h : 257049 ≤ d
            ·
              by_cases h : 257053 ≤ d
              ·
                by_cases h : 257055 ≤ d
                ·
                  by_cases h : 257056 ≤ d
                  ·
                    have : d = 257056 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257055 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257054 ≤ d
                  ·
                    have : d = 257054 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257053 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257051 ≤ d
                ·
                  by_cases h : 257052 ≤ d
                  ·
                    have : d = 257052 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257051 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257050 ≤ d
                  ·
                    have : d = 257050 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 53) (by norm_num)
      exact by decide
                  ·
                    have : d = 257049 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257045 ≤ d
              ·
                by_cases h : 257047 ≤ d
                ·
                  by_cases h : 257048 ≤ d
                  ·
                    have : d = 257048 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257047 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257046 ≤ d
                  ·
                    have : d = 257046 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257045 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257043 ≤ d
                ·
                  by_cases h : 257044 ≤ d
                  ·
                    have : d = 257044 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 179) (by norm_num)
      exact by decide
                  ·
                    have : d = 257043 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257042 ≤ d
                  ·
                    have : d = 257042 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257041 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 257033 ≤ d
            ·
              by_cases h : 257037 ≤ d
              ·
                by_cases h : 257039 ≤ d
                ·
                  by_cases h : 257040 ≤ d
                  ·
                    have : d = 257040 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 257039 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257038 ≤ d
                  ·
                    have : d = 257038 := by omega
                    subst d
      exact fullRecordGapTerm02396_not_prime
                  ·
                    have : d = 257037 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257035 ≤ d
                ·
                  by_cases h : 257036 ≤ d
                  ·
                    have : d = 257036 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257035 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257034 ≤ d
                  ·
                    have : d = 257034 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257033 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 257029 ≤ d
              ·
                by_cases h : 257031 ≤ d
                ·
                  by_cases h : 257032 ≤ d
                  ·
                    have : d = 257032 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 257031 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257030 ≤ d
                  ·
                    have : d = 257030 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257029 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 257027 ≤ d
                ·
                  by_cases h : 257028 ≤ d
                  ·
                    have : d = 257028 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 21419) (by norm_num)
      exact by decide
                  ·
                    have : d = 257027 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 257026 ≤ d
                  ·
                    have : d = 257026 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 257025 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩

end PrimeFactorUnimodality
