import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapFermat

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

theorem fullRecordGapAddBlock_part1892 (d : Nat) (512001 ≤ d) (d ≤ 512512) : ¬(recordGapCenter + d).Prime := by
  by_cases h : 512257 ≤ d
  ·
    by_cases h : 512385 ≤ d
    ·
      by_cases h : 512449 ≤ d
      ·
        by_cases h : 512481 ≤ d
        ·
          by_cases h : 512497 ≤ d
          ·
            by_cases h : 512505 ≤ d
            ·
              by_cases h : 512509 ≤ d
              ·
                by_cases h : 512511 ≤ d
                ·
                  by_cases h : 512512 ≤ d
                  ·
                    have : d = 512512 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512511 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512510 ≤ d
                  ·
                    have : d = 512510 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 53)
      exact by decide
                  ·
                    have : d = 512509 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512507 ≤ d
                ·
                  by_cases h : 512508 ≤ d
                  ·
                    have : d = 512508 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512507 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512506 ≤ d
                  ·
                    have : d = 512506 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512505 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512501 ≤ d
              ·
                by_cases h : 512503 ≤ d
                ·
                  by_cases h : 512504 ≤ d
                  ·
                    have : d = 512504 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512503 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512502 ≤ d
                  ·
                    have : d = 512502 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 229)
      exact by decide
                  ·
                    have : d = 512501 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512499 ≤ d
                ·
                  by_cases h : 512500 ≤ d
                  ·
                    have : d = 512500 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512499 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512498 ≤ d
                  ·
                    have : d = 512498 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 36607)
      exact by decide
                  ·
                    have : d = 512497 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 512489 ≤ d
            ·
              by_cases h : 512493 ≤ d
              ·
                by_cases h : 512495 ≤ d
                ·
                  by_cases h : 512496 ≤ d
                  ·
                    have : d = 512496 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3559)
      exact by decide
                  ·
                    have : d = 512495 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512494 ≤ d
                  ·
                    have : d = 512494 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512493 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512491 ≤ d
                ·
                  by_cases h : 512492 ≤ d
                  ·
                    have : d = 512492 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 512491 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512490 ≤ d
                  ·
                    have : d = 512490 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512489 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512485 ≤ d
              ·
                by_cases h : 512487 ≤ d
                ·
                  by_cases h : 512488 ≤ d
                  ·
                    have : d = 512488 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512487 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512486 ≤ d
                  ·
                    have : d = 512486 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512485 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512483 ≤ d
                ·
                  by_cases h : 512484 ≤ d
                  ·
                    have : d = 512484 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512483 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512482 ≤ d
                  ·
                    have : d = 512482 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512481 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 512465 ≤ d
          ·
            by_cases h : 512473 ≤ d
            ·
              by_cases h : 512477 ≤ d
              ·
                by_cases h : 512479 ≤ d
                ·
                  by_cases h : 512480 ≤ d
                  ·
                    have : d = 512480 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3203)
      exact by decide
                  ·
                    have : d = 512479 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512478 ≤ d
                  ·
                    have : d = 512478 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 71)
      exact by decide
                  ·
                    have : d = 512477 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512475 ≤ d
                ·
                  by_cases h : 512476 ≤ d
                  ·
                    have : d = 512476 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512475 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512474 ≤ d
                  ·
                    have : d = 512474 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512473 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512469 ≤ d
              ·
                by_cases h : 512471 ≤ d
                ·
                  by_cases h : 512472 ≤ d
                  ·
                    have : d = 512472 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 131)
      exact by decide
                  ·
                    have : d = 512471 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512470 ≤ d
                  ·
                    have : d = 512470 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512469 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512467 ≤ d
                ·
                  by_cases h : 512468 ≤ d
                  ·
                    have : d = 512468 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 512467 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512466 ≤ d
                  ·
                    have : d = 512466 := by omega
                    subst d
      exact fullRecordGapTerm08595_not_prime
                  ·
                    have : d = 512465 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 512457 ≤ d
            ·
              by_cases h : 512461 ≤ d
              ·
                by_cases h : 512463 ≤ d
                ·
                  by_cases h : 512464 ≤ d
                  ·
                    have : d = 512464 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512463 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512462 ≤ d
                  ·
                    have : d = 512462 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512461 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512459 ≤ d
                ·
                  by_cases h : 512460 ≤ d
                  ·
                    have : d = 512460 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 512459 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512458 ≤ d
                  ·
                    have : d = 512458 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512457 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512453 ≤ d
              ·
                by_cases h : 512455 ≤ d
                ·
                  by_cases h : 512456 ≤ d
                  ·
                    have : d = 512456 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 9151)
      exact by decide
                  ·
                    have : d = 512455 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512454 ≤ d
                  ·
                    have : d = 512454 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512453 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512451 ≤ d
                ·
                  by_cases h : 512452 ≤ d
                  ·
                    have : d = 512452 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512451 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512450 ≤ d
                  ·
                    have : d = 512450 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 512449 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 512417 ≤ d
        ·
          by_cases h : 512433 ≤ d
          ·
            by_cases h : 512441 ≤ d
            ·
              by_cases h : 512445 ≤ d
              ·
                by_cases h : 512447 ≤ d
                ·
                  by_cases h : 512448 ≤ d
                  ·
                    have : d = 512448 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512447 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512446 ≤ d
                  ·
                    have : d = 512446 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512445 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512443 ≤ d
                ·
                  by_cases h : 512444 ≤ d
                  ·
                    have : d = 512444 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512443 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512442 ≤ d
                  ·
                    have : d = 512442 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512441 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512437 ≤ d
              ·
                by_cases h : 512439 ≤ d
                ·
                  by_cases h : 512440 ≤ d
                  ·
                    have : d = 512440 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512439 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512438 ≤ d
                  ·
                    have : d = 512438 := by omega
                    subst d
      exact fullRecordGapTerm08594_not_prime
                  ·
                    have : d = 512437 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512435 ≤ d
                ·
                  by_cases h : 512436 ≤ d
                  ·
                    have : d = 512436 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 42703)
      exact by decide
                  ·
                    have : d = 512435 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512434 ≤ d
                  ·
                    have : d = 512434 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512433 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 512425 ≤ d
            ·
              by_cases h : 512429 ≤ d
              ·
                by_cases h : 512431 ≤ d
                ·
                  by_cases h : 512432 ≤ d
                  ·
                    have : d = 512432 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 32027)
      exact by decide
                  ·
                    have : d = 512431 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512430 ≤ d
                  ·
                    have : d = 512430 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 512429 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512427 ≤ d
                ·
                  by_cases h : 512428 ≤ d
                  ·
                    have : d = 512428 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512427 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512426 ≤ d
                  ·
                    have : d = 512426 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 173)
      exact by decide
                  ·
                    have : d = 512425 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512421 ≤ d
              ·
                by_cases h : 512423 ≤ d
                ·
                  by_cases h : 512424 ≤ d
                  ·
                    have : d = 512424 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512423 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512422 ≤ d
                  ·
                    have : d = 512422 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512421 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512419 ≤ d
                ·
                  by_cases h : 512420 ≤ d
                  ·
                    have : d = 512420 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512419 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512418 ≤ d
                  ·
                    have : d = 512418 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 41)
      exact by decide
                  ·
                    have : d = 512417 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 512401 ≤ d
          ·
            by_cases h : 512409 ≤ d
            ·
              by_cases h : 512413 ≤ d
              ·
                by_cases h : 512415 ≤ d
                ·
                  by_cases h : 512416 ≤ d
                  ·
                    have : d = 512416 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512415 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512414 ≤ d
                  ·
                    have : d = 512414 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512413 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512411 ≤ d
                ·
                  by_cases h : 512412 ≤ d
                  ·
                    have : d = 512412 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 42701)
      exact by decide
                  ·
                    have : d = 512411 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512410 ≤ d
                  ·
                    have : d = 512410 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512409 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512405 ≤ d
              ·
                by_cases h : 512407 ≤ d
                ·
                  by_cases h : 512408 ≤ d
                  ·
                    have : d = 512408 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 512407 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512406 ≤ d
                  ·
                    have : d = 512406 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512405 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512403 ≤ d
                ·
                  by_cases h : 512404 ≤ d
                  ·
                    have : d = 512404 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512403 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512402 ≤ d
                  ·
                    have : d = 512402 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23291)
      exact by decide
                  ·
                    have : d = 512401 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 512393 ≤ d
            ·
              by_cases h : 512397 ≤ d
              ·
                by_cases h : 512399 ≤ d
                ·
                  by_cases h : 512400 ≤ d
                  ·
                    have : d = 512400 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 61)
      exact by decide
                  ·
                    have : d = 512399 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512398 ≤ d
                  ·
                    have : d = 512398 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512397 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512395 ≤ d
                ·
                  by_cases h : 512396 ≤ d
                  ·
                    have : d = 512396 := by omega
                    subst d
      exact fullRecordGapTerm08593_not_prime
                  ·
                    have : d = 512395 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512394 ≤ d
                  ·
                    have : d = 512394 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512393 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512389 ≤ d
              ·
                by_cases h : 512391 ≤ d
                ·
                  by_cases h : 512392 ≤ d
                  ·
                    have : d = 512392 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512391 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512390 ≤ d
                  ·
                    have : d = 512390 := by omega
                    subst d
      exact fullRecordGapTerm08592_not_prime
                  ·
                    have : d = 512389 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512387 ≤ d
                ·
                  by_cases h : 512388 ≤ d
                  ·
                    have : d = 512388 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 43)
      exact by decide
                  ·
                    have : d = 512387 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512386 ≤ d
                  ·
                    have : d = 512386 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512385 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 512321 ≤ d
      ·
        by_cases h : 512353 ≤ d
        ·
          by_cases h : 512369 ≤ d
          ·
            by_cases h : 512377 ≤ d
            ·
              by_cases h : 512381 ≤ d
              ·
                by_cases h : 512383 ≤ d
                ·
                  by_cases h : 512384 ≤ d
                  ·
                    have : d = 512384 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512383 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512382 ≤ d
                  ·
                    have : d = 512382 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 512381 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512379 ≤ d
                ·
                  by_cases h : 512380 ≤ d
                  ·
                    have : d = 512380 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512379 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512378 ≤ d
                  ·
                    have : d = 512378 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512377 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512373 ≤ d
              ·
                by_cases h : 512375 ≤ d
                ·
                  by_cases h : 512376 ≤ d
                  ·
                    have : d = 512376 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512375 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512374 ≤ d
                  ·
                    have : d = 512374 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512373 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512371 ≤ d
                ·
                  by_cases h : 512372 ≤ d
                  ·
                    have : d = 512372 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 512371 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512370 ≤ d
                  ·
                    have : d = 512370 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5693)
      exact by decide
                  ·
                    have : d = 512369 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 512361 ≤ d
            ·
              by_cases h : 512365 ≤ d
              ·
                by_cases h : 512367 ≤ d
                ·
                  by_cases h : 512368 ≤ d
                  ·
                    have : d = 512368 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512367 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512366 ≤ d
                  ·
                    have : d = 512366 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 241)
      exact by decide
                  ·
                    have : d = 512365 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512363 ≤ d
                ·
                  by_cases h : 512364 ≤ d
                  ·
                    have : d = 512364 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512363 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512362 ≤ d
                  ·
                    have : d = 512362 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512361 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512357 ≤ d
              ·
                by_cases h : 512359 ≤ d
                ·
                  by_cases h : 512360 ≤ d
                  ·
                    have : d = 512360 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 12809)
      exact by decide
                  ·
                    have : d = 512359 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512358 ≤ d
                  ·
                    have : d = 512358 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1109)
      exact by decide
                  ·
                    have : d = 512357 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512355 ≤ d
                ·
                  by_cases h : 512356 ≤ d
                  ·
                    have : d = 512356 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512355 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512354 ≤ d
                  ·
                    have : d = 512354 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512353 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 512337 ≤ d
          ·
            by_cases h : 512345 ≤ d
            ·
              by_cases h : 512349 ≤ d
              ·
                by_cases h : 512351 ≤ d
                ·
                  by_cases h : 512352 ≤ d
                  ·
                    have : d = 512352 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 593)
      exact by decide
                  ·
                    have : d = 512351 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512350 ≤ d
                  ·
                    have : d = 512350 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512349 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512347 ≤ d
                ·
                  by_cases h : 512348 ≤ d
                  ·
                    have : d = 512348 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 512347 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512346 ≤ d
                  ·
                    have : d = 512346 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 512345 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512341 ≤ d
              ·
                by_cases h : 512343 ≤ d
                ·
                  by_cases h : 512344 ≤ d
                  ·
                    have : d = 512344 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512343 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512342 ≤ d
                  ·
                    have : d = 512342 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 113)
      exact by decide
                  ·
                    have : d = 512341 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512339 ≤ d
                ·
                  by_cases h : 512340 ≤ d
                  ·
                    have : d = 512340 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 8539)
      exact by decide
                  ·
                    have : d = 512339 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512338 ≤ d
                  ·
                    have : d = 512338 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512337 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 512329 ≤ d
            ·
              by_cases h : 512333 ≤ d
              ·
                by_cases h : 512335 ≤ d
                ·
                  by_cases h : 512336 ≤ d
                  ·
                    have : d = 512336 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512335 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512334 ≤ d
                  ·
                    have : d = 512334 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512333 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512331 ≤ d
                ·
                  by_cases h : 512332 ≤ d
                  ·
                    have : d = 512332 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512331 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512330 ≤ d
                  ·
                    have : d = 512330 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 512329 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512325 ≤ d
              ·
                by_cases h : 512327 ≤ d
                ·
                  by_cases h : 512328 ≤ d
                  ·
                    have : d = 512328 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 21347)
      exact by decide
                  ·
                    have : d = 512327 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512326 ≤ d
                  ·
                    have : d = 512326 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512325 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512323 ≤ d
                ·
                  by_cases h : 512324 ≤ d
                  ·
                    have : d = 512324 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512323 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512322 ≤ d
                  ·
                    have : d = 512322 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512321 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 512289 ≤ d
        ·
          by_cases h : 512305 ≤ d
          ·
            by_cases h : 512313 ≤ d
            ·
              by_cases h : 512317 ≤ d
              ·
                by_cases h : 512319 ≤ d
                ·
                  by_cases h : 512320 ≤ d
                  ·
                    have : d = 512320 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512319 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512318 ≤ d
                  ·
                    have : d = 512318 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 127)
      exact by decide
                  ·
                    have : d = 512317 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512315 ≤ d
                ·
                  by_cases h : 512316 ≤ d
                  ·
                    have : d = 512316 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 512315 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512314 ≤ d
                  ·
                    have : d = 512314 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512313 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512309 ≤ d
              ·
                by_cases h : 512311 ≤ d
                ·
                  by_cases h : 512312 ≤ d
                  ·
                    have : d = 512312 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 512311 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512310 ≤ d
                  ·
                    have : d = 512310 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512309 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512307 ≤ d
                ·
                  by_cases h : 512308 ≤ d
                  ·
                    have : d = 512308 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512307 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512306 ≤ d
                  ·
                    have : d = 512306 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 512305 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 512297 ≤ d
            ·
              by_cases h : 512301 ≤ d
              ·
                by_cases h : 512303 ≤ d
                ·
                  by_cases h : 512304 ≤ d
                  ·
                    have : d = 512304 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512303 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512302 ≤ d
                  ·
                    have : d = 512302 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512301 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512299 ≤ d
                ·
                  by_cases h : 512300 ≤ d
                  ·
                    have : d = 512300 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 47)
      exact by decide
                  ·
                    have : d = 512299 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512298 ≤ d
                  ·
                    have : d = 512298 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 53)
      exact by decide
                  ·
                    have : d = 512297 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512293 ≤ d
              ·
                by_cases h : 512295 ≤ d
                ·
                  by_cases h : 512296 ≤ d
                  ·
                    have : d = 512296 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512295 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512294 ≤ d
                  ·
                    have : d = 512294 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512293 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512291 ≤ d
                ·
                  by_cases h : 512292 ≤ d
                  ·
                    have : d = 512292 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3881)
      exact by decide
                  ·
                    have : d = 512291 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512290 ≤ d
                  ·
                    have : d = 512290 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512289 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 512273 ≤ d
          ·
            by_cases h : 512281 ≤ d
            ·
              by_cases h : 512285 ≤ d
              ·
                by_cases h : 512287 ≤ d
                ·
                  by_cases h : 512288 ≤ d
                  ·
                    have : d = 512288 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512287 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512286 ≤ d
                  ·
                    have : d = 512286 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 848341271)
      right
      exact ⟨847828985, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512285 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512283 ≤ d
                ·
                  by_cases h : 512284 ≤ d
                  ·
                    have : d = 512284 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512283 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512282 ≤ d
                  ·
                    have : d = 512282 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 67)
      exact by decide
                  ·
                    have : d = 512281 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512277 ≤ d
              ·
                by_cases h : 512279 ≤ d
                ·
                  by_cases h : 512280 ≤ d
                  ·
                    have : d = 512280 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512279 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512278 ≤ d
                  ·
                    have : d = 512278 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512277 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512275 ≤ d
                ·
                  by_cases h : 512276 ≤ d
                  ·
                    have : d = 512276 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 83)
      exact by decide
                  ·
                    have : d = 512275 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512274 ≤ d
                  ·
                    have : d = 512274 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512273 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 512265 ≤ d
            ·
              by_cases h : 512269 ≤ d
              ·
                by_cases h : 512271 ≤ d
                ·
                  by_cases h : 512272 ≤ d
                  ·
                    have : d = 512272 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512271 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512270 ≤ d
                  ·
                    have : d = 512270 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 4657)
      exact by decide
                  ·
                    have : d = 512269 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512267 ≤ d
                ·
                  by_cases h : 512268 ≤ d
                  ·
                    have : d = 512268 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 42689)
      exact by decide
                  ·
                    have : d = 512267 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512266 ≤ d
                  ·
                    have : d = 512266 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512265 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512261 ≤ d
              ·
                by_cases h : 512263 ≤ d
                ·
                  by_cases h : 512264 ≤ d
                  ·
                    have : d = 512264 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512263 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512262 ≤ d
                  ·
                    have : d = 512262 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 149)
      exact by decide
                  ·
                    have : d = 512261 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512259 ≤ d
                ·
                  by_cases h : 512260 ≤ d
                  ·
                    have : d = 512260 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512259 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512258 ≤ d
                  ·
                    have : d = 512258 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 133241)
      right
      exact ⟨20706, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512257 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
  ·
    by_cases h : 512129 ≤ d
    ·
      by_cases h : 512193 ≤ d
      ·
        by_cases h : 512225 ≤ d
        ·
          by_cases h : 512241 ≤ d
          ·
            by_cases h : 512249 ≤ d
            ·
              by_cases h : 512253 ≤ d
              ·
                by_cases h : 512255 ≤ d
                ·
                  by_cases h : 512256 ≤ d
                  ·
                    have : d = 512256 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 512255 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512254 ≤ d
                  ·
                    have : d = 512254 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512253 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512251 ≤ d
                ·
                  by_cases h : 512252 ≤ d
                  ·
                    have : d = 512252 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512251 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512250 ≤ d
                  ·
                    have : d = 512250 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 683)
      exact by decide
                  ·
                    have : d = 512249 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512245 ≤ d
              ·
                by_cases h : 512247 ≤ d
                ·
                  by_cases h : 512248 ≤ d
                  ·
                    have : d = 512248 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512247 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512246 ≤ d
                  ·
                    have : d = 512246 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5227)
      exact by decide
                  ·
                    have : d = 512245 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512243 ≤ d
                ·
                  by_cases h : 512244 ≤ d
                  ·
                    have : d = 512244 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512243 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512242 ≤ d
                  ·
                    have : d = 512242 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512241 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 512233 ≤ d
            ·
              by_cases h : 512237 ≤ d
              ·
                by_cases h : 512239 ≤ d
                ·
                  by_cases h : 512240 ≤ d
                  ·
                    have : d = 512240 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 512239 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512238 ≤ d
                  ·
                    have : d = 512238 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512237 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512235 ≤ d
                ·
                  by_cases h : 512236 ≤ d
                  ·
                    have : d = 512236 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512235 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512234 ≤ d
                  ·
                    have : d = 512234 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512233 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512229 ≤ d
              ·
                by_cases h : 512231 ≤ d
                ·
                  by_cases h : 512232 ≤ d
                  ·
                    have : d = 512232 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3049)
      exact by decide
                  ·
                    have : d = 512231 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512230 ≤ d
                  ·
                    have : d = 512230 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512229 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512227 ≤ d
                ·
                  by_cases h : 512228 ≤ d
                  ·
                    have : d = 512228 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 512227 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512226 ≤ d
                  ·
                    have : d = 512226 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 512225 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 512209 ≤ d
          ·
            by_cases h : 512217 ≤ d
            ·
              by_cases h : 512221 ≤ d
              ·
                by_cases h : 512223 ≤ d
                ·
                  by_cases h : 512224 ≤ d
                  ·
                    have : d = 512224 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512223 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512222 ≤ d
                  ·
                    have : d = 512222 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512221 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512219 ≤ d
                ·
                  by_cases h : 512220 ≤ d
                  ·
                    have : d = 512220 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 8537)
      exact by decide
                  ·
                    have : d = 512219 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512218 ≤ d
                  ·
                    have : d = 512218 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512217 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512213 ≤ d
              ·
                by_cases h : 512215 ≤ d
                ·
                  by_cases h : 512216 ≤ d
                  ·
                    have : d = 512216 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 43)
      exact by decide
                  ·
                    have : d = 512215 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512214 ≤ d
                  ·
                    have : d = 512214 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512213 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512211 ≤ d
                ·
                  by_cases h : 512212 ≤ d
                  ·
                    have : d = 512212 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512211 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512210 ≤ d
                  ·
                    have : d = 512210 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512209 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 512201 ≤ d
            ·
              by_cases h : 512205 ≤ d
              ·
                by_cases h : 512207 ≤ d
                ·
                  by_cases h : 512208 ≤ d
                  ·
                    have : d = 512208 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3557)
      exact by decide
                  ·
                    have : d = 512207 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512206 ≤ d
                  ·
                    have : d = 512206 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512205 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512203 ≤ d
                ·
                  by_cases h : 512204 ≤ d
                  ·
                    have : d = 512204 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512203 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512202 ≤ d
                  ·
                    have : d = 512202 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 512201 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512197 ≤ d
              ·
                by_cases h : 512199 ≤ d
                ·
                  by_cases h : 512200 ≤ d
                  ·
                    have : d = 512200 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512199 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512198 ≤ d
                  ·
                    have : d = 512198 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 512197 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512195 ≤ d
                ·
                  by_cases h : 512196 ≤ d
                  ·
                    have : d = 512196 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512195 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512194 ≤ d
                  ·
                    have : d = 512194 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512193 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 512161 ≤ d
        ·
          by_cases h : 512177 ≤ d
          ·
            by_cases h : 512185 ≤ d
            ·
              by_cases h : 512189 ≤ d
              ·
                by_cases h : 512191 ≤ d
                ·
                  by_cases h : 512192 ≤ d
                  ·
                    have : d = 512192 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 53)
      exact by decide
                  ·
                    have : d = 512191 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512190 ≤ d
                  ·
                    have : d = 512190 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 271)
      exact by decide
                  ·
                    have : d = 512189 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512187 ≤ d
                ·
                  by_cases h : 512188 ≤ d
                  ·
                    have : d = 512188 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512187 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512186 ≤ d
                  ·
                    have : d = 512186 := by omega
                    subst d
      exact fullRecordGapTerm08591_not_prime
                  ·
                    have : d = 512185 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512181 ≤ d
              ·
                by_cases h : 512183 ≤ d
                ·
                  by_cases h : 512184 ≤ d
                  ·
                    have : d = 512184 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512183 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512182 ≤ d
                  ·
                    have : d = 512182 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512181 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512179 ≤ d
                ·
                  by_cases h : 512180 ≤ d
                  ·
                    have : d = 512180 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 25609)
      exact by decide
                  ·
                    have : d = 512179 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512178 ≤ d
                  ·
                    have : d = 512178 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512177 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 512169 ≤ d
            ·
              by_cases h : 512173 ≤ d
              ·
                by_cases h : 512175 ≤ d
                ·
                  by_cases h : 512176 ≤ d
                  ·
                    have : d = 512176 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512175 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512174 ≤ d
                  ·
                    have : d = 512174 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512173 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512171 ≤ d
                ·
                  by_cases h : 512172 ≤ d
                  ·
                    have : d = 512172 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 41)
      exact by decide
                  ·
                    have : d = 512171 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512170 ≤ d
                  ·
                    have : d = 512170 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512169 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512165 ≤ d
              ·
                by_cases h : 512167 ≤ d
                ·
                  by_cases h : 512168 ≤ d
                  ·
                    have : d = 512168 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512167 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512166 ≤ d
                  ·
                    have : d = 512166 := by omega
                    subst d
      exact fullRecordGapTerm08590_not_prime
                  ·
                    have : d = 512165 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512163 ≤ d
                ·
                  by_cases h : 512164 ≤ d
                  ·
                    have : d = 512164 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512163 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512162 ≤ d
                  ·
                    have : d = 512162 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 36583)
      exact by decide
                  ·
                    have : d = 512161 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 512145 ≤ d
          ·
            by_cases h : 512153 ≤ d
            ·
              by_cases h : 512157 ≤ d
              ·
                by_cases h : 512159 ≤ d
                ·
                  by_cases h : 512160 ≤ d
                  ·
                    have : d = 512160 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 97)
      exact by decide
                  ·
                    have : d = 512159 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512158 ≤ d
                  ·
                    have : d = 512158 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512157 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512155 ≤ d
                ·
                  by_cases h : 512156 ≤ d
                  ·
                    have : d = 512156 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512155 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512154 ≤ d
                  ·
                    have : d = 512154 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512153 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512149 ≤ d
              ·
                by_cases h : 512151 ≤ d
                ·
                  by_cases h : 512152 ≤ d
                  ·
                    have : d = 512152 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512151 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512150 ≤ d
                  ·
                    have : d = 512150 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 10243)
      exact by decide
                  ·
                    have : d = 512149 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512147 ≤ d
                ·
                  by_cases h : 512148 ≤ d
                  ·
                    have : d = 512148 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 512147 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512146 ≤ d
                  ·
                    have : d = 512146 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512145 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 512137 ≤ d
            ·
              by_cases h : 512141 ≤ d
              ·
                by_cases h : 512143 ≤ d
                ·
                  by_cases h : 512144 ≤ d
                  ·
                    have : d = 512144 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512143 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512142 ≤ d
                  ·
                    have : d = 512142 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 512141 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512139 ≤ d
                ·
                  by_cases h : 512140 ≤ d
                  ·
                    have : d = 512140 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512139 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512138 ≤ d
                  ·
                    have : d = 512138 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23279)
      exact by decide
                  ·
                    have : d = 512137 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512133 ≤ d
              ·
                by_cases h : 512135 ≤ d
                ·
                  by_cases h : 512136 ≤ d
                  ·
                    have : d = 512136 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2371)
      exact by decide
                  ·
                    have : d = 512135 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512134 ≤ d
                  ·
                    have : d = 512134 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512133 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512131 ≤ d
                ·
                  by_cases h : 512132 ≤ d
                  ·
                    have : d = 512132 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 224233)
      right
      exact ⟨160567, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512131 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512130 ≤ d
                  ·
                    have : d = 512130 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 43)
      exact by decide
                  ·
                    have : d = 512129 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 512065 ≤ d
      ·
        by_cases h : 512097 ≤ d
        ·
          by_cases h : 512113 ≤ d
          ·
            by_cases h : 512121 ≤ d
            ·
              by_cases h : 512125 ≤ d
              ·
                by_cases h : 512127 ≤ d
                ·
                  by_cases h : 512128 ≤ d
                  ·
                    have : d = 512128 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512127 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512126 ≤ d
                  ·
                    have : d = 512126 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512125 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512123 ≤ d
                ·
                  by_cases h : 512124 ≤ d
                  ·
                    have : d = 512124 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512123 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512122 ≤ d
                  ·
                    have : d = 512122 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512121 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512117 ≤ d
              ·
                by_cases h : 512119 ≤ d
                ·
                  by_cases h : 512120 ≤ d
                  ·
                    have : d = 512120 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 512119 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512118 ≤ d
                  ·
                    have : d = 512118 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 512117 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512115 ≤ d
                ·
                  by_cases h : 512116 ≤ d
                  ·
                    have : d = 512116 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512115 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512114 ≤ d
                  ·
                    have : d = 512114 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512113 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 512105 ≤ d
            ·
              by_cases h : 512109 ≤ d
              ·
                by_cases h : 512111 ≤ d
                ·
                  by_cases h : 512112 ≤ d
                  ·
                    have : d = 512112 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512111 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512110 ≤ d
                  ·
                    have : d = 512110 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512109 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512107 ≤ d
                ·
                  by_cases h : 512108 ≤ d
                  ·
                    have : d = 512108 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 512107 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512106 ≤ d
                  ·
                    have : d = 512106 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 89)
      exact by decide
                  ·
                    have : d = 512105 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512101 ≤ d
              ·
                by_cases h : 512103 ≤ d
                ·
                  by_cases h : 512104 ≤ d
                  ·
                    have : d = 512104 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512103 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512102 ≤ d
                  ·
                    have : d = 512102 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 107)
      exact by decide
                  ·
                    have : d = 512101 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512099 ≤ d
                ·
                  by_cases h : 512100 ≤ d
                  ·
                    have : d = 512100 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 569)
      exact by decide
                  ·
                    have : d = 512099 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512098 ≤ d
                  ·
                    have : d = 512098 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512097 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 512081 ≤ d
          ·
            by_cases h : 512089 ≤ d
            ·
              by_cases h : 512093 ≤ d
              ·
                by_cases h : 512095 ≤ d
                ·
                  by_cases h : 512096 ≤ d
                  ·
                    have : d = 512096 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 512095 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512094 ≤ d
                  ·
                    have : d = 512094 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512093 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512091 ≤ d
                ·
                  by_cases h : 512092 ≤ d
                  ·
                    have : d = 512092 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512091 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512090 ≤ d
                  ·
                    have : d = 512090 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512089 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512085 ≤ d
              ·
                by_cases h : 512087 ≤ d
                ·
                  by_cases h : 512088 ≤ d
                  ·
                    have : d = 512088 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 512087 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512086 ≤ d
                  ·
                    have : d = 512086 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512085 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512083 ≤ d
                ·
                  by_cases h : 512084 ≤ d
                  ·
                    have : d = 512084 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512083 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512082 ≤ d
                  ·
                    have : d = 512082 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 512081 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 512073 ≤ d
            ·
              by_cases h : 512077 ≤ d
              ·
                by_cases h : 512079 ≤ d
                ·
                  by_cases h : 512080 ≤ d
                  ·
                    have : d = 512080 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512079 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512078 ≤ d
                  ·
                    have : d = 512078 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 79)
      exact by decide
                  ·
                    have : d = 512077 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512075 ≤ d
                ·
                  by_cases h : 512076 ≤ d
                  ·
                    have : d = 512076 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 139)
      exact by decide
                  ·
                    have : d = 512075 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512074 ≤ d
                  ·
                    have : d = 512074 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512073 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512069 ≤ d
              ·
                by_cases h : 512071 ≤ d
                ·
                  by_cases h : 512072 ≤ d
                  ·
                    have : d = 512072 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 512071 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512070 ≤ d
                  ·
                    have : d = 512070 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512069 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512067 ≤ d
                ·
                  by_cases h : 512068 ≤ d
                  ·
                    have : d = 512068 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512067 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512066 ≤ d
                  ·
                    have : d = 512066 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3445919)
      right
      exact ⟨2933853, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512065 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 512033 ≤ d
        ·
          by_cases h : 512049 ≤ d
          ·
            by_cases h : 512057 ≤ d
            ·
              by_cases h : 512061 ≤ d
              ·
                by_cases h : 512063 ≤ d
                ·
                  by_cases h : 512064 ≤ d
                  ·
                    have : d = 512064 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512063 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512062 ≤ d
                  ·
                    have : d = 512062 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512061 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512059 ≤ d
                ·
                  by_cases h : 512060 ≤ d
                  ·
                    have : d = 512060 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 25603)
      exact by decide
                  ·
                    have : d = 512059 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512058 ≤ d
                  ·
                    have : d = 512058 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 512057 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512053 ≤ d
              ·
                by_cases h : 512055 ≤ d
                ·
                  by_cases h : 512056 ≤ d
                  ·
                    have : d = 512056 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512055 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512054 ≤ d
                  ·
                    have : d = 512054 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512053 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512051 ≤ d
                ·
                  by_cases h : 512052 ≤ d
                  ·
                    have : d = 512052 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 71)
      exact by decide
                  ·
                    have : d = 512051 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512050 ≤ d
                  ·
                    have : d = 512050 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512049 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 512041 ≤ d
            ·
              by_cases h : 512045 ≤ d
              ·
                by_cases h : 512047 ≤ d
                ·
                  by_cases h : 512048 ≤ d
                  ·
                    have : d = 512048 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 32003)
      exact by decide
                  ·
                    have : d = 512047 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512046 ≤ d
                  ·
                    have : d = 512046 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512045 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512043 ≤ d
                ·
                  by_cases h : 512044 ≤ d
                  ·
                    have : d = 512044 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512043 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512042 ≤ d
                  ·
                    have : d = 512042 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512041 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512037 ≤ d
              ·
                by_cases h : 512039 ≤ d
                ·
                  by_cases h : 512040 ≤ d
                  ·
                    have : d = 512040 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 512039 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512038 ≤ d
                  ·
                    have : d = 512038 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512037 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512035 ≤ d
                ·
                  by_cases h : 512036 ≤ d
                  ·
                    have : d = 512036 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 18287)
      exact by decide
                  ·
                    have : d = 512035 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512034 ≤ d
                  ·
                    have : d = 512034 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512033 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 512017 ≤ d
          ·
            by_cases h : 512025 ≤ d
            ·
              by_cases h : 512029 ≤ d
              ·
                by_cases h : 512031 ≤ d
                ·
                  by_cases h : 512032 ≤ d
                  ·
                    have : d = 512032 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512031 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512030 ≤ d
                  ·
                    have : d = 512030 := by omega
                    subst d
      exact fullRecordGapTerm08589_not_prime
                  ·
                    have : d = 512029 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512027 ≤ d
                ·
                  by_cases h : 512028 ≤ d
                  ·
                    have : d = 512028 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512027 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512026 ≤ d
                  ·
                    have : d = 512026 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512025 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512021 ≤ d
              ·
                by_cases h : 512023 ≤ d
                ·
                  by_cases h : 512024 ≤ d
                  ·
                    have : d = 512024 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512023 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512022 ≤ d
                  ·
                    have : d = 512022 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 73)
      exact by decide
                  ·
                    have : d = 512021 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512019 ≤ d
                ·
                  by_cases h : 512020 ≤ d
                  ·
                    have : d = 512020 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512019 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512018 ≤ d
                  ·
                    have : d = 512018 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 512017 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 512009 ≤ d
            ·
              by_cases h : 512013 ≤ d
              ·
                by_cases h : 512015 ≤ d
                ·
                  by_cases h : 512016 ≤ d
                  ·
                    have : d = 512016 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 10667)
      exact by decide
                  ·
                    have : d = 512015 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512014 ≤ d
                  ·
                    have : d = 512014 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512013 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512011 ≤ d
                ·
                  by_cases h : 512012 ≤ d
                  ·
                    have : d = 512012 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 512011 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512010 ≤ d
                  ·
                    have : d = 512010 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5689)
      exact by decide
                  ·
                    have : d = 512009 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 512005 ≤ d
              ·
                by_cases h : 512007 ≤ d
                ·
                  by_cases h : 512008 ≤ d
                  ·
                    have : d = 512008 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512007 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512006 ≤ d
                  ·
                    have : d = 512006 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 512005 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 512003 ≤ d
                ·
                  by_cases h : 512004 ≤ d
                  ·
                    have : d = 512004 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512003 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 512002 ≤ d
                  ·
                    have : d = 512002 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 512001 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩

end PrimeFactorUnimodality
