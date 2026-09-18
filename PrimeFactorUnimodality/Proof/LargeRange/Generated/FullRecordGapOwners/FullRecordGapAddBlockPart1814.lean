import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapFermat

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

theorem fullRecordGapAddBlock_part1814 (d : Nat) (472065 ≤ d) (d ≤ 472576) : ¬(recordGapCenter + d).Prime := by
  by_cases h : 472321 ≤ d
  ·
    by_cases h : 472449 ≤ d
    ·
      by_cases h : 472513 ≤ d
      ·
        by_cases h : 472545 ≤ d
        ·
          by_cases h : 472561 ≤ d
          ·
            by_cases h : 472569 ≤ d
            ·
              by_cases h : 472573 ≤ d
              ·
                by_cases h : 472575 ≤ d
                ·
                  by_cases h : 472576 ≤ d
                  ·
                    have : d = 472576 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472575 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472574 ≤ d
                  ·
                    have : d = 472574 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472573 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472571 ≤ d
                ·
                  by_cases h : 472572 ≤ d
                  ·
                    have : d = 472572 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13127)
      exact by decide
                  ·
                    have : d = 472571 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472570 ≤ d
                  ·
                    have : d = 472570 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472569 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472565 ≤ d
              ·
                by_cases h : 472567 ≤ d
                ·
                  by_cases h : 472568 ≤ d
                  ·
                    have : d = 472568 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 472567 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472566 ≤ d
                  ·
                    have : d = 472566 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 472565 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472563 ≤ d
                ·
                  by_cases h : 472564 ≤ d
                  ·
                    have : d = 472564 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472563 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472562 ≤ d
                  ·
                    have : d = 472562 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472561 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 472553 ≤ d
            ·
              by_cases h : 472557 ≤ d
              ·
                by_cases h : 472559 ≤ d
                ·
                  by_cases h : 472560 ≤ d
                  ·
                    have : d = 472560 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 179)
      exact by decide
                  ·
                    have : d = 472559 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472558 ≤ d
                  ·
                    have : d = 472558 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472557 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472555 ≤ d
                ·
                  by_cases h : 472556 ≤ d
                  ·
                    have : d = 472556 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472555 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472554 ≤ d
                  ·
                    have : d = 472554 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472553 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472549 ≤ d
              ·
                by_cases h : 472551 ≤ d
                ·
                  by_cases h : 472552 ≤ d
                  ·
                    have : d = 472552 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472551 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472550 ≤ d
                  ·
                    have : d = 472550 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 472549 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472547 ≤ d
                ·
                  by_cases h : 472548 ≤ d
                  ·
                    have : d = 472548 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472547 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472546 ≤ d
                  ·
                    have : d = 472546 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472545 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 472529 ≤ d
          ·
            by_cases h : 472537 ≤ d
            ·
              by_cases h : 472541 ≤ d
              ·
                by_cases h : 472543 ≤ d
                ·
                  by_cases h : 472544 ≤ d
                  ·
                    have : d = 472544 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472543 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472542 ≤ d
                  ·
                    have : d = 472542 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11251)
      exact by decide
                  ·
                    have : d = 472541 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472539 ≤ d
                ·
                  by_cases h : 472540 ≤ d
                  ·
                    have : d = 472540 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472539 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472538 ≤ d
                  ·
                    have : d = 472538 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 47)
      exact by decide
                  ·
                    have : d = 472537 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472533 ≤ d
              ·
                by_cases h : 472535 ≤ d
                ·
                  by_cases h : 472536 ≤ d
                  ·
                    have : d = 472536 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 6563)
      exact by decide
                  ·
                    have : d = 472535 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472534 ≤ d
                  ·
                    have : d = 472534 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472533 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472531 ≤ d
                ·
                  by_cases h : 472532 ≤ d
                  ·
                    have : d = 472532 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 472531 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472530 ≤ d
                  ·
                    have : d = 472530 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 472529 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 472521 ≤ d
            ·
              by_cases h : 472525 ≤ d
              ·
                by_cases h : 472527 ≤ d
                ·
                  by_cases h : 472528 ≤ d
                  ·
                    have : d = 472528 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472527 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472526 ≤ d
                  ·
                    have : d = 472526 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 472525 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472523 ≤ d
                ·
                  by_cases h : 472524 ≤ d
                  ·
                    have : d = 472524 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472523 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472522 ≤ d
                  ·
                    have : d = 472522 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472521 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472517 ≤ d
              ·
                by_cases h : 472519 ≤ d
                ·
                  by_cases h : 472520 ≤ d
                  ·
                    have : d = 472520 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472519 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472518 ≤ d
                  ·
                    have : d = 472518 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 26251)
      exact by decide
                  ·
                    have : d = 472517 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472515 ≤ d
                ·
                  by_cases h : 472516 ≤ d
                  ·
                    have : d = 472516 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472515 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472514 ≤ d
                  ·
                    have : d = 472514 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472513 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 472481 ≤ d
        ·
          by_cases h : 472497 ≤ d
          ·
            by_cases h : 472505 ≤ d
            ·
              by_cases h : 472509 ≤ d
              ·
                by_cases h : 472511 ≤ d
                ·
                  by_cases h : 472512 ≤ d
                  ·
                    have : d = 472512 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472511 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472510 ≤ d
                  ·
                    have : d = 472510 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472509 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472507 ≤ d
                ·
                  by_cases h : 472508 ≤ d
                  ·
                    have : d = 472508 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 94649)
      right
      exact ⟨737, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472507 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472506 ≤ d
                  ·
                    have : d = 472506 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472505 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472501 ≤ d
              ·
                by_cases h : 472503 ≤ d
                ·
                  by_cases h : 472504 ≤ d
                  ·
                    have : d = 472504 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472503 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472502 ≤ d
                  ·
                    have : d = 472502 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 472501 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472499 ≤ d
                ·
                  by_cases h : 472500 ≤ d
                  ·
                    have : d = 472500 := by omega
                    subst d
      exact fullRecordGapTerm08045_not_prime
                  ·
                    have : d = 472499 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472498 ≤ d
                  ·
                    have : d = 472498 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472497 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 472489 ≤ d
            ·
              by_cases h : 472493 ≤ d
              ·
                by_cases h : 472495 ≤ d
                ·
                  by_cases h : 472496 ≤ d
                  ·
                    have : d = 472496 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29531)
      exact by decide
                  ·
                    have : d = 472495 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472494 ≤ d
                  ·
                    have : d = 472494 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472493 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472491 ≤ d
                ·
                  by_cases h : 472492 ≤ d
                  ·
                    have : d = 472492 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472491 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472490 ≤ d
                  ·
                    have : d = 472490 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472489 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472485 ≤ d
              ·
                by_cases h : 472487 ≤ d
                ·
                  by_cases h : 472488 ≤ d
                  ·
                    have : d = 472488 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19687)
      exact by decide
                  ·
                    have : d = 472487 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472486 ≤ d
                  ·
                    have : d = 472486 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472485 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472483 ≤ d
                ·
                  by_cases h : 472484 ≤ d
                  ·
                    have : d = 472484 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472483 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472482 ≤ d
                  ·
                    have : d = 472482 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 26249)
      exact by decide
                  ·
                    have : d = 472481 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 472465 ≤ d
          ·
            by_cases h : 472473 ≤ d
            ·
              by_cases h : 472477 ≤ d
              ·
                by_cases h : 472479 ≤ d
                ·
                  by_cases h : 472480 ≤ d
                  ·
                    have : d = 472480 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472479 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472478 ≤ d
                  ·
                    have : d = 472478 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472477 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472475 ≤ d
                ·
                  by_cases h : 472476 ≤ d
                  ·
                    have : d = 472476 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 39373)
      exact by decide
                  ·
                    have : d = 472475 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472474 ≤ d
                  ·
                    have : d = 472474 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472473 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472469 ≤ d
              ·
                by_cases h : 472471 ≤ d
                ·
                  by_cases h : 472472 ≤ d
                  ·
                    have : d = 472472 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 472471 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472470 ≤ d
                  ·
                    have : d = 472470 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 15749)
      exact by decide
                  ·
                    have : d = 472469 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472467 ≤ d
                ·
                  by_cases h : 472468 ≤ d
                  ·
                    have : d = 472468 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472467 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472466 ≤ d
                  ·
                    have : d = 472466 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 472465 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 472457 ≤ d
            ·
              by_cases h : 472461 ≤ d
              ·
                by_cases h : 472463 ≤ d
                ·
                  by_cases h : 472464 ≤ d
                  ·
                    have : d = 472464 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472463 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472462 ≤ d
                  ·
                    have : d = 472462 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472461 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472459 ≤ d
                ·
                  by_cases h : 472460 ≤ d
                  ·
                    have : d = 472460 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23623)
      exact by decide
                  ·
                    have : d = 472459 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472458 ≤ d
                  ·
                    have : d = 472458 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1607)
      exact by decide
                  ·
                    have : d = 472457 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472453 ≤ d
              ·
                by_cases h : 472455 ≤ d
                ·
                  by_cases h : 472456 ≤ d
                  ·
                    have : d = 472456 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472455 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472454 ≤ d
                  ·
                    have : d = 472454 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472453 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472451 ≤ d
                ·
                  by_cases h : 472452 ≤ d
                  ·
                    have : d = 472452 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 39371)
      exact by decide
                  ·
                    have : d = 472451 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472450 ≤ d
                  ·
                    have : d = 472450 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472449 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 472385 ≤ d
      ·
        by_cases h : 472417 ≤ d
        ·
          by_cases h : 472433 ≤ d
          ·
            by_cases h : 472441 ≤ d
            ·
              by_cases h : 472445 ≤ d
              ·
                by_cases h : 472447 ≤ d
                ·
                  by_cases h : 472448 ≤ d
                  ·
                    have : d = 472448 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3691)
      exact by decide
                  ·
                    have : d = 472447 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472446 ≤ d
                  ·
                    have : d = 472446 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472445 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472443 ≤ d
                ·
                  by_cases h : 472444 ≤ d
                  ·
                    have : d = 472444 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472443 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472442 ≤ d
                  ·
                    have : d = 472442 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 53)
      exact by decide
                  ·
                    have : d = 472441 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472437 ≤ d
              ·
                by_cases h : 472439 ≤ d
                ·
                  by_cases h : 472440 ≤ d
                  ·
                    have : d = 472440 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 472439 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472438 ≤ d
                  ·
                    have : d = 472438 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472437 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472435 ≤ d
                ·
                  by_cases h : 472436 ≤ d
                  ·
                    have : d = 472436 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472435 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472434 ≤ d
                  ·
                    have : d = 472434 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472433 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 472425 ≤ d
            ·
              by_cases h : 472429 ≤ d
              ·
                by_cases h : 472431 ≤ d
                ·
                  by_cases h : 472432 ≤ d
                  ·
                    have : d = 472432 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472431 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472430 ≤ d
                  ·
                    have : d = 472430 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 472429 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472427 ≤ d
                ·
                  by_cases h : 472428 ≤ d
                  ·
                    have : d = 472428 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1193)
      exact by decide
                  ·
                    have : d = 472427 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472426 ≤ d
                  ·
                    have : d = 472426 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472425 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472421 ≤ d
              ·
                by_cases h : 472423 ≤ d
                ·
                  by_cases h : 472424 ≤ d
                  ·
                    have : d = 472424 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472423 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472422 ≤ d
                  ·
                    have : d = 472422 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472421 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472419 ≤ d
                ·
                  by_cases h : 472420 ≤ d
                  ·
                    have : d = 472420 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472419 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472418 ≤ d
                  ·
                    have : d = 472418 := by omega
                    subst d
      exact fullRecordGapTerm08044_not_prime
                  ·
                    have : d = 472417 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 472401 ≤ d
          ·
            by_cases h : 472409 ≤ d
            ·
              by_cases h : 472413 ≤ d
              ·
                by_cases h : 472415 ≤ d
                ·
                  by_cases h : 472416 ≤ d
                  ·
                    have : d = 472416 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 472415 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472414 ≤ d
                  ·
                    have : d = 472414 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472413 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472411 ≤ d
                ·
                  by_cases h : 472412 ≤ d
                  ·
                    have : d = 472412 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 89)
      exact by decide
                  ·
                    have : d = 472411 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472410 ≤ d
                  ·
                    have : d = 472410 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 472409 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472405 ≤ d
              ·
                by_cases h : 472407 ≤ d
                ·
                  by_cases h : 472408 ≤ d
                  ·
                    have : d = 472408 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472407 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472406 ≤ d
                  ·
                    have : d = 472406 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 109)
      exact by decide
                  ·
                    have : d = 472405 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472403 ≤ d
                ·
                  by_cases h : 472404 ≤ d
                  ·
                    have : d = 472404 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472403 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472402 ≤ d
                  ·
                    have : d = 472402 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472401 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 472393 ≤ d
            ·
              by_cases h : 472397 ≤ d
              ·
                by_cases h : 472399 ≤ d
                ·
                  by_cases h : 472400 ≤ d
                  ·
                    have : d = 472400 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1181)
      exact by decide
                  ·
                    have : d = 472399 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472398 ≤ d
                  ·
                    have : d = 472398 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 43)
      exact by decide
                  ·
                    have : d = 472397 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472395 ≤ d
                ·
                  by_cases h : 472396 ≤ d
                  ·
                    have : d = 472396 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472395 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472394 ≤ d
                  ·
                    have : d = 472394 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472393 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472389 ≤ d
              ·
                by_cases h : 472391 ≤ d
                ·
                  by_cases h : 472392 ≤ d
                  ·
                    have : d = 472392 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 53927)
      right
      exact ⟨12951, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472391 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472390 ≤ d
                  ·
                    have : d = 472390 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472389 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472387 ≤ d
                ·
                  by_cases h : 472388 ≤ d
                  ·
                    have : d = 472388 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 16871)
      exact by decide
                  ·
                    have : d = 472387 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472386 ≤ d
                  ·
                    have : d = 472386 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 131)
      exact by decide
                  ·
                    have : d = 472385 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 472353 ≤ d
        ·
          by_cases h : 472369 ≤ d
          ·
            by_cases h : 472377 ≤ d
            ·
              by_cases h : 472381 ≤ d
              ·
                by_cases h : 472383 ≤ d
                ·
                  by_cases h : 472384 ≤ d
                  ·
                    have : d = 472384 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472383 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472382 ≤ d
                  ·
                    have : d = 472382 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 251)
      exact by decide
                  ·
                    have : d = 472381 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472379 ≤ d
                ·
                  by_cases h : 472380 ≤ d
                  ·
                    have : d = 472380 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472379 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472378 ≤ d
                  ·
                    have : d = 472378 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472377 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472373 ≤ d
              ·
                by_cases h : 472375 ≤ d
                ·
                  by_cases h : 472376 ≤ d
                  ·
                    have : d = 472376 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 137)
      exact by decide
                  ·
                    have : d = 472375 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472374 ≤ d
                  ·
                    have : d = 472374 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472373 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472371 ≤ d
                ·
                  by_cases h : 472372 ≤ d
                  ·
                    have : d = 472372 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472371 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472370 ≤ d
                  ·
                    have : d = 472370 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 635659)
      right
      exact ⟨163289, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472369 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 472361 ≤ d
            ·
              by_cases h : 472365 ≤ d
              ·
                by_cases h : 472367 ≤ d
                ·
                  by_cases h : 472368 ≤ d
                  ·
                    have : d = 472368 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 472367 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472366 ≤ d
                  ·
                    have : d = 472366 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472365 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472363 ≤ d
                ·
                  by_cases h : 472364 ≤ d
                  ·
                    have : d = 472364 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472363 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472362 ≤ d
                  ·
                    have : d = 472362 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 472361 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472357 ≤ d
              ·
                by_cases h : 472359 ≤ d
                ·
                  by_cases h : 472360 ≤ d
                  ·
                    have : d = 472360 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472359 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472358 ≤ d
                  ·
                    have : d = 472358 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472357 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472355 ≤ d
                ·
                  by_cases h : 472356 ≤ d
                  ·
                    have : d = 472356 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13121)
      exact by decide
                  ·
                    have : d = 472355 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472354 ≤ d
                  ·
                    have : d = 472354 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472353 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 472337 ≤ d
          ·
            by_cases h : 472345 ≤ d
            ·
              by_cases h : 472349 ≤ d
              ·
                by_cases h : 472351 ≤ d
                ·
                  by_cases h : 472352 ≤ d
                  ·
                    have : d = 472352 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472351 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472350 ≤ d
                  ·
                    have : d = 472350 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 47)
      exact by decide
                  ·
                    have : d = 472349 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472347 ≤ d
                ·
                  by_cases h : 472348 ≤ d
                  ·
                    have : d = 472348 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472347 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472346 ≤ d
                  ·
                    have : d = 472346 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 33739)
      exact by decide
                  ·
                    have : d = 472345 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472341 ≤ d
              ·
                by_cases h : 472343 ≤ d
                ·
                  by_cases h : 472344 ≤ d
                  ·
                    have : d = 472344 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472343 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472342 ≤ d
                  ·
                    have : d = 472342 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472341 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472339 ≤ d
                ·
                  by_cases h : 472340 ≤ d
                  ·
                    have : d = 472340 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 472339 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472338 ≤ d
                  ·
                    have : d = 472338 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472337 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 472329 ≤ d
            ·
              by_cases h : 472333 ≤ d
              ·
                by_cases h : 472335 ≤ d
                ·
                  by_cases h : 472336 ≤ d
                  ·
                    have : d = 472336 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472335 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472334 ≤ d
                  ·
                    have : d = 472334 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472333 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472331 ≤ d
                ·
                  by_cases h : 472332 ≤ d
                  ·
                    have : d = 472332 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5623)
      exact by decide
                  ·
                    have : d = 472331 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472330 ≤ d
                  ·
                    have : d = 472330 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472329 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472325 ≤ d
              ·
                by_cases h : 472327 ≤ d
                ·
                  by_cases h : 472328 ≤ d
                  ·
                    have : d = 472328 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 472327 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472326 ≤ d
                  ·
                    have : d = 472326 := by omega
                    subst d
      exact fullRecordGapTerm08043_not_prime
                  ·
                    have : d = 472325 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472323 ≤ d
                ·
                  by_cases h : 472324 ≤ d
                  ·
                    have : d = 472324 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472323 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472322 ≤ d
                  ·
                    have : d = 472322 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 139)
      exact by decide
                  ·
                    have : d = 472321 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
  ·
    by_cases h : 472193 ≤ d
    ·
      by_cases h : 472257 ≤ d
      ·
        by_cases h : 472289 ≤ d
        ·
          by_cases h : 472305 ≤ d
          ·
            by_cases h : 472313 ≤ d
            ·
              by_cases h : 472317 ≤ d
              ·
                by_cases h : 472319 ≤ d
                ·
                  by_cases h : 472320 ≤ d
                  ·
                    have : d = 472320 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 41)
      exact by decide
                  ·
                    have : d = 472319 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472318 ≤ d
                  ·
                    have : d = 472318 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472317 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472315 ≤ d
                ·
                  by_cases h : 472316 ≤ d
                  ·
                    have : d = 472316 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 472315 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472314 ≤ d
                  ·
                    have : d = 472314 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472313 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472309 ≤ d
              ·
                by_cases h : 472311 ≤ d
                ·
                  by_cases h : 472312 ≤ d
                  ·
                    have : d = 472312 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472311 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472310 ≤ d
                  ·
                    have : d = 472310 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472309 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472307 ≤ d
                ·
                  by_cases h : 472308 ≤ d
                  ·
                    have : d = 472308 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 39359)
      exact by decide
                  ·
                    have : d = 472307 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472306 ≤ d
                  ·
                    have : d = 472306 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472305 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 472297 ≤ d
            ·
              by_cases h : 472301 ≤ d
              ·
                by_cases h : 472303 ≤ d
                ·
                  by_cases h : 472304 ≤ d
                  ·
                    have : d = 472304 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472303 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472302 ≤ d
                  ·
                    have : d = 472302 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 472301 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472299 ≤ d
                ·
                  by_cases h : 472300 ≤ d
                  ·
                    have : d = 472300 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472299 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472298 ≤ d
                  ·
                    have : d = 472298 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 107)
      exact by decide
                  ·
                    have : d = 472297 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472293 ≤ d
              ·
                by_cases h : 472295 ≤ d
                ·
                  by_cases h : 472296 ≤ d
                  ·
                    have : d = 472296 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472295 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472294 ≤ d
                  ·
                    have : d = 472294 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472293 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472291 ≤ d
                ·
                  by_cases h : 472292 ≤ d
                  ·
                    have : d = 472292 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472291 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472290 ≤ d
                  ·
                    have : d = 472290 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 472289 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 472273 ≤ d
          ·
            by_cases h : 472281 ≤ d
            ·
              by_cases h : 472285 ≤ d
              ·
                by_cases h : 472287 ≤ d
                ·
                  by_cases h : 472288 ≤ d
                  ·
                    have : d = 472288 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472287 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472286 ≤ d
                  ·
                    have : d = 472286 := by omega
                    subst d
      exact fullRecordGapTerm08042_not_prime
                  ·
                    have : d = 472285 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472283 ≤ d
                ·
                  by_cases h : 472284 ≤ d
                  ·
                    have : d = 472284 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472283 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472282 ≤ d
                  ·
                    have : d = 472282 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472281 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472277 ≤ d
              ·
                by_cases h : 472279 ≤ d
                ·
                  by_cases h : 472280 ≤ d
                  ·
                    have : d = 472280 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11807)
      exact by decide
                  ·
                    have : d = 472279 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472278 ≤ d
                  ·
                    have : d = 472278 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 301235197)
      right
      exact ⟨300762919, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472277 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472275 ≤ d
                ·
                  by_cases h : 472276 ≤ d
                  ·
                    have : d = 472276 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472275 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472274 ≤ d
                  ·
                    have : d = 472274 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472273 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 472265 ≤ d
            ·
              by_cases h : 472269 ≤ d
              ·
                by_cases h : 472271 ≤ d
                ·
                  by_cases h : 472272 ≤ d
                  ·
                    have : d = 472272 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 9839)
      exact by decide
                  ·
                    have : d = 472271 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472270 ≤ d
                  ·
                    have : d = 472270 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472269 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472267 ≤ d
                ·
                  by_cases h : 472268 ≤ d
                  ·
                    have : d = 472268 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472267 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472266 ≤ d
                  ·
                    have : d = 472266 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 26237)
      exact by decide
                  ·
                    have : d = 472265 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472261 ≤ d
              ·
                by_cases h : 472263 ≤ d
                ·
                  by_cases h : 472264 ≤ d
                  ·
                    have : d = 472264 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472263 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472262 ≤ d
                  ·
                    have : d = 472262 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 61)
      exact by decide
                  ·
                    have : d = 472261 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472259 ≤ d
                ·
                  by_cases h : 472260 ≤ d
                  ·
                    have : d = 472260 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 472259 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472258 ≤ d
                  ·
                    have : d = 472258 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472257 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 472225 ≤ d
        ·
          by_cases h : 472241 ≤ d
          ·
            by_cases h : 472249 ≤ d
            ·
              by_cases h : 472253 ≤ d
              ·
                by_cases h : 472255 ≤ d
                ·
                  by_cases h : 472256 ≤ d
                  ·
                    have : d = 472256 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 47)
      exact by decide
                  ·
                    have : d = 472255 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472254 ≤ d
                  ·
                    have : d = 472254 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472253 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472251 ≤ d
                ·
                  by_cases h : 472252 ≤ d
                  ·
                    have : d = 472252 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472251 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472250 ≤ d
                  ·
                    have : d = 472250 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1889)
      exact by decide
                  ·
                    have : d = 472249 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472245 ≤ d
              ·
                by_cases h : 472247 ≤ d
                ·
                  by_cases h : 472248 ≤ d
                  ·
                    have : d = 472248 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472247 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472246 ≤ d
                  ·
                    have : d = 472246 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472245 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472243 ≤ d
                ·
                  by_cases h : 472244 ≤ d
                  ·
                    have : d = 472244 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472243 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472242 ≤ d
                  ·
                    have : d = 472242 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 77801)
      right
      exact ⟨72365, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472241 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 472233 ≤ d
            ·
              by_cases h : 472237 ≤ d
              ·
                by_cases h : 472239 ≤ d
                ·
                  by_cases h : 472240 ≤ d
                  ·
                    have : d = 472240 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472239 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472238 ≤ d
                  ·
                    have : d = 472238 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 472237 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472235 ≤ d
                ·
                  by_cases h : 472236 ≤ d
                  ·
                    have : d = 472236 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 472235 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472234 ≤ d
                  ·
                    have : d = 472234 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472233 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472229 ≤ d
              ·
                by_cases h : 472231 ≤ d
                ·
                  by_cases h : 472232 ≤ d
                  ·
                    have : d = 472232 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 346849)
      right
      exact ⟨221466, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472231 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472230 ≤ d
                  ·
                    have : d = 472230 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 53)
      exact by decide
                  ·
                    have : d = 472229 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472227 ≤ d
                ·
                  by_cases h : 472228 ≤ d
                  ·
                    have : d = 472228 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472227 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472226 ≤ d
                  ·
                    have : d = 472226 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472225 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 472209 ≤ d
          ·
            by_cases h : 472217 ≤ d
            ·
              by_cases h : 472221 ≤ d
              ·
                by_cases h : 472223 ≤ d
                ·
                  by_cases h : 472224 ≤ d
                  ·
                    have : d = 472224 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472223 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472222 ≤ d
                  ·
                    have : d = 472222 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472221 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472219 ≤ d
                ·
                  by_cases h : 472220 ≤ d
                  ·
                    have : d = 472220 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3373)
      exact by decide
                  ·
                    have : d = 472219 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472218 ≤ d
                  ·
                    have : d = 472218 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 211)
      exact by decide
                  ·
                    have : d = 472217 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472213 ≤ d
              ·
                by_cases h : 472215 ≤ d
                ·
                  by_cases h : 472216 ≤ d
                  ·
                    have : d = 472216 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472215 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472214 ≤ d
                  ·
                    have : d = 472214 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472213 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472211 ≤ d
                ·
                  by_cases h : 472212 ≤ d
                  ·
                    have : d = 472212 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472211 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472210 ≤ d
                  ·
                    have : d = 472210 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472209 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 472201 ≤ d
            ·
              by_cases h : 472205 ≤ d
              ·
                by_cases h : 472207 ≤ d
                ·
                  by_cases h : 472208 ≤ d
                  ·
                    have : d = 472208 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2683)
      exact by decide
                  ·
                    have : d = 472207 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472206 ≤ d
                  ·
                    have : d = 472206 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11243)
      exact by decide
                  ·
                    have : d = 472205 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472203 ≤ d
                ·
                  by_cases h : 472204 ≤ d
                  ·
                    have : d = 472204 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472203 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472202 ≤ d
                  ·
                    have : d = 472202 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 179)
      exact by decide
                  ·
                    have : d = 472201 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472197 ≤ d
              ·
                by_cases h : 472199 ≤ d
                ·
                  by_cases h : 472200 ≤ d
                  ·
                    have : d = 472200 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 787)
      exact by decide
                  ·
                    have : d = 472199 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472198 ≤ d
                  ·
                    have : d = 472198 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472197 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472195 ≤ d
                ·
                  by_cases h : 472196 ≤ d
                  ·
                    have : d = 472196 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 97)
      exact by decide
                  ·
                    have : d = 472195 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472194 ≤ d
                  ·
                    have : d = 472194 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472193 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 472129 ≤ d
      ·
        by_cases h : 472161 ≤ d
        ·
          by_cases h : 472177 ≤ d
          ·
            by_cases h : 472185 ≤ d
            ·
              by_cases h : 472189 ≤ d
              ·
                by_cases h : 472191 ≤ d
                ·
                  by_cases h : 472192 ≤ d
                  ·
                    have : d = 472192 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472191 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472190 ≤ d
                  ·
                    have : d = 472190 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 472189 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472187 ≤ d
                ·
                  by_cases h : 472188 ≤ d
                  ·
                    have : d = 472188 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 472187 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472186 ≤ d
                  ·
                    have : d = 472186 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472185 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472181 ≤ d
              ·
                by_cases h : 472183 ≤ d
                ·
                  by_cases h : 472184 ≤ d
                  ·
                    have : d = 472184 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472183 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472182 ≤ d
                  ·
                    have : d = 472182 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472181 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472179 ≤ d
                ·
                  by_cases h : 472180 ≤ d
                  ·
                    have : d = 472180 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472179 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472178 ≤ d
                  ·
                    have : d = 472178 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 472177 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 472169 ≤ d
            ·
              by_cases h : 472173 ≤ d
              ·
                by_cases h : 472175 ≤ d
                ·
                  by_cases h : 472176 ≤ d
                  ·
                    have : d = 472176 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1093)
      exact by decide
                  ·
                    have : d = 472175 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472174 ≤ d
                  ·
                    have : d = 472174 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472173 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472171 ≤ d
                ·
                  by_cases h : 472172 ≤ d
                  ·
                    have : d = 472172 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 795587041)
      right
      exact ⟨795114869, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472171 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472170 ≤ d
                  ·
                    have : d = 472170 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472169 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472165 ≤ d
              ·
                by_cases h : 472167 ≤ d
                ·
                  by_cases h : 472168 ≤ d
                  ·
                    have : d = 472168 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472167 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472166 ≤ d
                  ·
                    have : d = 472166 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 307)
      exact by decide
                  ·
                    have : d = 472165 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472163 ≤ d
                ·
                  by_cases h : 472164 ≤ d
                  ·
                    have : d = 472164 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472163 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472162 ≤ d
                  ·
                    have : d = 472162 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472161 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 472145 ≤ d
          ·
            by_cases h : 472153 ≤ d
            ·
              by_cases h : 472157 ≤ d
              ·
                by_cases h : 472159 ≤ d
                ·
                  by_cases h : 472160 ≤ d
                  ·
                    have : d = 472160 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472159 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472158 ≤ d
                  ·
                    have : d = 472158 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 472157 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472155 ≤ d
                ·
                  by_cases h : 472156 ≤ d
                  ·
                    have : d = 472156 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472155 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472154 ≤ d
                  ·
                    have : d = 472154 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472153 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472149 ≤ d
              ·
                by_cases h : 472151 ≤ d
                ·
                  by_cases h : 472152 ≤ d
                  ·
                    have : d = 472152 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 103)
      exact by decide
                  ·
                    have : d = 472151 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472150 ≤ d
                  ·
                    have : d = 472150 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472149 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472147 ≤ d
                ·
                  by_cases h : 472148 ≤ d
                  ·
                    have : d = 472148 := by omega
                    subst d
      exact fullRecordGapTerm08041_not_prime
                  ·
                    have : d = 472147 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472146 ≤ d
                  ·
                    have : d = 472146 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 47189)
      right
      exact ⟨46933, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472145 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 472137 ≤ d
            ·
              by_cases h : 472141 ≤ d
              ·
                by_cases h : 472143 ≤ d
                ·
                  by_cases h : 472144 ≤ d
                  ·
                    have : d = 472144 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472143 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472142 ≤ d
                  ·
                    have : d = 472142 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472141 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472139 ≤ d
                ·
                  by_cases h : 472140 ≤ d
                  ·
                    have : d = 472140 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 43)
      exact by decide
                  ·
                    have : d = 472139 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472138 ≤ d
                  ·
                    have : d = 472138 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472137 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472133 ≤ d
              ·
                by_cases h : 472135 ≤ d
                ·
                  by_cases h : 472136 ≤ d
                  ·
                    have : d = 472136 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 8431)
      exact by decide
                  ·
                    have : d = 472135 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472134 ≤ d
                  ·
                    have : d = 472134 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472133 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472131 ≤ d
                ·
                  by_cases h : 472132 ≤ d
                  ·
                    have : d = 472132 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472131 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472130 ≤ d
                  ·
                    have : d = 472130 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 472129 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 472097 ≤ d
        ·
          by_cases h : 472113 ≤ d
          ·
            by_cases h : 472121 ≤ d
            ·
              by_cases h : 472125 ≤ d
              ·
                by_cases h : 472127 ≤ d
                ·
                  by_cases h : 472128 ≤ d
                  ·
                    have : d = 472128 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472127 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472126 ≤ d
                  ·
                    have : d = 472126 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472125 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472123 ≤ d
                ·
                  by_cases h : 472124 ≤ d
                  ·
                    have : d = 472124 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472123 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472122 ≤ d
                  ·
                    have : d = 472122 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1249)
      exact by decide
                  ·
                    have : d = 472121 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472117 ≤ d
              ·
                by_cases h : 472119 ≤ d
                ·
                  by_cases h : 472120 ≤ d
                  ·
                    have : d = 472120 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472119 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472118 ≤ d
                  ·
                    have : d = 472118 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 59)
      exact by decide
                  ·
                    have : d = 472117 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472115 ≤ d
                ·
                  by_cases h : 472116 ≤ d
                  ·
                    have : d = 472116 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472115 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472114 ≤ d
                  ·
                    have : d = 472114 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472113 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 472105 ≤ d
            ·
              by_cases h : 472109 ≤ d
              ·
                by_cases h : 472111 ≤ d
                ·
                  by_cases h : 472112 ≤ d
                  ·
                    have : d = 472112 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 472111 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472110 ≤ d
                  ·
                    have : d = 472110 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 15737)
      exact by decide
                  ·
                    have : d = 472109 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472107 ≤ d
                ·
                  by_cases h : 472108 ≤ d
                  ·
                    have : d = 472108 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472107 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472106 ≤ d
                  ·
                    have : d = 472106 := by omega
                    subst d
      exact fullRecordGapTerm08040_not_prime
                  ·
                    have : d = 472105 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472101 ≤ d
              ·
                by_cases h : 472103 ≤ d
                ·
                  by_cases h : 472104 ≤ d
                  ·
                    have : d = 472104 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472103 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472102 ≤ d
                  ·
                    have : d = 472102 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472101 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472099 ≤ d
                ·
                  by_cases h : 472100 ≤ d
                  ·
                    have : d = 472100 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472099 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472098 ≤ d
                  ·
                    have : d = 472098 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 472097 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 472081 ≤ d
          ·
            by_cases h : 472089 ≤ d
            ·
              by_cases h : 472093 ≤ d
              ·
                by_cases h : 472095 ≤ d
                ·
                  by_cases h : 472096 ≤ d
                  ·
                    have : d = 472096 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472095 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472094 ≤ d
                  ·
                    have : d = 472094 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472093 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472091 ≤ d
                ·
                  by_cases h : 472092 ≤ d
                  ·
                    have : d = 472092 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 39341)
      exact by decide
                  ·
                    have : d = 472091 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472090 ≤ d
                  ·
                    have : d = 472090 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472089 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472085 ≤ d
              ·
                by_cases h : 472087 ≤ d
                ·
                  by_cases h : 472088 ≤ d
                  ·
                    have : d = 472088 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 44417)
      right
      exact ⟨16499, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472087 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472086 ≤ d
                  ·
                    have : d = 472086 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472085 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472083 ≤ d
                ·
                  by_cases h : 472084 ≤ d
                  ·
                    have : d = 472084 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472083 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472082 ≤ d
                  ·
                    have : d = 472082 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 472081 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 472073 ≤ d
            ·
              by_cases h : 472077 ≤ d
              ·
                by_cases h : 472079 ≤ d
                ·
                  by_cases h : 472080 ≤ d
                  ·
                    have : d = 472080 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 281)
      exact by decide
                  ·
                    have : d = 472079 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472078 ≤ d
                  ·
                    have : d = 472078 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472077 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472075 ≤ d
                ·
                  by_cases h : 472076 ≤ d
                  ·
                    have : d = 472076 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 10729)
      exact by decide
                  ·
                    have : d = 472075 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472074 ≤ d
                  ·
                    have : d = 472074 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472073 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 472069 ≤ d
              ·
                by_cases h : 472071 ≤ d
                ·
                  by_cases h : 472072 ≤ d
                  ·
                    have : d = 472072 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472071 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472070 ≤ d
                  ·
                    have : d = 472070 := by omega
                    subst d
      exact fullRecordGapTerm08039_not_prime
                  ·
                    have : d = 472069 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 472067 ≤ d
                ·
                  by_cases h : 472068 ≤ d
                  ·
                    have : d = 472068 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 472067 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 472066 ≤ d
                  ·
                    have : d = 472066 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 472065 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩

end PrimeFactorUnimodality
