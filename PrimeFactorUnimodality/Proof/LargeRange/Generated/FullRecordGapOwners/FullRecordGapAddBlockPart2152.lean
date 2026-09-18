import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapFermat

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

theorem fullRecordGapAddBlock_part2152 (d : Nat) (645121 ≤ d) (d ≤ 645632) : ¬(recordGapCenter + d).Prime := by
  by_cases h : 645377 ≤ d
  ·
    by_cases h : 645505 ≤ d
    ·
      by_cases h : 645569 ≤ d
      ·
        by_cases h : 645601 ≤ d
        ·
          by_cases h : 645617 ≤ d
          ·
            by_cases h : 645625 ≤ d
            ·
              by_cases h : 645629 ≤ d
              ·
                by_cases h : 645631 ≤ d
                ·
                  by_cases h : 645632 ≤ d
                  ·
                    have : d = 645632 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 645631 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645630 ≤ d
                  ·
                    have : d = 645630 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645629 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645627 ≤ d
                ·
                  by_cases h : 645628 ≤ d
                  ·
                    have : d = 645628 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645627 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645626 ≤ d
                  ·
                    have : d = 645626 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 645625 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645621 ≤ d
              ·
                by_cases h : 645623 ≤ d
                ·
                  by_cases h : 645624 ≤ d
                  ·
                    have : d = 645624 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645623 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645622 ≤ d
                  ·
                    have : d = 645622 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645621 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645619 ≤ d
                ·
                  by_cases h : 645620 ≤ d
                  ·
                    have : d = 645620 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 645619 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645618 ≤ d
                  ·
                    have : d = 645618 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1615799333)
      right
      exact ⟨1615153715, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645617 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 645609 ≤ d
            ·
              by_cases h : 645613 ≤ d
              ·
                by_cases h : 645615 ≤ d
                ·
                  by_cases h : 645616 ≤ d
                  ·
                    have : d = 645616 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645615 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645614 ≤ d
                  ·
                    have : d = 645614 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645613 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645611 ≤ d
                ·
                  by_cases h : 645612 ≤ d
                  ·
                    have : d = 645612 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 67)
      exact by decide
                  ·
                    have : d = 645611 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645610 ≤ d
                  ·
                    have : d = 645610 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645609 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645605 ≤ d
              ·
                by_cases h : 645607 ≤ d
                ·
                  by_cases h : 645608 ≤ d
                  ·
                    have : d = 645608 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645607 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645606 ≤ d
                  ·
                    have : d = 645606 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 645605 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645603 ≤ d
                ·
                  by_cases h : 645604 ≤ d
                  ·
                    have : d = 645604 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645603 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645602 ≤ d
                  ·
                    have : d = 645602 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645601 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 645585 ≤ d
          ·
            by_cases h : 645593 ≤ d
            ·
              by_cases h : 645597 ≤ d
              ·
                by_cases h : 645599 ≤ d
                ·
                  by_cases h : 645600 ≤ d
                  ·
                    have : d = 645600 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 269)
      exact by decide
                  ·
                    have : d = 645599 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645598 ≤ d
                  ·
                    have : d = 645598 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645597 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645595 ≤ d
                ·
                  by_cases h : 645596 ≤ d
                  ·
                    have : d = 645596 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23057)
      exact by decide
                  ·
                    have : d = 645595 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645594 ≤ d
                  ·
                    have : d = 645594 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645593 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645589 ≤ d
              ·
                by_cases h : 645591 ≤ d
                ·
                  by_cases h : 645592 ≤ d
                  ·
                    have : d = 645592 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645591 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645590 ≤ d
                  ·
                    have : d = 645590 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5869)
      exact by decide
                  ·
                    have : d = 645589 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645587 ≤ d
                ·
                  by_cases h : 645588 ≤ d
                  ·
                    have : d = 645588 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645587 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645586 ≤ d
                  ·
                    have : d = 645586 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645585 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 645577 ≤ d
            ·
              by_cases h : 645581 ≤ d
              ·
                by_cases h : 645583 ≤ d
                ·
                  by_cases h : 645584 ≤ d
                  ·
                    have : d = 645584 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645583 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645582 ≤ d
                  ·
                    have : d = 645582 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 645581 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645579 ≤ d
                ·
                  by_cases h : 645580 ≤ d
                  ·
                    have : d = 645580 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645579 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645578 ≤ d
                  ·
                    have : d = 645578 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 59)
      exact by decide
                  ·
                    have : d = 645577 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645573 ≤ d
              ·
                by_cases h : 645575 ≤ d
                ·
                  by_cases h : 645576 ≤ d
                  ·
                    have : d = 645576 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 645575 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645574 ≤ d
                  ·
                    have : d = 645574 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645573 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645571 ≤ d
                ·
                  by_cases h : 645572 ≤ d
                  ·
                    have : d = 645572 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 251)
      exact by decide
                  ·
                    have : d = 645571 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645570 ≤ d
                  ·
                    have : d = 645570 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 797)
      exact by decide
                  ·
                    have : d = 645569 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 645537 ≤ d
        ·
          by_cases h : 645553 ≤ d
          ·
            by_cases h : 645561 ≤ d
            ·
              by_cases h : 645565 ≤ d
              ·
                by_cases h : 645567 ≤ d
                ·
                  by_cases h : 645568 ≤ d
                  ·
                    have : d = 645568 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645567 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645566 ≤ d
                  ·
                    have : d = 645566 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 263729)
      right
      exact ⟨145621, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645565 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645563 ≤ d
                ·
                  by_cases h : 645564 ≤ d
                  ·
                    have : d = 645564 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645563 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645562 ≤ d
                  ·
                    have : d = 645562 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645561 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645557 ≤ d
              ·
                by_cases h : 645559 ≤ d
                ·
                  by_cases h : 645560 ≤ d
                  ·
                    have : d = 645560 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645559 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645558 ≤ d
                  ·
                    have : d = 645558 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 645557 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645555 ≤ d
                ·
                  by_cases h : 645556 ≤ d
                  ·
                    have : d = 645556 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645555 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645554 ≤ d
                  ·
                    have : d = 645554 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645553 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 645545 ≤ d
            ·
              by_cases h : 645549 ≤ d
              ·
                by_cases h : 645551 ≤ d
                ·
                  by_cases h : 645552 ≤ d
                  ·
                    have : d = 645552 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 4483)
      exact by decide
                  ·
                    have : d = 645551 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645550 ≤ d
                  ·
                    have : d = 645550 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645549 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645547 ≤ d
                ·
                  by_cases h : 645548 ≤ d
                  ·
                    have : d = 645548 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 323903)
      right
      exact ⟨2258, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645547 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645546 ≤ d
                  ·
                    have : d = 645546 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645545 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645541 ≤ d
              ·
                by_cases h : 645543 ≤ d
                ·
                  by_cases h : 645544 ≤ d
                  ·
                    have : d = 645544 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645543 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645542 ≤ d
                  ·
                    have : d = 645542 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645541 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645539 ≤ d
                ·
                  by_cases h : 645540 ≤ d
                  ·
                    have : d = 645540 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 645539 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645538 ≤ d
                  ·
                    have : d = 645538 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645537 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 645521 ≤ d
          ·
            by_cases h : 645529 ≤ d
            ·
              by_cases h : 645533 ≤ d
              ·
                by_cases h : 645535 ≤ d
                ·
                  by_cases h : 645536 ≤ d
                  ·
                    have : d = 645536 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 20173)
      exact by decide
                  ·
                    have : d = 645535 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645534 ≤ d
                  ·
                    have : d = 645534 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645533 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645531 ≤ d
                ·
                  by_cases h : 645532 ≤ d
                  ·
                    have : d = 645532 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645531 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645530 ≤ d
                  ·
                    have : d = 645530 := by omega
                    subst d
      exact fullRecordGapTerm10701_not_prime
                  ·
                    have : d = 645529 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645525 ≤ d
              ·
                by_cases h : 645527 ≤ d
                ·
                  by_cases h : 645528 ≤ d
                  ·
                    have : d = 645528 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 645527 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645526 ≤ d
                  ·
                    have : d = 645526 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645525 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645523 ≤ d
                ·
                  by_cases h : 645524 ≤ d
                  ·
                    have : d = 645524 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645523 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645522 ≤ d
                  ·
                    have : d = 645522 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 271)
      exact by decide
                  ·
                    have : d = 645521 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 645513 ≤ d
            ·
              by_cases h : 645517 ≤ d
              ·
                by_cases h : 645519 ≤ d
                ·
                  by_cases h : 645520 ≤ d
                  ·
                    have : d = 645520 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645519 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645518 ≤ d
                  ·
                    have : d = 645518 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645517 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645515 ≤ d
                ·
                  by_cases h : 645516 ≤ d
                  ·
                    have : d = 645516 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 43)
      exact by decide
                  ·
                    have : d = 645515 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645514 ≤ d
                  ·
                    have : d = 645514 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645513 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645509 ≤ d
              ·
                by_cases h : 645511 ≤ d
                ·
                  by_cases h : 645512 ≤ d
                  ·
                    have : d = 645512 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11527)
      exact by decide
                  ·
                    have : d = 645511 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645510 ≤ d
                  ·
                    have : d = 645510 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 21517)
      exact by decide
                  ·
                    have : d = 645509 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645507 ≤ d
                ·
                  by_cases h : 645508 ≤ d
                  ·
                    have : d = 645508 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645507 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645506 ≤ d
                  ·
                    have : d = 645506 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 645505 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 645441 ≤ d
      ·
        by_cases h : 645473 ≤ d
        ·
          by_cases h : 645489 ≤ d
          ·
            by_cases h : 645497 ≤ d
            ·
              by_cases h : 645501 ≤ d
              ·
                by_cases h : 645503 ≤ d
                ·
                  by_cases h : 645504 ≤ d
                  ·
                    have : d = 645504 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645503 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645502 ≤ d
                  ·
                    have : d = 645502 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645501 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645499 ≤ d
                ·
                  by_cases h : 645500 ≤ d
                  ·
                    have : d = 645500 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1291)
      exact by decide
                  ·
                    have : d = 645499 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645498 ≤ d
                  ·
                    have : d = 645498 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645497 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645493 ≤ d
              ·
                by_cases h : 645495 ≤ d
                ·
                  by_cases h : 645496 ≤ d
                  ·
                    have : d = 645496 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645495 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645494 ≤ d
                  ·
                    have : d = 645494 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645493 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645491 ≤ d
                ·
                  by_cases h : 645492 ≤ d
                  ·
                    have : d = 645492 := by omega
                    subst d
      exact fullRecordGapTerm10700_not_prime
                  ·
                    have : d = 645491 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645490 ≤ d
                  ·
                    have : d = 645490 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645489 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 645481 ≤ d
            ·
              by_cases h : 645485 ≤ d
              ·
                by_cases h : 645487 ≤ d
                ·
                  by_cases h : 645488 ≤ d
                  ·
                    have : d = 645488 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 40343)
      exact by decide
                  ·
                    have : d = 645487 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645486 ≤ d
                  ·
                    have : d = 645486 := by omega
                    subst d
      exact fullRecordGapTerm10699_not_prime
                  ·
                    have : d = 645485 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645483 ≤ d
                ·
                  by_cases h : 645484 ≤ d
                  ·
                    have : d = 645484 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645483 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645482 ≤ d
                  ·
                    have : d = 645482 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 645481 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645477 ≤ d
              ·
                by_cases h : 645479 ≤ d
                ·
                  by_cases h : 645480 ≤ d
                  ·
                    have : d = 645480 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 163)
      exact by decide
                  ·
                    have : d = 645479 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645478 ≤ d
                  ·
                    have : d = 645478 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645477 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645475 ≤ d
                ·
                  by_cases h : 645476 ≤ d
                  ·
                    have : d = 645476 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645475 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645474 ≤ d
                  ·
                    have : d = 645474 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645473 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 645457 ≤ d
          ·
            by_cases h : 645465 ≤ d
            ·
              by_cases h : 645469 ≤ d
              ·
                by_cases h : 645471 ≤ d
                ·
                  by_cases h : 645472 ≤ d
                  ·
                    have : d = 645472 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645471 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645470 ≤ d
                  ·
                    have : d = 645470 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 9221)
      exact by decide
                  ·
                    have : d = 645469 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645467 ≤ d
                ·
                  by_cases h : 645468 ≤ d
                  ·
                    have : d = 645468 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 645467 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645466 ≤ d
                  ·
                    have : d = 645466 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645465 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645461 ≤ d
              ·
                by_cases h : 645463 ≤ d
                ·
                  by_cases h : 645464 ≤ d
                  ·
                    have : d = 645464 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645463 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645462 ≤ d
                  ·
                    have : d = 645462 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645461 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645459 ≤ d
                ·
                  by_cases h : 645460 ≤ d
                  ·
                    have : d = 645460 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645459 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645458 ≤ d
                  ·
                    have : d = 645458 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29339)
      exact by decide
                  ·
                    have : d = 645457 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 645449 ≤ d
            ·
              by_cases h : 645453 ≤ d
              ·
                by_cases h : 645455 ≤ d
                ·
                  by_cases h : 645456 ≤ d
                  ·
                    have : d = 645456 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 645455 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645454 ≤ d
                  ·
                    have : d = 645454 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645453 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645451 ≤ d
                ·
                  by_cases h : 645452 ≤ d
                  ·
                    have : d = 645452 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1817087)
      right
      exact ⟨1171635, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645451 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645450 ≤ d
                  ·
                    have : d = 645450 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 645449 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645445 ≤ d
              ·
                by_cases h : 645447 ≤ d
                ·
                  by_cases h : 645448 ≤ d
                  ·
                    have : d = 645448 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645447 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645446 ≤ d
                  ·
                    have : d = 645446 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 181)
      exact by decide
                  ·
                    have : d = 645445 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645443 ≤ d
                ·
                  by_cases h : 645444 ≤ d
                  ·
                    have : d = 645444 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645443 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645442 ≤ d
                  ·
                    have : d = 645442 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645441 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 645409 ≤ d
        ·
          by_cases h : 645425 ≤ d
          ·
            by_cases h : 645433 ≤ d
            ·
              by_cases h : 645437 ≤ d
              ·
                by_cases h : 645439 ≤ d
                ·
                  by_cases h : 645440 ≤ d
                  ·
                    have : d = 645440 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2017)
      exact by decide
                  ·
                    have : d = 645439 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645438 ≤ d
                  ·
                    have : d = 645438 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 97)
      exact by decide
                  ·
                    have : d = 645437 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645435 ≤ d
                ·
                  by_cases h : 645436 ≤ d
                  ·
                    have : d = 645436 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645435 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645434 ≤ d
                  ·
                    have : d = 645434 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645433 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645429 ≤ d
              ·
                by_cases h : 645431 ≤ d
                ·
                  by_cases h : 645432 ≤ d
                  ·
                    have : d = 645432 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645431 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645430 ≤ d
                  ·
                    have : d = 645430 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645429 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645427 ≤ d
                ·
                  by_cases h : 645428 ≤ d
                  ·
                    have : d = 645428 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 645427 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645426 ≤ d
                  ·
                    have : d = 645426 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 645425 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 645417 ≤ d
            ·
              by_cases h : 645421 ≤ d
              ·
                by_cases h : 645423 ≤ d
                ·
                  by_cases h : 645424 ≤ d
                  ·
                    have : d = 645424 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645423 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645422 ≤ d
                  ·
                    have : d = 645422 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 645421 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645419 ≤ d
                ·
                  by_cases h : 645420 ≤ d
                  ·
                    have : d = 645420 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645419 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645418 ≤ d
                  ·
                    have : d = 645418 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645417 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645413 ≤ d
              ·
                by_cases h : 645415 ≤ d
                ·
                  by_cases h : 645416 ≤ d
                  ·
                    have : d = 645416 := by omega
                    subst d
      exact fullRecordGapTerm10698_not_prime
                  ·
                    have : d = 645415 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645414 ≤ d
                  ·
                    have : d = 645414 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645413 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645411 ≤ d
                ·
                  by_cases h : 645412 ≤ d
                  ·
                    have : d = 645412 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645411 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645410 ≤ d
                  ·
                    have : d = 645410 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645409 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 645393 ≤ d
          ·
            by_cases h : 645401 ≤ d
            ·
              by_cases h : 645405 ≤ d
              ·
                by_cases h : 645407 ≤ d
                ·
                  by_cases h : 645408 ≤ d
                  ·
                    have : d = 645408 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 83)
      exact by decide
                  ·
                    have : d = 645407 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645406 ≤ d
                  ·
                    have : d = 645406 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645405 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645403 ≤ d
                ·
                  by_cases h : 645404 ≤ d
                  ·
                    have : d = 645404 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645403 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645402 ≤ d
                  ·
                    have : d = 645402 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 263)
      exact by decide
                  ·
                    have : d = 645401 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645397 ≤ d
              ·
                by_cases h : 645399 ≤ d
                ·
                  by_cases h : 645400 ≤ d
                  ·
                    have : d = 645400 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645399 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645398 ≤ d
                  ·
                    have : d = 645398 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 645397 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645395 ≤ d
                ·
                  by_cases h : 645396 ≤ d
                  ·
                    have : d = 645396 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 68643031)
      right
      exact ⟨67997635, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645395 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645394 ≤ d
                  ·
                    have : d = 645394 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645393 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 645385 ≤ d
            ·
              by_cases h : 645389 ≤ d
              ·
                by_cases h : 645391 ≤ d
                ·
                  by_cases h : 645392 ≤ d
                  ·
                    have : d = 645392 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645391 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645390 ≤ d
                  ·
                    have : d = 645390 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 71)
      exact by decide
                  ·
                    have : d = 645389 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645387 ≤ d
                ·
                  by_cases h : 645388 ≤ d
                  ·
                    have : d = 645388 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645387 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645386 ≤ d
                  ·
                    have : d = 645386 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 51461)
      right
      exact ⟨23607, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645385 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645381 ≤ d
              ·
                by_cases h : 645383 ≤ d
                ·
                  by_cases h : 645384 ≤ d
                  ·
                    have : d = 645384 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645383 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645382 ≤ d
                  ·
                    have : d = 645382 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645381 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645379 ≤ d
                ·
                  by_cases h : 645380 ≤ d
                  ·
                    have : d = 645380 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 645379 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645378 ≤ d
                  ·
                    have : d = 645378 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645377 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
  ·
    by_cases h : 645249 ≤ d
    ·
      by_cases h : 645313 ≤ d
      ·
        by_cases h : 645345 ≤ d
        ·
          by_cases h : 645361 ≤ d
          ·
            by_cases h : 645369 ≤ d
            ·
              by_cases h : 645373 ≤ d
              ·
                by_cases h : 645375 ≤ d
                ·
                  by_cases h : 645376 ≤ d
                  ·
                    have : d = 645376 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645375 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645374 ≤ d
                  ·
                    have : d = 645374 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645373 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645371 ≤ d
                ·
                  by_cases h : 645372 ≤ d
                  ·
                    have : d = 645372 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 645371 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645370 ≤ d
                  ·
                    have : d = 645370 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645369 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645365 ≤ d
              ·
                by_cases h : 645367 ≤ d
                ·
                  by_cases h : 645368 ≤ d
                  ·
                    have : d = 645368 := by omega
                    subst d
      exact fullRecordGapTerm10697_not_prime
                  ·
                    have : d = 645367 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645366 ≤ d
                  ·
                    have : d = 645366 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645365 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645363 ≤ d
                ·
                  by_cases h : 645364 ≤ d
                  ·
                    have : d = 645364 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645363 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645362 ≤ d
                  ·
                    have : d = 645362 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 223)
      exact by decide
                  ·
                    have : d = 645361 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 645353 ≤ d
            ·
              by_cases h : 645357 ≤ d
              ·
                by_cases h : 645359 ≤ d
                ·
                  by_cases h : 645360 ≤ d
                  ·
                    have : d = 645360 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2689)
      exact by decide
                  ·
                    have : d = 645359 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645358 ≤ d
                  ·
                    have : d = 645358 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645357 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645355 ≤ d
                ·
                  by_cases h : 645356 ≤ d
                  ·
                    have : d = 645356 := by omega
                    subst d
      exact fullRecordGapTerm10696_not_prime
                  ·
                    have : d = 645355 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645354 ≤ d
                  ·
                    have : d = 645354 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645353 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645349 ≤ d
              ·
                by_cases h : 645351 ≤ d
                ·
                  by_cases h : 645352 ≤ d
                  ·
                    have : d = 645352 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645351 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645350 ≤ d
                  ·
                    have : d = 645350 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645349 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645347 ≤ d
                ·
                  by_cases h : 645348 ≤ d
                  ·
                    have : d = 645348 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 4889)
      exact by decide
                  ·
                    have : d = 645347 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645346 ≤ d
                  ·
                    have : d = 645346 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645345 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 645329 ≤ d
          ·
            by_cases h : 645337 ≤ d
            ·
              by_cases h : 645341 ≤ d
              ·
                by_cases h : 645343 ≤ d
                ·
                  by_cases h : 645344 ≤ d
                  ·
                    have : d = 645344 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645343 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645342 ≤ d
                  ·
                    have : d = 645342 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 59)
      exact by decide
                  ·
                    have : d = 645341 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645339 ≤ d
                ·
                  by_cases h : 645340 ≤ d
                  ·
                    have : d = 645340 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645339 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645338 ≤ d
                  ·
                    have : d = 645338 := by omega
                    subst d
      exact fullRecordGapTerm10695_not_prime
                  ·
                    have : d = 645337 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645333 ≤ d
              ·
                by_cases h : 645335 ≤ d
                ·
                  by_cases h : 645336 ≤ d
                  ·
                    have : d = 645336 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645335 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645334 ≤ d
                  ·
                    have : d = 645334 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645333 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645331 ≤ d
                ·
                  by_cases h : 645332 ≤ d
                  ·
                    have : d = 645332 := by omega
                    subst d
      exact fullRecordGapTerm10694_not_prime
                  ·
                    have : d = 645331 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645330 ≤ d
                  ·
                    have : d = 645330 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 439)
      exact by decide
                  ·
                    have : d = 645329 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 645321 ≤ d
            ·
              by_cases h : 645325 ≤ d
              ·
                by_cases h : 645327 ≤ d
                ·
                  by_cases h : 645328 ≤ d
                  ·
                    have : d = 645328 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645327 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645326 ≤ d
                  ·
                    have : d = 645326 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29333)
      exact by decide
                  ·
                    have : d = 645325 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645323 ≤ d
                ·
                  by_cases h : 645324 ≤ d
                  ·
                    have : d = 645324 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645323 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645322 ≤ d
                  ·
                    have : d = 645322 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645321 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645317 ≤ d
              ·
                by_cases h : 645319 ≤ d
                ·
                  by_cases h : 645320 ≤ d
                  ·
                    have : d = 645320 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 645319 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645318 ≤ d
                  ·
                    have : d = 645318 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 35851)
      exact by decide
                  ·
                    have : d = 645317 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645315 ≤ d
                ·
                  by_cases h : 645316 ≤ d
                  ·
                    have : d = 645316 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645315 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645314 ≤ d
                  ·
                    have : d = 645314 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645313 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 645281 ≤ d
        ·
          by_cases h : 645297 ≤ d
          ·
            by_cases h : 645305 ≤ d
            ·
              by_cases h : 645309 ≤ d
              ·
                by_cases h : 645311 ≤ d
                ·
                  by_cases h : 645312 ≤ d
                  ·
                    have : d = 645312 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3361)
      exact by decide
                  ·
                    have : d = 645311 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645310 ≤ d
                  ·
                    have : d = 645310 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645309 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645307 ≤ d
                ·
                  by_cases h : 645308 ≤ d
                  ·
                    have : d = 645308 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645307 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645306 ≤ d
                  ·
                    have : d = 645306 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 131)
      exact by decide
                  ·
                    have : d = 645305 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645301 ≤ d
              ·
                by_cases h : 645303 ≤ d
                ·
                  by_cases h : 645304 ≤ d
                  ·
                    have : d = 645304 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645303 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645302 ≤ d
                  ·
                    have : d = 645302 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 246689)
      right
      exact ⟨94765, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645301 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645299 ≤ d
                ·
                  by_cases h : 645300 ≤ d
                  ·
                    have : d = 645300 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645299 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645298 ≤ d
                  ·
                    have : d = 645298 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645297 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 645289 ≤ d
            ·
              by_cases h : 645293 ≤ d
              ·
                by_cases h : 645295 ≤ d
                ·
                  by_cases h : 645296 ≤ d
                  ·
                    have : d = 645296 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 645295 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645294 ≤ d
                  ·
                    have : d = 645294 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645293 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645291 ≤ d
                ·
                  by_cases h : 645292 ≤ d
                  ·
                    have : d = 645292 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645291 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645290 ≤ d
                  ·
                    have : d = 645290 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 173)
      exact by decide
                  ·
                    have : d = 645289 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645285 ≤ d
              ·
                by_cases h : 645287 ≤ d
                ·
                  by_cases h : 645288 ≤ d
                  ·
                    have : d = 645288 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 645287 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645286 ≤ d
                  ·
                    have : d = 645286 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645285 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645283 ≤ d
                ·
                  by_cases h : 645284 ≤ d
                  ·
                    have : d = 645284 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645283 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645282 ≤ d
                  ·
                    have : d = 645282 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3259)
      exact by decide
                  ·
                    have : d = 645281 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 645265 ≤ d
          ·
            by_cases h : 645273 ≤ d
            ·
              by_cases h : 645277 ≤ d
              ·
                by_cases h : 645279 ≤ d
                ·
                  by_cases h : 645280 ≤ d
                  ·
                    have : d = 645280 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645279 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645278 ≤ d
                  ·
                    have : d = 645278 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645277 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645275 ≤ d
                ·
                  by_cases h : 645276 ≤ d
                  ·
                    have : d = 645276 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 119881)
      right
      exact ⟨74010, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645275 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645274 ≤ d
                  ·
                    have : d = 645274 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645273 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645269 ≤ d
              ·
                by_cases h : 645271 ≤ d
                ·
                  by_cases h : 645272 ≤ d
                  ·
                    have : d = 645272 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 79)
      exact by decide
                  ·
                    have : d = 645271 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645270 ≤ d
                  ·
                    have : d = 645270 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 137)
      exact by decide
                  ·
                    have : d = 645269 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645267 ≤ d
                ·
                  by_cases h : 645268 ≤ d
                  ·
                    have : d = 645268 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645267 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645266 ≤ d
                  ·
                    have : d = 645266 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645265 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 645257 ≤ d
            ·
              by_cases h : 645261 ≤ d
              ·
                by_cases h : 645263 ≤ d
                ·
                  by_cases h : 645264 ≤ d
                  ·
                    have : d = 645264 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645263 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645262 ≤ d
                  ·
                    have : d = 645262 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645261 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645259 ≤ d
                ·
                  by_cases h : 645260 ≤ d
                  ·
                    have : d = 645260 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 419)
      exact by decide
                  ·
                    have : d = 645259 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645258 ≤ d
                  ·
                    have : d = 645258 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 41)
      exact by decide
                  ·
                    have : d = 645257 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645253 ≤ d
              ·
                by_cases h : 645255 ≤ d
                ·
                  by_cases h : 645256 ≤ d
                  ·
                    have : d = 645256 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645255 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645254 ≤ d
                  ·
                    have : d = 645254 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645253 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645251 ≤ d
                ·
                  by_cases h : 645252 ≤ d
                  ·
                    have : d = 645252 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645251 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645250 ≤ d
                  ·
                    have : d = 645250 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645249 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 645185 ≤ d
      ·
        by_cases h : 645217 ≤ d
        ·
          by_cases h : 645233 ≤ d
          ·
            by_cases h : 645241 ≤ d
            ·
              by_cases h : 645245 ≤ d
              ·
                by_cases h : 645247 ≤ d
                ·
                  by_cases h : 645248 ≤ d
                  ·
                    have : d = 645248 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 71)
      exact by decide
                  ·
                    have : d = 645247 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645246 ≤ d
                  ·
                    have : d = 645246 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 569)
      exact by decide
                  ·
                    have : d = 645245 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645243 ≤ d
                ·
                  by_cases h : 645244 ≤ d
                  ·
                    have : d = 645244 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645243 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645242 ≤ d
                  ·
                    have : d = 645242 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 645241 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645237 ≤ d
              ·
                by_cases h : 645239 ≤ d
                ·
                  by_cases h : 645240 ≤ d
                  ·
                    have : d = 645240 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 645239 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645238 ≤ d
                  ·
                    have : d = 645238 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645237 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645235 ≤ d
                ·
                  by_cases h : 645236 ≤ d
                  ·
                    have : d = 645236 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 110680463)
      right
      exact ⟨110035227, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645235 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645234 ≤ d
                  ·
                    have : d = 645234 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645233 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 645225 ≤ d
            ·
              by_cases h : 645229 ≤ d
              ·
                by_cases h : 645231 ≤ d
                ·
                  by_cases h : 645232 ≤ d
                  ·
                    have : d = 645232 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645231 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645230 ≤ d
                  ·
                    have : d = 645230 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 113)
      exact by decide
                  ·
                    have : d = 645229 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645227 ≤ d
                ·
                  by_cases h : 645228 ≤ d
                  ·
                    have : d = 645228 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17923)
      exact by decide
                  ·
                    have : d = 645227 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645226 ≤ d
                  ·
                    have : d = 645226 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645225 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645221 ≤ d
              ·
                by_cases h : 645223 ≤ d
                ·
                  by_cases h : 645224 ≤ d
                  ·
                    have : d = 645224 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645223 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645222 ≤ d
                  ·
                    have : d = 645222 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 53)
      exact by decide
                  ·
                    have : d = 645221 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645219 ≤ d
                ·
                  by_cases h : 645220 ≤ d
                  ·
                    have : d = 645220 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645219 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645218 ≤ d
                  ·
                    have : d = 645218 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 645217 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 645201 ≤ d
          ·
            by_cases h : 645209 ≤ d
            ·
              by_cases h : 645213 ≤ d
              ·
                by_cases h : 645215 ≤ d
                ·
                  by_cases h : 645216 ≤ d
                  ·
                    have : d = 645216 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 645215 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645214 ≤ d
                  ·
                    have : d = 645214 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645213 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645211 ≤ d
                ·
                  by_cases h : 645212 ≤ d
                  ·
                    have : d = 645212 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645211 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645210 ≤ d
                  ·
                    have : d = 645210 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645209 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645205 ≤ d
              ·
                by_cases h : 645207 ≤ d
                ·
                  by_cases h : 645208 ≤ d
                  ·
                    have : d = 645208 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645207 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645206 ≤ d
                  ·
                    have : d = 645206 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 645205 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645203 ≤ d
                ·
                  by_cases h : 645204 ≤ d
                  ·
                    have : d = 645204 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645203 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645202 ≤ d
                  ·
                    have : d = 645202 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645201 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 645193 ≤ d
            ·
              by_cases h : 645197 ≤ d
              ·
                by_cases h : 645199 ≤ d
                ·
                  by_cases h : 645200 ≤ d
                  ·
                    have : d = 645200 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1613)
      exact by decide
                  ·
                    have : d = 645199 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645198 ≤ d
                  ·
                    have : d = 645198 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 191)
      exact by decide
                  ·
                    have : d = 645197 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645195 ≤ d
                ·
                  by_cases h : 645196 ≤ d
                  ·
                    have : d = 645196 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645195 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645194 ≤ d
                  ·
                    have : d = 645194 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645193 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645189 ≤ d
              ·
                by_cases h : 645191 ≤ d
                ·
                  by_cases h : 645192 ≤ d
                  ·
                    have : d = 645192 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 645191 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645190 ≤ d
                  ·
                    have : d = 645190 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645189 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645187 ≤ d
                ·
                  by_cases h : 645188 ≤ d
                  ·
                    have : d = 645188 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 101)
      exact by decide
                  ·
                    have : d = 645187 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645186 ≤ d
                  ·
                    have : d = 645186 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 293)
      exact by decide
                  ·
                    have : d = 645185 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 645153 ≤ d
        ·
          by_cases h : 645169 ≤ d
          ·
            by_cases h : 645177 ≤ d
            ·
              by_cases h : 645181 ≤ d
              ·
                by_cases h : 645183 ≤ d
                ·
                  by_cases h : 645184 ≤ d
                  ·
                    have : d = 645184 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645183 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645182 ≤ d
                  ·
                    have : d = 645182 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645181 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645179 ≤ d
                ·
                  by_cases h : 645180 ≤ d
                  ·
                    have : d = 645180 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 10753)
      exact by decide
                  ·
                    have : d = 645179 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645178 ≤ d
                  ·
                    have : d = 645178 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645177 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645173 ≤ d
              ·
                by_cases h : 645175 ≤ d
                ·
                  by_cases h : 645176 ≤ d
                  ·
                    have : d = 645176 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 41)
      exact by decide
                  ·
                    have : d = 645175 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645174 ≤ d
                  ·
                    have : d = 645174 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645173 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645171 ≤ d
                ·
                  by_cases h : 645172 ≤ d
                  ·
                    have : d = 645172 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645171 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645170 ≤ d
                  ·
                    have : d = 645170 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 149)
      exact by decide
                  ·
                    have : d = 645169 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 645161 ≤ d
            ·
              by_cases h : 645165 ≤ d
              ·
                by_cases h : 645167 ≤ d
                ·
                  by_cases h : 645168 ≤ d
                  ·
                    have : d = 645168 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645167 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645166 ≤ d
                  ·
                    have : d = 645166 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645165 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645163 ≤ d
                ·
                  by_cases h : 645164 ≤ d
                  ·
                    have : d = 645164 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645163 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645162 ≤ d
                  ·
                    have : d = 645162 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 15361)
      exact by decide
                  ·
                    have : d = 645161 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645157 ≤ d
              ·
                by_cases h : 645159 ≤ d
                ·
                  by_cases h : 645160 ≤ d
                  ·
                    have : d = 645160 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645159 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645158 ≤ d
                  ·
                    have : d = 645158 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 199)
      exact by decide
                  ·
                    have : d = 645157 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645155 ≤ d
                ·
                  by_cases h : 645156 ≤ d
                  ·
                    have : d = 645156 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17921)
      exact by decide
                  ·
                    have : d = 645155 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645154 ≤ d
                  ·
                    have : d = 645154 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645153 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 645137 ≤ d
          ·
            by_cases h : 645145 ≤ d
            ·
              by_cases h : 645149 ≤ d
              ·
                by_cases h : 645151 ≤ d
                ·
                  by_cases h : 645152 ≤ d
                  ·
                    have : d = 645152 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 20161)
      exact by decide
                  ·
                    have : d = 645151 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645150 ≤ d
                  ·
                    have : d = 645150 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 645149 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645147 ≤ d
                ·
                  by_cases h : 645148 ≤ d
                  ·
                    have : d = 645148 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645147 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645146 ≤ d
                  ·
                    have : d = 645146 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645145 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645141 ≤ d
              ·
                by_cases h : 645143 ≤ d
                ·
                  by_cases h : 645144 ≤ d
                  ·
                    have : d = 645144 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645143 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645142 ≤ d
                  ·
                    have : d = 645142 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645141 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645139 ≤ d
                ·
                  by_cases h : 645140 ≤ d
                  ·
                    have : d = 645140 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645139 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645138 ≤ d
                  ·
                    have : d = 645138 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 645137 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 645129 ≤ d
            ·
              by_cases h : 645133 ≤ d
              ·
                by_cases h : 645135 ≤ d
                ·
                  by_cases h : 645136 ≤ d
                  ·
                    have : d = 645136 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645135 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645134 ≤ d
                  ·
                    have : d = 645134 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645133 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645131 ≤ d
                ·
                  by_cases h : 645132 ≤ d
                  ·
                    have : d = 645132 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 645131 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645130 ≤ d
                  ·
                    have : d = 645130 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645129 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 645125 ≤ d
              ·
                by_cases h : 645127 ≤ d
                ·
                  by_cases h : 645128 ≤ d
                  ·
                    have : d = 645128 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7331)
      exact by decide
                  ·
                    have : d = 645127 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645126 ≤ d
                  ·
                    have : d = 645126 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645125 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 645123 ≤ d
                ·
                  by_cases h : 645124 ≤ d
                  ·
                    have : d = 645124 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 645123 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 645122 ≤ d
                  ·
                    have : d = 645122 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 47)
      exact by decide
                  ·
                    have : d = 645121 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩

end PrimeFactorUnimodality
