import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapFermat

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

theorem fullRecordGapAddBlock_part1697 (d : Nat) (412161 ≤ d) (d ≤ 412672) : ¬(recordGapCenter + d).Prime := by
  by_cases h : 412417 ≤ d
  ·
    by_cases h : 412545 ≤ d
    ·
      by_cases h : 412609 ≤ d
      ·
        by_cases h : 412641 ≤ d
        ·
          by_cases h : 412657 ≤ d
          ·
            by_cases h : 412665 ≤ d
            ·
              by_cases h : 412669 ≤ d
              ·
                by_cases h : 412671 ≤ d
                ·
                  by_cases h : 412672 ≤ d
                  ·
                    have : d = 412672 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412671 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412670 ≤ d
                  ·
                    have : d = 412670 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412669 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412667 ≤ d
                ·
                  by_cases h : 412668 ≤ d
                  ·
                    have : d = 412668 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3821)
      exact by decide
                  ·
                    have : d = 412667 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412666 ≤ d
                  ·
                    have : d = 412666 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412665 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412661 ≤ d
              ·
                by_cases h : 412663 ≤ d
                ·
                  by_cases h : 412664 ≤ d
                  ·
                    have : d = 412664 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412663 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412662 ≤ d
                  ·
                    have : d = 412662 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11527806343)
      right
      exact ⟨11527393681, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412661 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412659 ≤ d
                ·
                  by_cases h : 412660 ≤ d
                  ·
                    have : d = 412660 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412659 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412658 ≤ d
                  ·
                    have : d = 412658 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 412657 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 412649 ≤ d
            ·
              by_cases h : 412653 ≤ d
              ·
                by_cases h : 412655 ≤ d
                ·
                  by_cases h : 412656 ≤ d
                  ·
                    have : d = 412656 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412655 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412654 ≤ d
                  ·
                    have : d = 412654 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412653 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412651 ≤ d
                ·
                  by_cases h : 412652 ≤ d
                  ·
                    have : d = 412652 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 71)
      exact by decide
                  ·
                    have : d = 412651 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412650 ≤ d
                  ·
                    have : d = 412650 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412649 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412645 ≤ d
              ·
                by_cases h : 412647 ≤ d
                ·
                  by_cases h : 412648 ≤ d
                  ·
                    have : d = 412648 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412647 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412646 ≤ d
                  ·
                    have : d = 412646 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 412645 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412643 ≤ d
                ·
                  by_cases h : 412644 ≤ d
                  ·
                    have : d = 412644 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412643 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412642 ≤ d
                  ·
                    have : d = 412642 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412641 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 412625 ≤ d
          ·
            by_cases h : 412633 ≤ d
            ·
              by_cases h : 412637 ≤ d
              ·
                by_cases h : 412639 ≤ d
                ·
                  by_cases h : 412640 ≤ d
                  ·
                    have : d = 412640 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2579)
      exact by decide
                  ·
                    have : d = 412639 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412638 ≤ d
                  ·
                    have : d = 412638 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 97)
      exact by decide
                  ·
                    have : d = 412637 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412635 ≤ d
                ·
                  by_cases h : 412636 ≤ d
                  ·
                    have : d = 412636 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412635 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412634 ≤ d
                  ·
                    have : d = 412634 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412633 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412629 ≤ d
              ·
                by_cases h : 412631 ≤ d
                ·
                  by_cases h : 412632 ≤ d
                  ·
                    have : d = 412632 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 521)
      exact by decide
                  ·
                    have : d = 412631 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412630 ≤ d
                  ·
                    have : d = 412630 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412629 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412627 ≤ d
                ·
                  by_cases h : 412628 ≤ d
                  ·
                    have : d = 412628 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412627 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412626 ≤ d
                  ·
                    have : d = 412626 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 115705999)
      right
      exact ⟨115293373, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412625 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 412617 ≤ d
            ·
              by_cases h : 412621 ≤ d
              ·
                by_cases h : 412623 ≤ d
                ·
                  by_cases h : 412624 ≤ d
                  ·
                    have : d = 412624 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412623 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412622 ≤ d
                  ·
                    have : d = 412622 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29473)
      exact by decide
                  ·
                    have : d = 412621 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412619 ≤ d
                ·
                  by_cases h : 412620 ≤ d
                  ·
                    have : d = 412620 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 412619 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412618 ≤ d
                  ·
                    have : d = 412618 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412617 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412613 ≤ d
              ·
                by_cases h : 412615 ≤ d
                ·
                  by_cases h : 412616 ≤ d
                  ·
                    have : d = 412616 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 508297)
      right
      exact ⟨95681, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412615 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412614 ≤ d
                  ·
                    have : d = 412614 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412613 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412611 ≤ d
                ·
                  by_cases h : 412612 ≤ d
                  ·
                    have : d = 412612 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412611 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412610 ≤ d
                  ·
                    have : d = 412610 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 412609 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 412577 ≤ d
        ·
          by_cases h : 412593 ≤ d
          ·
            by_cases h : 412601 ≤ d
            ·
              by_cases h : 412605 ≤ d
              ·
                by_cases h : 412607 ≤ d
                ·
                  by_cases h : 412608 ≤ d
                  ·
                    have : d = 412608 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 307)
      exact by decide
                  ·
                    have : d = 412607 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412606 ≤ d
                  ·
                    have : d = 412606 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412605 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412603 ≤ d
                ·
                  by_cases h : 412604 ≤ d
                  ·
                    have : d = 412604 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412603 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412602 ≤ d
                  ·
                    have : d = 412602 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 51473)
      right
      exact ⟨50655, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412601 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412597 ≤ d
              ·
                by_cases h : 412599 ≤ d
                ·
                  by_cases h : 412600 ≤ d
                  ·
                    have : d = 412600 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412599 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412598 ≤ d
                  ·
                    have : d = 412598 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 8215099)
      right
      exact ⟨7802501, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412597 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412595 ≤ d
                ·
                  by_cases h : 412596 ≤ d
                  ·
                    have : d = 412596 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 73)
      exact by decide
                  ·
                    have : d = 412595 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412594 ≤ d
                  ·
                    have : d = 412594 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412593 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 412585 ≤ d
            ·
              by_cases h : 412589 ≤ d
              ·
                by_cases h : 412591 ≤ d
                ·
                  by_cases h : 412592 ≤ d
                  ·
                    have : d = 412592 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 107)
      exact by decide
                  ·
                    have : d = 412591 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412590 ≤ d
                  ·
                    have : d = 412590 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 412589 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412587 ≤ d
                ·
                  by_cases h : 412588 ≤ d
                  ·
                    have : d = 412588 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412587 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412586 ≤ d
                  ·
                    have : d = 412586 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412585 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412581 ≤ d
              ·
                by_cases h : 412583 ≤ d
                ·
                  by_cases h : 412584 ≤ d
                  ·
                    have : d = 412584 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412583 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412582 ≤ d
                  ·
                    have : d = 412582 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412581 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412579 ≤ d
                ·
                  by_cases h : 412580 ≤ d
                  ·
                    have : d = 412580 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 421)
      exact by decide
                  ·
                    have : d = 412579 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412578 ≤ d
                  ·
                    have : d = 412578 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 22921)
      exact by decide
                  ·
                    have : d = 412577 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 412561 ≤ d
          ·
            by_cases h : 412569 ≤ d
            ·
              by_cases h : 412573 ≤ d
              ·
                by_cases h : 412575 ≤ d
                ·
                  by_cases h : 412576 ≤ d
                  ·
                    have : d = 412576 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412575 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412574 ≤ d
                  ·
                    have : d = 412574 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412573 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412571 ≤ d
                ·
                  by_cases h : 412572 ≤ d
                  ·
                    have : d = 412572 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412571 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412570 ≤ d
                  ·
                    have : d = 412570 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412569 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412565 ≤ d
              ·
                by_cases h : 412567 ≤ d
                ·
                  by_cases h : 412568 ≤ d
                  ·
                    have : d = 412568 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 412567 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412566 ≤ d
                  ·
                    have : d = 412566 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 412565 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412563 ≤ d
                ·
                  by_cases h : 412564 ≤ d
                  ·
                    have : d = 412564 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412563 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412562 ≤ d
                  ·
                    have : d = 412562 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412561 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 412553 ≤ d
            ·
              by_cases h : 412557 ≤ d
              ·
                by_cases h : 412559 ≤ d
                ·
                  by_cases h : 412560 ≤ d
                  ·
                    have : d = 412560 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 191)
      exact by decide
                  ·
                    have : d = 412559 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412558 ≤ d
                  ·
                    have : d = 412558 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412557 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412555 ≤ d
                ·
                  by_cases h : 412556 ≤ d
                  ·
                    have : d = 412556 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 412555 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412554 ≤ d
                  ·
                    have : d = 412554 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412553 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412549 ≤ d
              ·
                by_cases h : 412551 ≤ d
                ·
                  by_cases h : 412552 ≤ d
                  ·
                    have : d = 412552 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412551 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412550 ≤ d
                  ·
                    have : d = 412550 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 412549 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412547 ≤ d
                ·
                  by_cases h : 412548 ≤ d
                  ·
                    have : d = 412548 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 412547 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412546 ≤ d
                  ·
                    have : d = 412546 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412545 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 412481 ≤ d
      ·
        by_cases h : 412513 ≤ d
        ·
          by_cases h : 412529 ≤ d
          ·
            by_cases h : 412537 ≤ d
            ·
              by_cases h : 412541 ≤ d
              ·
                by_cases h : 412543 ≤ d
                ·
                  by_cases h : 412544 ≤ d
                  ·
                    have : d = 412544 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412543 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412542 ≤ d
                  ·
                    have : d = 412542 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 412541 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412539 ≤ d
                ·
                  by_cases h : 412540 ≤ d
                  ·
                    have : d = 412540 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412539 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412538 ≤ d
                  ·
                    have : d = 412538 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 79)
      exact by decide
                  ·
                    have : d = 412537 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412533 ≤ d
              ·
                by_cases h : 412535 ≤ d
                ·
                  by_cases h : 412536 ≤ d
                  ·
                    have : d = 412536 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17189)
      exact by decide
                  ·
                    have : d = 412535 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412534 ≤ d
                  ·
                    have : d = 412534 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412533 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412531 ≤ d
                ·
                  by_cases h : 412532 ≤ d
                  ·
                    have : d = 412532 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 151)
      exact by decide
                  ·
                    have : d = 412531 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412530 ≤ d
                  ·
                    have : d = 412530 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412529 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 412521 ≤ d
            ·
              by_cases h : 412525 ≤ d
              ·
                by_cases h : 412527 ≤ d
                ·
                  by_cases h : 412528 ≤ d
                  ·
                    have : d = 412528 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412527 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412526 ≤ d
                  ·
                    have : d = 412526 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 22391027)
      right
      exact ⟨21978501, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412525 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412523 ≤ d
                ·
                  by_cases h : 412524 ≤ d
                  ·
                    have : d = 412524 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412523 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412522 ≤ d
                  ·
                    have : d = 412522 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412521 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412517 ≤ d
              ·
                by_cases h : 412519 ≤ d
                ·
                  by_cases h : 412520 ≤ d
                  ·
                    have : d = 412520 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 10313)
      exact by decide
                  ·
                    have : d = 412519 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412518 ≤ d
                  ·
                    have : d = 412518 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412517 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412515 ≤ d
                ·
                  by_cases h : 412516 ≤ d
                  ·
                    have : d = 412516 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412515 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412514 ≤ d
                  ·
                    have : d = 412514 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412513 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 412497 ≤ d
          ·
            by_cases h : 412505 ≤ d
            ·
              by_cases h : 412509 ≤ d
              ·
                by_cases h : 412511 ≤ d
                ·
                  by_cases h : 412512 ≤ d
                  ·
                    have : d = 412512 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 4297)
      exact by decide
                  ·
                    have : d = 412511 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412510 ≤ d
                  ·
                    have : d = 412510 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412509 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412507 ≤ d
                ·
                  by_cases h : 412508 ≤ d
                  ·
                    have : d = 412508 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 281)
      exact by decide
                  ·
                    have : d = 412507 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412506 ≤ d
                  ·
                    have : d = 412506 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7639)
      exact by decide
                  ·
                    have : d = 412505 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412501 ≤ d
              ·
                by_cases h : 412503 ≤ d
                ·
                  by_cases h : 412504 ≤ d
                  ·
                    have : d = 412504 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412503 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412502 ≤ d
                  ·
                    have : d = 412502 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412501 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412499 ≤ d
                ·
                  by_cases h : 412500 ≤ d
                  ·
                    have : d = 412500 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 201769)
      right
      exact ⟨192807, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412499 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412498 ≤ d
                  ·
                    have : d = 412498 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412497 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 412489 ≤ d
            ·
              by_cases h : 412493 ≤ d
              ·
                by_cases h : 412495 ≤ d
                ·
                  by_cases h : 412496 ≤ d
                  ·
                    have : d = 412496 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412495 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412494 ≤ d
                  ·
                    have : d = 412494 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412493 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412491 ≤ d
                ·
                  by_cases h : 412492 ≤ d
                  ·
                    have : d = 412492 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412491 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412490 ≤ d
                  ·
                    have : d = 412490 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 412489 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412485 ≤ d
              ·
                by_cases h : 412487 ≤ d
                ·
                  by_cases h : 412488 ≤ d
                  ·
                    have : d = 412488 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412487 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412486 ≤ d
                  ·
                    have : d = 412486 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412485 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412483 ≤ d
                ·
                  by_cases h : 412484 ≤ d
                  ·
                    have : d = 412484 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412483 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412482 ≤ d
                  ·
                    have : d = 412482 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 412481 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 412449 ≤ d
        ·
          by_cases h : 412465 ≤ d
          ·
            by_cases h : 412473 ≤ d
            ·
              by_cases h : 412477 ≤ d
              ·
                by_cases h : 412479 ≤ d
                ·
                  by_cases h : 412480 ≤ d
                  ·
                    have : d = 412480 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412479 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412478 ≤ d
                  ·
                    have : d = 412478 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 18749)
      exact by decide
                  ·
                    have : d = 412477 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412475 ≤ d
                ·
                  by_cases h : 412476 ≤ d
                  ·
                    have : d = 412476 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 412475 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412474 ≤ d
                  ·
                    have : d = 412474 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412473 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412469 ≤ d
              ·
                by_cases h : 412471 ≤ d
                ·
                  by_cases h : 412472 ≤ d
                  ·
                    have : d = 412472 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 47)
      exact by decide
                  ·
                    have : d = 412471 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412470 ≤ d
                  ·
                    have : d = 412470 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 4583)
      exact by decide
                  ·
                    have : d = 412469 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412467 ≤ d
                ·
                  by_cases h : 412468 ≤ d
                  ·
                    have : d = 412468 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412467 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412466 ≤ d
                  ·
                    have : d = 412466 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 596749273)
      right
      exact ⟨596336807, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412465 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 412457 ≤ d
            ·
              by_cases h : 412461 ≤ d
              ·
                by_cases h : 412463 ≤ d
                ·
                  by_cases h : 412464 ≤ d
                  ·
                    have : d = 412464 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412463 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412462 ≤ d
                  ·
                    have : d = 412462 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412461 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412459 ≤ d
                ·
                  by_cases h : 412460 ≤ d
                  ·
                    have : d = 412460 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412459 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412458 ≤ d
                  ·
                    have : d = 412458 := by omega
                    subst d
      exact fullRecordGapTerm07237_not_prime
                  ·
                    have : d = 412457 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412453 ≤ d
              ·
                by_cases h : 412455 ≤ d
                ·
                  by_cases h : 412456 ≤ d
                  ·
                    have : d = 412456 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412455 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412454 ≤ d
                  ·
                    have : d = 412454 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412453 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412451 ≤ d
                ·
                  by_cases h : 412452 ≤ d
                  ·
                    have : d = 412452 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412451 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412450 ≤ d
                  ·
                    have : d = 412450 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412449 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 412433 ≤ d
          ·
            by_cases h : 412441 ≤ d
            ·
              by_cases h : 412445 ≤ d
              ·
                by_cases h : 412447 ≤ d
                ·
                  by_cases h : 412448 ≤ d
                  ·
                    have : d = 412448 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 12889)
      exact by decide
                  ·
                    have : d = 412447 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412446 ≤ d
                  ·
                    have : d = 412446 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412445 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412443 ≤ d
                ·
                  by_cases h : 412444 ≤ d
                  ·
                    have : d = 412444 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412443 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412442 ≤ d
                  ·
                    have : d = 412442 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 355519)
      right
      exact ⟨298596, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412441 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412437 ≤ d
              ·
                by_cases h : 412439 ≤ d
                ·
                  by_cases h : 412440 ≤ d
                  ·
                    have : d = 412440 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 491)
      exact by decide
                  ·
                    have : d = 412439 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412438 ≤ d
                  ·
                    have : d = 412438 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412437 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412435 ≤ d
                ·
                  by_cases h : 412436 ≤ d
                  ·
                    have : d = 412436 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 412435 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412434 ≤ d
                  ·
                    have : d = 412434 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412433 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 412425 ≤ d
            ·
              by_cases h : 412429 ≤ d
              ·
                by_cases h : 412431 ≤ d
                ·
                  by_cases h : 412432 ≤ d
                  ·
                    have : d = 412432 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412431 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412430 ≤ d
                  ·
                    have : d = 412430 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412429 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412427 ≤ d
                ·
                  by_cases h : 412428 ≤ d
                  ·
                    have : d = 412428 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 34369)
      exact by decide
                  ·
                    have : d = 412427 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412426 ≤ d
                  ·
                    have : d = 412426 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412425 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412421 ≤ d
              ·
                by_cases h : 412423 ≤ d
                ·
                  by_cases h : 412424 ≤ d
                  ·
                    have : d = 412424 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412423 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412422 ≤ d
                  ·
                    have : d = 412422 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 18407052353)
      right
      exact ⟨18406639931, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412421 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412419 ≤ d
                ·
                  by_cases h : 412420 ≤ d
                  ·
                    have : d = 412420 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412419 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412418 ≤ d
                  ·
                    have : d = 412418 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412417 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
  ·
    by_cases h : 412289 ≤ d
    ·
      by_cases h : 412353 ≤ d
      ·
        by_cases h : 412385 ≤ d
        ·
          by_cases h : 412401 ≤ d
          ·
            by_cases h : 412409 ≤ d
            ·
              by_cases h : 412413 ≤ d
              ·
                by_cases h : 412415 ≤ d
                ·
                  by_cases h : 412416 ≤ d
                  ·
                    have : d = 412416 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 179)
      exact by decide
                  ·
                    have : d = 412415 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412414 ≤ d
                  ·
                    have : d = 412414 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412413 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412411 ≤ d
                ·
                  by_cases h : 412412 ≤ d
                  ·
                    have : d = 412412 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 412411 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412410 ≤ d
                  ·
                    have : d = 412410 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 59)
      exact by decide
                  ·
                    have : d = 412409 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412405 ≤ d
              ·
                by_cases h : 412407 ≤ d
                ·
                  by_cases h : 412408 ≤ d
                  ·
                    have : d = 412408 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412407 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412406 ≤ d
                  ·
                    have : d = 412406 := by omega
                    subst d
      exact fullRecordGapTerm07236_not_prime
                  ·
                    have : d = 412405 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412403 ≤ d
                ·
                  by_cases h : 412404 ≤ d
                  ·
                    have : d = 412404 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412403 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412402 ≤ d
                  ·
                    have : d = 412402 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412401 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 412393 ≤ d
            ·
              by_cases h : 412397 ≤ d
              ·
                by_cases h : 412399 ≤ d
                ·
                  by_cases h : 412400 ≤ d
                  ·
                    have : d = 412400 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1031)
      exact by decide
                  ·
                    have : d = 412399 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412398 ≤ d
                  ·
                    have : d = 412398 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1091)
      exact by decide
                  ·
                    have : d = 412397 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412395 ≤ d
                ·
                  by_cases h : 412396 ≤ d
                  ·
                    have : d = 412396 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412395 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412394 ≤ d
                  ·
                    have : d = 412394 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412393 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412389 ≤ d
              ·
                by_cases h : 412391 ≤ d
                ·
                  by_cases h : 412392 ≤ d
                  ·
                    have : d = 412392 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17183)
      exact by decide
                  ·
                    have : d = 412391 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412390 ≤ d
                  ·
                    have : d = 412390 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412389 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412387 ≤ d
                ·
                  by_cases h : 412388 ≤ d
                  ·
                    have : d = 412388 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 131)
      exact by decide
                  ·
                    have : d = 412387 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412386 ≤ d
                  ·
                    have : d = 412386 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412385 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 412369 ≤ d
          ·
            by_cases h : 412377 ≤ d
            ·
              by_cases h : 412381 ≤ d
              ·
                by_cases h : 412383 ≤ d
                ·
                  by_cases h : 412384 ≤ d
                  ·
                    have : d = 412384 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412383 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412382 ≤ d
                  ·
                    have : d = 412382 := by omega
                    subst d
      exact fullRecordGapTerm07235_not_prime
                  ·
                    have : d = 412381 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412379 ≤ d
                ·
                  by_cases h : 412380 ≤ d
                  ·
                    have : d = 412380 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 412379 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412378 ≤ d
                  ·
                    have : d = 412378 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412377 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412373 ≤ d
              ·
                by_cases h : 412375 ≤ d
                ·
                  by_cases h : 412376 ≤ d
                  ·
                    have : d = 412376 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412375 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412374 ≤ d
                  ·
                    have : d = 412374 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412373 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412371 ≤ d
                ·
                  by_cases h : 412372 ≤ d
                  ·
                    have : d = 412372 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412371 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412370 ≤ d
                  ·
                    have : d = 412370 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 43)
      exact by decide
                  ·
                    have : d = 412369 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 412361 ≤ d
            ·
              by_cases h : 412365 ≤ d
              ·
                by_cases h : 412367 ≤ d
                ·
                  by_cases h : 412368 ≤ d
                  ·
                    have : d = 412368 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 71)
      exact by decide
                  ·
                    have : d = 412367 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412366 ≤ d
                  ·
                    have : d = 412366 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412365 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412363 ≤ d
                ·
                  by_cases h : 412364 ≤ d
                  ·
                    have : d = 412364 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412363 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412362 ≤ d
                  ·
                    have : d = 412362 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412361 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412357 ≤ d
              ·
                by_cases h : 412359 ≤ d
                ·
                  by_cases h : 412360 ≤ d
                  ·
                    have : d = 412360 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412359 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412358 ≤ d
                  ·
                    have : d = 412358 := by omega
                    subst d
      exact fullRecordGapTerm07234_not_prime
                  ·
                    have : d = 412357 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412355 ≤ d
                ·
                  by_cases h : 412356 ≤ d
                  ·
                    have : d = 412356 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 4909)
      exact by decide
                  ·
                    have : d = 412355 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412354 ≤ d
                  ·
                    have : d = 412354 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412353 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 412321 ≤ d
        ·
          by_cases h : 412337 ≤ d
          ·
            by_cases h : 412345 ≤ d
            ·
              by_cases h : 412349 ≤ d
              ·
                by_cases h : 412351 ≤ d
                ·
                  by_cases h : 412352 ≤ d
                  ·
                    have : d = 412352 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 412351 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412350 ≤ d
                  ·
                    have : d = 412350 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2749)
      exact by decide
                  ·
                    have : d = 412349 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412347 ≤ d
                ·
                  by_cases h : 412348 ≤ d
                  ·
                    have : d = 412348 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412347 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412346 ≤ d
                  ·
                    have : d = 412346 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 18743)
      exact by decide
                  ·
                    have : d = 412345 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412341 ≤ d
              ·
                by_cases h : 412343 ≤ d
                ·
                  by_cases h : 412344 ≤ d
                  ·
                    have : d = 412344 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412343 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412342 ≤ d
                  ·
                    have : d = 412342 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412341 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412339 ≤ d
                ·
                  by_cases h : 412340 ≤ d
                  ·
                    have : d = 412340 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 53)
      exact by decide
                  ·
                    have : d = 412339 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412338 ≤ d
                  ·
                    have : d = 412338 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 412337 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 412329 ≤ d
            ·
              by_cases h : 412333 ≤ d
              ·
                by_cases h : 412335 ≤ d
                ·
                  by_cases h : 412336 ≤ d
                  ·
                    have : d = 412336 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412335 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412334 ≤ d
                  ·
                    have : d = 412334 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412333 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412331 ≤ d
                ·
                  by_cases h : 412332 ≤ d
                  ·
                    have : d = 412332 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 34361)
      exact by decide
                  ·
                    have : d = 412331 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412330 ≤ d
                  ·
                    have : d = 412330 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412329 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412325 ≤ d
              ·
                by_cases h : 412327 ≤ d
                ·
                  by_cases h : 412328 ≤ d
                  ·
                    have : d = 412328 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 412327 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412326 ≤ d
                  ·
                    have : d = 412326 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 22907)
      exact by decide
                  ·
                    have : d = 412325 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412323 ≤ d
                ·
                  by_cases h : 412324 ≤ d
                  ·
                    have : d = 412324 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412323 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412322 ≤ d
                  ·
                    have : d = 412322 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 412321 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 412305 ≤ d
          ·
            by_cases h : 412313 ≤ d
            ·
              by_cases h : 412317 ≤ d
              ·
                by_cases h : 412319 ≤ d
                ·
                  by_cases h : 412320 ≤ d
                  ·
                    have : d = 412320 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412319 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412318 ≤ d
                  ·
                    have : d = 412318 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412317 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412315 ≤ d
                ·
                  by_cases h : 412316 ≤ d
                  ·
                    have : d = 412316 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1887499)
      right
      exact ⟨1475183, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412315 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412314 ≤ d
                  ·
                    have : d = 412314 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412313 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412309 ≤ d
              ·
                by_cases h : 412311 ≤ d
                ·
                  by_cases h : 412312 ≤ d
                  ·
                    have : d = 412312 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412311 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412310 ≤ d
                  ·
                    have : d = 412310 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 41231)
      exact by decide
                  ·
                    have : d = 412309 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412307 ≤ d
                ·
                  by_cases h : 412308 ≤ d
                  ·
                    have : d = 412308 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 412307 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412306 ≤ d
                  ·
                    have : d = 412306 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412305 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 412297 ≤ d
            ·
              by_cases h : 412301 ≤ d
              ·
                by_cases h : 412303 ≤ d
                ·
                  by_cases h : 412304 ≤ d
                  ·
                    have : d = 412304 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412303 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412302 ≤ d
                  ·
                    have : d = 412302 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 6247)
      exact by decide
                  ·
                    have : d = 412301 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412299 ≤ d
                ·
                  by_cases h : 412300 ≤ d
                  ·
                    have : d = 412300 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412299 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412298 ≤ d
                  ·
                    have : d = 412298 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412297 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412293 ≤ d
              ·
                by_cases h : 412295 ≤ d
                ·
                  by_cases h : 412296 ≤ d
                  ·
                    have : d = 412296 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 41)
      exact by decide
                  ·
                    have : d = 412295 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412294 ≤ d
                  ·
                    have : d = 412294 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412293 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412291 ≤ d
                ·
                  by_cases h : 412292 ≤ d
                  ·
                    have : d = 412292 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412291 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412290 ≤ d
                  ·
                    have : d = 412290 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 509)
      exact by decide
                  ·
                    have : d = 412289 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 412225 ≤ d
      ·
        by_cases h : 412257 ≤ d
        ·
          by_cases h : 412273 ≤ d
          ·
            by_cases h : 412281 ≤ d
            ·
              by_cases h : 412285 ≤ d
              ·
                by_cases h : 412287 ≤ d
                ·
                  by_cases h : 412288 ≤ d
                  ·
                    have : d = 412288 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412287 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412286 ≤ d
                  ·
                    have : d = 412286 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 601)
      exact by decide
                  ·
                    have : d = 412285 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412283 ≤ d
                ·
                  by_cases h : 412284 ≤ d
                  ·
                    have : d = 412284 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412283 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412282 ≤ d
                  ·
                    have : d = 412282 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412281 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412277 ≤ d
              ·
                by_cases h : 412279 ≤ d
                ·
                  by_cases h : 412280 ≤ d
                  ·
                    have : d = 412280 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 937)
      exact by decide
                  ·
                    have : d = 412279 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412278 ≤ d
                  ·
                    have : d = 412278 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412277 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412275 ≤ d
                ·
                  by_cases h : 412276 ≤ d
                  ·
                    have : d = 412276 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412275 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412274 ≤ d
                  ·
                    have : d = 412274 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412273 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 412265 ≤ d
            ·
              by_cases h : 412269 ≤ d
              ·
                by_cases h : 412271 ≤ d
                ·
                  by_cases h : 412272 ≤ d
                  ·
                    have : d = 412272 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 409)
      exact by decide
                  ·
                    have : d = 412271 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412270 ≤ d
                  ·
                    have : d = 412270 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412269 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412267 ≤ d
                ·
                  by_cases h : 412268 ≤ d
                  ·
                    have : d = 412268 := by omega
                    subst d
      exact fullRecordGapTerm07233_not_prime
                  ·
                    have : d = 412267 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412266 ≤ d
                  ·
                    have : d = 412266 := by omega
                    subst d
      exact fullRecordGapTerm07232_not_prime
                  ·
                    have : d = 412265 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412261 ≤ d
              ·
                by_cases h : 412263 ≤ d
                ·
                  by_cases h : 412264 ≤ d
                  ·
                    have : d = 412264 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412263 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412262 ≤ d
                  ·
                    have : d = 412262 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 412261 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412259 ≤ d
                ·
                  by_cases h : 412260 ≤ d
                  ·
                    have : d = 412260 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 6871)
      exact by decide
                  ·
                    have : d = 412259 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412258 ≤ d
                  ·
                    have : d = 412258 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412257 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 412241 ≤ d
          ·
            by_cases h : 412249 ≤ d
            ·
              by_cases h : 412253 ≤ d
              ·
                by_cases h : 412255 ≤ d
                ·
                  by_cases h : 412256 ≤ d
                  ·
                    have : d = 412256 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 412255 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412254 ≤ d
                  ·
                    have : d = 412254 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412253 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412251 ≤ d
                ·
                  by_cases h : 412252 ≤ d
                  ·
                    have : d = 412252 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412251 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412250 ≤ d
                  ·
                    have : d = 412250 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412249 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412245 ≤ d
              ·
                by_cases h : 412247 ≤ d
                ·
                  by_cases h : 412248 ≤ d
                  ·
                    have : d = 412248 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 89)
      exact by decide
                  ·
                    have : d = 412247 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412246 ≤ d
                  ·
                    have : d = 412246 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412245 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412243 ≤ d
                ·
                  by_cases h : 412244 ≤ d
                  ·
                    have : d = 412244 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412243 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412242 ≤ d
                  ·
                    have : d = 412242 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 127)
      exact by decide
                  ·
                    have : d = 412241 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 412233 ≤ d
            ·
              by_cases h : 412237 ≤ d
              ·
                by_cases h : 412239 ≤ d
                ·
                  by_cases h : 412240 ≤ d
                  ·
                    have : d = 412240 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412239 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412238 ≤ d
                  ·
                    have : d = 412238 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 412237 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412235 ≤ d
                ·
                  by_cases h : 412236 ≤ d
                  ·
                    have : d = 412236 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412235 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412234 ≤ d
                  ·
                    have : d = 412234 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412233 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412229 ≤ d
              ·
                by_cases h : 412231 ≤ d
                ·
                  by_cases h : 412232 ≤ d
                  ·
                    have : d = 412232 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412231 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412230 ≤ d
                  ·
                    have : d = 412230 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 412229 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412227 ≤ d
                ·
                  by_cases h : 412228 ≤ d
                  ·
                    have : d = 412228 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412227 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412226 ≤ d
                  ·
                    have : d = 412226 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 71)
      exact by decide
                  ·
                    have : d = 412225 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 412193 ≤ d
        ·
          by_cases h : 412209 ≤ d
          ·
            by_cases h : 412217 ≤ d
            ·
              by_cases h : 412221 ≤ d
              ·
                by_cases h : 412223 ≤ d
                ·
                  by_cases h : 412224 ≤ d
                  ·
                    have : d = 412224 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412223 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412222 ≤ d
                  ·
                    have : d = 412222 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412221 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412219 ≤ d
                ·
                  by_cases h : 412220 ≤ d
                  ·
                    have : d = 412220 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 20611)
      exact by decide
                  ·
                    have : d = 412219 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412218 ≤ d
                  ·
                    have : d = 412218 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 22901)
      exact by decide
                  ·
                    have : d = 412217 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412213 ≤ d
              ·
                by_cases h : 412215 ≤ d
                ·
                  by_cases h : 412216 ≤ d
                  ·
                    have : d = 412216 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412215 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412214 ≤ d
                  ·
                    have : d = 412214 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412213 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412211 ≤ d
                ·
                  by_cases h : 412212 ≤ d
                  ·
                    have : d = 412212 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 34351)
      exact by decide
                  ·
                    have : d = 412211 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412210 ≤ d
                  ·
                    have : d = 412210 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412209 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 412201 ≤ d
            ·
              by_cases h : 412205 ≤ d
              ·
                by_cases h : 412207 ≤ d
                ·
                  by_cases h : 412208 ≤ d
                  ·
                    have : d = 412208 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412207 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412206 ≤ d
                  ·
                    have : d = 412206 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 412205 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412203 ≤ d
                ·
                  by_cases h : 412204 ≤ d
                  ·
                    have : d = 412204 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412203 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412202 ≤ d
                  ·
                    have : d = 412202 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29443)
      exact by decide
                  ·
                    have : d = 412201 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412197 ≤ d
              ·
                by_cases h : 412199 ≤ d
                ·
                  by_cases h : 412200 ≤ d
                  ·
                    have : d = 412200 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 229)
      exact by decide
                  ·
                    have : d = 412199 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412198 ≤ d
                  ·
                    have : d = 412198 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412197 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412195 ≤ d
                ·
                  by_cases h : 412196 ≤ d
                  ·
                    have : d = 412196 := by omega
                    subst d
      exact fullRecordGapTerm07231_not_prime
                  ·
                    have : d = 412195 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412194 ≤ d
                  ·
                    have : d = 412194 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412193 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 412177 ≤ d
          ·
            by_cases h : 412185 ≤ d
            ·
              by_cases h : 412189 ≤ d
              ·
                by_cases h : 412191 ≤ d
                ·
                  by_cases h : 412192 ≤ d
                  ·
                    have : d = 412192 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412191 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412190 ≤ d
                  ·
                    have : d = 412190 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 47)
      exact by decide
                  ·
                    have : d = 412189 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412187 ≤ d
                ·
                  by_cases h : 412188 ≤ d
                  ·
                    have : d = 412188 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412187 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412186 ≤ d
                  ·
                    have : d = 412186 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412185 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412181 ≤ d
              ·
                by_cases h : 412183 ≤ d
                ·
                  by_cases h : 412184 ≤ d
                  ·
                    have : d = 412184 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412183 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412182 ≤ d
                  ·
                    have : d = 412182 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 412181 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412179 ≤ d
                ·
                  by_cases h : 412180 ≤ d
                  ·
                    have : d = 412180 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412179 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412178 ≤ d
                  ·
                    have : d = 412178 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 412177 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 412169 ≤ d
            ·
              by_cases h : 412173 ≤ d
              ·
                by_cases h : 412175 ≤ d
                ·
                  by_cases h : 412176 ≤ d
                  ·
                    have : d = 412176 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 412175 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412174 ≤ d
                  ·
                    have : d = 412174 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412173 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412171 ≤ d
                ·
                  by_cases h : 412172 ≤ d
                  ·
                    have : d = 412172 := by omega
                    subst d
      exact fullRecordGapTerm07230_not_prime
                  ·
                    have : d = 412171 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412170 ≤ d
                  ·
                    have : d = 412170 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1249)
      exact by decide
                  ·
                    have : d = 412169 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 412165 ≤ d
              ·
                by_cases h : 412167 ≤ d
                ·
                  by_cases h : 412168 ≤ d
                  ·
                    have : d = 412168 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412167 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412166 ≤ d
                  ·
                    have : d = 412166 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412165 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 412163 ≤ d
                ·
                  by_cases h : 412164 ≤ d
                  ·
                    have : d = 412164 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412163 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 412162 ≤ d
                  ·
                    have : d = 412162 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 412161 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩

end PrimeFactorUnimodality
