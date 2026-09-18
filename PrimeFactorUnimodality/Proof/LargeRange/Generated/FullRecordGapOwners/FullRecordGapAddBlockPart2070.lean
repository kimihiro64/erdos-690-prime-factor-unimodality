import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapFermat

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

theorem fullRecordGapAddBlock_part2070 (d : Nat) (603137 ≤ d) (d ≤ 603648) : ¬(recordGapCenter + d).Prime := by
  by_cases h : 603393 ≤ d
  ·
    by_cases h : 603521 ≤ d
    ·
      by_cases h : 603585 ≤ d
      ·
        by_cases h : 603617 ≤ d
        ·
          by_cases h : 603633 ≤ d
          ·
            by_cases h : 603641 ≤ d
            ·
              by_cases h : 603645 ≤ d
              ·
                by_cases h : 603647 ≤ d
                ·
                  by_cases h : 603648 ≤ d
                  ·
                    have : d = 603648 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 131)
      exact by decide
                  ·
                    have : d = 603647 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603646 ≤ d
                  ·
                    have : d = 603646 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603645 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603643 ≤ d
                ·
                  by_cases h : 603644 ≤ d
                  ·
                    have : d = 603644 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603643 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603642 ≤ d
                  ·
                    have : d = 603642 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 603641 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603637 ≤ d
              ·
                by_cases h : 603639 ≤ d
                ·
                  by_cases h : 603640 ≤ d
                  ·
                    have : d = 603640 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603639 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603638 ≤ d
                  ·
                    have : d = 603638 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1207147)
      right
      exact ⟨603509, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603637 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603635 ≤ d
                ·
                  by_cases h : 603636 ≤ d
                  ·
                    have : d = 603636 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 603635 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603634 ≤ d
                  ·
                    have : d = 603634 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603633 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 603625 ≤ d
            ·
              by_cases h : 603629 ≤ d
              ·
                by_cases h : 603631 ≤ d
                ·
                  by_cases h : 603632 ≤ d
                  ·
                    have : d = 603632 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603631 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603630 ≤ d
                  ·
                    have : d = 603630 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603629 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603627 ≤ d
                ·
                  by_cases h : 603628 ≤ d
                  ·
                    have : d = 603628 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603627 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603626 ≤ d
                  ·
                    have : d = 603626 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 802370609)
      right
      exact ⟨801766983, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603625 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603621 ≤ d
              ·
                by_cases h : 603623 ≤ d
                ·
                  by_cases h : 603624 ≤ d
                  ·
                    have : d = 603624 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603623 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603622 ≤ d
                  ·
                    have : d = 603622 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603621 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603619 ≤ d
                ·
                  by_cases h : 603620 ≤ d
                  ·
                    have : d = 603620 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 30181)
      exact by decide
                  ·
                    have : d = 603619 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603618 ≤ d
                  ·
                    have : d = 603618 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 603617 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 603601 ≤ d
          ·
            by_cases h : 603609 ≤ d
            ·
              by_cases h : 603613 ≤ d
              ·
                by_cases h : 603615 ≤ d
                ·
                  by_cases h : 603616 ≤ d
                  ·
                    have : d = 603616 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603615 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603614 ≤ d
                  ·
                    have : d = 603614 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603613 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603611 ≤ d
                ·
                  by_cases h : 603612 ≤ d
                  ·
                    have : d = 603612 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 603611 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603610 ≤ d
                  ·
                    have : d = 603610 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603609 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603605 ≤ d
              ·
                by_cases h : 603607 ≤ d
                ·
                  by_cases h : 603608 ≤ d
                  ·
                    have : d = 603608 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 197)
      exact by decide
                  ·
                    have : d = 603607 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603606 ≤ d
                  ·
                    have : d = 603606 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 603605 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603603 ≤ d
                ·
                  by_cases h : 603604 ≤ d
                  ·
                    have : d = 603604 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603603 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603602 ≤ d
                  ·
                    have : d = 603602 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603601 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 603593 ≤ d
            ·
              by_cases h : 603597 ≤ d
              ·
                by_cases h : 603599 ≤ d
                ·
                  by_cases h : 603600 ≤ d
                  ·
                    have : d = 603600 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 503)
      exact by decide
                  ·
                    have : d = 603599 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603598 ≤ d
                  ·
                    have : d = 603598 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603597 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603595 ≤ d
                ·
                  by_cases h : 603596 ≤ d
                  ·
                    have : d = 603596 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 21557)
      exact by decide
                  ·
                    have : d = 603595 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603594 ≤ d
                  ·
                    have : d = 603594 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603593 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603589 ≤ d
              ·
                by_cases h : 603591 ≤ d
                ·
                  by_cases h : 603592 ≤ d
                  ·
                    have : d = 603592 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603591 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603590 ≤ d
                  ·
                    have : d = 603590 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 603589 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603587 ≤ d
                ·
                  by_cases h : 603588 ≤ d
                  ·
                    have : d = 603588 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603587 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603586 ≤ d
                  ·
                    have : d = 603586 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603585 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 603553 ≤ d
        ·
          by_cases h : 603569 ≤ d
          ·
            by_cases h : 603577 ≤ d
            ·
              by_cases h : 603581 ≤ d
              ·
                by_cases h : 603583 ≤ d
                ·
                  by_cases h : 603584 ≤ d
                  ·
                    have : d = 603584 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603583 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603582 ≤ d
                  ·
                    have : d = 603582 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2053)
      exact by decide
                  ·
                    have : d = 603581 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603579 ≤ d
                ·
                  by_cases h : 603580 ≤ d
                  ·
                    have : d = 603580 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603579 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603578 ≤ d
                  ·
                    have : d = 603578 := by omega
                    subst d
      exact fullRecordGapTerm10024_not_prime
                  ·
                    have : d = 603577 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603573 ≤ d
              ·
                by_cases h : 603575 ≤ d
                ·
                  by_cases h : 603576 ≤ d
                  ·
                    have : d = 603576 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 83)
      exact by decide
                  ·
                    have : d = 603575 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603574 ≤ d
                  ·
                    have : d = 603574 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603573 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603571 ≤ d
                ·
                  by_cases h : 603572 ≤ d
                  ·
                    have : d = 603572 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 270619)
      right
      exact ⟨208285, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603571 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603570 ≤ d
                  ·
                    have : d = 603570 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 603569 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 603561 ≤ d
            ·
              by_cases h : 603565 ≤ d
              ·
                by_cases h : 603567 ≤ d
                ·
                  by_cases h : 603568 ≤ d
                  ·
                    have : d = 603568 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603567 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603566 ≤ d
                  ·
                    have : d = 603566 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603565 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603563 ≤ d
                ·
                  by_cases h : 603564 ≤ d
                  ·
                    have : d = 603564 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603563 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603562 ≤ d
                  ·
                    have : d = 603562 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603561 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603557 ≤ d
              ·
                by_cases h : 603559 ≤ d
                ·
                  by_cases h : 603560 ≤ d
                  ·
                    have : d = 603560 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603559 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603558 ≤ d
                  ·
                    have : d = 603558 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11177)
      exact by decide
                  ·
                    have : d = 603557 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603555 ≤ d
                ·
                  by_cases h : 603556 ≤ d
                  ·
                    have : d = 603556 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603555 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603554 ≤ d
                  ·
                    have : d = 603554 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603553 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 603537 ≤ d
          ·
            by_cases h : 603545 ≤ d
            ·
              by_cases h : 603549 ≤ d
              ·
                by_cases h : 603551 ≤ d
                ·
                  by_cases h : 603552 ≤ d
                  ·
                    have : d = 603552 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 6287)
      exact by decide
                  ·
                    have : d = 603551 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603550 ≤ d
                  ·
                    have : d = 603550 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603549 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603547 ≤ d
                ·
                  by_cases h : 603548 ≤ d
                  ·
                    have : d = 603548 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 29)
      exact by decide
                  ·
                    have : d = 603547 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603546 ≤ d
                  ·
                    have : d = 603546 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603545 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603541 ≤ d
              ·
                by_cases h : 603543 ≤ d
                ·
                  by_cases h : 603544 ≤ d
                  ·
                    have : d = 603544 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603543 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603542 ≤ d
                  ·
                    have : d = 603542 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 523)
      exact by decide
                  ·
                    have : d = 603541 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603539 ≤ d
                ·
                  by_cases h : 603540 ≤ d
                  ·
                    have : d = 603540 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 479)
      exact by decide
                  ·
                    have : d = 603539 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603538 ≤ d
                  ·
                    have : d = 603538 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603537 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 603529 ≤ d
            ·
              by_cases h : 603533 ≤ d
              ·
                by_cases h : 603535 ≤ d
                ·
                  by_cases h : 603536 ≤ d
                  ·
                    have : d = 603536 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 67)
      exact by decide
                  ·
                    have : d = 603535 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603534 ≤ d
                  ·
                    have : d = 603534 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603533 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603531 ≤ d
                ·
                  by_cases h : 603532 ≤ d
                  ·
                    have : d = 603532 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603531 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603530 ≤ d
                  ·
                    have : d = 603530 := by omega
                    subst d
      exact fullRecordGapTerm10023_not_prime
                  ·
                    have : d = 603529 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603525 ≤ d
              ·
                by_cases h : 603527 ≤ d
                ·
                  by_cases h : 603528 ≤ d
                  ·
                    have : d = 603528 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 25147)
      exact by decide
                  ·
                    have : d = 603527 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603526 ≤ d
                  ·
                    have : d = 603526 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603525 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603523 ≤ d
                ·
                  by_cases h : 603524 ≤ d
                  ·
                    have : d = 603524 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603523 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603522 ≤ d
                  ·
                    have : d = 603522 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603521 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 603457 ≤ d
      ·
        by_cases h : 603489 ≤ d
        ·
          by_cases h : 603505 ≤ d
          ·
            by_cases h : 603513 ≤ d
            ·
              by_cases h : 603517 ≤ d
              ·
                by_cases h : 603519 ≤ d
                ·
                  by_cases h : 603520 ≤ d
                  ·
                    have : d = 603520 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603519 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603518 ≤ d
                  ·
                    have : d = 603518 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603517 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603515 ≤ d
                ·
                  by_cases h : 603516 ≤ d
                  ·
                    have : d = 603516 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 603515 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603514 ≤ d
                  ·
                    have : d = 603514 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603513 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603509 ≤ d
              ·
                by_cases h : 603511 ≤ d
                ·
                  by_cases h : 603512 ≤ d
                  ·
                    have : d = 603512 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 603511 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603510 ≤ d
                  ·
                    have : d = 603510 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 20117)
      exact by decide
                  ·
                    have : d = 603509 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603507 ≤ d
                ·
                  by_cases h : 603508 ≤ d
                  ·
                    have : d = 603508 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603507 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603506 ≤ d
                  ·
                    have : d = 603506 := by omega
                    subst d
      exact fullRecordGapTerm10022_not_prime
                  ·
                    have : d = 603505 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 603497 ≤ d
            ·
              by_cases h : 603501 ≤ d
              ·
                by_cases h : 603503 ≤ d
                ·
                  by_cases h : 603504 ≤ d
                  ·
                    have : d = 603504 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603503 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603502 ≤ d
                  ·
                    have : d = 603502 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603501 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603499 ≤ d
                ·
                  by_cases h : 603500 ≤ d
                  ·
                    have : d = 603500 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603499 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603498 ≤ d
                  ·
                    have : d = 603498 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 14369)
      exact by decide
                  ·
                    have : d = 603497 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603493 ≤ d
              ·
                by_cases h : 603495 ≤ d
                ·
                  by_cases h : 603496 ≤ d
                  ·
                    have : d = 603496 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603495 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603494 ≤ d
                  ·
                    have : d = 603494 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603493 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603491 ≤ d
                ·
                  by_cases h : 603492 ≤ d
                  ·
                    have : d = 603492 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 63234763)
      right
      exact ⟨62631271, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603491 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603490 ≤ d
                  ·
                    have : d = 603490 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603489 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 603473 ≤ d
          ·
            by_cases h : 603481 ≤ d
            ·
              by_cases h : 603485 ≤ d
              ·
                by_cases h : 603487 ≤ d
                ·
                  by_cases h : 603488 ≤ d
                  ·
                    have : d = 603488 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 18859)
      exact by decide
                  ·
                    have : d = 603487 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603486 ≤ d
                  ·
                    have : d = 603486 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 603485 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603483 ≤ d
                ·
                  by_cases h : 603484 ≤ d
                  ·
                    have : d = 603484 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603483 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603482 ≤ d
                  ·
                    have : d = 603482 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 27431)
      exact by decide
                  ·
                    have : d = 603481 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603477 ≤ d
              ·
                by_cases h : 603479 ≤ d
                ·
                  by_cases h : 603480 ≤ d
                  ·
                    have : d = 603480 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 47)
      exact by decide
                  ·
                    have : d = 603479 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603478 ≤ d
                  ·
                    have : d = 603478 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603477 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603475 ≤ d
                ·
                  by_cases h : 603476 ≤ d
                  ·
                    have : d = 603476 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603475 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603474 ≤ d
                  ·
                    have : d = 603474 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603473 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 603465 ≤ d
            ·
              by_cases h : 603469 ≤ d
              ·
                by_cases h : 603471 ≤ d
                ·
                  by_cases h : 603472 ≤ d
                  ·
                    have : d = 603472 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603471 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603470 ≤ d
                  ·
                    have : d = 603470 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 603469 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603467 ≤ d
                ·
                  by_cases h : 603468 ≤ d
                  ·
                    have : d = 603468 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 16763)
      exact by decide
                  ·
                    have : d = 603467 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603466 ≤ d
                  ·
                    have : d = 603466 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603465 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603461 ≤ d
              ·
                by_cases h : 603463 ≤ d
                ·
                  by_cases h : 603464 ≤ d
                  ·
                    have : d = 603464 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603463 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603462 ≤ d
                  ·
                    have : d = 603462 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603461 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603459 ≤ d
                ·
                  by_cases h : 603460 ≤ d
                  ·
                    have : d = 603460 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603459 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603458 ≤ d
                  ·
                    have : d = 603458 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 53)
      exact by decide
                  ·
                    have : d = 603457 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 603425 ≤ d
        ·
          by_cases h : 603441 ≤ d
          ·
            by_cases h : 603449 ≤ d
            ·
              by_cases h : 603453 ≤ d
              ·
                by_cases h : 603455 ≤ d
                ·
                  by_cases h : 603456 ≤ d
                  ·
                    have : d = 603456 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603455 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603454 ≤ d
                  ·
                    have : d = 603454 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603453 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603451 ≤ d
                ·
                  by_cases h : 603452 ≤ d
                  ·
                    have : d = 603452 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 59)
      exact by decide
                  ·
                    have : d = 603451 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603450 ≤ d
                  ·
                    have : d = 603450 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 149)
      exact by decide
                  ·
                    have : d = 603449 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603445 ≤ d
              ·
                by_cases h : 603447 ≤ d
                ·
                  by_cases h : 603448 ≤ d
                  ·
                    have : d = 603448 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603447 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603446 ≤ d
                  ·
                    have : d = 603446 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 603445 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603443 ≤ d
                ·
                  by_cases h : 603444 ≤ d
                  ·
                    have : d = 603444 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603443 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603442 ≤ d
                  ·
                    have : d = 603442 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603441 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 603433 ≤ d
            ·
              by_cases h : 603437 ≤ d
              ·
                by_cases h : 603439 ≤ d
                ·
                  by_cases h : 603440 ≤ d
                  ·
                    have : d = 603440 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 603439 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603438 ≤ d
                  ·
                    have : d = 603438 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 41)
      exact by decide
                  ·
                    have : d = 603437 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603435 ≤ d
                ·
                  by_cases h : 603436 ≤ d
                  ·
                    have : d = 603436 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603435 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603434 ≤ d
                  ·
                    have : d = 603434 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603433 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603429 ≤ d
              ·
                by_cases h : 603431 ≤ d
                ·
                  by_cases h : 603432 ≤ d
                  ·
                    have : d = 603432 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 603431 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603430 ≤ d
                  ·
                    have : d = 603430 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603429 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603427 ≤ d
                ·
                  by_cases h : 603428 ≤ d
                  ·
                    have : d = 603428 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 603427 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603426 ≤ d
                  ·
                    have : d = 603426 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 163)
      exact by decide
                  ·
                    have : d = 603425 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 603409 ≤ d
          ·
            by_cases h : 603417 ≤ d
            ·
              by_cases h : 603421 ≤ d
              ·
                by_cases h : 603423 ≤ d
                ·
                  by_cases h : 603424 ≤ d
                  ·
                    have : d = 603424 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603423 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603422 ≤ d
                  ·
                    have : d = 603422 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 4735037)
      right
      exact ⟨4131615, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603421 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603419 ≤ d
                ·
                  by_cases h : 603420 ≤ d
                  ·
                    have : d = 603420 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603419 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603418 ≤ d
                  ·
                    have : d = 603418 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603417 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603413 ≤ d
              ·
                by_cases h : 603415 ≤ d
                ·
                  by_cases h : 603416 ≤ d
                  ·
                    have : d = 603416 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 6857)
      exact by decide
                  ·
                    have : d = 603415 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603414 ≤ d
                  ·
                    have : d = 603414 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603413 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603411 ≤ d
                ·
                  by_cases h : 603412 ≤ d
                  ·
                    have : d = 603412 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603411 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603410 ≤ d
                  ·
                    have : d = 603410 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 83)
      exact by decide
                  ·
                    have : d = 603409 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 603401 ≤ d
            ·
              by_cases h : 603405 ≤ d
              ·
                by_cases h : 603407 ≤ d
                ·
                  by_cases h : 603408 ≤ d
                  ·
                    have : d = 603408 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 603407 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603406 ≤ d
                  ·
                    have : d = 603406 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603405 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603403 ≤ d
                ·
                  by_cases h : 603404 ≤ d
                  ·
                    have : d = 603404 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603403 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603402 ≤ d
                  ·
                    have : d = 603402 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 603401 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603397 ≤ d
              ·
                by_cases h : 603399 ≤ d
                ·
                  by_cases h : 603400 ≤ d
                  ·
                    have : d = 603400 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603399 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603398 ≤ d
                  ·
                    have : d = 603398 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 603397 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603395 ≤ d
                ·
                  by_cases h : 603396 ≤ d
                  ·
                    have : d = 603396 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 603395 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603394 ≤ d
                  ·
                    have : d = 603394 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603393 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
  ·
    by_cases h : 603265 ≤ d
    ·
      by_cases h : 603329 ≤ d
      ·
        by_cases h : 603361 ≤ d
        ·
          by_cases h : 603377 ≤ d
          ·
            by_cases h : 603385 ≤ d
            ·
              by_cases h : 603389 ≤ d
              ·
                by_cases h : 603391 ≤ d
                ·
                  by_cases h : 603392 ≤ d
                  ·
                    have : d = 603392 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603391 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603390 ≤ d
                  ·
                    have : d = 603390 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603389 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603387 ≤ d
                ·
                  by_cases h : 603388 ≤ d
                  ·
                    have : d = 603388 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603387 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603386 ≤ d
                  ·
                    have : d = 603386 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 47)
      exact by decide
                  ·
                    have : d = 603385 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603381 ≤ d
              ·
                by_cases h : 603383 ≤ d
                ·
                  by_cases h : 603384 ≤ d
                  ·
                    have : d = 603384 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603383 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603382 ≤ d
                  ·
                    have : d = 603382 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603381 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603379 ≤ d
                ·
                  by_cases h : 603380 ≤ d
                  ·
                    have : d = 603380 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 30169)
      exact by decide
                  ·
                    have : d = 603379 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603378 ≤ d
                  ·
                    have : d = 603378 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603377 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 603369 ≤ d
            ·
              by_cases h : 603373 ≤ d
              ·
                by_cases h : 603375 ≤ d
                ·
                  by_cases h : 603376 ≤ d
                  ·
                    have : d = 603376 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603375 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603374 ≤ d
                  ·
                    have : d = 603374 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603373 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603371 ≤ d
                ·
                  by_cases h : 603372 ≤ d
                  ·
                    have : d = 603372 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 653)
      exact by decide
                  ·
                    have : d = 603371 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603370 ≤ d
                  ·
                    have : d = 603370 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603369 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603365 ≤ d
              ·
                by_cases h : 603367 ≤ d
                ·
                  by_cases h : 603368 ≤ d
                  ·
                    have : d = 603368 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603367 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603366 ≤ d
                  ·
                    have : d = 603366 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 227)
      exact by decide
                  ·
                    have : d = 603365 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603363 ≤ d
                ·
                  by_cases h : 603364 ≤ d
                  ·
                    have : d = 603364 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603363 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603362 ≤ d
                  ·
                    have : d = 603362 := by omega
                    subst d
      exact fullRecordGapTerm10021_not_prime
                  ·
                    have : d = 603361 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 603345 ≤ d
          ·
            by_cases h : 603353 ≤ d
            ·
              by_cases h : 603357 ≤ d
              ·
                by_cases h : 603359 ≤ d
                ·
                  by_cases h : 603360 ≤ d
                  ·
                    have : d = 603360 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 419)
      exact by decide
                  ·
                    have : d = 603359 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603358 ≤ d
                  ·
                    have : d = 603358 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603357 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603355 ≤ d
                ·
                  by_cases h : 603356 ≤ d
                  ·
                    have : d = 603356 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 603355 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603354 ≤ d
                  ·
                    have : d = 603354 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603353 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603349 ≤ d
              ·
                by_cases h : 603351 ≤ d
                ·
                  by_cases h : 603352 ≤ d
                  ·
                    have : d = 603352 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603351 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603350 ≤ d
                  ·
                    have : d = 603350 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603349 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603347 ≤ d
                ·
                  by_cases h : 603348 ≤ d
                  ·
                    have : d = 603348 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 137)
      exact by decide
                  ·
                    have : d = 603347 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603346 ≤ d
                  ·
                    have : d = 603346 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603345 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 603337 ≤ d
            ·
              by_cases h : 603341 ≤ d
              ·
                by_cases h : 603343 ≤ d
                ·
                  by_cases h : 603344 ≤ d
                  ·
                    have : d = 603344 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603343 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603342 ≤ d
                  ·
                    have : d = 603342 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11173)
      exact by decide
                  ·
                    have : d = 603341 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603339 ≤ d
                ·
                  by_cases h : 603340 ≤ d
                  ·
                    have : d = 603340 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603339 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603338 ≤ d
                  ·
                    have : d = 603338 := by omega
                    subst d
      exact fullRecordGapTerm10020_not_prime
                  ·
                    have : d = 603337 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603333 ≤ d
              ·
                by_cases h : 603335 ≤ d
                ·
                  by_cases h : 603336 ≤ d
                  ·
                    have : d = 603336 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603335 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603334 ≤ d
                  ·
                    have : d = 603334 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603333 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603331 ≤ d
                ·
                  by_cases h : 603332 ≤ d
                  ·
                    have : d = 603332 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 885782363)
      right
      exact ⟨885179031, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603331 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603330 ≤ d
                  ·
                    have : d = 603330 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 603329 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 603297 ≤ d
        ·
          by_cases h : 603313 ≤ d
          ·
            by_cases h : 603321 ≤ d
            ·
              by_cases h : 603325 ≤ d
              ·
                by_cases h : 603327 ≤ d
                ·
                  by_cases h : 603328 ≤ d
                  ·
                    have : d = 603328 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603327 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603326 ≤ d
                  ·
                    have : d = 603326 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 603325 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603323 ≤ d
                ·
                  by_cases h : 603324 ≤ d
                  ·
                    have : d = 603324 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603323 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603322 ≤ d
                  ·
                    have : d = 603322 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603321 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603317 ≤ d
              ·
                by_cases h : 603319 ≤ d
                ·
                  by_cases h : 603320 ≤ d
                  ·
                    have : d = 603320 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 15083)
      exact by decide
                  ·
                    have : d = 603319 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603318 ≤ d
                  ·
                    have : d = 603318 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 193)
      exact by decide
                  ·
                    have : d = 603317 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603315 ≤ d
                ·
                  by_cases h : 603316 ≤ d
                  ·
                    have : d = 603316 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603315 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603314 ≤ d
                  ·
                    have : d = 603314 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603313 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 603305 ≤ d
            ·
              by_cases h : 603309 ≤ d
              ·
                by_cases h : 603311 ≤ d
                ·
                  by_cases h : 603312 ≤ d
                  ·
                    have : d = 603312 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 12569)
      exact by decide
                  ·
                    have : d = 603311 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603310 ≤ d
                  ·
                    have : d = 603310 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603309 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603307 ≤ d
                ·
                  by_cases h : 603308 ≤ d
                  ·
                    have : d = 603308 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603307 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603306 ≤ d
                  ·
                    have : d = 603306 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 277)
      exact by decide
                  ·
                    have : d = 603305 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603301 ≤ d
              ·
                by_cases h : 603303 ≤ d
                ·
                  by_cases h : 603304 ≤ d
                  ·
                    have : d = 603304 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603303 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603302 ≤ d
                  ·
                    have : d = 603302 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603301 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603299 ≤ d
                ·
                  by_cases h : 603300 ≤ d
                  ·
                    have : d = 603300 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2011)
      exact by decide
                  ·
                    have : d = 603299 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603298 ≤ d
                  ·
                    have : d = 603298 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603297 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 603281 ≤ d
          ·
            by_cases h : 603289 ≤ d
            ·
              by_cases h : 603293 ≤ d
              ·
                by_cases h : 603295 ≤ d
                ·
                  by_cases h : 603296 ≤ d
                  ·
                    have : d = 603296 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 603295 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603294 ≤ d
                  ·
                    have : d = 603294 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603293 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603291 ≤ d
                ·
                  by_cases h : 603292 ≤ d
                  ·
                    have : d = 603292 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603291 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603290 ≤ d
                  ·
                    have : d = 603290 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 603289 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603285 ≤ d
              ·
                by_cases h : 603287 ≤ d
                ·
                  by_cases h : 603288 ≤ d
                  ·
                    have : d = 603288 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 603287 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603286 ≤ d
                  ·
                    have : d = 603286 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603285 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603283 ≤ d
                ·
                  by_cases h : 603284 ≤ d
                  ·
                    have : d = 603284 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603283 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603282 ≤ d
                  ·
                    have : d = 603282 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 634339787)
      right
      exact ⟨633736505, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603281 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 603273 ≤ d
            ·
              by_cases h : 603277 ≤ d
              ·
                by_cases h : 603279 ≤ d
                ·
                  by_cases h : 603280 ≤ d
                  ·
                    have : d = 603280 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603279 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603278 ≤ d
                  ·
                    have : d = 603278 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 603277 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603275 ≤ d
                ·
                  by_cases h : 603276 ≤ d
                  ·
                    have : d = 603276 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 731363)
      right
      exact ⟨128087, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603275 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603274 ≤ d
                  ·
                    have : d = 603274 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603273 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603269 ≤ d
              ·
                by_cases h : 603271 ≤ d
                ·
                  by_cases h : 603272 ≤ d
                  ·
                    have : d = 603272 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 73)
      exact by decide
                  ·
                    have : d = 603271 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603270 ≤ d
                  ·
                    have : d = 603270 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 6703)
      exact by decide
                  ·
                    have : d = 603269 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603267 ≤ d
                ·
                  by_cases h : 603268 ≤ d
                  ·
                    have : d = 603268 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603267 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603266 ≤ d
                  ·
                    have : d = 603266 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603265 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 603201 ≤ d
      ·
        by_cases h : 603233 ≤ d
        ·
          by_cases h : 603249 ≤ d
          ·
            by_cases h : 603257 ≤ d
            ·
              by_cases h : 603261 ≤ d
              ·
                by_cases h : 603263 ≤ d
                ·
                  by_cases h : 603264 ≤ d
                  ·
                    have : d = 603264 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603263 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603262 ≤ d
                  ·
                    have : d = 603262 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603261 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603259 ≤ d
                ·
                  by_cases h : 603260 ≤ d
                  ·
                    have : d = 603260 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 31)
      exact by decide
                  ·
                    have : d = 603259 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603258 ≤ d
                  ·
                    have : d = 603258 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603257 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603253 ≤ d
              ·
                by_cases h : 603255 ≤ d
                ·
                  by_cases h : 603256 ≤ d
                  ·
                    have : d = 603256 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603255 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603254 ≤ d
                  ·
                    have : d = 603254 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603253 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603251 ≤ d
                ·
                  by_cases h : 603252 ≤ d
                  ·
                    have : d = 603252 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603251 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603250 ≤ d
                  ·
                    have : d = 603250 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603249 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 603241 ≤ d
            ·
              by_cases h : 603245 ≤ d
              ·
                by_cases h : 603247 ≤ d
                ·
                  by_cases h : 603248 ≤ d
                  ·
                    have : d = 603248 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 37)
      exact by decide
                  ·
                    have : d = 603247 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603246 ≤ d
                  ·
                    have : d = 603246 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 53)
      exact by decide
                  ·
                    have : d = 603245 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603243 ≤ d
                ·
                  by_cases h : 603244 ≤ d
                  ·
                    have : d = 603244 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603243 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603242 ≤ d
                  ·
                    have : d = 603242 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 89)
      exact by decide
                  ·
                    have : d = 603241 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603237 ≤ d
              ·
                by_cases h : 603239 ≤ d
                ·
                  by_cases h : 603240 ≤ d
                  ·
                    have : d = 603240 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 457)
      exact by decide
                  ·
                    have : d = 603239 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603238 ≤ d
                  ·
                    have : d = 603238 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603237 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603235 ≤ d
                ·
                  by_cases h : 603236 ≤ d
                  ·
                    have : d = 603236 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603235 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603234 ≤ d
                  ·
                    have : d = 603234 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603233 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 603217 ≤ d
          ·
            by_cases h : 603225 ≤ d
            ·
              by_cases h : 603229 ≤ d
              ·
                by_cases h : 603231 ≤ d
                ·
                  by_cases h : 603232 ≤ d
                  ·
                    have : d = 603232 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603231 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603230 ≤ d
                  ·
                    have : d = 603230 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 179)
      exact by decide
                  ·
                    have : d = 603229 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603227 ≤ d
                ·
                  by_cases h : 603228 ≤ d
                  ·
                    have : d = 603228 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 17)
      exact by decide
                  ·
                    have : d = 603227 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603226 ≤ d
                  ·
                    have : d = 603226 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603225 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603221 ≤ d
              ·
                by_cases h : 603223 ≤ d
                ·
                  by_cases h : 603224 ≤ d
                  ·
                    have : d = 603224 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603223 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603222 ≤ d
                  ·
                    have : d = 603222 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 50777)
      right
      exact ⟨6102, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603221 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603219 ≤ d
                ·
                  by_cases h : 603220 ≤ d
                  ·
                    have : d = 603220 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603219 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603218 ≤ d
                  ·
                    have : d = 603218 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3917)
      exact by decide
                  ·
                    have : d = 603217 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 603209 ≤ d
            ·
              by_cases h : 603213 ≤ d
              ·
                by_cases h : 603215 ≤ d
                ·
                  by_cases h : 603216 ≤ d
                  ·
                    have : d = 603216 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 59)
      exact by decide
                  ·
                    have : d = 603215 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603214 ≤ d
                  ·
                    have : d = 603214 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603213 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603211 ≤ d
                ·
                  by_cases h : 603212 ≤ d
                  ·
                    have : d = 603212 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 19)
      exact by decide
                  ·
                    have : d = 603211 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603210 ≤ d
                  ·
                    have : d = 603210 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603209 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603205 ≤ d
              ·
                by_cases h : 603207 ≤ d
                ·
                  by_cases h : 603208 ≤ d
                  ·
                    have : d = 603208 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603207 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603206 ≤ d
                  ·
                    have : d = 603206 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 109)
      exact by decide
                  ·
                    have : d = 603205 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603203 ≤ d
                ·
                  by_cases h : 603204 ≤ d
                  ·
                    have : d = 603204 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603203 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603202 ≤ d
                  ·
                    have : d = 603202 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603201 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 603169 ≤ d
        ·
          by_cases h : 603185 ≤ d
          ·
            by_cases h : 603193 ≤ d
            ·
              by_cases h : 603197 ≤ d
              ·
                by_cases h : 603199 ≤ d
                ·
                  by_cases h : 603200 ≤ d
                  ·
                    have : d = 603200 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 13)
      exact by decide
                  ·
                    have : d = 603199 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603198 ≤ d
                  ·
                    have : d = 603198 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 603197 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603195 ≤ d
                ·
                  by_cases h : 603196 ≤ d
                  ·
                    have : d = 603196 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603195 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603194 ≤ d
                  ·
                    have : d = 603194 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603193 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603189 ≤ d
              ·
                by_cases h : 603191 ≤ d
                ·
                  by_cases h : 603192 ≤ d
                  ·
                    have : d = 603192 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603191 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603190 ≤ d
                  ·
                    have : d = 603190 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603189 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603187 ≤ d
                ·
                  by_cases h : 603188 ≤ d
                  ·
                    have : d = 603188 := by omega
                    subst d
      exact fullRecordGapTerm10019_not_prime
                  ·
                    have : d = 603187 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603186 ≤ d
                  ·
                    have : d = 603186 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 229)
      exact by decide
                  ·
                    have : d = 603185 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 603177 ≤ d
            ·
              by_cases h : 603181 ≤ d
              ·
                by_cases h : 603183 ≤ d
                ·
                  by_cases h : 603184 ≤ d
                  ·
                    have : d = 603184 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603183 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603182 ≤ d
                  ·
                    have : d = 603182 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603181 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603179 ≤ d
                ·
                  by_cases h : 603180 ≤ d
                  ·
                    have : d = 603180 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 1117)
      exact by decide
                  ·
                    have : d = 603179 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603178 ≤ d
                  ·
                    have : d = 603178 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603177 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603173 ≤ d
              ·
                by_cases h : 603175 ≤ d
                ·
                  by_cases h : 603176 ≤ d
                  ·
                    have : d = 603176 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 10771)
      exact by decide
                  ·
                    have : d = 603175 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603174 ≤ d
                  ·
                    have : d = 603174 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603173 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603171 ≤ d
                ·
                  by_cases h : 603172 ≤ d
                  ·
                    have : d = 603172 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603171 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603170 ≤ d
                  ·
                    have : d = 603170 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 11)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603169 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 603153 ≤ d
          ·
            by_cases h : 603161 ≤ d
            ·
              by_cases h : 603165 ≤ d
              ·
                by_cases h : 603167 ≤ d
                ·
                  by_cases h : 603168 ≤ d
                  ·
                    have : d = 603168 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603167 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603166 ≤ d
                  ·
                    have : d = 603166 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603165 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603163 ≤ d
                ·
                  by_cases h : 603164 ≤ d
                  ·
                    have : d = 603164 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603163 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603162 ≤ d
                  ·
                    have : d = 603162 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 4787)
      exact by decide
                  ·
                    have : d = 603161 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603157 ≤ d
              ·
                by_cases h : 603159 ≤ d
                ·
                  by_cases h : 603160 ≤ d
                  ·
                    have : d = 603160 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603159 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603158 ≤ d
                  ·
                    have : d = 603158 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 171203)
      right
      exact ⟨81654, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603157 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603155 ≤ d
                ·
                  by_cases h : 603156 ≤ d
                  ·
                    have : d = 603156 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 4792133)
      right
      exact ⟨4188977, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603155 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603154 ≤ d
                  ·
                    have : d = 603154 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603153 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 603145 ≤ d
            ·
              by_cases h : 603149 ≤ d
              ·
                by_cases h : 603151 ≤ d
                ·
                  by_cases h : 603152 ≤ d
                  ·
                    have : d = 603152 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 23)
      exact by decide
                  ·
                    have : d = 603151 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603150 ≤ d
                  ·
                    have : d = 603150 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 4021)
      exact by decide
                  ·
                    have : d = 603149 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603147 ≤ d
                ·
                  by_cases h : 603148 ≤ d
                  ·
                    have : d = 603148 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603147 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603146 ≤ d
                  ·
                    have : d = 603146 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 97)
      exact by decide
                  ·
                    have : d = 603145 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 603141 ≤ d
              ·
                by_cases h : 603143 ≤ d
                ·
                  by_cases h : 603144 ≤ d
                  ·
                    have : d = 603144 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 5)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603143 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603142 ≤ d
                  ·
                    have : d = 603142 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 3)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603141 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 603139 ≤ d
                ·
                  by_cases h : 603140 ≤ d
                  ·
                    have : d = 603140 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 7)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 603139 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 603138 ≤ d
                  ·
                    have : d = 603138 := by omega
                    subst d
      exact fullRecordGapTerm10018_not_prime
                  ·
                    have : d = 603137 := by omega
                    subst d
      apply fullRecordGap_add_not_prime (q := 2)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num⟩

end PrimeFactorUnimodality
