import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapFermat

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

theorem fullRecordGapSubBlock_part0187 (d : Nat) (95233 ≤ d) (d ≤ 95744) : ¬(recordGapCenter - d).Prime := by
  by_cases h : 95489 ≤ d
  ·
    by_cases h : 95617 ≤ d
    ·
      by_cases h : 95681 ≤ d
      ·
        by_cases h : 95713 ≤ d
        ·
          by_cases h : 95729 ≤ d
          ·
            by_cases h : 95737 ≤ d
            ·
              by_cases h : 95741 ≤ d
              ·
                by_cases h : 95743 ≤ d
                ·
                  by_cases h : 95744 ≤ d
                  ·
                    have : d = 95744 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95743 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95742 ≤ d
                  ·
                    have : d = 95742 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 197) (by norm_num)
      exact by decide
                  ·
                    have : d = 95741 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95739 ≤ d
                ·
                  by_cases h : 95740 ≤ d
                  ·
                    have : d = 95740 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95739 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95738 ≤ d
                  ·
                    have : d = 95738 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95737 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95733 ≤ d
              ·
                by_cases h : 95735 ≤ d
                ·
                  by_cases h : 95736 ≤ d
                  ·
                    have : d = 95736 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95735 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95734 ≤ d
                  ·
                    have : d = 95734 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 151) (by norm_num)
      exact by decide
                  ·
                    have : d = 95733 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95731 ≤ d
                ·
                  by_cases h : 95732 ≤ d
                  ·
                    have : d = 95732 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95731 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95730 ≤ d
                  ·
                    have : d = 95730 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3191) (by norm_num)
      exact by decide
                  ·
                    have : d = 95729 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 95721 ≤ d
            ·
              by_cases h : 95725 ≤ d
              ·
                by_cases h : 95727 ≤ d
                ·
                  by_cases h : 95728 ≤ d
                  ·
                    have : d = 95728 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 31) (by norm_num)
      exact by decide
                  ·
                    have : d = 95727 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95726 ≤ d
                  ·
                    have : d = 95726 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95725 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95723 ≤ d
                ·
                  by_cases h : 95724 ≤ d
                  ·
                    have : d = 95724 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2659) (by norm_num)
      exact by decide
                  ·
                    have : d = 95723 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95722 ≤ d
                  ·
                    have : d = 95722 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 95721 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95717 ≤ d
              ·
                by_cases h : 95719 ≤ d
                ·
                  by_cases h : 95720 ≤ d
                  ·
                    have : d = 95720 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95719 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95718 ≤ d
                  ·
                    have : d = 95718 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 43) (by norm_num)
      exact by decide
                  ·
                    have : d = 95717 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95715 ≤ d
                ·
                  by_cases h : 95716 ≤ d
                  ·
                    have : d = 95716 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95715 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95714 ≤ d
                  ·
                    have : d = 95714 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95713 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 95697 ≤ d
          ·
            by_cases h : 95705 ≤ d
            ·
              by_cases h : 95709 ≤ d
              ·
                by_cases h : 95711 ≤ d
                ·
                  by_cases h : 95712 ≤ d
                  ·
                    have : d = 95712 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95711 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95710 ≤ d
                  ·
                    have : d = 95710 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 95709 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95707 ≤ d
                ·
                  by_cases h : 95708 ≤ d
                  ·
                    have : d = 95708 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95707 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95706 ≤ d
                  ·
                    have : d = 95706 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95705 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95701 ≤ d
              ·
                by_cases h : 95703 ≤ d
                ·
                  by_cases h : 95704 ≤ d
                  ·
                    have : d = 95704 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95703 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95702 ≤ d
                  ·
                    have : d = 95702 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95701 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95699 ≤ d
                ·
                  by_cases h : 95700 ≤ d
                  ·
                    have : d = 95700 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 29) (by norm_num)
      exact by decide
                  ·
                    have : d = 95699 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95698 ≤ d
                  ·
                    have : d = 95698 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95697 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 95689 ≤ d
            ·
              by_cases h : 95693 ≤ d
              ·
                by_cases h : 95695 ≤ d
                ·
                  by_cases h : 95696 ≤ d
                  ·
                    have : d = 95696 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95695 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95694 ≤ d
                  ·
                    have : d = 95694 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 41) (by norm_num)
      exact by decide
                  ·
                    have : d = 95693 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95691 ≤ d
                ·
                  by_cases h : 95692 ≤ d
                  ·
                    have : d = 95692 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 47) (by norm_num)
      exact by decide
                  ·
                    have : d = 95691 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95690 ≤ d
                  ·
                    have : d = 95690 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95689 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95685 ≤ d
              ·
                by_cases h : 95687 ≤ d
                ·
                  by_cases h : 95688 ≤ d
                  ·
                    have : d = 95688 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 443) (by norm_num)
      exact by decide
                  ·
                    have : d = 95687 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95686 ≤ d
                  ·
                    have : d = 95686 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95685 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95683 ≤ d
                ·
                  by_cases h : 95684 ≤ d
                  ·
                    have : d = 95684 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95683 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95682 ≤ d
                  ·
                    have : d = 95682 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95681 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 95649 ≤ d
        ·
          by_cases h : 95665 ≤ d
          ·
            by_cases h : 95673 ≤ d
            ·
              by_cases h : 95677 ≤ d
              ·
                by_cases h : 95679 ≤ d
                ·
                  by_cases h : 95680 ≤ d
                  ·
                    have : d = 95680 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 95679 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95678 ≤ d
                  ·
                    have : d = 95678 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95677 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95675 ≤ d
                ·
                  by_cases h : 95676 ≤ d
                  ·
                    have : d = 95676 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95675 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95674 ≤ d
                  ·
                    have : d = 95674 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 151339) (by norm_num)
      right
      exact ⟨95674, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95673 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95669 ≤ d
              ·
                by_cases h : 95671 ≤ d
                ·
                  by_cases h : 95672 ≤ d
                  ·
                    have : d = 95672 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95671 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95670 ≤ d
                  ·
                    have : d = 95670 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95669 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95667 ≤ d
                ·
                  by_cases h : 95668 ≤ d
                  ·
                    have : d = 95668 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23917) (by norm_num)
      exact by decide
                  ·
                    have : d = 95667 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95666 ≤ d
                  ·
                    have : d = 95666 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95665 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 95657 ≤ d
            ·
              by_cases h : 95661 ≤ d
              ·
                by_cases h : 95663 ≤ d
                ·
                  by_cases h : 95664 ≤ d
                  ·
                    have : d = 95664 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1993) (by norm_num)
      exact by decide
                  ·
                    have : d = 95663 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95662 ≤ d
                  ·
                    have : d = 95662 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 6833) (by norm_num)
      exact by decide
                  ·
                    have : d = 95661 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95659 ≤ d
                ·
                  by_cases h : 95660 ≤ d
                  ·
                    have : d = 95660 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95659 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95658 ≤ d
                  ·
                    have : d = 95658 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 107) (by norm_num)
      exact by decide
                  ·
                    have : d = 95657 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95653 ≤ d
              ·
                by_cases h : 95655 ≤ d
                ·
                  by_cases h : 95656 ≤ d
                  ·
                    have : d = 95656 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95655 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95654 ≤ d
                  ·
                    have : d = 95654 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95653 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95651 ≤ d
                ·
                  by_cases h : 95652 ≤ d
                  ·
                    have : d = 95652 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2657) (by norm_num)
      exact by decide
                  ·
                    have : d = 95651 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95650 ≤ d
                  ·
                    have : d = 95650 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1913) (by norm_num)
      exact by decide
                  ·
                    have : d = 95649 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 95633 ≤ d
          ·
            by_cases h : 95641 ≤ d
            ·
              by_cases h : 95645 ≤ d
              ·
                by_cases h : 95647 ≤ d
                ·
                  by_cases h : 95648 ≤ d
                  ·
                    have : d = 95648 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95647 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95646 ≤ d
                  ·
                    have : d = 95646 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95645 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95643 ≤ d
                ·
                  by_cases h : 95644 ≤ d
                  ·
                    have : d = 95644 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23911) (by norm_num)
      exact by decide
                  ·
                    have : d = 95643 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95642 ≤ d
                  ·
                    have : d = 95642 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95641 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95637 ≤ d
              ·
                by_cases h : 95639 ≤ d
                ·
                  by_cases h : 95640 ≤ d
                  ·
                    have : d = 95640 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 797) (by norm_num)
      exact by decide
                  ·
                    have : d = 95639 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95638 ≤ d
                  ·
                    have : d = 95638 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95637 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95635 ≤ d
                ·
                  by_cases h : 95636 ≤ d
                  ·
                    have : d = 95636 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95635 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95634 ≤ d
                  ·
                    have : d = 95634 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23) (by norm_num)
      exact by decide
                  ·
                    have : d = 95633 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 95625 ≤ d
            ·
              by_cases h : 95629 ≤ d
              ·
                by_cases h : 95631 ≤ d
                ·
                  by_cases h : 95632 ≤ d
                  ·
                    have : d = 95632 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 43) (by norm_num)
      exact by decide
                  ·
                    have : d = 95631 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95630 ≤ d
                  ·
                    have : d = 95630 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95629 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95627 ≤ d
                ·
                  by_cases h : 95628 ≤ d
                  ·
                    have : d = 95628 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95627 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95626 ≤ d
                  ·
                    have : d = 95626 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95625 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95621 ≤ d
              ·
                by_cases h : 95623 ≤ d
                ·
                  by_cases h : 95624 ≤ d
                  ·
                    have : d = 95624 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95623 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95622 ≤ d
                  ·
                    have : d = 95622 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 15937) (by norm_num)
      exact by decide
                  ·
                    have : d = 95621 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95619 ≤ d
                ·
                  by_cases h : 95620 ≤ d
                  ·
                    have : d = 95620 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 683) (by norm_num)
      exact by decide
                  ·
                    have : d = 95619 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95618 ≤ d
                  ·
                    have : d = 95618 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95617 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 95553 ≤ d
      ·
        by_cases h : 95585 ≤ d
        ·
          by_cases h : 95601 ≤ d
          ·
            by_cases h : 95609 ≤ d
            ·
              by_cases h : 95613 ≤ d
              ·
                by_cases h : 95615 ≤ d
                ·
                  by_cases h : 95616 ≤ d
                  ·
                    have : d = 95616 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95615 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95614 ≤ d
                  ·
                    have : d = 95614 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95613 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95611 ≤ d
                ·
                  by_cases h : 95612 ≤ d
                  ·
                    have : d = 95612 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95611 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95610 ≤ d
                  ·
                    have : d = 95610 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3187) (by norm_num)
      exact by decide
                  ·
                    have : d = 95609 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95605 ≤ d
              ·
                by_cases h : 95607 ≤ d
                ·
                  by_cases h : 95608 ≤ d
                  ·
                    have : d = 95608 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 95607 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95606 ≤ d
                  ·
                    have : d = 95606 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95605 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95603 ≤ d
                ·
                  by_cases h : 95604 ≤ d
                  ·
                    have : d = 95604 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 31) (by norm_num)
      exact by decide
                  ·
                    have : d = 95603 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95602 ≤ d
                  ·
                    have : d = 95602 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 95601 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 95593 ≤ d
            ·
              by_cases h : 95597 ≤ d
              ·
                by_cases h : 95599 ≤ d
                ·
                  by_cases h : 95600 ≤ d
                  ·
                    have : d = 95600 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95599 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95598 ≤ d
                  ·
                    have : d = 95598 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 47) (by norm_num)
      exact by decide
                  ·
                    have : d = 95597 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95595 ≤ d
                ·
                  by_cases h : 95596 ≤ d
                  ·
                    have : d = 95596 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95595 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95594 ≤ d
                  ·
                    have : d = 95594 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95593 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95589 ≤ d
              ·
                by_cases h : 95591 ≤ d
                ·
                  by_cases h : 95592 ≤ d
                  ·
                    have : d = 95592 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 569) (by norm_num)
      exact by decide
                  ·
                    have : d = 95591 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95590 ≤ d
                  ·
                    have : d = 95590 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 79) (by norm_num)
      exact by decide
                  ·
                    have : d = 95589 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95587 ≤ d
                ·
                  by_cases h : 95588 ≤ d
                  ·
                    have : d = 95588 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95587 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95586 ≤ d
                  ·
                    have : d = 95586 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95585 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 95569 ≤ d
          ·
            by_cases h : 95577 ≤ d
            ·
              by_cases h : 95581 ≤ d
              ·
                by_cases h : 95583 ≤ d
                ·
                  by_cases h : 95584 ≤ d
                  ·
                    have : d = 95584 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 29) (by norm_num)
      exact by decide
                  ·
                    have : d = 95583 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95582 ≤ d
                  ·
                    have : d = 95582 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95581 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95579 ≤ d
                ·
                  by_cases h : 95580 ≤ d
                  ·
                    have : d = 95580 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 59) (by norm_num)
      exact by decide
                  ·
                    have : d = 95579 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95578 ≤ d
                  ·
                    have : d = 95578 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 6827) (by norm_num)
      exact by decide
                  ·
                    have : d = 95577 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95573 ≤ d
              ·
                by_cases h : 95575 ≤ d
                ·
                  by_cases h : 95576 ≤ d
                  ·
                    have : d = 95576 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95575 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95574 ≤ d
                  ·
                    have : d = 95574 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 95573 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95571 ≤ d
                ·
                  by_cases h : 95572 ≤ d
                  ·
                    have : d = 95572 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95571 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95570 ≤ d
                  ·
                    have : d = 95570 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95569 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 95561 ≤ d
            ·
              by_cases h : 95565 ≤ d
              ·
                by_cases h : 95567 ≤ d
                ·
                  by_cases h : 95568 ≤ d
                  ·
                    have : d = 95568 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 181) (by norm_num)
      exact by decide
                  ·
                    have : d = 95567 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95566 ≤ d
                  ·
                    have : d = 95566 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95565 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95563 ≤ d
                ·
                  by_cases h : 95564 ≤ d
                  ·
                    have : d = 95564 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95563 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95562 ≤ d
                  ·
                    have : d = 95562 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5309) (by norm_num)
      exact by decide
                  ·
                    have : d = 95561 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95557 ≤ d
              ·
                by_cases h : 95559 ≤ d
                ·
                  by_cases h : 95560 ≤ d
                  ·
                    have : d = 95560 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2389) (by norm_num)
      exact by decide
                  ·
                    have : d = 95559 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95558 ≤ d
                  ·
                    have : d = 95558 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95557 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95555 ≤ d
                ·
                  by_cases h : 95556 ≤ d
                  ·
                    have : d = 95556 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95555 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95554 ≤ d
                  ·
                    have : d = 95554 := by omega
                    subst d
      exact fullRecordGapTerm03523_not_prime
                  ·
                    have : d = 95553 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 95521 ≤ d
        ·
          by_cases h : 95537 ≤ d
          ·
            by_cases h : 95545 ≤ d
            ·
              by_cases h : 95549 ≤ d
              ·
                by_cases h : 95551 ≤ d
                ·
                  by_cases h : 95552 ≤ d
                  ·
                    have : d = 95552 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95551 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95550 ≤ d
                  ·
                    have : d = 95550 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95549 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95547 ≤ d
                ·
                  by_cases h : 95548 ≤ d
                  ·
                    have : d = 95548 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23887) (by norm_num)
      exact by decide
                  ·
                    have : d = 95547 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95546 ≤ d
                  ·
                    have : d = 95546 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95545 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95541 ≤ d
              ·
                by_cases h : 95543 ≤ d
                ·
                  by_cases h : 95544 ≤ d
                  ·
                    have : d = 95544 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95543 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95542 ≤ d
                  ·
                    have : d = 95542 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23) (by norm_num)
      exact by decide
                  ·
                    have : d = 95541 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95539 ≤ d
                ·
                  by_cases h : 95540 ≤ d
                  ·
                    have : d = 95540 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95539 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95538 ≤ d
                  ·
                    have : d = 95538 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 15923) (by norm_num)
      exact by decide
                  ·
                    have : d = 95537 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 95529 ≤ d
            ·
              by_cases h : 95533 ≤ d
              ·
                by_cases h : 95535 ≤ d
                ·
                  by_cases h : 95536 ≤ d
                  ·
                    have : d = 95536 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95535 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95534 ≤ d
                  ·
                    have : d = 95534 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95533 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95531 ≤ d
                ·
                  by_cases h : 95532 ≤ d
                  ·
                    have : d = 95532 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 95531 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95530 ≤ d
                  ·
                    have : d = 95530 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95529 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95525 ≤ d
              ·
                by_cases h : 95527 ≤ d
                ·
                  by_cases h : 95528 ≤ d
                  ·
                    have : d = 95528 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95527 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95526 ≤ d
                  ·
                    have : d = 95526 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95525 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95523 ≤ d
                ·
                  by_cases h : 95524 ≤ d
                  ·
                    have : d = 95524 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 95523 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95522 ≤ d
                  ·
                    have : d = 95522 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95521 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 95505 ≤ d
          ·
            by_cases h : 95513 ≤ d
            ·
              by_cases h : 95517 ≤ d
              ·
                by_cases h : 95519 ≤ d
                ·
                  by_cases h : 95520 ≤ d
                  ·
                    have : d = 95520 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 199) (by norm_num)
      exact by decide
                  ·
                    have : d = 95519 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95518 ≤ d
                  ·
                    have : d = 95518 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 163) (by norm_num)
      exact by decide
                  ·
                    have : d = 95517 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95515 ≤ d
                ·
                  by_cases h : 95516 ≤ d
                  ·
                    have : d = 95516 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95515 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95514 ≤ d
                  ·
                    have : d = 95514 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 15919) (by norm_num)
      exact by decide
                  ·
                    have : d = 95513 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95509 ≤ d
              ·
                by_cases h : 95511 ≤ d
                ·
                  by_cases h : 95512 ≤ d
                  ·
                    have : d = 95512 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11939) (by norm_num)
      exact by decide
                  ·
                    have : d = 95511 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95510 ≤ d
                  ·
                    have : d = 95510 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95509 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95507 ≤ d
                ·
                  by_cases h : 95508 ≤ d
                  ·
                    have : d = 95508 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 379) (by norm_num)
      exact by decide
                  ·
                    have : d = 95507 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95506 ≤ d
                  ·
                    have : d = 95506 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95505 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 95497 ≤ d
            ·
              by_cases h : 95501 ≤ d
              ·
                by_cases h : 95503 ≤ d
                ·
                  by_cases h : 95504 ≤ d
                  ·
                    have : d = 95504 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95503 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95502 ≤ d
                  ·
                    have : d = 95502 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95501 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95499 ≤ d
                ·
                  by_cases h : 95500 ≤ d
                  ·
                    have : d = 95500 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 191) (by norm_num)
      exact by decide
                  ·
                    have : d = 95499 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95498 ≤ d
                  ·
                    have : d = 95498 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95497 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95493 ≤ d
              ·
                by_cases h : 95495 ≤ d
                ·
                  by_cases h : 95496 ≤ d
                  ·
                    have : d = 95496 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95495 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95494 ≤ d
                  ·
                    have : d = 95494 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 95493 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95491 ≤ d
                ·
                  by_cases h : 95492 ≤ d
                  ·
                    have : d = 95492 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95491 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95490 ≤ d
                  ·
                    have : d = 95490 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1061) (by norm_num)
      exact by decide
                  ·
                    have : d = 95489 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
  ·
    by_cases h : 95361 ≤ d
    ·
      by_cases h : 95425 ≤ d
      ·
        by_cases h : 95457 ≤ d
        ·
          by_cases h : 95473 ≤ d
          ·
            by_cases h : 95481 ≤ d
            ·
              by_cases h : 95485 ≤ d
              ·
                by_cases h : 95487 ≤ d
                ·
                  by_cases h : 95488 ≤ d
                  ·
                    have : d = 95488 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95487 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95486 ≤ d
                  ·
                    have : d = 95486 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95485 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95483 ≤ d
                ·
                  by_cases h : 95484 ≤ d
                  ·
                    have : d = 95484 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95483 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95482 ≤ d
                  ·
                    have : d = 95482 := by omega
                    subst d
      exact fullRecordGapTerm03524_not_prime
                  ·
                    have : d = 95481 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95477 ≤ d
              ·
                by_cases h : 95479 ≤ d
                ·
                  by_cases h : 95480 ≤ d
                  ·
                    have : d = 95480 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95479 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95478 ≤ d
                  ·
                    have : d = 95478 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 15913) (by norm_num)
      exact by decide
                  ·
                    have : d = 95477 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95475 ≤ d
                ·
                  by_cases h : 95476 ≤ d
                  ·
                    have : d = 95476 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95475 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95474 ≤ d
                  ·
                    have : d = 95474 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95473 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 95465 ≤ d
            ·
              by_cases h : 95469 ≤ d
              ·
                by_cases h : 95471 ≤ d
                ·
                  by_cases h : 95472 ≤ d
                  ·
                    have : d = 95472 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 95471 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95470 ≤ d
                  ·
                    have : d = 95470 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 9547) (by norm_num)
      exact by decide
                  ·
                    have : d = 95469 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95467 ≤ d
                ·
                  by_cases h : 95468 ≤ d
                  ·
                    have : d = 95468 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95467 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95466 ≤ d
                  ·
                    have : d = 95466 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95465 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95461 ≤ d
              ·
                by_cases h : 95463 ≤ d
                ·
                  by_cases h : 95464 ≤ d
                  ·
                    have : d = 95464 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11933) (by norm_num)
      exact by decide
                  ·
                    have : d = 95463 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95462 ≤ d
                  ·
                    have : d = 95462 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95461 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95459 ≤ d
                ·
                  by_cases h : 95460 ≤ d
                  ·
                    have : d = 95460 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95459 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95458 ≤ d
                  ·
                    have : d = 95458 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 4339) (by norm_num)
      exact by decide
                  ·
                    have : d = 95457 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 95441 ≤ d
          ·
            by_cases h : 95449 ≤ d
            ·
              by_cases h : 95453 ≤ d
              ·
                by_cases h : 95455 ≤ d
                ·
                  by_cases h : 95456 ≤ d
                  ·
                    have : d = 95456 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95455 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95454 ≤ d
                  ·
                    have : d = 95454 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5303) (by norm_num)
      exact by decide
                  ·
                    have : d = 95453 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95451 ≤ d
                ·
                  by_cases h : 95452 ≤ d
                  ·
                    have : d = 95452 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 487) (by norm_num)
      exact by decide
                  ·
                    have : d = 95451 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95450 ≤ d
                  ·
                    have : d = 95450 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95449 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95445 ≤ d
              ·
                by_cases h : 95447 ≤ d
                ·
                  by_cases h : 95448 ≤ d
                  ·
                    have : d = 95448 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 41) (by norm_num)
      exact by decide
                  ·
                    have : d = 95447 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95446 ≤ d
                  ·
                    have : d = 95446 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95445 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95443 ≤ d
                ·
                  by_cases h : 95444 ≤ d
                  ·
                    have : d = 95444 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95443 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95442 ≤ d
                  ·
                    have : d = 95442 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 15907) (by norm_num)
      exact by decide
                  ·
                    have : d = 95441 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 95433 ≤ d
            ·
              by_cases h : 95437 ≤ d
              ·
                by_cases h : 95439 ≤ d
                ·
                  by_cases h : 95440 ≤ d
                  ·
                    have : d = 95440 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95439 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95438 ≤ d
                  ·
                    have : d = 95438 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95437 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95435 ≤ d
                ·
                  by_cases h : 95436 ≤ d
                  ·
                    have : d = 95436 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95435 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95434 ≤ d
                  ·
                    have : d = 95434 := by omega
                    subst d
      exact fullRecordGapTerm03525_not_prime
                  ·
                    have : d = 95433 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95429 ≤ d
              ·
                by_cases h : 95431 ≤ d
                ·
                  by_cases h : 95432 ≤ d
                  ·
                    have : d = 95432 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95431 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95430 ≤ d
                  ·
                    have : d = 95430 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3181) (by norm_num)
      exact by decide
                  ·
                    have : d = 95429 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95427 ≤ d
                ·
                  by_cases h : 95428 ≤ d
                  ·
                    have : d = 95428 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23857) (by norm_num)
      exact by decide
                  ·
                    have : d = 95427 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95426 ≤ d
                  ·
                    have : d = 95426 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95425 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 95393 ≤ d
        ·
          by_cases h : 95409 ≤ d
          ·
            by_cases h : 95417 ≤ d
            ·
              by_cases h : 95421 ≤ d
              ·
                by_cases h : 95423 ≤ d
                ·
                  by_cases h : 95424 ≤ d
                  ·
                    have : d = 95424 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 71) (by norm_num)
      exact by decide
                  ·
                    have : d = 95423 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95422 ≤ d
                  ·
                    have : d = 95422 := by omega
                    subst d
      exact fullRecordGapTerm03526_not_prime
                  ·
                    have : d = 95421 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95419 ≤ d
                ·
                  by_cases h : 95420 ≤ d
                  ·
                    have : d = 95420 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95419 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95418 ≤ d
                  ·
                    have : d = 95418 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95417 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95413 ≤ d
              ·
                by_cases h : 95415 ≤ d
                ·
                  by_cases h : 95416 ≤ d
                  ·
                    have : d = 95416 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95415 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95414 ≤ d
                  ·
                    have : d = 95414 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95413 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95411 ≤ d
                ·
                  by_cases h : 95412 ≤ d
                  ·
                    have : d = 95412 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7951) (by norm_num)
      exact by decide
                  ·
                    have : d = 95411 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95410 ≤ d
                  ·
                    have : d = 95410 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 29) (by norm_num)
      exact by decide
                  ·
                    have : d = 95409 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 95401 ≤ d
            ·
              by_cases h : 95405 ≤ d
              ·
                by_cases h : 95407 ≤ d
                ·
                  by_cases h : 95408 ≤ d
                  ·
                    have : d = 95408 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95407 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95406 ≤ d
                  ·
                    have : d = 95406 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95405 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95403 ≤ d
                ·
                  by_cases h : 95404 ≤ d
                  ·
                    have : d = 95404 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95403 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95402 ≤ d
                  ·
                    have : d = 95402 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95401 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95397 ≤ d
              ·
                by_cases h : 95399 ≤ d
                ·
                  by_cases h : 95400 ≤ d
                  ·
                    have : d = 95400 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 53) (by norm_num)
      exact by decide
                  ·
                    have : d = 95399 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95398 ≤ d
                  ·
                    have : d = 95398 := by omega
                    subst d
      exact fullRecordGapTerm03527_not_prime
                  ·
                    have : d = 95397 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95395 ≤ d
                ·
                  by_cases h : 95396 ≤ d
                  ·
                    have : d = 95396 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95395 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95394 ≤ d
                  ·
                    have : d = 95394 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 95393 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 95377 ≤ d
          ·
            by_cases h : 95385 ≤ d
            ·
              by_cases h : 95389 ≤ d
              ·
                by_cases h : 95391 ≤ d
                ·
                  by_cases h : 95392 ≤ d
                  ·
                    have : d = 95392 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 271) (by norm_num)
      exact by decide
                  ·
                    have : d = 95391 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95390 ≤ d
                  ·
                    have : d = 95390 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95389 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95387 ≤ d
                ·
                  by_cases h : 95388 ≤ d
                  ·
                    have : d = 95388 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7949) (by norm_num)
      exact by decide
                  ·
                    have : d = 95387 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95386 ≤ d
                  ·
                    have : d = 95386 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95385 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95381 ≤ d
              ·
                by_cases h : 95383 ≤ d
                ·
                  by_cases h : 95384 ≤ d
                  ·
                    have : d = 95384 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95383 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95382 ≤ d
                  ·
                    have : d = 95382 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 757) (by norm_num)
      exact by decide
                  ·
                    have : d = 95381 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95379 ≤ d
                ·
                  by_cases h : 95380 ≤ d
                  ·
                    have : d = 95380 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 95379 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95378 ≤ d
                  ·
                    have : d = 95378 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95377 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 95369 ≤ d
            ·
              by_cases h : 95373 ≤ d
              ·
                by_cases h : 95375 ≤ d
                ·
                  by_cases h : 95376 ≤ d
                  ·
                    have : d = 95376 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95375 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95374 ≤ d
                  ·
                    have : d = 95374 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95373 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95371 ≤ d
                ·
                  by_cases h : 95372 ≤ d
                  ·
                    have : d = 95372 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95371 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95370 ≤ d
                  ·
                    have : d = 95370 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 95369 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95365 ≤ d
              ·
                by_cases h : 95367 ≤ d
                ·
                  by_cases h : 95368 ≤ d
                  ·
                    have : d = 95368 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 95367 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95366 ≤ d
                  ·
                    have : d = 95366 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95365 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95363 ≤ d
                ·
                  by_cases h : 95364 ≤ d
                  ·
                    have : d = 95364 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 883) (by norm_num)
      exact by decide
                  ·
                    have : d = 95363 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95362 ≤ d
                  ·
                    have : d = 95362 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95361 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    ·
      by_cases h : 95297 ≤ d
      ·
        by_cases h : 95329 ≤ d
        ·
          by_cases h : 95345 ≤ d
          ·
            by_cases h : 95353 ≤ d
            ·
              by_cases h : 95357 ≤ d
              ·
                by_cases h : 95359 ≤ d
                ·
                  by_cases h : 95360 ≤ d
                  ·
                    have : d = 95360 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95359 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95358 ≤ d
                  ·
                    have : d = 95358 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23) (by norm_num)
      exact by decide
                  ·
                    have : d = 95357 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95355 ≤ d
                ·
                  by_cases h : 95356 ≤ d
                  ·
                    have : d = 95356 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95355 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95354 ≤ d
                  ·
                    have : d = 95354 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95353 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95349 ≤ d
              ·
                by_cases h : 95351 ≤ d
                ·
                  by_cases h : 95352 ≤ d
                  ·
                    have : d = 95352 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95351 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95350 ≤ d
                  ·
                    have : d = 95350 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 1907) (by norm_num)
      exact by decide
                  ·
                    have : d = 95349 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95347 ≤ d
                ·
                  by_cases h : 95348 ≤ d
                  ·
                    have : d = 95348 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95347 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95346 ≤ d
                  ·
                    have : d = 95346 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95345 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 95337 ≤ d
            ·
              by_cases h : 95341 ≤ d
              ·
                by_cases h : 95343 ≤ d
                ·
                  by_cases h : 95344 ≤ d
                  ·
                    have : d = 95344 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 59) (by norm_num)
      exact by decide
                  ·
                    have : d = 95343 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95342 ≤ d
                  ·
                    have : d = 95342 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95341 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95339 ≤ d
                ·
                  by_cases h : 95340 ≤ d
                  ·
                    have : d = 95340 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 227) (by norm_num)
      exact by decide
                  ·
                    have : d = 95339 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95338 ≤ d
                  ·
                    have : d = 95338 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 73) (by norm_num)
      exact by decide
                  ·
                    have : d = 95337 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95333 ≤ d
              ·
                by_cases h : 95335 ≤ d
                ·
                  by_cases h : 95336 ≤ d
                  ·
                    have : d = 95336 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95335 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95334 ≤ d
                  ·
                    have : d = 95334 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95333 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95331 ≤ d
                ·
                  by_cases h : 95332 ≤ d
                  ·
                    have : d = 95332 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 23833) (by norm_num)
      exact by decide
                  ·
                    have : d = 95331 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95330 ≤ d
                  ·
                    have : d = 95330 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95329 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 95313 ≤ d
          ·
            by_cases h : 95321 ≤ d
            ·
              by_cases h : 95325 ≤ d
              ·
                by_cases h : 95327 ≤ d
                ·
                  by_cases h : 95328 ≤ d
                  ·
                    have : d = 95328 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 331) (by norm_num)
      exact by decide
                  ·
                    have : d = 95327 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95326 ≤ d
                  ·
                    have : d = 95326 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95325 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95323 ≤ d
                ·
                  by_cases h : 95324 ≤ d
                  ·
                    have : d = 95324 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95323 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95322 ≤ d
                  ·
                    have : d = 95322 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 15887) (by norm_num)
      exact by decide
                  ·
                    have : d = 95321 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95317 ≤ d
              ·
                by_cases h : 95319 ≤ d
                ·
                  by_cases h : 95320 ≤ d
                  ·
                    have : d = 95320 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95319 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95318 ≤ d
                  ·
                    have : d = 95318 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95317 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95315 ≤ d
                ·
                  by_cases h : 95316 ≤ d
                  ·
                    have : d = 95316 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95315 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95314 ≤ d
                  ·
                    have : d = 95314 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 141307) (by norm_num)
      right
      exact ⟨95314, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95313 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 95305 ≤ d
            ·
              by_cases h : 95309 ≤ d
              ·
                by_cases h : 95311 ≤ d
                ·
                  by_cases h : 95312 ≤ d
                  ·
                    have : d = 95312 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95311 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95310 ≤ d
                  ·
                    have : d = 95310 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 353) (by norm_num)
      exact by decide
                  ·
                    have : d = 95309 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95307 ≤ d
                ·
                  by_cases h : 95308 ≤ d
                  ·
                    have : d = 95308 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95307 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95306 ≤ d
                  ·
                    have : d = 95306 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95305 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95301 ≤ d
              ·
                by_cases h : 95303 ≤ d
                ·
                  by_cases h : 95304 ≤ d
                  ·
                    have : d = 95304 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 19) (by norm_num)
      exact by decide
                  ·
                    have : d = 95303 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95302 ≤ d
                  ·
                    have : d = 95302 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 95301 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95299 ≤ d
                ·
                  by_cases h : 95300 ≤ d
                  ·
                    have : d = 95300 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95299 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95298 ≤ d
                  ·
                    have : d = 95298 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2269) (by norm_num)
      exact by decide
                  ·
                    have : d = 95297 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      ·
        by_cases h : 95265 ≤ d
        ·
          by_cases h : 95281 ≤ d
          ·
            by_cases h : 95289 ≤ d
            ·
              by_cases h : 95293 ≤ d
              ·
                by_cases h : 95295 ≤ d
                ·
                  by_cases h : 95296 ≤ d
                  ·
                    have : d = 95296 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95295 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95294 ≤ d
                  ·
                    have : d = 95294 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95293 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95291 ≤ d
                ·
                  by_cases h : 95292 ≤ d
                  ·
                    have : d = 95292 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95291 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95290 ≤ d
                  ·
                    have : d = 95290 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 95289 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95285 ≤ d
              ·
                by_cases h : 95287 ≤ d
                ·
                  by_cases h : 95288 ≤ d
                  ·
                    have : d = 95288 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95287 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95286 ≤ d
                  ·
                    have : d = 95286 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95285 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95283 ≤ d
                ·
                  by_cases h : 95284 ≤ d
                  ·
                    have : d = 95284 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 41) (by norm_num)
      exact by decide
                  ·
                    have : d = 95283 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95282 ≤ d
                  ·
                    have : d = 95282 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95281 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 95273 ≤ d
            ·
              by_cases h : 95277 ≤ d
              ·
                by_cases h : 95279 ≤ d
                ·
                  by_cases h : 95280 ≤ d
                  ·
                    have : d = 95280 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 397) (by norm_num)
      exact by decide
                  ·
                    have : d = 95279 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95278 ≤ d
                  ·
                    have : d = 95278 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95277 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95275 ≤ d
                ·
                  by_cases h : 95276 ≤ d
                  ·
                    have : d = 95276 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95275 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95274 ≤ d
                  ·
                    have : d = 95274 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 67) (by norm_num)
      exact by decide
                  ·
                    have : d = 95273 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95269 ≤ d
              ·
                by_cases h : 95271 ≤ d
                ·
                  by_cases h : 95272 ≤ d
                  ·
                    have : d = 95272 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11909) (by norm_num)
      exact by decide
                  ·
                    have : d = 95271 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95270 ≤ d
                  ·
                    have : d = 95270 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95269 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95267 ≤ d
                ·
                  by_cases h : 95268 ≤ d
                  ·
                    have : d = 95268 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 17) (by norm_num)
      exact by decide
                  ·
                    have : d = 95267 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95266 ≤ d
                  ·
                    have : d = 95266 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95265 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        ·
          by_cases h : 95249 ≤ d
          ·
            by_cases h : 95257 ≤ d
            ·
              by_cases h : 95261 ≤ d
              ·
                by_cases h : 95263 ≤ d
                ·
                  by_cases h : 95264 ≤ d
                  ·
                    have : d = 95264 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95263 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95262 ≤ d
                  ·
                    have : d = 95262 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 15877) (by norm_num)
      exact by decide
                  ·
                    have : d = 95261 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95259 ≤ d
                ·
                  by_cases h : 95260 ≤ d
                  ·
                    have : d = 95260 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 433) (by norm_num)
      exact by decide
                  ·
                    have : d = 95259 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95258 ≤ d
                  ·
                    have : d = 95258 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95257 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95253 ≤ d
              ·
                by_cases h : 95255 ≤ d
                ·
                  by_cases h : 95256 ≤ d
                  ·
                    have : d = 95256 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95255 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95254 ≤ d
                  ·
                    have : d = 95254 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 97) (by norm_num)
      exact by decide
                  ·
                    have : d = 95253 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95251 ≤ d
                ·
                  by_cases h : 95252 ≤ d
                  ·
                    have : d = 95252 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95251 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95250 ≤ d
                  ·
                    have : d = 95250 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95249 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
          ·
            by_cases h : 95241 ≤ d
            ·
              by_cases h : 95245 ≤ d
              ·
                by_cases h : 95247 ≤ d
                ·
                  by_cases h : 95248 ≤ d
                  ·
                    have : d = 95248 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5953) (by norm_num)
      exact by decide
                  ·
                    have : d = 95247 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95246 ≤ d
                  ·
                    have : d = 95246 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95245 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95243 ≤ d
                ·
                  by_cases h : 95244 ≤ d
                  ·
                    have : d = 95244 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 7937) (by norm_num)
      exact by decide
                  ·
                    have : d = 95243 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95242 ≤ d
                  ·
                    have : d = 95242 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 11) (by norm_num)
      right
      exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95241 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
            ·
              by_cases h : 95237 ≤ d
              ·
                by_cases h : 95239 ≤ d
                ·
                  by_cases h : 95240 ≤ d
                  ·
                    have : d = 95240 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95239 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95238 ≤ d
                  ·
                    have : d = 95238 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 13) (by norm_num)
      exact by decide
                  ·
                    have : d = 95237 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
              ·
                by_cases h : 95235 ≤ d
                ·
                  by_cases h : 95236 ≤ d
                  ·
                    have : d = 95236 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 5) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95235 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
                ·
                  by_cases h : 95234 ≤ d
                  ·
                    have : d = 95234 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 3) (by norm_num)
      right
      exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
                  ·
                    have : d = 95233 := by omega
                    subst d
      apply fullRecordGap_sub_not_prime (q := 2) (by norm_num)
      right
      exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩

end PrimeFactorUnimodality
