import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 198 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16703) (q := 16729) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16729) (q := 16741) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16741) (q := 16747) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16747) (q := 16759) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16759) (q := 16763) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16763) (q := 16787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16787) (q := 16811) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16811) (q := 16823) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part06_chain :
    DusartPrimeRowsChain 16703 16823 dusartPrimeRows_16319_17158_part06 := by
  apply DusartPrimeRowsChain.cons
  · change 16703 ≤ 16703; omega
  · change 16703 ≤ 16728; omega
  · apply DusartPrimeRowsChain.cons
    · change 16729 ≤ 16729; omega
    · change 16729 ≤ 16740; omega
    · apply DusartPrimeRowsChain.cons
      · change 16741 ≤ 16741; omega
      · change 16741 ≤ 16746; omega
      · apply DusartPrimeRowsChain.cons
        · change 16747 ≤ 16747; omega
        · change 16747 ≤ 16758; omega
        · apply DusartPrimeRowsChain.cons
          · change 16759 ≤ 16759; omega
          · change 16759 ≤ 16762; omega
          · apply DusartPrimeRowsChain.cons
            · change 16763 ≤ 16763; omega
            · change 16763 ≤ 16786; omega
            · apply DusartPrimeRowsChain.cons
              · change 16787 ≤ 16787; omega
              · change 16787 ≤ 16810; omega
              · apply DusartPrimeRowsChain.cons
                · change 16811 ≤ 16811; omega
                · change 16811 ≤ 16822; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
