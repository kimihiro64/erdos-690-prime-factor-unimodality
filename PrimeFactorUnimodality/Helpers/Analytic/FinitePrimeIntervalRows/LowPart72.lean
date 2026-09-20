import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 72 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 7793) (q := 7817) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7817) (q := 7823) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7823) (q := 7829) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7829) (q := 7841) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7841) (q := 7853) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7853) (q := 7867) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7867) (q := 7873) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7873) (q := 7877) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part02_chain :
    DusartPrimeRowsChain 7793 7877 dusartPrimeRows_7717_8110_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 7793 ≤ 7793; omega
  · change 7793 ≤ 7816; omega
  · apply DusartPrimeRowsChain.cons
    · change 7817 ≤ 7817; omega
    · change 7817 ≤ 7822; omega
    · apply DusartPrimeRowsChain.cons
      · change 7823 ≤ 7823; omega
      · change 7823 ≤ 7828; omega
      · apply DusartPrimeRowsChain.cons
        · change 7829 ≤ 7829; omega
        · change 7829 ≤ 7840; omega
        · apply DusartPrimeRowsChain.cons
          · change 7841 ≤ 7841; omega
          · change 7841 ≤ 7852; omega
          · apply DusartPrimeRowsChain.cons
            · change 7853 ≤ 7853; omega
            · change 7853 ≤ 7866; omega
            · apply DusartPrimeRowsChain.cons
              · change 7867 ≤ 7867; omega
              · change 7867 ≤ 7872; omega
              · apply DusartPrimeRowsChain.cons
                · change 7873 ≤ 7873; omega
                · change 7873 ≤ 7876; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
