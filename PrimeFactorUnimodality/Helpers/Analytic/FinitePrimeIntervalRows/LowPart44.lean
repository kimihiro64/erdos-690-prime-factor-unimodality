import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 44 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6007_6310_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6310 (p := 6007) (q := 6011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6011) (q := 6029) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6029) (q := 6037) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6037) (q := 6043) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6043) (q := 6047) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6047) (q := 6053) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6053) (q := 6067) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6067) (q := 6073) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6007_6310_part01_chain :
    DusartPrimeRowsChain 6007 6073 dusartPrimeRows_6007_6310_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 6007 ≤ 6007; omega
  · change 6007 ≤ 6010; omega
  · apply DusartPrimeRowsChain.cons
    · change 6011 ≤ 6011; omega
    · change 6011 ≤ 6028; omega
    · apply DusartPrimeRowsChain.cons
      · change 6029 ≤ 6029; omega
      · change 6029 ≤ 6036; omega
      · apply DusartPrimeRowsChain.cons
        · change 6037 ≤ 6037; omega
        · change 6037 ≤ 6042; omega
        · apply DusartPrimeRowsChain.cons
          · change 6043 ≤ 6043; omega
          · change 6043 ≤ 6046; omega
          · apply DusartPrimeRowsChain.cons
            · change 6047 ≤ 6047; omega
            · change 6047 ≤ 6052; omega
            · apply DusartPrimeRowsChain.cons
              · change 6053 ≤ 6053; omega
              · change 6053 ≤ 6066; omega
              · apply DusartPrimeRowsChain.cons
                · change 6067 ≤ 6067; omega
                · change 6067 ≤ 6072; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
