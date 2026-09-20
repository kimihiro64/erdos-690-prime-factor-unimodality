import PrimeFactorUnimodality.Helpers.Analytic.DusartLemma33MidrangeCover

set_option autoImplicit false

/-! # Finite rows for Dusart's Lemma 3.3

This module assembles the direct prefix and midrange row families. -/

namespace PrimeFactorUnimodality

noncomputable section

def dusartLemma33FinitePrefixRows : List DusartLemma33FiniteRow :=
  [dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
   dusartLemma33FiniteRow_three, dusartLemma33FiniteRow_four,
   dusartLemma33FiniteRow_five, dusartLemma33FiniteRow_six,
   dusartLemma33FiniteRow_seven, dusartLemma33FiniteRow_eight,
   dusartLemma33FiniteRow_nine, dusartLemma33FiniteRow_ten_twentyfour,
   dusartLemma33FiniteRow_twentyfive_thirtyfive,
   dusartLemma33FiniteRow_thirtysix_sixtythree,
   dusartLemma33FiniteRow_sixtyfour_onetwenty,
   dusartLemma33FiniteRow_onetwentyone_onehundredsixtyseven,
   dusartLemma33FiniteRow_onehundredsixtyeight,
   dusartLemma33FiniteRow_onenine_sixtythree,
   dusartLemma33FiniteRow_twohundredfiftysix_twohundredeightyeight,
   dusartLemma33FiniteRow_twohundredeightynine_threehundredfortytwo,
   dusartLemma33FiniteRow_threehundredfortythree_threehundredsixty,
   dusartLemma33FiniteRow_threehundredsixtyone_fivehundredeleven,
   dusartLemma33FiniteRow_fivehundredtwelve_fivehundredeight,
   dusartLemma33FiniteRow_fivehundredtwentynine_fivehundredseventyfive,
   dusartLemma33FiniteRow_fivehundredseventysix_sixhundredtwentyfour,
   dusartLemma33FiniteRow_sixhundredtwentyfive_sixhundredseventyfive,
   dusartLemma33FiniteRow_sixhundredseventysix_sevenhundredtwentyeight,
   dusartLemma33FiniteRow_sevenhundredtwentynine_eighthundredforty,
   dusartLemma33FiniteRow_eighthundredfortyone_ninehundredsixty,
   dusartLemma33FiniteRow_ninehundredsixtyone_tenthousandtwentythree,
   dusartLemma33FiniteRow_tenthousandtwentyfour_thirteenhundredsixtyeight,
   dusartLemma33FiniteRow_thirteenhundredsixtynine_sixteeneighty,
   dusartLemma33FiniteRow_sixteeneighty_one_eighteenfortyeight,
   dusartLemma33FiniteRow_eighteenfortynine_twothousandfortyseven,
   dusartLemma33FiniteRow_twothousandtwentyfive_twothousandonehundredninetysix,
   dusartLemma33FiniteRow_twothousandonehundredninetyseven_twothousandtwohundredeight,
   dusartLemma33FiniteRow_twothousandtwohundredeightynine_threehundredfortytwo,
   dusartLemma33FiniteRow_twothousandtwohundrednine_twothousandfourhundred,
   dusartLemma33FiniteRow_exact_twofourzeroone]

theorem dusartLemma33FinitePrefixRowsCover :
    DusartLemma33FiniteRowsCover dusartLemma33FinitePrefixRows 2401 := by
  simpa [dusartLemma33FinitePrefixRows] using
    dusartLemma33FiniteRowsCover_twofourzeroone

theorem dusartLemma33FiniteRowsCover_through_10000000 :
    DusartLemma33FiniteRowsCover
      (dusartLemma33FinitePrefixRows ++
        dusartLemma33MidrangeRows) 10000000 := by
  exact dusartLemma33FiniteRowsCover_append
    dusartLemma33FinitePrefixRowsCover
    dusartLemma33MidrangeRowsCover

theorem dusart_lemma_3_3_finite_through_10000000 :
    ∀ x : Real, 0 < x → x ≤ 10000000 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_through_10000000

end

end PrimeFactorUnimodality
