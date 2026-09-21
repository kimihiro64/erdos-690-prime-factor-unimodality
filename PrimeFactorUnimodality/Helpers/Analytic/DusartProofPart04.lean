import PrimeFactorUnimodality.Helpers.Analytic.DusartProofPart03


set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/- The finite boundary in Dusart's Lemma 3.3 is exactly 10^33. -/

theorem dusartLemma33FiniteRowsCover_sixhundredseventyfive :
    DusartLemma33FiniteRowsCover
      ([dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
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
        dusartLemma33FiniteRow_fivehundredseventysix_sixhundredtwentyfour] ++
        [dusartLemma33FiniteRow_sixhundredtwentyfive_sixhundredseventyfive]) 675 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_sixhundredtwentyfour
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_sevenhundredtwentyeight :
    DusartLemma33FiniteRowsCover
      ([dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
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
        dusartLemma33FiniteRow_sixhundredtwentyfive_sixhundredseventyfive] ++
        [dusartLemma33FiniteRow_sixhundredseventysix_sevenhundredtwentyeight]) 728 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_sixhundredseventyfive
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_eighthundredforty :
    DusartLemma33FiniteRowsCover
      ([dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
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
        dusartLemma33FiniteRow_sixhundredseventysix_sevenhundredtwentyeight] ++
        [dusartLemma33FiniteRow_sevenhundredtwentynine_eighthundredforty]) 840 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_sevenhundredtwentyeight
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_ninehundredsixty :
    DusartLemma33FiniteRowsCover
      ([dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
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
        dusartLemma33FiniteRow_sevenhundredtwentynine_eighthundredforty] ++
        [dusartLemma33FiniteRow_eighthundredfortyone_ninehundredsixty]) 960 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_eighthundredforty
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_tenthousandtwentythree :
    DusartLemma33FiniteRowsCover
      ([dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
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
        dusartLemma33FiniteRow_eighthundredfortyone_ninehundredsixty] ++
        [dusartLemma33FiniteRow_ninehundredsixtyone_tenthousandtwentythree]) 1023 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_ninehundredsixty
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_thirteenhundredsixtyeight :
    DusartLemma33FiniteRowsCover
      ([dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
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
        dusartLemma33FiniteRow_ninehundredsixtyone_tenthousandtwentythree] ++
        [dusartLemma33FiniteRow_tenthousandtwentyfour_thirteenhundredsixtyeight]) 1368 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_tenthousandtwentythree
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_sixteeneighty :
    DusartLemma33FiniteRowsCover
      ([dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
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
        dusartLemma33FiniteRow_tenthousandtwentyfour_thirteenhundredsixtyeight] ++
        [dusartLemma33FiniteRow_thirteenhundredsixtynine_sixteeneighty]) 1680 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_thirteenhundredsixtyeight
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_eighteenfortyeight :
    DusartLemma33FiniteRowsCover
      ([dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
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
        dusartLemma33FiniteRow_thirteenhundredsixtynine_sixteeneighty] ++
        [dusartLemma33FiniteRow_sixteeneighty_one_eighteenfortyeight]) 1848 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_sixteeneighty
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_twothousandfortyseven :
    DusartLemma33FiniteRowsCover
      ([dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
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
        dusartLemma33FiniteRow_sixteeneighty_one_eighteenfortyeight] ++
        [dusartLemma33FiniteRow_eighteenfortynine_twothousandfortyseven]) 2047 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_eighteenfortyeight
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_twothousandonehundredninetysix :
    DusartLemma33FiniteRowsCover
      ([dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
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
        dusartLemma33FiniteRow_eighteenfortynine_twothousandfortyseven] ++
        [dusartLemma33FiniteRow_twothousandtwentyfive_twothousandonehundredninetysix]) 2196 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_twothousandfortyseven
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_twothousandtwohundredeight :
    DusartLemma33FiniteRowsCover
      ([dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
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
        dusartLemma33FiniteRow_twothousandtwentyfive_twothousandonehundredninetysix] ++
        [dusartLemma33FiniteRow_twothousandonehundredninetyseven_twothousandtwohundredeight]) 2208 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_twothousandonehundredninetysix
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_twothousandfourhundred :
    DusartLemma33FiniteRowsCover
      ([dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
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
        dusartLemma33FiniteRow_twothousandonehundredninetyseven_twothousandtwohundredeight] ++
        [dusartLemma33FiniteRow_twothousandtwohundrednine_twothousandfourhundred]) 2400 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_twothousandtwohundredeight
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_twofourzeroone :
    DusartLemma33FiniteRowsCover
      ([dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
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
        dusartLemma33FiniteRow_twothousandtwohundrednine_twothousandfourhundred] ++
        [dusartLemma33FiniteRow_exact_twofourzeroone]) 2401 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_twothousandfourhundred
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusart_lemma_3_3_finite_120 :
    ∀ x : Real, 0 < x → x ≤ 120 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_onetwenty_compact

theorem dusart_lemma_3_3_finite_255 :
    ∀ x : Real, 0 < x → x ≤ 255 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_twohundredfiftyfive

theorem dusart_lemma_3_3_finite_288 :
    ∀ x : Real, 0 < x → x ≤ 288 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_twohundredeightyeight

theorem dusart_lemma_3_3_finite_360 :
    ∀ x : Real, 0 < x → x ≤ 360 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_threesixty

theorem dusart_lemma_3_3_finite_511 :
    ∀ x : Real, 0 < x → x ≤ 511 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_fivehundredeleven

theorem dusart_lemma_3_3_finite_624 :
    ∀ x : Real, 0 < x → x ≤ 624 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_sixhundredtwentyfour

theorem dusart_lemma_3_3_finite_675 :
    ∀ x : Real, 0 < x → x ≤ 675 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_sixhundredseventyfive

theorem dusart_lemma_3_3_finite_728 :
    ∀ x : Real, 0 < x → x ≤ 728 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_sevenhundredtwentyeight

theorem dusart_lemma_3_3_finite_840 :
    ∀ x : Real, 0 < x → x ≤ 840 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_eighthundredforty

theorem dusart_lemma_3_3_finite_960 :
    ∀ x : Real, 0 < x → x ≤ 960 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_ninehundredsixty

theorem dusart_lemma_3_3_finite_1023 :
    ∀ x : Real, 0 < x → x ≤ 1023 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_tenthousandtwentythree

theorem dusart_lemma_3_3_finite_1368 :
    ∀ x : Real, 0 < x → x ≤ 1368 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_thirteenhundredsixtyeight

theorem dusart_lemma_3_3_finite_1680 :
    ∀ x : Real, 0 < x → x ≤ 1680 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_sixteeneighty

theorem dusart_lemma_3_3_finite_1848 :
    ∀ x : Real, 0 < x → x ≤ 1848 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_eighteenfortyeight

theorem dusart_lemma_3_3_finite_2047 :
    ∀ x : Real, 0 < x → x ≤ 2047 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_twothousandfortyseven

theorem dusart_lemma_3_3_finite_2196 :
    ∀ x : Real, 0 < x → x ≤ 2196 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_twothousandonehundredninetysix

theorem dusart_lemma_3_3_finite_2208 :
    ∀ x : Real, 0 < x → x ≤ 2208 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_twothousandtwohundredeight

theorem dusart_lemma_3_3_finite_2400 :
    ∀ x : Real, 0 < x → x ≤ 2400 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_twothousandfourhundred

theorem dusart_lemma_3_3_finite_2401 :
    ∀ x : Real, 0 < x → x ≤ 2401 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_twofourzeroone

theorem dusart_lemma_3_3_finite_2402 :
    ∀ x : Real, 0 < x → x ≤ 2402 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  intro x hx hX
  by_cases hprefix : x ≤ 2401
  · exact dusart_lemma_3_3_finite_2401 x hx hprefix
  · exact dusartLemma33FiniteRow_exact_twofourzeroone_two.valid x hx
      (by norm_num; linarith) (by norm_num; linarith)

/-! The existing closed prefix is also exported through the chunk boundary;
    later generated chunks can be appended without changing this consumer. -/
def dusartLemma33FiniteChunk_2401 : DusartLemma33FiniteChunk :=
  DusartLemma33FiniteChunk.of_list
    (cutoff := (2401 : Real)) dusartLemma33FiniteRowsCover_twofourzeroone

def dusartLemma33FiniteProofChunk_2401 : DusartLemma33FiniteProofChunk :=
  dusartLemma33FiniteChunk_2401.toProofChunk

/-! The proved midrange table is assembled after the direct prefix.  Keeping
    the two pieces as proof chunks makes the boundary reusable without
    materializing a second copy of the prefix rows. -/
def dusartLemma33FiniteProofChunk_10m : DusartLemma33FiniteProofChunk :=
  { cutoff := (10000000 : Real)
    valid := by
      intro x hx hX
      by_cases hprefix : x ≤ (2401 : Real)
      · exact dusartLemma33FiniteProofChunk_2401.valid x hx hprefix
      · obtain ⟨row, hrow, hleft, hright⟩ :=
          dusartLemma33MidrangeRowsCover x (by linarith) hX
        exact row.valid x hx hleft hright }

theorem dusart_lemma_3_3_finite_10m :
    ∀ x : Real, 0 < x → x ≤ 10000000 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusartLemma33FiniteProofChunk_10m.valid

theorem dusart_lemma_3_3_of_10m_intermediate_and_theta_upper
    (theta_upper : ∀ y : Real, 0 < y →
      Chebyshev.theta y < (1000081 : Real) / 1000000 * y) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  intro x hx
  by_cases hsmall : x ≤ (10000000 : Real)
  · exact dusartLemma33FiniteProofChunk_10m.valid x hx hsmall
  · by_cases hmid : x ≤ (10 ^ 11 : Real) ^ 3
    · exact dusart_lemma_3_3_intermediate (by norm_num; linarith)
        hmid theta_upper
    · exact dusart_lemma_3_3_large (by norm_num; linarith) theta_upper

theorem dusart_lemma_3_3_finite_chunk_2401 :
    ∀ x : Real, 0 < x → x ≤ 2401 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusartLemma33FiniteChunk_2401.provides

theorem dusart_proposition_3_2_small_64
    {x : Real} (hx : 0 < x) (hx64 : x < 64) :
    Chebyshev.psi x - Chebyshev.theta x <
      (100007 : Real) / 100000 * Real.sqrt x +
        (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  have htransport : Chebyshev.psi x - Chebyshev.theta x =
      Chebyshev.psi (⌊x⌋₊ : Real) - Chebyshev.theta (⌊x⌋₊ : Real) := by
    rw [Chebyshev.psi_eq_psi_coe_floor, Chebyshev.theta_eq_theta_coe_floor]
  by_cases h9 : x < 9
  · by_cases h4 : x < 4
    · have hzero : Chebyshev.psi x - Chebyshev.theta x = 0 := by
        have hf : ⌊x⌋₊ < 4 := (Nat.floor_lt hx.le).2 h4
        have hfloor : (⌊x⌋₊ : Real) ≤ 3 := by
          exact_mod_cast Nat.le_of_lt_succ hf
        have hupper : Chebyshev.psi x - Chebyshev.theta x ≤ 0 := by
          rw [htransport]
          exact (psi_sub_theta_mono hfloor).trans_eq
            psi_sub_theta_nat_3_eq_zero
        have hnonneg : 0 ≤ Chebyshev.psi x - Chebyshev.theta x := by
          exact sub_nonneg.mpr (Chebyshev.theta_le_psi x)
        exact le_antisymm hupper hnonneg
      rw [hzero]
      positivity
    · have hx4 : (4 : Real) ≤ x := le_of_not_gt h4
      have hfloor : (⌊x⌋₊ : Real) ≤ 8 := by
        exact_mod_cast Nat.le_of_lt_succ
          ((Nat.floor_lt hx.le).2 (by norm_num; exact h9))
      have hleft : Chebyshev.psi x - Chebyshev.theta x < 2 := by
        rw [htransport]
        exact (psi_sub_theta_mono hfloor).trans_lt psi_sub_theta_nat_8_lt_two
      have hsqrt : (2 : Real) ≤ Real.sqrt x := by
        nlinarith [Real.sq_sqrt (show 0 ≤ x by linarith), Real.sqrt_nonneg x]
      nlinarith [hleft, hsqrt,
        Real.rpow_nonneg (show 0 ≤ x by linarith) (1 / 3 : Real)]
  · have hx9 : (9 : Real) ≤ x := le_of_not_gt h9
    by_cases h25 : x < 25
    · have hfloor : (⌊x⌋₊ : Real) ≤ 24 := by
        exact_mod_cast Nat.le_of_lt_succ
          ((Nat.floor_lt hx.le).2 (by norm_num; exact h25))
      have hleft : Chebyshev.psi x - Chebyshev.theta x < 4 := by
        rw [htransport]
        exact (psi_sub_theta_mono hfloor).trans_lt psi_sub_theta_nat_24_lt_four
      have hsqrt : (3 : Real) ≤ Real.sqrt x := by
        nlinarith [Real.sq_sqrt (show 0 ≤ x by linarith), Real.sqrt_nonneg x]
      have hcuberoot : (2 : Real) ≤ x ^ (1 / 3 : Real) := by
        have hpow := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 8)
          (by linarith : (8 : Real) ≤ x)
          (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
        norm_num at hpow ⊢
        exact hpow
      nlinarith [hleft, hsqrt, hcuberoot]
    · have hx25 : (25 : Real) ≤ x := le_of_not_gt h25
      by_cases h36 : x < 36
      · have hfloor : (⌊x⌋₊ : Real) ≤ 35 := by
          exact_mod_cast Nat.le_of_lt_succ
            ((Nat.floor_lt hx.le).2 (by norm_num; exact h36))
        have hleft : Chebyshev.psi x - Chebyshev.theta x < 8 := by
          rw [htransport]
          exact (psi_sub_theta_mono hfloor).trans_lt psi_sub_theta_nat_35_lt_eight
        have hsqrt : (5 : Real) ≤ Real.sqrt x := by
          nlinarith [Real.sq_sqrt (show 0 ≤ x by linarith), Real.sqrt_nonneg x]
        have hcuberoot : (2 : Real) ≤ x ^ (1 / 3 : Real) := by
          have hpow := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 8)
            (by linarith : (8 : Real) ≤ x)
            (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
          norm_num at hpow ⊢
          exact hpow
        nlinarith [hleft, hsqrt, hcuberoot]
      · have hx36 : (36 : Real) ≤ x := le_of_not_gt h36
        have hfloor : (⌊x⌋₊ : Real) ≤ 63 := by
          exact_mod_cast Nat.le_of_lt_succ
            ((Nat.floor_lt hx.le).2 (by norm_num; exact hx64))
        have hleft : Chebyshev.psi x - Chebyshev.theta x < 9 := by
          rw [htransport]
          exact (psi_sub_theta_mono hfloor).trans_lt psi_sub_theta_nat_63_lt_nine
        have hsqrt : (6 : Real) ≤ Real.sqrt x := by
          nlinarith [Real.sq_sqrt (show 0 ≤ x by linarith), Real.sqrt_nonneg x]
        have hcuberoot : (2 : Real) ≤ x ^ (1 / 3 : Real) := by
          have hpow := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 8)
            (by linarith : (8 : Real) ≤ x)
            (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
          norm_num at hpow ⊢
          exact hpow
        nlinarith [hleft, hsqrt, hcuberoot]

end

end PrimeFactorUnimodality
