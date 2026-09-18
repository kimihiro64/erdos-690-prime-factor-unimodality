import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00007_values : List Nat :=
  [fullRecordGapCenterValue - 333714,
    fullRecordGapCenterValue - 333694,
    fullRecordGapCenterValue - 333682,
    fullRecordGapCenterValue - 333618,
    fullRecordGapCenterValue - 333604,
    fullRecordGapCenterValue - 333478,
    fullRecordGapCenterValue - 333364,
    fullRecordGapCenterValue - 333262,
    fullRecordGapCenterValue - 333202,
    fullRecordGapCenterValue - 333028,
    fullRecordGapCenterValue - 332922,
    fullRecordGapCenterValue - 332884,
    fullRecordGapCenterValue - 332814,
    fullRecordGapCenterValue - 332742,
    fullRecordGapCenterValue - 332394,
    fullRecordGapCenterValue - 332058,
    fullRecordGapCenterValue - 331924,
    fullRecordGapCenterValue - 331774,
    fullRecordGapCenterValue - 331714,
    fullRecordGapCenterValue - 331564,
    fullRecordGapCenterValue - 331494,
    fullRecordGapCenterValue - 331438,
    fullRecordGapCenterValue - 331252,
    fullRecordGapCenterValue - 331242,
    fullRecordGapCenterValue - 331222,
    fullRecordGapCenterValue - 331174,
    fullRecordGapCenterValue - 331138,
    fullRecordGapCenterValue - 331102,
    fullRecordGapCenterValue - 331054,
    fullRecordGapCenterValue - 330978,
    fullRecordGapCenterValue - 330762,
    fullRecordGapCenterValue - 330750,
    fullRecordGapCenterValue - 330628,
    fullRecordGapCenterValue - 330364,
    fullRecordGapCenterValue - 330178,
    fullRecordGapCenterValue - 330082,
    fullRecordGapCenterValue - 330028,
    fullRecordGapCenterValue - 330000,
    fullRecordGapCenterValue - 329898,
    fullRecordGapCenterValue - 329838,
    fullRecordGapCenterValue - 329578,
    fullRecordGapCenterValue - 329572,
    fullRecordGapCenterValue - 329502,
    fullRecordGapCenterValue - 329404,
    fullRecordGapCenterValue - 329280,
    fullRecordGapCenterValue - 329214,
    fullRecordGapCenterValue - 329068,
    fullRecordGapCenterValue - 329044,
    fullRecordGapCenterValue - 328954,
    fullRecordGapCenterValue - 328894,
    fullRecordGapCenterValue - 328858,
    fullRecordGapCenterValue - 328732,
    fullRecordGapCenterValue - 328722,
    fullRecordGapCenterValue - 328612,
    fullRecordGapCenterValue - 328564,
    fullRecordGapCenterValue - 328534,
    fullRecordGapCenterValue - 328362,
    fullRecordGapCenterValue - 328278,
    fullRecordGapCenterValue - 328234,
    fullRecordGapCenterValue - 328204,
    fullRecordGapCenterValue - 328114,
    fullRecordGapCenterValue - 328102,
    fullRecordGapCenterValue - 328038,
    fullRecordGapCenterValue - 327994,
    fullRecordGapCenterValue - 327982,
    fullRecordGapCenterValue - 327802,
    fullRecordGapCenterValue - 327724,
    fullRecordGapCenterValue - 327718,
    fullRecordGapCenterValue - 327498,
    fullRecordGapCenterValue - 327462,
    fullRecordGapCenterValue - 327394,
    fullRecordGapCenterValue - 327388,
    fullRecordGapCenterValue - 327358,
    fullRecordGapCenterValue - 327322,
    fullRecordGapCenterValue - 327282,
    fullRecordGapCenterValue - 327274,
    fullRecordGapCenterValue - 327018,
    fullRecordGapCenterValue - 326994,
    fullRecordGapCenterValue - 326812,
    fullRecordGapCenterValue - 326734,
    fullRecordGapCenterValue - 326694,
    fullRecordGapCenterValue - 326514,
    fullRecordGapCenterValue - 326478,
    fullRecordGapCenterValue - 326422,
    fullRecordGapCenterValue - 326338,
    fullRecordGapCenterValue - 326254,
    fullRecordGapCenterValue - 326212,
    fullRecordGapCenterValue - 326202,
    fullRecordGapCenterValue - 326122,
    fullRecordGapCenterValue - 326038,
    fullRecordGapCenterValue - 325938,
    fullRecordGapCenterValue - 325828,
    fullRecordGapCenterValue - 325614,
    fullRecordGapCenterValue - 325498,
    fullRecordGapCenterValue - 325462,
    fullRecordGapCenterValue - 325372,
    fullRecordGapCenterValue - 325302,
    fullRecordGapCenterValue - 325282,
    fullRecordGapCenterValue - 325258,
    fullRecordGapCenterValue - 325132,
    fullRecordGapCenterValue - 325002,
    fullRecordGapCenterValue - 324798,
    fullRecordGapCenterValue - 324778,
    fullRecordGapCenterValue - 324718,
    fullRecordGapCenterValue - 324652,
    fullRecordGapCenterValue - 324628,
    fullRecordGapCenterValue - 324538,
    fullRecordGapCenterValue - 324498,
    fullRecordGapCenterValue - 324442,
    fullRecordGapCenterValue - 324354,
    fullRecordGapCenterValue - 324238,
    fullRecordGapCenterValue - 324172,
    fullRecordGapCenterValue - 324118,
    fullRecordGapCenterValue - 324078,
    fullRecordGapCenterValue - 324034,
    fullRecordGapCenterValue - 324022,
    fullRecordGapCenterValue - 324000,
    fullRecordGapCenterValue - 323938,
    fullRecordGapCenterValue - 323812,
    fullRecordGapCenterValue - 323754,
    fullRecordGapCenterValue - 323692,
    fullRecordGapCenterValue - 323644,
    fullRecordGapCenterValue - 323542,
    fullRecordGapCenterValue - 323538,
    fullRecordGapCenterValue - 323502,
    fullRecordGapCenterValue - 323482,
    fullRecordGapCenterValue - 323458,
    fullRecordGapCenterValue - 323452,
    fullRecordGapCenterValue - 323322,
    fullRecordGapCenterValue - 323278,
    fullRecordGapCenterValue - 323094,
    fullRecordGapCenterValue - 322948,
    fullRecordGapCenterValue - 322914,
    fullRecordGapCenterValue - 322732,
    fullRecordGapCenterValue - 322698,
    fullRecordGapCenterValue - 322618,
    fullRecordGapCenterValue - 322534,
    fullRecordGapCenterValue - 322444,
    fullRecordGapCenterValue - 322402,
    fullRecordGapCenterValue - 322314,
    fullRecordGapCenterValue - 322228,
    fullRecordGapCenterValue - 321942,
    fullRecordGapCenterValue - 321702,
    fullRecordGapCenterValue - 321654,
    fullRecordGapCenterValue - 321634,
    fullRecordGapCenterValue - 321562,
    fullRecordGapCenterValue - 321558,
    fullRecordGapCenterValue - 321502,
    fullRecordGapCenterValue - 321478,
    fullRecordGapCenterValue - 321418,
    fullRecordGapCenterValue - 321394,
    fullRecordGapCenterValue - 321388,
    fullRecordGapCenterValue - 321274,
    fullRecordGapCenterValue - 321004,
    fullRecordGapCenterValue - 320932,
    fullRecordGapCenterValue - 320884,
    fullRecordGapCenterValue - 320668,
    fullRecordGapCenterValue - 320442,
    fullRecordGapCenterValue - 320308,
    fullRecordGapCenterValue - 320284,
    fullRecordGapCenterValue - 320262,
    fullRecordGapCenterValue - 320154,
    fullRecordGapCenterValue - 320098,
    fullRecordGapCenterValue - 319954,
    fullRecordGapCenterValue - 319938,
    fullRecordGapCenterValue - 319798,
    fullRecordGapCenterValue - 319582,
    fullRecordGapCenterValue - 319492,
    fullRecordGapCenterValue - 319402,
    fullRecordGapCenterValue - 319342,
    fullRecordGapCenterValue - 319234,
    fullRecordGapCenterValue - 319204,
    fullRecordGapCenterValue - 319108,
    fullRecordGapCenterValue - 318814,
    fullRecordGapCenterValue - 318778,
    fullRecordGapCenterValue - 318462,
    fullRecordGapCenterValue - 318414,
    fullRecordGapCenterValue - 318334,
    fullRecordGapCenterValue - 318244,
    fullRecordGapCenterValue - 318148,
    fullRecordGapCenterValue - 318034,
    fullRecordGapCenterValue - 317994,
    fullRecordGapCenterValue - 317818,
    fullRecordGapCenterValue - 317802,
    fullRecordGapCenterValue - 317554,
    fullRecordGapCenterValue - 317274,
    fullRecordGapCenterValue - 317154,
    fullRecordGapCenterValue - 317022,
    fullRecordGapCenterValue - 316978,
    fullRecordGapCenterValue - 316902,
    fullRecordGapCenterValue - 316858,
    fullRecordGapCenterValue - 316714,
    fullRecordGapCenterValue - 316698,
    fullRecordGapCenterValue - 316614,
    fullRecordGapCenterValue - 316612,
    fullRecordGapCenterValue - 316542,
    fullRecordGapCenterValue - 316362,
    fullRecordGapCenterValue - 316258,
    fullRecordGapCenterValue - 316252,
    fullRecordGapCenterValue - 316182,
    fullRecordGapCenterValue - 316038,
    fullRecordGapCenterValue - 315982,
    fullRecordGapCenterValue - 315762,
    fullRecordGapCenterValue - 315654,
    fullRecordGapCenterValue - 315598,
    fullRecordGapCenterValue - 315508,
    fullRecordGapCenterValue - 315474,
    fullRecordGapCenterValue - 315292,
    fullRecordGapCenterValue - 315174,
    fullRecordGapCenterValue - 315142,
    fullRecordGapCenterValue - 314914,
    fullRecordGapCenterValue - 314788,
    fullRecordGapCenterValue - 314718,
    fullRecordGapCenterValue - 314614,
    fullRecordGapCenterValue - 314554,
    fullRecordGapCenterValue - 314332,
    fullRecordGapCenterValue - 314284,
    fullRecordGapCenterValue - 314178,
    fullRecordGapCenterValue - 314068,
    fullRecordGapCenterValue - 314044,
    fullRecordGapCenterValue - 314038,
    fullRecordGapCenterValue - 313942,
    fullRecordGapCenterValue - 313798,
    fullRecordGapCenterValue - 313774,
    fullRecordGapCenterValue - 313602,
    fullRecordGapCenterValue - 313600,
    fullRecordGapCenterValue - 313422,
    fullRecordGapCenterValue - 313414,
    fullRecordGapCenterValue - 313338,
    fullRecordGapCenterValue - 313134,
    fullRecordGapCenterValue - 313078,
    fullRecordGapCenterValue - 312982,
    fullRecordGapCenterValue - 312934,
    fullRecordGapCenterValue - 312882,
    fullRecordGapCenterValue - 312874,
    fullRecordGapCenterValue - 312772,
    fullRecordGapCenterValue - 312484,
    fullRecordGapCenterValue - 312414,
    fullRecordGapCenterValue - 312342,
    fullRecordGapCenterValue - 312262,
    fullRecordGapCenterValue - 312142,
    fullRecordGapCenterValue - 312028,
    fullRecordGapCenterValue - 311908,
    fullRecordGapCenterValue - 311862,
    fullRecordGapCenterValue - 311850,
    fullRecordGapCenterValue - 311782,
    fullRecordGapCenterValue - 311602,
    fullRecordGapCenterValue - 311554,
    fullRecordGapCenterValue - 311478,
    fullRecordGapCenterValue - 311442,
    fullRecordGapCenterValue - 311434,
    fullRecordGapCenterValue - 311394,
    fullRecordGapCenterValue - 311218,
    fullRecordGapCenterValue - 311118,
    fullRecordGapCenterValue - 311034,
    fullRecordGapCenterValue - 310852]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00007_fermat : ∀ n ∈ fullRecordGapRow00007_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01537_not_prime : ¬(recordGapCenter - 333714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 333714]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01538_not_prime : ¬(recordGapCenter - 333694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 333694]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01539_not_prime : ¬(recordGapCenter - 333682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 333682]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01540_not_prime : ¬(recordGapCenter - 333618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 333618]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01541_not_prime : ¬(recordGapCenter - 333604).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 333604]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01542_not_prime : ¬(recordGapCenter - 333478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 333478]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01543_not_prime : ¬(recordGapCenter - 333364).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 333364]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01544_not_prime : ¬(recordGapCenter - 333262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 333262]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01545_not_prime : ¬(recordGapCenter - 333202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 333202]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01546_not_prime : ¬(recordGapCenter - 333028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 333028]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01547_not_prime : ¬(recordGapCenter - 332922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 332922]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01548_not_prime : ¬(recordGapCenter - 332884).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 332884]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01549_not_prime : ¬(recordGapCenter - 332814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 332814]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01550_not_prime : ¬(recordGapCenter - 332742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 332742]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01551_not_prime : ¬(recordGapCenter - 332394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 332394]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01552_not_prime : ¬(recordGapCenter - 332058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 332058]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01553_not_prime : ¬(recordGapCenter - 331924).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 331924]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01554_not_prime : ¬(recordGapCenter - 331774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 331774]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01555_not_prime : ¬(recordGapCenter - 331714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 331714]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01556_not_prime : ¬(recordGapCenter - 331564).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 331564]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01557_not_prime : ¬(recordGapCenter - 331494).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 331494]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01558_not_prime : ¬(recordGapCenter - 331438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 331438]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01559_not_prime : ¬(recordGapCenter - 331252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 331252]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01560_not_prime : ¬(recordGapCenter - 331242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 331242]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01561_not_prime : ¬(recordGapCenter - 331222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 331222]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01562_not_prime : ¬(recordGapCenter - 331174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 331174]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01563_not_prime : ¬(recordGapCenter - 331138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 331138]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01564_not_prime : ¬(recordGapCenter - 331102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 331102]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01565_not_prime : ¬(recordGapCenter - 331054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 331054]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01566_not_prime : ¬(recordGapCenter - 330978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 330978]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01567_not_prime : ¬(recordGapCenter - 330762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 330762]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01568_not_prime : ¬(recordGapCenter - 330750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 330750]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01569_not_prime : ¬(recordGapCenter - 330628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 330628]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01570_not_prime : ¬(recordGapCenter - 330364).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 330364]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01571_not_prime : ¬(recordGapCenter - 330178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 330178]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01572_not_prime : ¬(recordGapCenter - 330082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 330082]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01573_not_prime : ¬(recordGapCenter - 330028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 330028]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01574_not_prime : ¬(recordGapCenter - 330000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 330000]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01575_not_prime : ¬(recordGapCenter - 329898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 329898]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01576_not_prime : ¬(recordGapCenter - 329838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 329838]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01577_not_prime : ¬(recordGapCenter - 329578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 329578]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01578_not_prime : ¬(recordGapCenter - 329572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 329572]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01579_not_prime : ¬(recordGapCenter - 329502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 329502]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01580_not_prime : ¬(recordGapCenter - 329404).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 329404]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01581_not_prime : ¬(recordGapCenter - 329280).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 329280]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01582_not_prime : ¬(recordGapCenter - 329214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 329214]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01583_not_prime : ¬(recordGapCenter - 329068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 329068]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01584_not_prime : ¬(recordGapCenter - 329044).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 329044]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01585_not_prime : ¬(recordGapCenter - 328954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328954]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01586_not_prime : ¬(recordGapCenter - 328894).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328894]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01587_not_prime : ¬(recordGapCenter - 328858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328858]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01588_not_prime : ¬(recordGapCenter - 328732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328732]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01589_not_prime : ¬(recordGapCenter - 328722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328722]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01590_not_prime : ¬(recordGapCenter - 328612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328612]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01591_not_prime : ¬(recordGapCenter - 328564).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328564]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01592_not_prime : ¬(recordGapCenter - 328534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328534]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01593_not_prime : ¬(recordGapCenter - 328362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328362]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01594_not_prime : ¬(recordGapCenter - 328278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328278]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01595_not_prime : ¬(recordGapCenter - 328234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328234]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01596_not_prime : ¬(recordGapCenter - 328204).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328204]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01597_not_prime : ¬(recordGapCenter - 328114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328114]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01598_not_prime : ¬(recordGapCenter - 328102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328102]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01599_not_prime : ¬(recordGapCenter - 328038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328038]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01600_not_prime : ¬(recordGapCenter - 327994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 327994]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01601_not_prime : ¬(recordGapCenter - 327982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 327982]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01602_not_prime : ¬(recordGapCenter - 327802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 327802]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01603_not_prime : ¬(recordGapCenter - 327724).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 327724]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01604_not_prime : ¬(recordGapCenter - 327718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 327718]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01605_not_prime : ¬(recordGapCenter - 327498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 327498]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01606_not_prime : ¬(recordGapCenter - 327462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 327462]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01607_not_prime : ¬(recordGapCenter - 327394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 327394]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01608_not_prime : ¬(recordGapCenter - 327388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 327388]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01609_not_prime : ¬(recordGapCenter - 327358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 327358]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01610_not_prime : ¬(recordGapCenter - 327322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 327322]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01611_not_prime : ¬(recordGapCenter - 327282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 327282]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01612_not_prime : ¬(recordGapCenter - 327274).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 327274]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01613_not_prime : ¬(recordGapCenter - 327018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 327018]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01614_not_prime : ¬(recordGapCenter - 326994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 326994]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01615_not_prime : ¬(recordGapCenter - 326812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 326812]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01616_not_prime : ¬(recordGapCenter - 326734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 326734]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01617_not_prime : ¬(recordGapCenter - 326694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 326694]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01618_not_prime : ¬(recordGapCenter - 326514).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 326514]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01619_not_prime : ¬(recordGapCenter - 326478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 326478]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01620_not_prime : ¬(recordGapCenter - 326422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 326422]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01621_not_prime : ¬(recordGapCenter - 326338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 326338]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01622_not_prime : ¬(recordGapCenter - 326254).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 326254]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01623_not_prime : ¬(recordGapCenter - 326212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 326212]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01624_not_prime : ¬(recordGapCenter - 326202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 326202]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01625_not_prime : ¬(recordGapCenter - 326122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 326122]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01626_not_prime : ¬(recordGapCenter - 326038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 326038]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01627_not_prime : ¬(recordGapCenter - 325938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 325938]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01628_not_prime : ¬(recordGapCenter - 325828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 325828]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01629_not_prime : ¬(recordGapCenter - 325614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 325614]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01630_not_prime : ¬(recordGapCenter - 325498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 325498]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01631_not_prime : ¬(recordGapCenter - 325462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 325462]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01632_not_prime : ¬(recordGapCenter - 325372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 325372]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01633_not_prime : ¬(recordGapCenter - 325302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 325302]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01634_not_prime : ¬(recordGapCenter - 325282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 325282]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01635_not_prime : ¬(recordGapCenter - 325258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 325258]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01636_not_prime : ¬(recordGapCenter - 325132).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 325132]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01637_not_prime : ¬(recordGapCenter - 325002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 325002]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01638_not_prime : ¬(recordGapCenter - 324798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324798]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01639_not_prime : ¬(recordGapCenter - 324778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324778]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01640_not_prime : ¬(recordGapCenter - 324718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324718]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01641_not_prime : ¬(recordGapCenter - 324652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324652]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01642_not_prime : ¬(recordGapCenter - 324628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324628]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01643_not_prime : ¬(recordGapCenter - 324538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324538]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01644_not_prime : ¬(recordGapCenter - 324498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324498]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01645_not_prime : ¬(recordGapCenter - 324442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324442]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01646_not_prime : ¬(recordGapCenter - 324354).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324354]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01647_not_prime : ¬(recordGapCenter - 324238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324238]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01648_not_prime : ¬(recordGapCenter - 324172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324172]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01649_not_prime : ¬(recordGapCenter - 324118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324118]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01650_not_prime : ¬(recordGapCenter - 324078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324078]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01651_not_prime : ¬(recordGapCenter - 324034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324034]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01652_not_prime : ¬(recordGapCenter - 324022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324022]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01653_not_prime : ¬(recordGapCenter - 324000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324000]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01654_not_prime : ¬(recordGapCenter - 323938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 323938]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01655_not_prime : ¬(recordGapCenter - 323812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 323812]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01656_not_prime : ¬(recordGapCenter - 323754).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 323754]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01657_not_prime : ¬(recordGapCenter - 323692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 323692]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01658_not_prime : ¬(recordGapCenter - 323644).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 323644]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01659_not_prime : ¬(recordGapCenter - 323542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 323542]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01660_not_prime : ¬(recordGapCenter - 323538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 323538]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01661_not_prime : ¬(recordGapCenter - 323502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 323502]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01662_not_prime : ¬(recordGapCenter - 323482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 323482]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01663_not_prime : ¬(recordGapCenter - 323458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 323458]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01664_not_prime : ¬(recordGapCenter - 323452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 323452]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01665_not_prime : ¬(recordGapCenter - 323322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 323322]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01666_not_prime : ¬(recordGapCenter - 323278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 323278]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01667_not_prime : ¬(recordGapCenter - 323094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 323094]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01668_not_prime : ¬(recordGapCenter - 322948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 322948]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01669_not_prime : ¬(recordGapCenter - 322914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 322914]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01670_not_prime : ¬(recordGapCenter - 322732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 322732]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01671_not_prime : ¬(recordGapCenter - 322698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 322698]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01672_not_prime : ¬(recordGapCenter - 322618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 322618]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01673_not_prime : ¬(recordGapCenter - 322534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 322534]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01674_not_prime : ¬(recordGapCenter - 322444).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 322444]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01675_not_prime : ¬(recordGapCenter - 322402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 322402]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01676_not_prime : ¬(recordGapCenter - 322314).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 322314]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01677_not_prime : ¬(recordGapCenter - 322228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 322228]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01678_not_prime : ¬(recordGapCenter - 321942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 321942]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01679_not_prime : ¬(recordGapCenter - 321702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 321702]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01680_not_prime : ¬(recordGapCenter - 321654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 321654]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01681_not_prime : ¬(recordGapCenter - 321634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 321634]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01682_not_prime : ¬(recordGapCenter - 321562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 321562]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01683_not_prime : ¬(recordGapCenter - 321558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 321558]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01684_not_prime : ¬(recordGapCenter - 321502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 321502]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01685_not_prime : ¬(recordGapCenter - 321478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 321478]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01686_not_prime : ¬(recordGapCenter - 321418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 321418]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01687_not_prime : ¬(recordGapCenter - 321394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 321394]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01688_not_prime : ¬(recordGapCenter - 321388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 321388]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01689_not_prime : ¬(recordGapCenter - 321274).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 321274]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01690_not_prime : ¬(recordGapCenter - 321004).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 321004]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01691_not_prime : ¬(recordGapCenter - 320932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 320932]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01692_not_prime : ¬(recordGapCenter - 320884).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 320884]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01693_not_prime : ¬(recordGapCenter - 320668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 320668]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01694_not_prime : ¬(recordGapCenter - 320442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 320442]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01695_not_prime : ¬(recordGapCenter - 320308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 320308]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01696_not_prime : ¬(recordGapCenter - 320284).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 320284]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01697_not_prime : ¬(recordGapCenter - 320262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 320262]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01698_not_prime : ¬(recordGapCenter - 320154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 320154]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01699_not_prime : ¬(recordGapCenter - 320098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 320098]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01700_not_prime : ¬(recordGapCenter - 319954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 319954]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01701_not_prime : ¬(recordGapCenter - 319938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 319938]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01702_not_prime : ¬(recordGapCenter - 319798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 319798]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01703_not_prime : ¬(recordGapCenter - 319582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 319582]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01704_not_prime : ¬(recordGapCenter - 319492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 319492]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01705_not_prime : ¬(recordGapCenter - 319402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 319402]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01706_not_prime : ¬(recordGapCenter - 319342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 319342]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01707_not_prime : ¬(recordGapCenter - 319234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 319234]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01708_not_prime : ¬(recordGapCenter - 319204).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 319204]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01709_not_prime : ¬(recordGapCenter - 319108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 319108]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01710_not_prime : ¬(recordGapCenter - 318814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 318814]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01711_not_prime : ¬(recordGapCenter - 318778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 318778]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01712_not_prime : ¬(recordGapCenter - 318462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 318462]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01713_not_prime : ¬(recordGapCenter - 318414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 318414]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01714_not_prime : ¬(recordGapCenter - 318334).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 318334]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01715_not_prime : ¬(recordGapCenter - 318244).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 318244]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01716_not_prime : ¬(recordGapCenter - 318148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 318148]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01717_not_prime : ¬(recordGapCenter - 318034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 318034]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01718_not_prime : ¬(recordGapCenter - 317994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 317994]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01719_not_prime : ¬(recordGapCenter - 317818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 317818]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01720_not_prime : ¬(recordGapCenter - 317802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 317802]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01721_not_prime : ¬(recordGapCenter - 317554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 317554]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01722_not_prime : ¬(recordGapCenter - 317274).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 317274]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01723_not_prime : ¬(recordGapCenter - 317154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 317154]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01724_not_prime : ¬(recordGapCenter - 317022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 317022]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01725_not_prime : ¬(recordGapCenter - 316978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 316978]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01726_not_prime : ¬(recordGapCenter - 316902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 316902]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01727_not_prime : ¬(recordGapCenter - 316858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 316858]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01728_not_prime : ¬(recordGapCenter - 316714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 316714]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01729_not_prime : ¬(recordGapCenter - 316698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 316698]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01730_not_prime : ¬(recordGapCenter - 316614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 316614]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01731_not_prime : ¬(recordGapCenter - 316612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 316612]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01732_not_prime : ¬(recordGapCenter - 316542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 316542]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01733_not_prime : ¬(recordGapCenter - 316362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 316362]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01734_not_prime : ¬(recordGapCenter - 316258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 316258]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01735_not_prime : ¬(recordGapCenter - 316252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 316252]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01736_not_prime : ¬(recordGapCenter - 316182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 316182]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01737_not_prime : ¬(recordGapCenter - 316038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 316038]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01738_not_prime : ¬(recordGapCenter - 315982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 315982]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01739_not_prime : ¬(recordGapCenter - 315762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 315762]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01740_not_prime : ¬(recordGapCenter - 315654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 315654]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01741_not_prime : ¬(recordGapCenter - 315598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 315598]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01742_not_prime : ¬(recordGapCenter - 315508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 315508]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01743_not_prime : ¬(recordGapCenter - 315474).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 315474]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01744_not_prime : ¬(recordGapCenter - 315292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 315292]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01745_not_prime : ¬(recordGapCenter - 315174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 315174]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01746_not_prime : ¬(recordGapCenter - 315142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 315142]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01747_not_prime : ¬(recordGapCenter - 314914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 314914]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01748_not_prime : ¬(recordGapCenter - 314788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 314788]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01749_not_prime : ¬(recordGapCenter - 314718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 314718]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01750_not_prime : ¬(recordGapCenter - 314614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 314614]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01751_not_prime : ¬(recordGapCenter - 314554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 314554]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01752_not_prime : ¬(recordGapCenter - 314332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 314332]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01753_not_prime : ¬(recordGapCenter - 314284).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 314284]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01754_not_prime : ¬(recordGapCenter - 314178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 314178]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01755_not_prime : ¬(recordGapCenter - 314068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 314068]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01756_not_prime : ¬(recordGapCenter - 314044).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 314044]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01757_not_prime : ¬(recordGapCenter - 314038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 314038]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01758_not_prime : ¬(recordGapCenter - 313942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 313942]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01759_not_prime : ¬(recordGapCenter - 313798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 313798]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01760_not_prime : ¬(recordGapCenter - 313774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 313774]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01761_not_prime : ¬(recordGapCenter - 313602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 313602]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01762_not_prime : ¬(recordGapCenter - 313600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 313600]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01763_not_prime : ¬(recordGapCenter - 313422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 313422]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01764_not_prime : ¬(recordGapCenter - 313414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 313414]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01765_not_prime : ¬(recordGapCenter - 313338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 313338]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01766_not_prime : ¬(recordGapCenter - 313134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 313134]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01767_not_prime : ¬(recordGapCenter - 313078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 313078]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01768_not_prime : ¬(recordGapCenter - 312982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 312982]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01769_not_prime : ¬(recordGapCenter - 312934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 312934]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01770_not_prime : ¬(recordGapCenter - 312882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 312882]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01771_not_prime : ¬(recordGapCenter - 312874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 312874]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01772_not_prime : ¬(recordGapCenter - 312772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 312772]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01773_not_prime : ¬(recordGapCenter - 312484).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 312484]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01774_not_prime : ¬(recordGapCenter - 312414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 312414]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01775_not_prime : ¬(recordGapCenter - 312342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 312342]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01776_not_prime : ¬(recordGapCenter - 312262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 312262]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01777_not_prime : ¬(recordGapCenter - 312142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 312142]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01778_not_prime : ¬(recordGapCenter - 312028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 312028]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01779_not_prime : ¬(recordGapCenter - 311908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 311908]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01780_not_prime : ¬(recordGapCenter - 311862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 311862]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01781_not_prime : ¬(recordGapCenter - 311850).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 311850]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01782_not_prime : ¬(recordGapCenter - 311782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 311782]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01783_not_prime : ¬(recordGapCenter - 311602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 311602]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01784_not_prime : ¬(recordGapCenter - 311554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 311554]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01785_not_prime : ¬(recordGapCenter - 311478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 311478]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01786_not_prime : ¬(recordGapCenter - 311442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 311442]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01787_not_prime : ¬(recordGapCenter - 311434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 311434]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01788_not_prime : ¬(recordGapCenter - 311394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 311394]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01789_not_prime : ¬(recordGapCenter - 311218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 311218]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01790_not_prime : ¬(recordGapCenter - 311118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 311118]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01791_not_prime : ¬(recordGapCenter - 311034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 311034]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm01792_not_prime : ¬(recordGapCenter - 310852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 310852]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

end PrimeFactorUnimodality
