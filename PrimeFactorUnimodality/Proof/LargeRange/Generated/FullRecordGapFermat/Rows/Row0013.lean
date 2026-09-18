import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00013_values : List Nat :=
  [fullRecordGapCenterValue - 173002,
    fullRecordGapCenterValue - 172828,
    fullRecordGapCenterValue - 172804,
    fullRecordGapCenterValue - 172762,
    fullRecordGapCenterValue - 172714,
    fullRecordGapCenterValue - 172498,
    fullRecordGapCenterValue - 172402,
    fullRecordGapCenterValue - 171982,
    fullRecordGapCenterValue - 171694,
    fullRecordGapCenterValue - 171562,
    fullRecordGapCenterValue - 171502,
    fullRecordGapCenterValue - 171334,
    fullRecordGapCenterValue - 171238,
    fullRecordGapCenterValue - 171154,
    fullRecordGapCenterValue - 171034,
    fullRecordGapCenterValue - 170902,
    fullRecordGapCenterValue - 170854,
    fullRecordGapCenterValue - 170518,
    fullRecordGapCenterValue - 170494,
    fullRecordGapCenterValue - 170182,
    fullRecordGapCenterValue - 170100,
    fullRecordGapCenterValue - 169894,
    fullRecordGapCenterValue - 169738,
    fullRecordGapCenterValue - 169654,
    fullRecordGapCenterValue - 169522,
    fullRecordGapCenterValue - 169402,
    fullRecordGapCenterValue - 169258,
    fullRecordGapCenterValue - 169102,
    fullRecordGapCenterValue - 169018,
    fullRecordGapCenterValue - 168934,
    fullRecordGapCenterValue - 168802,
    fullRecordGapCenterValue - 168754,
    fullRecordGapCenterValue - 168598,
    fullRecordGapCenterValue - 168094,
    fullRecordGapCenterValue - 168034,
    fullRecordGapCenterValue - 167554,
    fullRecordGapCenterValue - 167242,
    fullRecordGapCenterValue - 167158,
    fullRecordGapCenterValue - 167122,
    fullRecordGapCenterValue - 166942,
    fullRecordGapCenterValue - 166798,
    fullRecordGapCenterValue - 166714,
    fullRecordGapCenterValue - 166534,
    fullRecordGapCenterValue - 166462,
    fullRecordGapCenterValue - 166012,
    fullRecordGapCenterValue - 165778,
    fullRecordGapCenterValue - 165622,
    fullRecordGapCenterValue - 165562,
    fullRecordGapCenterValue - 165442,
    fullRecordGapCenterValue - 165238,
    fullRecordGapCenterValue - 165058,
    fullRecordGapCenterValue - 164698,
    fullRecordGapCenterValue - 164482,
    fullRecordGapCenterValue - 164434,
    fullRecordGapCenterValue - 164062,
    fullRecordGapCenterValue - 163942,
    fullRecordGapCenterValue - 163840,
    fullRecordGapCenterValue - 163678,
    fullRecordGapCenterValue - 163522,
    fullRecordGapCenterValue - 163414,
    fullRecordGapCenterValue - 163342,
    fullRecordGapCenterValue - 163294,
    fullRecordGapCenterValue - 163258,
    fullRecordGapCenterValue - 163138,
    fullRecordGapCenterValue - 163054,
    fullRecordGapCenterValue - 162802,
    fullRecordGapCenterValue - 162742,
    fullRecordGapCenterValue - 162718,
    fullRecordGapCenterValue - 162154,
    fullRecordGapCenterValue - 162094,
    fullRecordGapCenterValue - 162000,
    fullRecordGapCenterValue - 161700,
    fullRecordGapCenterValue - 161698,
    fullRecordGapCenterValue - 161662,
    fullRecordGapCenterValue - 161362,
    fullRecordGapCenterValue - 161338,
    fullRecordGapCenterValue - 161280,
    fullRecordGapCenterValue - 160858,
    fullRecordGapCenterValue - 160774,
    fullRecordGapCenterValue - 160618,
    fullRecordGapCenterValue - 160078,
    fullRecordGapCenterValue - 159778,
    fullRecordGapCenterValue - 159694,
    fullRecordGapCenterValue - 159634,
    fullRecordGapCenterValue - 159382,
    fullRecordGapCenterValue - 158760,
    fullRecordGapCenterValue - 158674,
    fullRecordGapCenterValue - 158482,
    fullRecordGapCenterValue - 158400,
    fullRecordGapCenterValue - 158302,
    fullRecordGapCenterValue - 158062,
    fullRecordGapCenterValue - 157978,
    fullRecordGapCenterValue - 157714,
    fullRecordGapCenterValue - 157618,
    fullRecordGapCenterValue - 157594,
    fullRecordGapCenterValue - 157582,
    fullRecordGapCenterValue - 156874,
    fullRecordGapCenterValue - 156802,
    fullRecordGapCenterValue - 156694,
    fullRecordGapCenterValue - 156382,
    fullRecordGapCenterValue - 156250,
    fullRecordGapCenterValue - 156082,
    fullRecordGapCenterValue - 155998,
    fullRecordGapCenterValue - 155902,
    fullRecordGapCenterValue - 155734,
    fullRecordGapCenterValue - 155602,
    fullRecordGapCenterValue - 155398,
    fullRecordGapCenterValue - 155362,
    fullRecordGapCenterValue - 155232,
    fullRecordGapCenterValue - 154702,
    fullRecordGapCenterValue - 154558,
    fullRecordGapCenterValue - 154342,
    fullRecordGapCenterValue - 154282,
    fullRecordGapCenterValue - 154138,
    fullRecordGapCenterValue - 153922,
    fullRecordGapCenterValue - 153838,
    fullRecordGapCenterValue - 153664,
    fullRecordGapCenterValue - 153600,
    fullRecordGapCenterValue - 153562,
    fullRecordGapCenterValue - 153514,
    fullRecordGapCenterValue - 153358,
    fullRecordGapCenterValue - 153262,
    fullRecordGapCenterValue - 153214,
    fullRecordGapCenterValue - 152962,
    fullRecordGapCenterValue - 152842,
    fullRecordGapCenterValue - 152758,
    fullRecordGapCenterValue - 152158,
    fullRecordGapCenterValue - 152064,
    fullRecordGapCenterValue - 151594,
    fullRecordGapCenterValue - 151414,
    fullRecordGapCenterValue - 151282,
    fullRecordGapCenterValue - 151258,
    fullRecordGapCenterValue - 151234,
    fullRecordGapCenterValue - 151200,
    fullRecordGapCenterValue - 150958,
    fullRecordGapCenterValue - 150694,
    fullRecordGapCenterValue - 150538,
    fullRecordGapCenterValue - 150034,
    fullRecordGapCenterValue - 149398,
    fullRecordGapCenterValue - 149134,
    fullRecordGapCenterValue - 149062,
    fullRecordGapCenterValue - 148942,
    fullRecordGapCenterValue - 148714,
    fullRecordGapCenterValue - 148462,
    fullRecordGapCenterValue - 148354,
    fullRecordGapCenterValue - 148102,
    fullRecordGapCenterValue - 148054,
    fullRecordGapCenterValue - 147840,
    fullRecordGapCenterValue - 147214,
    fullRecordGapCenterValue - 147094,
    fullRecordGapCenterValue - 146758,
    fullRecordGapCenterValue - 146662,
    fullRecordGapCenterValue - 146410,
    fullRecordGapCenterValue - 146362,
    fullRecordGapCenterValue - 146158,
    fullRecordGapCenterValue - 146038,
    fullRecordGapCenterValue - 145954,
    fullRecordGapCenterValue - 145800,
    fullRecordGapCenterValue - 145738,
    fullRecordGapCenterValue - 145438,
    fullRecordGapCenterValue - 145414,
    fullRecordGapCenterValue - 145102,
    fullRecordGapCenterValue - 144934,
    fullRecordGapCenterValue - 144862,
    fullRecordGapCenterValue - 144682,
    fullRecordGapCenterValue - 144574,
    fullRecordGapCenterValue - 144322,
    fullRecordGapCenterValue - 144178,
    fullRecordGapCenterValue - 144154,
    fullRecordGapCenterValue - 143974,
    fullRecordGapCenterValue - 143748,
    fullRecordGapCenterValue - 143722,
    fullRecordGapCenterValue - 143698,
    fullRecordGapCenterValue - 143614,
    fullRecordGapCenterValue - 143398,
    fullRecordGapCenterValue - 143098,
    fullRecordGapCenterValue - 142884,
    fullRecordGapCenterValue - 142858,
    fullRecordGapCenterValue - 142678,
    fullRecordGapCenterValue - 142342,
    fullRecordGapCenterValue - 142294,
    fullRecordGapCenterValue - 142162,
    fullRecordGapCenterValue - 142138,
    fullRecordGapCenterValue - 141874,
    fullRecordGapCenterValue - 141682,
    fullRecordGapCenterValue - 141238,
    fullRecordGapCenterValue - 140962,
    fullRecordGapCenterValue - 140878,
    fullRecordGapCenterValue - 140362,
    fullRecordGapCenterValue - 140242,
    fullRecordGapCenterValue - 140158,
    fullRecordGapCenterValue - 140038,
    fullRecordGapCenterValue - 139654,
    fullRecordGapCenterValue - 139642,
    fullRecordGapCenterValue - 139558,
    fullRecordGapCenterValue - 139474,
    fullRecordGapCenterValue - 139078,
    fullRecordGapCenterValue - 138862,
    fullRecordGapCenterValue - 138742,
    fullRecordGapCenterValue - 138682,
    fullRecordGapCenterValue - 138600,
    fullRecordGapCenterValue - 138442,
    fullRecordGapCenterValue - 138394,
    fullRecordGapCenterValue - 138238,
    fullRecordGapCenterValue - 138022,
    fullRecordGapCenterValue - 137794,
    fullRecordGapCenterValue - 137500,
    fullRecordGapCenterValue - 137458,
    fullRecordGapCenterValue - 137374,
    fullRecordGapCenterValue - 137200,
    fullRecordGapCenterValue - 137134,
    fullRecordGapCenterValue - 137062,
    fullRecordGapCenterValue - 136978,
    fullRecordGapCenterValue - 136894,
    fullRecordGapCenterValue - 136702,
    fullRecordGapCenterValue - 136342,
    fullRecordGapCenterValue - 136198,
    fullRecordGapCenterValue - 135658,
    fullRecordGapCenterValue - 135202,
    fullRecordGapCenterValue - 135118,
    fullRecordGapCenterValue - 134998,
    fullRecordGapCenterValue - 134962,
    fullRecordGapCenterValue - 134818,
    fullRecordGapCenterValue - 134782,
    fullRecordGapCenterValue - 134362,
    fullRecordGapCenterValue - 134122,
    fullRecordGapCenterValue - 133954,
    fullRecordGapCenterValue - 133894,
    fullRecordGapCenterValue - 133702,
    fullRecordGapCenterValue - 133650,
    fullRecordGapCenterValue - 133618,
    fullRecordGapCenterValue - 132982,
    fullRecordGapCenterValue - 132898,
    fullRecordGapCenterValue - 132718,
    fullRecordGapCenterValue - 132094,
    fullRecordGapCenterValue - 131962,
    fullRecordGapCenterValue - 131914,
    fullRecordGapCenterValue - 131842,
    fullRecordGapCenterValue - 131712,
    fullRecordGapCenterValue - 131662,
    fullRecordGapCenterValue - 131302,
    fullRecordGapCenterValue - 131250,
    fullRecordGapCenterValue - 131158,
    fullRecordGapCenterValue - 131038,
    fullRecordGapCenterValue - 130680,
    fullRecordGapCenterValue - 130654,
    fullRecordGapCenterValue - 130294,
    fullRecordGapCenterValue - 130258,
    fullRecordGapCenterValue - 129838,
    fullRecordGapCenterValue - 129418,
    fullRecordGapCenterValue - 129360,
    fullRecordGapCenterValue - 129322,
    fullRecordGapCenterValue - 129202,
    fullRecordGapCenterValue - 128434,
    fullRecordGapCenterValue - 128314,
    fullRecordGapCenterValue - 128302]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00013_fermat : ∀ n ∈ fullRecordGapRow00013_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03073_not_prime : ¬(recordGapCenter - 173002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 173002]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03074_not_prime : ¬(recordGapCenter - 172828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 172828]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03075_not_prime : ¬(recordGapCenter - 172804).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 172804]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03076_not_prime : ¬(recordGapCenter - 172762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 172762]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03077_not_prime : ¬(recordGapCenter - 172714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 172714]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03078_not_prime : ¬(recordGapCenter - 172498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 172498]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03079_not_prime : ¬(recordGapCenter - 172402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 172402]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03080_not_prime : ¬(recordGapCenter - 171982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 171982]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03081_not_prime : ¬(recordGapCenter - 171694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 171694]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03082_not_prime : ¬(recordGapCenter - 171562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 171562]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03083_not_prime : ¬(recordGapCenter - 171502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 171502]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03084_not_prime : ¬(recordGapCenter - 171334).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 171334]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03085_not_prime : ¬(recordGapCenter - 171238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 171238]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03086_not_prime : ¬(recordGapCenter - 171154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 171154]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03087_not_prime : ¬(recordGapCenter - 171034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 171034]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03088_not_prime : ¬(recordGapCenter - 170902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 170902]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03089_not_prime : ¬(recordGapCenter - 170854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 170854]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03090_not_prime : ¬(recordGapCenter - 170518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 170518]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03091_not_prime : ¬(recordGapCenter - 170494).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 170494]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03092_not_prime : ¬(recordGapCenter - 170182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 170182]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03093_not_prime : ¬(recordGapCenter - 170100).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 170100]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03094_not_prime : ¬(recordGapCenter - 169894).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 169894]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03095_not_prime : ¬(recordGapCenter - 169738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 169738]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03096_not_prime : ¬(recordGapCenter - 169654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 169654]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03097_not_prime : ¬(recordGapCenter - 169522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 169522]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03098_not_prime : ¬(recordGapCenter - 169402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 169402]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03099_not_prime : ¬(recordGapCenter - 169258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 169258]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03100_not_prime : ¬(recordGapCenter - 169102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 169102]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03101_not_prime : ¬(recordGapCenter - 169018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 169018]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03102_not_prime : ¬(recordGapCenter - 168934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 168934]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03103_not_prime : ¬(recordGapCenter - 168802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 168802]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03104_not_prime : ¬(recordGapCenter - 168754).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 168754]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03105_not_prime : ¬(recordGapCenter - 168598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 168598]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03106_not_prime : ¬(recordGapCenter - 168094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 168094]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03107_not_prime : ¬(recordGapCenter - 168034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 168034]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03108_not_prime : ¬(recordGapCenter - 167554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 167554]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03109_not_prime : ¬(recordGapCenter - 167242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 167242]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03110_not_prime : ¬(recordGapCenter - 167158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 167158]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03111_not_prime : ¬(recordGapCenter - 167122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 167122]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03112_not_prime : ¬(recordGapCenter - 166942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 166942]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03113_not_prime : ¬(recordGapCenter - 166798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 166798]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03114_not_prime : ¬(recordGapCenter - 166714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 166714]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03115_not_prime : ¬(recordGapCenter - 166534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 166534]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03116_not_prime : ¬(recordGapCenter - 166462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 166462]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03117_not_prime : ¬(recordGapCenter - 166012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 166012]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03118_not_prime : ¬(recordGapCenter - 165778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 165778]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03119_not_prime : ¬(recordGapCenter - 165622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 165622]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03120_not_prime : ¬(recordGapCenter - 165562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 165562]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03121_not_prime : ¬(recordGapCenter - 165442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 165442]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03122_not_prime : ¬(recordGapCenter - 165238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 165238]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03123_not_prime : ¬(recordGapCenter - 165058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 165058]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03124_not_prime : ¬(recordGapCenter - 164698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 164698]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03125_not_prime : ¬(recordGapCenter - 164482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 164482]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03126_not_prime : ¬(recordGapCenter - 164434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 164434]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03127_not_prime : ¬(recordGapCenter - 164062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 164062]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03128_not_prime : ¬(recordGapCenter - 163942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 163942]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03129_not_prime : ¬(recordGapCenter - 163840).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 163840]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03130_not_prime : ¬(recordGapCenter - 163678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 163678]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03131_not_prime : ¬(recordGapCenter - 163522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 163522]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03132_not_prime : ¬(recordGapCenter - 163414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 163414]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03133_not_prime : ¬(recordGapCenter - 163342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 163342]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03134_not_prime : ¬(recordGapCenter - 163294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 163294]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03135_not_prime : ¬(recordGapCenter - 163258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 163258]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03136_not_prime : ¬(recordGapCenter - 163138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 163138]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03137_not_prime : ¬(recordGapCenter - 163054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 163054]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03138_not_prime : ¬(recordGapCenter - 162802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 162802]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03139_not_prime : ¬(recordGapCenter - 162742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 162742]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03140_not_prime : ¬(recordGapCenter - 162718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 162718]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03141_not_prime : ¬(recordGapCenter - 162154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 162154]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03142_not_prime : ¬(recordGapCenter - 162094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 162094]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03143_not_prime : ¬(recordGapCenter - 162000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 162000]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03144_not_prime : ¬(recordGapCenter - 161700).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 161700]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03145_not_prime : ¬(recordGapCenter - 161698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 161698]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03146_not_prime : ¬(recordGapCenter - 161662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 161662]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03147_not_prime : ¬(recordGapCenter - 161362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 161362]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03148_not_prime : ¬(recordGapCenter - 161338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 161338]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03149_not_prime : ¬(recordGapCenter - 161280).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 161280]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03150_not_prime : ¬(recordGapCenter - 160858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 160858]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03151_not_prime : ¬(recordGapCenter - 160774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 160774]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03152_not_prime : ¬(recordGapCenter - 160618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 160618]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03153_not_prime : ¬(recordGapCenter - 160078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 160078]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03154_not_prime : ¬(recordGapCenter - 159778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 159778]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03155_not_prime : ¬(recordGapCenter - 159694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 159694]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03156_not_prime : ¬(recordGapCenter - 159634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 159634]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03157_not_prime : ¬(recordGapCenter - 159382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 159382]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03158_not_prime : ¬(recordGapCenter - 158760).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 158760]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03159_not_prime : ¬(recordGapCenter - 158674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 158674]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03160_not_prime : ¬(recordGapCenter - 158482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 158482]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03161_not_prime : ¬(recordGapCenter - 158400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 158400]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03162_not_prime : ¬(recordGapCenter - 158302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 158302]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03163_not_prime : ¬(recordGapCenter - 158062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 158062]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03164_not_prime : ¬(recordGapCenter - 157978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 157978]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03165_not_prime : ¬(recordGapCenter - 157714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 157714]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03166_not_prime : ¬(recordGapCenter - 157618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 157618]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03167_not_prime : ¬(recordGapCenter - 157594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 157594]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03168_not_prime : ¬(recordGapCenter - 157582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 157582]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03169_not_prime : ¬(recordGapCenter - 156874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 156874]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03170_not_prime : ¬(recordGapCenter - 156802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 156802]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03171_not_prime : ¬(recordGapCenter - 156694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 156694]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03172_not_prime : ¬(recordGapCenter - 156382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 156382]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03173_not_prime : ¬(recordGapCenter - 156250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 156250]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03174_not_prime : ¬(recordGapCenter - 156082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 156082]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03175_not_prime : ¬(recordGapCenter - 155998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 155998]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03176_not_prime : ¬(recordGapCenter - 155902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 155902]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03177_not_prime : ¬(recordGapCenter - 155734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 155734]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03178_not_prime : ¬(recordGapCenter - 155602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 155602]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03179_not_prime : ¬(recordGapCenter - 155398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 155398]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03180_not_prime : ¬(recordGapCenter - 155362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 155362]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03181_not_prime : ¬(recordGapCenter - 155232).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 155232]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03182_not_prime : ¬(recordGapCenter - 154702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 154702]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03183_not_prime : ¬(recordGapCenter - 154558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 154558]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03184_not_prime : ¬(recordGapCenter - 154342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 154342]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03185_not_prime : ¬(recordGapCenter - 154282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 154282]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03186_not_prime : ¬(recordGapCenter - 154138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 154138]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03187_not_prime : ¬(recordGapCenter - 153922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 153922]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03188_not_prime : ¬(recordGapCenter - 153838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 153838]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03189_not_prime : ¬(recordGapCenter - 153664).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 153664]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03190_not_prime : ¬(recordGapCenter - 153600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 153600]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03191_not_prime : ¬(recordGapCenter - 153562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 153562]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03192_not_prime : ¬(recordGapCenter - 153514).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 153514]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03193_not_prime : ¬(recordGapCenter - 153358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 153358]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03194_not_prime : ¬(recordGapCenter - 153262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 153262]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03195_not_prime : ¬(recordGapCenter - 153214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 153214]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03196_not_prime : ¬(recordGapCenter - 152962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 152962]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03197_not_prime : ¬(recordGapCenter - 152842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 152842]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03198_not_prime : ¬(recordGapCenter - 152758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 152758]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03199_not_prime : ¬(recordGapCenter - 152158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 152158]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03200_not_prime : ¬(recordGapCenter - 152064).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 152064]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03201_not_prime : ¬(recordGapCenter - 151594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 151594]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03202_not_prime : ¬(recordGapCenter - 151414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 151414]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03203_not_prime : ¬(recordGapCenter - 151282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 151282]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03204_not_prime : ¬(recordGapCenter - 151258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 151258]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03205_not_prime : ¬(recordGapCenter - 151234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 151234]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03206_not_prime : ¬(recordGapCenter - 151200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 151200]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03207_not_prime : ¬(recordGapCenter - 150958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 150958]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03208_not_prime : ¬(recordGapCenter - 150694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 150694]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03209_not_prime : ¬(recordGapCenter - 150538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 150538]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03210_not_prime : ¬(recordGapCenter - 150034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 150034]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03211_not_prime : ¬(recordGapCenter - 149398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 149398]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03212_not_prime : ¬(recordGapCenter - 149134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 149134]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03213_not_prime : ¬(recordGapCenter - 149062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 149062]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03214_not_prime : ¬(recordGapCenter - 148942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 148942]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03215_not_prime : ¬(recordGapCenter - 148714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 148714]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03216_not_prime : ¬(recordGapCenter - 148462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 148462]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03217_not_prime : ¬(recordGapCenter - 148354).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 148354]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03218_not_prime : ¬(recordGapCenter - 148102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 148102]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03219_not_prime : ¬(recordGapCenter - 148054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 148054]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03220_not_prime : ¬(recordGapCenter - 147840).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 147840]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03221_not_prime : ¬(recordGapCenter - 147214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 147214]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03222_not_prime : ¬(recordGapCenter - 147094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 147094]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03223_not_prime : ¬(recordGapCenter - 146758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 146758]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03224_not_prime : ¬(recordGapCenter - 146662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 146662]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03225_not_prime : ¬(recordGapCenter - 146410).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 146410]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03226_not_prime : ¬(recordGapCenter - 146362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 146362]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03227_not_prime : ¬(recordGapCenter - 146158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 146158]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03228_not_prime : ¬(recordGapCenter - 146038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 146038]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03229_not_prime : ¬(recordGapCenter - 145954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 145954]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03230_not_prime : ¬(recordGapCenter - 145800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 145800]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03231_not_prime : ¬(recordGapCenter - 145738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 145738]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03232_not_prime : ¬(recordGapCenter - 145438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 145438]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03233_not_prime : ¬(recordGapCenter - 145414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 145414]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03234_not_prime : ¬(recordGapCenter - 145102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 145102]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03235_not_prime : ¬(recordGapCenter - 144934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 144934]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03236_not_prime : ¬(recordGapCenter - 144862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 144862]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03237_not_prime : ¬(recordGapCenter - 144682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 144682]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03238_not_prime : ¬(recordGapCenter - 144574).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 144574]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03239_not_prime : ¬(recordGapCenter - 144322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 144322]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03240_not_prime : ¬(recordGapCenter - 144178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 144178]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03241_not_prime : ¬(recordGapCenter - 144154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 144154]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03242_not_prime : ¬(recordGapCenter - 143974).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 143974]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03243_not_prime : ¬(recordGapCenter - 143748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 143748]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03244_not_prime : ¬(recordGapCenter - 143722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 143722]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03245_not_prime : ¬(recordGapCenter - 143698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 143698]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03246_not_prime : ¬(recordGapCenter - 143614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 143614]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03247_not_prime : ¬(recordGapCenter - 143398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 143398]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03248_not_prime : ¬(recordGapCenter - 143098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 143098]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03249_not_prime : ¬(recordGapCenter - 142884).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 142884]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03250_not_prime : ¬(recordGapCenter - 142858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 142858]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03251_not_prime : ¬(recordGapCenter - 142678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 142678]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03252_not_prime : ¬(recordGapCenter - 142342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 142342]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03253_not_prime : ¬(recordGapCenter - 142294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 142294]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03254_not_prime : ¬(recordGapCenter - 142162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 142162]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03255_not_prime : ¬(recordGapCenter - 142138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 142138]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03256_not_prime : ¬(recordGapCenter - 141874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 141874]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03257_not_prime : ¬(recordGapCenter - 141682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 141682]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03258_not_prime : ¬(recordGapCenter - 141238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 141238]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03259_not_prime : ¬(recordGapCenter - 140962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 140962]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03260_not_prime : ¬(recordGapCenter - 140878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 140878]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03261_not_prime : ¬(recordGapCenter - 140362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 140362]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03262_not_prime : ¬(recordGapCenter - 140242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 140242]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03263_not_prime : ¬(recordGapCenter - 140158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 140158]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03264_not_prime : ¬(recordGapCenter - 140038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 140038]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03265_not_prime : ¬(recordGapCenter - 139654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 139654]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03266_not_prime : ¬(recordGapCenter - 139642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 139642]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03267_not_prime : ¬(recordGapCenter - 139558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 139558]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03268_not_prime : ¬(recordGapCenter - 139474).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 139474]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03269_not_prime : ¬(recordGapCenter - 139078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 139078]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03270_not_prime : ¬(recordGapCenter - 138862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 138862]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03271_not_prime : ¬(recordGapCenter - 138742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 138742]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03272_not_prime : ¬(recordGapCenter - 138682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 138682]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03273_not_prime : ¬(recordGapCenter - 138600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 138600]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03274_not_prime : ¬(recordGapCenter - 138442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 138442]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03275_not_prime : ¬(recordGapCenter - 138394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 138394]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03276_not_prime : ¬(recordGapCenter - 138238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 138238]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03277_not_prime : ¬(recordGapCenter - 138022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 138022]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03278_not_prime : ¬(recordGapCenter - 137794).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 137794]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03279_not_prime : ¬(recordGapCenter - 137500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 137500]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03280_not_prime : ¬(recordGapCenter - 137458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 137458]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03281_not_prime : ¬(recordGapCenter - 137374).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 137374]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03282_not_prime : ¬(recordGapCenter - 137200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 137200]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03283_not_prime : ¬(recordGapCenter - 137134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 137134]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03284_not_prime : ¬(recordGapCenter - 137062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 137062]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03285_not_prime : ¬(recordGapCenter - 136978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 136978]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03286_not_prime : ¬(recordGapCenter - 136894).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 136894]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03287_not_prime : ¬(recordGapCenter - 136702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 136702]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03288_not_prime : ¬(recordGapCenter - 136342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 136342]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03289_not_prime : ¬(recordGapCenter - 136198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 136198]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03290_not_prime : ¬(recordGapCenter - 135658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 135658]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03291_not_prime : ¬(recordGapCenter - 135202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 135202]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03292_not_prime : ¬(recordGapCenter - 135118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 135118]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03293_not_prime : ¬(recordGapCenter - 134998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 134998]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03294_not_prime : ¬(recordGapCenter - 134962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 134962]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03295_not_prime : ¬(recordGapCenter - 134818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 134818]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03296_not_prime : ¬(recordGapCenter - 134782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 134782]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03297_not_prime : ¬(recordGapCenter - 134362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 134362]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03298_not_prime : ¬(recordGapCenter - 134122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 134122]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03299_not_prime : ¬(recordGapCenter - 133954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 133954]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03300_not_prime : ¬(recordGapCenter - 133894).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 133894]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03301_not_prime : ¬(recordGapCenter - 133702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 133702]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03302_not_prime : ¬(recordGapCenter - 133650).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 133650]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03303_not_prime : ¬(recordGapCenter - 133618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 133618]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03304_not_prime : ¬(recordGapCenter - 132982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 132982]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03305_not_prime : ¬(recordGapCenter - 132898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 132898]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03306_not_prime : ¬(recordGapCenter - 132718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 132718]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03307_not_prime : ¬(recordGapCenter - 132094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 132094]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03308_not_prime : ¬(recordGapCenter - 131962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 131962]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03309_not_prime : ¬(recordGapCenter - 131914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 131914]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03310_not_prime : ¬(recordGapCenter - 131842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 131842]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03311_not_prime : ¬(recordGapCenter - 131712).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 131712]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03312_not_prime : ¬(recordGapCenter - 131662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 131662]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03313_not_prime : ¬(recordGapCenter - 131302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 131302]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03314_not_prime : ¬(recordGapCenter - 131250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 131250]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03315_not_prime : ¬(recordGapCenter - 131158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 131158]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03316_not_prime : ¬(recordGapCenter - 131038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 131038]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03317_not_prime : ¬(recordGapCenter - 130680).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 130680]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03318_not_prime : ¬(recordGapCenter - 130654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 130654]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03319_not_prime : ¬(recordGapCenter - 130294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 130294]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03320_not_prime : ¬(recordGapCenter - 130258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 130258]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03321_not_prime : ¬(recordGapCenter - 129838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 129838]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03322_not_prime : ¬(recordGapCenter - 129418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 129418]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03323_not_prime : ¬(recordGapCenter - 129360).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 129360]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03324_not_prime : ¬(recordGapCenter - 129322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 129322]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03325_not_prime : ¬(recordGapCenter - 129202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 129202]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03326_not_prime : ¬(recordGapCenter - 128434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 128434]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03327_not_prime : ¬(recordGapCenter - 128314).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 128314]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm03328_not_prime : ¬(recordGapCenter - 128302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 128302]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

end PrimeFactorUnimodality
