import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00018_values : List Nat :=
  [fullRecordGapCenterValue + 134822,
    fullRecordGapCenterValue + 134906,
    fullRecordGapCenterValue + 135000,
    fullRecordGapCenterValue + 135158,
    fullRecordGapCenterValue + 135398,
    fullRecordGapCenterValue + 135446,
    fullRecordGapCenterValue + 135602,
    fullRecordGapCenterValue + 135828,
    fullRecordGapCenterValue + 135986,
    fullRecordGapCenterValue + 136080,
    fullRecordGapCenterValue + 136082,
    fullRecordGapCenterValue + 136118,
    fullRecordGapCenterValue + 136622,
    fullRecordGapCenterValue + 136778,
    fullRecordGapCenterValue + 136886,
    fullRecordGapCenterValue + 137366,
    fullRecordGapCenterValue + 137426,
    fullRecordGapCenterValue + 137498,
    fullRecordGapCenterValue + 137582,
    fullRecordGapCenterValue + 137798,
    fullRecordGapCenterValue + 138122,
    fullRecordGapCenterValue + 138146,
    fullRecordGapCenterValue + 138240,
    fullRecordGapCenterValue + 138302,
    fullRecordGapCenterValue + 138386,
    fullRecordGapCenterValue + 138518,
    fullRecordGapCenterValue + 138600,
    fullRecordGapCenterValue + 138806,
    fullRecordGapCenterValue + 138986,
    fullRecordGapCenterValue + 139382,
    fullRecordGapCenterValue + 139478,
    fullRecordGapCenterValue + 139526,
    fullRecordGapCenterValue + 139658,
    fullRecordGapCenterValue + 139862,
    fullRecordGapCenterValue + 140018,
    fullRecordGapCenterValue + 140078,
    fullRecordGapCenterValue + 140102,
    fullRecordGapCenterValue + 140198,
    fullRecordGapCenterValue + 140222,
    fullRecordGapCenterValue + 140282,
    fullRecordGapCenterValue + 140702,
    fullRecordGapCenterValue + 140918,
    fullRecordGapCenterValue + 141278,
    fullRecordGapCenterValue + 141458,
    fullRecordGapCenterValue + 141758,
    fullRecordGapCenterValue + 141842,
    fullRecordGapCenterValue + 141998,
    fullRecordGapCenterValue + 142178,
    fullRecordGapCenterValue + 142296,
    fullRecordGapCenterValue + 142322,
    fullRecordGapCenterValue + 142418,
    fullRecordGapCenterValue + 142560,
    fullRecordGapCenterValue + 142838,
    fullRecordGapCenterValue + 142958,
    fullRecordGapCenterValue + 143342,
    fullRecordGapCenterValue + 143360,
    fullRecordGapCenterValue + 143748,
    fullRecordGapCenterValue + 144000,
    fullRecordGapCenterValue + 144062,
    fullRecordGapCenterValue + 144182,
    fullRecordGapCenterValue + 144218,
    fullRecordGapCenterValue + 144446,
    fullRecordGapCenterValue + 144506,
    fullRecordGapCenterValue + 144842,
    fullRecordGapCenterValue + 144986,
    fullRecordGapCenterValue + 145118,
    fullRecordGapCenterValue + 145346,
    fullRecordGapCenterValue + 145358,
    fullRecordGapCenterValue + 145478,
    fullRecordGapCenterValue + 145530,
    fullRecordGapCenterValue + 145646,
    fullRecordGapCenterValue + 145800,
    fullRecordGapCenterValue + 145946,
    fullRecordGapCenterValue + 146282,
    fullRecordGapCenterValue + 146738,
    fullRecordGapCenterValue + 146906,
    fullRecordGapCenterValue + 146966,
    fullRecordGapCenterValue + 147386,
    fullRecordGapCenterValue + 147456,
    fullRecordGapCenterValue + 147698,
    fullRecordGapCenterValue + 147878,
    fullRecordGapCenterValue + 148142,
    fullRecordGapCenterValue + 148202,
    fullRecordGapCenterValue + 148262,
    fullRecordGapCenterValue + 148286,
    fullRecordGapCenterValue + 148766,
    fullRecordGapCenterValue + 149072,
    fullRecordGapCenterValue + 149306,
    fullRecordGapCenterValue + 149426,
    fullRecordGapCenterValue + 149438,
    fullRecordGapCenterValue + 149462,
    fullRecordGapCenterValue + 149642,
    fullRecordGapCenterValue + 149846,
    fullRecordGapCenterValue + 150000,
    fullRecordGapCenterValue + 150158,
    fullRecordGapCenterValue + 150266,
    fullRecordGapCenterValue + 150446,
    fullRecordGapCenterValue + 150578,
    fullRecordGapCenterValue + 150920,
    fullRecordGapCenterValue + 151142,
    fullRecordGapCenterValue + 151200,
    fullRecordGapCenterValue + 151250,
    fullRecordGapCenterValue + 151358,
    fullRecordGapCenterValue + 151586,
    fullRecordGapCenterValue + 151706,
    fullRecordGapCenterValue + 151826,
    fullRecordGapCenterValue + 152078,
    fullRecordGapCenterValue + 152162,
    fullRecordGapCenterValue + 152426,
    fullRecordGapCenterValue + 152462,
    fullRecordGapCenterValue + 152486,
    fullRecordGapCenterValue + 152738,
    fullRecordGapCenterValue + 153090,
    fullRecordGapCenterValue + 153158,
    fullRecordGapCenterValue + 153602,
    fullRecordGapCenterValue + 153638,
    fullRecordGapCenterValue + 153662,
    fullRecordGapCenterValue + 153746,
    fullRecordGapCenterValue + 154058,
    fullRecordGapCenterValue + 154082,
    fullRecordGapCenterValue + 155138,
    fullRecordGapCenterValue + 155232,
    fullRecordGapCenterValue + 155486,
    fullRecordGapCenterValue + 155520,
    fullRecordGapCenterValue + 155522,
    fullRecordGapCenterValue + 156062,
    fullRecordGapCenterValue + 156158,
    fullRecordGapCenterValue + 156242,
    fullRecordGapCenterValue + 156326,
    fullRecordGapCenterValue + 156458,
    fullRecordGapCenterValue + 156816,
    fullRecordGapCenterValue + 157382,
    fullRecordGapCenterValue + 157706,
    fullRecordGapCenterValue + 157778,
    fullRecordGapCenterValue + 157958,
    fullRecordGapCenterValue + 158126,
    fullRecordGapCenterValue + 158400,
    fullRecordGapCenterValue + 158466,
    fullRecordGapCenterValue + 158558,
    fullRecordGapCenterValue + 158618,
    fullRecordGapCenterValue + 158786,
    fullRecordGapCenterValue + 158798,
    fullRecordGapCenterValue + 159218,
    fullRecordGapCenterValue + 159266,
    fullRecordGapCenterValue + 159398,
    fullRecordGapCenterValue + 159602,
    fullRecordGapCenterValue + 159626,
    fullRecordGapCenterValue + 159720,
    fullRecordGapCenterValue + 159878,
    fullRecordGapCenterValue + 160142,
    fullRecordGapCenterValue + 160346,
    fullRecordGapCenterValue + 160382,
    fullRecordGapCenterValue + 160526,
    fullRecordGapCenterValue + 160682,
    fullRecordGapCenterValue + 160898,
    fullRecordGapCenterValue + 161618,
    fullRecordGapCenterValue + 161822,
    fullRecordGapCenterValue + 161858,
    fullRecordGapCenterValue + 161906,
    fullRecordGapCenterValue + 162362,
    fullRecordGapCenterValue + 162662,
    fullRecordGapCenterValue + 162878,
    fullRecordGapCenterValue + 162926,
    fullRecordGapCenterValue + 163238,
    fullRecordGapCenterValue + 163298,
    fullRecordGapCenterValue + 163350,
    fullRecordGapCenterValue + 163406,
    fullRecordGapCenterValue + 163538,
    fullRecordGapCenterValue + 163598,
    fullRecordGapCenterValue + 163706,
    fullRecordGapCenterValue + 163766,
    fullRecordGapCenterValue + 163802,
    fullRecordGapCenterValue + 163838,
    fullRecordGapCenterValue + 164018,
    fullRecordGapCenterValue + 164102,
    fullRecordGapCenterValue + 164258,
    fullRecordGapCenterValue + 164438,
    fullRecordGapCenterValue + 164678,
    fullRecordGapCenterValue + 164966,
    fullRecordGapCenterValue + 165182,
    fullRecordGapCenterValue + 165398,
    fullRecordGapCenterValue + 165518,
    fullRecordGapCenterValue + 166178,
    fullRecordGapCenterValue + 166406,
    fullRecordGapCenterValue + 166698,
    fullRecordGapCenterValue + 167126,
    fullRecordGapCenterValue + 167402,
    fullRecordGapCenterValue + 167546,
    fullRecordGapCenterValue + 167666,
    fullRecordGapCenterValue + 168326,
    fullRecordGapCenterValue + 168422,
    fullRecordGapCenterValue + 168782,
    fullRecordGapCenterValue + 168842,
    fullRecordGapCenterValue + 168926,
    fullRecordGapCenterValue + 168960,
    fullRecordGapCenterValue + 168962,
    fullRecordGapCenterValue + 169046,
    fullRecordGapCenterValue + 169382,
    fullRecordGapCenterValue + 169586,
    fullRecordGapCenterValue + 169982,
    fullRecordGapCenterValue + 170042,
    fullRecordGapCenterValue + 170318,
    fullRecordGapCenterValue + 170426,
    fullRecordGapCenterValue + 170726,
    fullRecordGapCenterValue + 171278,
    fullRecordGapCenterValue + 171638,
    fullRecordGapCenterValue + 171686,
    fullRecordGapCenterValue + 171818,
    fullRecordGapCenterValue + 171866,
    fullRecordGapCenterValue + 171998,
    fullRecordGapCenterValue + 172032,
    fullRecordGapCenterValue + 172226,
    fullRecordGapCenterValue + 172358,
    fullRecordGapCenterValue + 172532,
    fullRecordGapCenterValue + 172538,
    fullRecordGapCenterValue + 172622,
    fullRecordGapCenterValue + 172646,
    fullRecordGapCenterValue + 172826,
    fullRecordGapCenterValue + 173078,
    fullRecordGapCenterValue + 173198,
    fullRecordGapCenterValue + 173486,
    fullRecordGapCenterValue + 173702,
    fullRecordGapCenterValue + 173738,
    fullRecordGapCenterValue + 173918,
    fullRecordGapCenterValue + 173948,
    fullRecordGapCenterValue + 174206,
    fullRecordGapCenterValue + 174240,
    fullRecordGapCenterValue + 174422,
    fullRecordGapCenterValue + 174806,
    fullRecordGapCenterValue + 175046,
    fullRecordGapCenterValue + 175166,
    fullRecordGapCenterValue + 175178,
    fullRecordGapCenterValue + 175298,
    fullRecordGapCenterValue + 175586,
    fullRecordGapCenterValue + 175616,
    fullRecordGapCenterValue + 175862,
    fullRecordGapCenterValue + 175892,
    fullRecordGapCenterValue + 175988,
    fullRecordGapCenterValue + 176186,
    fullRecordGapCenterValue + 176642,
    fullRecordGapCenterValue + 176846,
    fullRecordGapCenterValue + 177026,
    fullRecordGapCenterValue + 177116,
    fullRecordGapCenterValue + 177482,
    fullRecordGapCenterValue + 177746,
    fullRecordGapCenterValue + 178082,
    fullRecordGapCenterValue + 178202,
    fullRecordGapCenterValue + 178628,
    fullRecordGapCenterValue + 178742,
    fullRecordGapCenterValue + 178796,
    fullRecordGapCenterValue + 178826,
    fullRecordGapCenterValue + 179042,
    fullRecordGapCenterValue + 179198,
    fullRecordGapCenterValue + 179306,
    fullRecordGapCenterValue + 179342,
    fullRecordGapCenterValue + 179378]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00018_fermat : ∀ n ∈ fullRecordGapRow00018_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04353_not_prime : ¬(recordGapCenter + 134822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 134822]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04354_not_prime : ¬(recordGapCenter + 134906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 134906]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04355_not_prime : ¬(recordGapCenter + 135000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 135000]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04356_not_prime : ¬(recordGapCenter + 135158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 135158]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04357_not_prime : ¬(recordGapCenter + 135398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 135398]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04358_not_prime : ¬(recordGapCenter + 135446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 135446]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04359_not_prime : ¬(recordGapCenter + 135602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 135602]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04360_not_prime : ¬(recordGapCenter + 135828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 135828]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04361_not_prime : ¬(recordGapCenter + 135986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 135986]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04362_not_prime : ¬(recordGapCenter + 136080).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 136080]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04363_not_prime : ¬(recordGapCenter + 136082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 136082]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04364_not_prime : ¬(recordGapCenter + 136118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 136118]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04365_not_prime : ¬(recordGapCenter + 136622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 136622]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04366_not_prime : ¬(recordGapCenter + 136778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 136778]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04367_not_prime : ¬(recordGapCenter + 136886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 136886]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04368_not_prime : ¬(recordGapCenter + 137366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 137366]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04369_not_prime : ¬(recordGapCenter + 137426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 137426]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04370_not_prime : ¬(recordGapCenter + 137498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 137498]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04371_not_prime : ¬(recordGapCenter + 137582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 137582]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04372_not_prime : ¬(recordGapCenter + 137798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 137798]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04373_not_prime : ¬(recordGapCenter + 138122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 138122]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04374_not_prime : ¬(recordGapCenter + 138146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 138146]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04375_not_prime : ¬(recordGapCenter + 138240).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 138240]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04376_not_prime : ¬(recordGapCenter + 138302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 138302]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04377_not_prime : ¬(recordGapCenter + 138386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 138386]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04378_not_prime : ¬(recordGapCenter + 138518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 138518]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04379_not_prime : ¬(recordGapCenter + 138600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 138600]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04380_not_prime : ¬(recordGapCenter + 138806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 138806]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04381_not_prime : ¬(recordGapCenter + 138986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 138986]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04382_not_prime : ¬(recordGapCenter + 139382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 139382]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04383_not_prime : ¬(recordGapCenter + 139478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 139478]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04384_not_prime : ¬(recordGapCenter + 139526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 139526]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04385_not_prime : ¬(recordGapCenter + 139658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 139658]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04386_not_prime : ¬(recordGapCenter + 139862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 139862]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04387_not_prime : ¬(recordGapCenter + 140018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 140018]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04388_not_prime : ¬(recordGapCenter + 140078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 140078]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04389_not_prime : ¬(recordGapCenter + 140102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 140102]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04390_not_prime : ¬(recordGapCenter + 140198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 140198]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04391_not_prime : ¬(recordGapCenter + 140222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 140222]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04392_not_prime : ¬(recordGapCenter + 140282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 140282]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04393_not_prime : ¬(recordGapCenter + 140702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 140702]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04394_not_prime : ¬(recordGapCenter + 140918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 140918]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04395_not_prime : ¬(recordGapCenter + 141278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 141278]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04396_not_prime : ¬(recordGapCenter + 141458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 141458]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04397_not_prime : ¬(recordGapCenter + 141758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 141758]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04398_not_prime : ¬(recordGapCenter + 141842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 141842]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04399_not_prime : ¬(recordGapCenter + 141998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 141998]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04400_not_prime : ¬(recordGapCenter + 142178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 142178]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04401_not_prime : ¬(recordGapCenter + 142296).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 142296]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04402_not_prime : ¬(recordGapCenter + 142322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 142322]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04403_not_prime : ¬(recordGapCenter + 142418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 142418]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04404_not_prime : ¬(recordGapCenter + 142560).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 142560]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04405_not_prime : ¬(recordGapCenter + 142838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 142838]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04406_not_prime : ¬(recordGapCenter + 142958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 142958]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04407_not_prime : ¬(recordGapCenter + 143342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 143342]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04408_not_prime : ¬(recordGapCenter + 143360).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 143360]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04409_not_prime : ¬(recordGapCenter + 143748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 143748]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04410_not_prime : ¬(recordGapCenter + 144000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 144000]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04411_not_prime : ¬(recordGapCenter + 144062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 144062]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04412_not_prime : ¬(recordGapCenter + 144182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 144182]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04413_not_prime : ¬(recordGapCenter + 144218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 144218]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04414_not_prime : ¬(recordGapCenter + 144446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 144446]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04415_not_prime : ¬(recordGapCenter + 144506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 144506]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04416_not_prime : ¬(recordGapCenter + 144842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 144842]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04417_not_prime : ¬(recordGapCenter + 144986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 144986]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04418_not_prime : ¬(recordGapCenter + 145118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 145118]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04419_not_prime : ¬(recordGapCenter + 145346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 145346]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04420_not_prime : ¬(recordGapCenter + 145358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 145358]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04421_not_prime : ¬(recordGapCenter + 145478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 145478]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04422_not_prime : ¬(recordGapCenter + 145530).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 145530]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04423_not_prime : ¬(recordGapCenter + 145646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 145646]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04424_not_prime : ¬(recordGapCenter + 145800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 145800]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04425_not_prime : ¬(recordGapCenter + 145946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 145946]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04426_not_prime : ¬(recordGapCenter + 146282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 146282]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04427_not_prime : ¬(recordGapCenter + 146738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 146738]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04428_not_prime : ¬(recordGapCenter + 146906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 146906]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04429_not_prime : ¬(recordGapCenter + 146966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 146966]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04430_not_prime : ¬(recordGapCenter + 147386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 147386]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04431_not_prime : ¬(recordGapCenter + 147456).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 147456]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04432_not_prime : ¬(recordGapCenter + 147698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 147698]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04433_not_prime : ¬(recordGapCenter + 147878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 147878]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04434_not_prime : ¬(recordGapCenter + 148142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 148142]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04435_not_prime : ¬(recordGapCenter + 148202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 148202]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04436_not_prime : ¬(recordGapCenter + 148262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 148262]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04437_not_prime : ¬(recordGapCenter + 148286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 148286]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04438_not_prime : ¬(recordGapCenter + 148766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 148766]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04439_not_prime : ¬(recordGapCenter + 149072).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 149072]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04440_not_prime : ¬(recordGapCenter + 149306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 149306]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04441_not_prime : ¬(recordGapCenter + 149426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 149426]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04442_not_prime : ¬(recordGapCenter + 149438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 149438]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04443_not_prime : ¬(recordGapCenter + 149462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 149462]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04444_not_prime : ¬(recordGapCenter + 149642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 149642]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04445_not_prime : ¬(recordGapCenter + 149846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 149846]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04446_not_prime : ¬(recordGapCenter + 150000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 150000]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04447_not_prime : ¬(recordGapCenter + 150158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 150158]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04448_not_prime : ¬(recordGapCenter + 150266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 150266]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04449_not_prime : ¬(recordGapCenter + 150446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 150446]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04450_not_prime : ¬(recordGapCenter + 150578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 150578]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04451_not_prime : ¬(recordGapCenter + 150920).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 150920]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04452_not_prime : ¬(recordGapCenter + 151142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 151142]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04453_not_prime : ¬(recordGapCenter + 151200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 151200]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04454_not_prime : ¬(recordGapCenter + 151250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 151250]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04455_not_prime : ¬(recordGapCenter + 151358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 151358]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04456_not_prime : ¬(recordGapCenter + 151586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 151586]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04457_not_prime : ¬(recordGapCenter + 151706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 151706]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04458_not_prime : ¬(recordGapCenter + 151826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 151826]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04459_not_prime : ¬(recordGapCenter + 152078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 152078]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04460_not_prime : ¬(recordGapCenter + 152162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 152162]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04461_not_prime : ¬(recordGapCenter + 152426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 152426]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04462_not_prime : ¬(recordGapCenter + 152462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 152462]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04463_not_prime : ¬(recordGapCenter + 152486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 152486]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04464_not_prime : ¬(recordGapCenter + 152738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 152738]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04465_not_prime : ¬(recordGapCenter + 153090).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 153090]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04466_not_prime : ¬(recordGapCenter + 153158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 153158]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04467_not_prime : ¬(recordGapCenter + 153602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 153602]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04468_not_prime : ¬(recordGapCenter + 153638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 153638]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04469_not_prime : ¬(recordGapCenter + 153662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 153662]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04470_not_prime : ¬(recordGapCenter + 153746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 153746]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04471_not_prime : ¬(recordGapCenter + 154058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 154058]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04472_not_prime : ¬(recordGapCenter + 154082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 154082]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04473_not_prime : ¬(recordGapCenter + 155138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 155138]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04474_not_prime : ¬(recordGapCenter + 155232).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 155232]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04475_not_prime : ¬(recordGapCenter + 155486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 155486]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04476_not_prime : ¬(recordGapCenter + 155520).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 155520]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04477_not_prime : ¬(recordGapCenter + 155522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 155522]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04478_not_prime : ¬(recordGapCenter + 156062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 156062]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04479_not_prime : ¬(recordGapCenter + 156158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 156158]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04480_not_prime : ¬(recordGapCenter + 156242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 156242]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04481_not_prime : ¬(recordGapCenter + 156326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 156326]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04482_not_prime : ¬(recordGapCenter + 156458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 156458]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04483_not_prime : ¬(recordGapCenter + 156816).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 156816]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04484_not_prime : ¬(recordGapCenter + 157382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 157382]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04485_not_prime : ¬(recordGapCenter + 157706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 157706]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04486_not_prime : ¬(recordGapCenter + 157778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 157778]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04487_not_prime : ¬(recordGapCenter + 157958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 157958]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04488_not_prime : ¬(recordGapCenter + 158126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 158126]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04489_not_prime : ¬(recordGapCenter + 158400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 158400]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04490_not_prime : ¬(recordGapCenter + 158466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 158466]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04491_not_prime : ¬(recordGapCenter + 158558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 158558]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04492_not_prime : ¬(recordGapCenter + 158618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 158618]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04493_not_prime : ¬(recordGapCenter + 158786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 158786]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04494_not_prime : ¬(recordGapCenter + 158798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 158798]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04495_not_prime : ¬(recordGapCenter + 159218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 159218]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04496_not_prime : ¬(recordGapCenter + 159266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 159266]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04497_not_prime : ¬(recordGapCenter + 159398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 159398]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04498_not_prime : ¬(recordGapCenter + 159602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 159602]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04499_not_prime : ¬(recordGapCenter + 159626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 159626]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04500_not_prime : ¬(recordGapCenter + 159720).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 159720]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04501_not_prime : ¬(recordGapCenter + 159878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 159878]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04502_not_prime : ¬(recordGapCenter + 160142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 160142]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04503_not_prime : ¬(recordGapCenter + 160346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 160346]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04504_not_prime : ¬(recordGapCenter + 160382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 160382]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04505_not_prime : ¬(recordGapCenter + 160526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 160526]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04506_not_prime : ¬(recordGapCenter + 160682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 160682]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04507_not_prime : ¬(recordGapCenter + 160898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 160898]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04508_not_prime : ¬(recordGapCenter + 161618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 161618]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04509_not_prime : ¬(recordGapCenter + 161822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 161822]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04510_not_prime : ¬(recordGapCenter + 161858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 161858]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04511_not_prime : ¬(recordGapCenter + 161906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 161906]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04512_not_prime : ¬(recordGapCenter + 162362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 162362]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04513_not_prime : ¬(recordGapCenter + 162662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 162662]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04514_not_prime : ¬(recordGapCenter + 162878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 162878]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04515_not_prime : ¬(recordGapCenter + 162926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 162926]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04516_not_prime : ¬(recordGapCenter + 163238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 163238]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04517_not_prime : ¬(recordGapCenter + 163298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 163298]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04518_not_prime : ¬(recordGapCenter + 163350).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 163350]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04519_not_prime : ¬(recordGapCenter + 163406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 163406]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04520_not_prime : ¬(recordGapCenter + 163538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 163538]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04521_not_prime : ¬(recordGapCenter + 163598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 163598]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04522_not_prime : ¬(recordGapCenter + 163706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 163706]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04523_not_prime : ¬(recordGapCenter + 163766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 163766]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04524_not_prime : ¬(recordGapCenter + 163802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 163802]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04525_not_prime : ¬(recordGapCenter + 163838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 163838]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04526_not_prime : ¬(recordGapCenter + 164018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 164018]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04527_not_prime : ¬(recordGapCenter + 164102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 164102]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04528_not_prime : ¬(recordGapCenter + 164258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 164258]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04529_not_prime : ¬(recordGapCenter + 164438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 164438]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04530_not_prime : ¬(recordGapCenter + 164678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 164678]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04531_not_prime : ¬(recordGapCenter + 164966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 164966]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04532_not_prime : ¬(recordGapCenter + 165182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 165182]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04533_not_prime : ¬(recordGapCenter + 165398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 165398]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04534_not_prime : ¬(recordGapCenter + 165518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 165518]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04535_not_prime : ¬(recordGapCenter + 166178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 166178]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04536_not_prime : ¬(recordGapCenter + 166406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 166406]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04537_not_prime : ¬(recordGapCenter + 166698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 166698]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04538_not_prime : ¬(recordGapCenter + 167126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 167126]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04539_not_prime : ¬(recordGapCenter + 167402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 167402]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04540_not_prime : ¬(recordGapCenter + 167546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 167546]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04541_not_prime : ¬(recordGapCenter + 167666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 167666]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04542_not_prime : ¬(recordGapCenter + 168326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 168326]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04543_not_prime : ¬(recordGapCenter + 168422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 168422]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04544_not_prime : ¬(recordGapCenter + 168782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 168782]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04545_not_prime : ¬(recordGapCenter + 168842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 168842]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04546_not_prime : ¬(recordGapCenter + 168926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 168926]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04547_not_prime : ¬(recordGapCenter + 168960).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 168960]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04548_not_prime : ¬(recordGapCenter + 168962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 168962]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04549_not_prime : ¬(recordGapCenter + 169046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 169046]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04550_not_prime : ¬(recordGapCenter + 169382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 169382]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04551_not_prime : ¬(recordGapCenter + 169586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 169586]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04552_not_prime : ¬(recordGapCenter + 169982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 169982]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04553_not_prime : ¬(recordGapCenter + 170042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 170042]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04554_not_prime : ¬(recordGapCenter + 170318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 170318]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04555_not_prime : ¬(recordGapCenter + 170426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 170426]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04556_not_prime : ¬(recordGapCenter + 170726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 170726]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04557_not_prime : ¬(recordGapCenter + 171278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 171278]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04558_not_prime : ¬(recordGapCenter + 171638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 171638]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04559_not_prime : ¬(recordGapCenter + 171686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 171686]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04560_not_prime : ¬(recordGapCenter + 171818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 171818]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04561_not_prime : ¬(recordGapCenter + 171866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 171866]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04562_not_prime : ¬(recordGapCenter + 171998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 171998]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04563_not_prime : ¬(recordGapCenter + 172032).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 172032]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04564_not_prime : ¬(recordGapCenter + 172226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 172226]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04565_not_prime : ¬(recordGapCenter + 172358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 172358]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04566_not_prime : ¬(recordGapCenter + 172532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 172532]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04567_not_prime : ¬(recordGapCenter + 172538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 172538]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04568_not_prime : ¬(recordGapCenter + 172622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 172622]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04569_not_prime : ¬(recordGapCenter + 172646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 172646]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04570_not_prime : ¬(recordGapCenter + 172826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 172826]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04571_not_prime : ¬(recordGapCenter + 173078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 173078]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04572_not_prime : ¬(recordGapCenter + 173198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 173198]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04573_not_prime : ¬(recordGapCenter + 173486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 173486]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04574_not_prime : ¬(recordGapCenter + 173702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 173702]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04575_not_prime : ¬(recordGapCenter + 173738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 173738]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04576_not_prime : ¬(recordGapCenter + 173918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 173918]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04577_not_prime : ¬(recordGapCenter + 173948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 173948]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04578_not_prime : ¬(recordGapCenter + 174206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 174206]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04579_not_prime : ¬(recordGapCenter + 174240).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 174240]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04580_not_prime : ¬(recordGapCenter + 174422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 174422]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04581_not_prime : ¬(recordGapCenter + 174806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 174806]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04582_not_prime : ¬(recordGapCenter + 175046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 175046]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04583_not_prime : ¬(recordGapCenter + 175166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 175166]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04584_not_prime : ¬(recordGapCenter + 175178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 175178]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04585_not_prime : ¬(recordGapCenter + 175298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 175298]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04586_not_prime : ¬(recordGapCenter + 175586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 175586]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04587_not_prime : ¬(recordGapCenter + 175616).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 175616]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04588_not_prime : ¬(recordGapCenter + 175862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 175862]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04589_not_prime : ¬(recordGapCenter + 175892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 175892]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04590_not_prime : ¬(recordGapCenter + 175988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 175988]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04591_not_prime : ¬(recordGapCenter + 176186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 176186]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04592_not_prime : ¬(recordGapCenter + 176642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 176642]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04593_not_prime : ¬(recordGapCenter + 176846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 176846]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04594_not_prime : ¬(recordGapCenter + 177026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 177026]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04595_not_prime : ¬(recordGapCenter + 177116).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 177116]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04596_not_prime : ¬(recordGapCenter + 177482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 177482]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04597_not_prime : ¬(recordGapCenter + 177746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 177746]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04598_not_prime : ¬(recordGapCenter + 178082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 178082]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04599_not_prime : ¬(recordGapCenter + 178202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 178202]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04600_not_prime : ¬(recordGapCenter + 178628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 178628]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04601_not_prime : ¬(recordGapCenter + 178742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 178742]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04602_not_prime : ¬(recordGapCenter + 178796).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 178796]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04603_not_prime : ¬(recordGapCenter + 178826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 178826]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04604_not_prime : ¬(recordGapCenter + 179042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 179042]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04605_not_prime : ¬(recordGapCenter + 179198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 179198]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04606_not_prime : ¬(recordGapCenter + 179306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 179306]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04607_not_prime : ¬(recordGapCenter + 179342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 179342]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm04608_not_prime : ¬(recordGapCenter + 179378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 179378]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

end PrimeFactorUnimodality
