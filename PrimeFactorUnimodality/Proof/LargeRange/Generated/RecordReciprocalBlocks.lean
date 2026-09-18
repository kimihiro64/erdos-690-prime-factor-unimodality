import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group001
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group002
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group003
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group004
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group005
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group006
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group007
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group008
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group009
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group010
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group011
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group012
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group013
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group014
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group015
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group016
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group017
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group018
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group019
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group020
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group021
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group022
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group023
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group024
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group025
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group026
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group027
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group028
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group029
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group030
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group031
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group032
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group033
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group034
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group035
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group036
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group037
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group038
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group039
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group040
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group041
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group042
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group043
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group044
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group045
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group046
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group047
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group048
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group049
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group050
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group051

set_option autoImplicit false

/-! Assembly of all segmented reciprocal wheel-sieve certificates. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalSieveSumBelow_500001_eq :
    roundedReciprocalSieveSumBelow 500001 = 2838580130 := by
  calc
    roundedReciprocalSieveSumBelow 500001 =
        roundedReciprocalSieveSumBelow 0 +
          roundedReciprocalBlockSum 0 500001 :=
      roundedReciprocalSieveSumBelow_add_block (by omega)
    _ = roundedReciprocalBlockSum 0 500001 := by
      simp [roundedReciprocalSieveSumBelow]
    _ = roundedReciprocalBlockSum 0 10000 + roundedReciprocalBlockSum 10000 20000 + roundedReciprocalBlockSum 20000 30000 + roundedReciprocalBlockSum 30000 40000 + roundedReciprocalBlockSum 40000 50000 + roundedReciprocalBlockSum 50000 60000 + roundedReciprocalBlockSum 60000 70000 + roundedReciprocalBlockSum 70000 80000 + roundedReciprocalBlockSum 80000 90000 + roundedReciprocalBlockSum 90000 100000 + roundedReciprocalBlockSum 100000 110000 + roundedReciprocalBlockSum 110000 120000 + roundedReciprocalBlockSum 120000 130000 + roundedReciprocalBlockSum 130000 140000 + roundedReciprocalBlockSum 140000 150000 + roundedReciprocalBlockSum 150000 160000 + roundedReciprocalBlockSum 160000 170000 + roundedReciprocalBlockSum 170000 180000 + roundedReciprocalBlockSum 180000 190000 + roundedReciprocalBlockSum 190000 200000 + roundedReciprocalBlockSum 200000 210000 + roundedReciprocalBlockSum 210000 220000 + roundedReciprocalBlockSum 220000 230000 + roundedReciprocalBlockSum 230000 240000 + roundedReciprocalBlockSum 240000 250000 + roundedReciprocalBlockSum 250000 260000 + roundedReciprocalBlockSum 260000 270000 + roundedReciprocalBlockSum 270000 280000 + roundedReciprocalBlockSum 280000 290000 + roundedReciprocalBlockSum 290000 300000 + roundedReciprocalBlockSum 300000 310000 + roundedReciprocalBlockSum 310000 320000 + roundedReciprocalBlockSum 320000 330000 + roundedReciprocalBlockSum 330000 340000 + roundedReciprocalBlockSum 340000 350000 + roundedReciprocalBlockSum 350000 360000 + roundedReciprocalBlockSum 360000 370000 + roundedReciprocalBlockSum 370000 380000 + roundedReciprocalBlockSum 380000 390000 + roundedReciprocalBlockSum 390000 400000 + roundedReciprocalBlockSum 400000 410000 + roundedReciprocalBlockSum 410000 420000 + roundedReciprocalBlockSum 420000 430000 + roundedReciprocalBlockSum 430000 440000 + roundedReciprocalBlockSum 440000 450000 + roundedReciprocalBlockSum 450000 460000 + roundedReciprocalBlockSum 460000 470000 + roundedReciprocalBlockSum 470000 480000 + roundedReciprocalBlockSum 480000 490000 + roundedReciprocalBlockSum 490000 500000 + roundedReciprocalBlockSum 500000 500001 := by
      rw [roundedReciprocalBlockSum_add_block (show 0 ≤ 500000 by omega) (show 500000 ≤ 500001 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 490000 by omega) (show 490000 ≤ 500000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 480000 by omega) (show 480000 ≤ 490000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 470000 by omega) (show 470000 ≤ 480000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 460000 by omega) (show 460000 ≤ 470000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 450000 by omega) (show 450000 ≤ 460000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 440000 by omega) (show 440000 ≤ 450000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 430000 by omega) (show 430000 ≤ 440000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 420000 by omega) (show 420000 ≤ 430000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 410000 by omega) (show 410000 ≤ 420000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 400000 by omega) (show 400000 ≤ 410000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 390000 by omega) (show 390000 ≤ 400000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 380000 by omega) (show 380000 ≤ 390000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 370000 by omega) (show 370000 ≤ 380000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 360000 by omega) (show 360000 ≤ 370000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 350000 by omega) (show 350000 ≤ 360000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 340000 by omega) (show 340000 ≤ 350000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 330000 by omega) (show 330000 ≤ 340000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 320000 by omega) (show 320000 ≤ 330000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 310000 by omega) (show 310000 ≤ 320000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 300000 by omega) (show 300000 ≤ 310000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 290000 by omega) (show 290000 ≤ 300000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 280000 by omega) (show 280000 ≤ 290000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 270000 by omega) (show 270000 ≤ 280000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 260000 by omega) (show 260000 ≤ 270000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 250000 by omega) (show 250000 ≤ 260000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 240000 by omega) (show 240000 ≤ 250000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 230000 by omega) (show 230000 ≤ 240000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 220000 by omega) (show 220000 ≤ 230000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 210000 by omega) (show 210000 ≤ 220000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 200000 by omega) (show 200000 ≤ 210000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 190000 by omega) (show 190000 ≤ 200000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 180000 by omega) (show 180000 ≤ 190000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 170000 by omega) (show 170000 ≤ 180000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 160000 by omega) (show 160000 ≤ 170000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 150000 by omega) (show 150000 ≤ 160000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 140000 by omega) (show 140000 ≤ 150000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 130000 by omega) (show 130000 ≤ 140000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 120000 by omega) (show 120000 ≤ 130000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 110000 by omega) (show 110000 ≤ 120000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 100000 by omega) (show 100000 ≤ 110000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 90000 by omega) (show 90000 ≤ 100000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 80000 by omega) (show 80000 ≤ 90000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 70000 by omega) (show 70000 ≤ 80000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 60000 by omega) (show 60000 ≤ 70000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 50000 by omega) (show 50000 ≤ 60000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 40000 by omega) (show 40000 ≤ 50000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 30000 by omega) (show 30000 ≤ 40000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 20000 by omega) (show 20000 ≤ 30000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 10000 by omega) (show 10000 ≤ 20000 by omega)]
    _ = 2483060565 + 71874803 + 39971206 + 27589049 + 20757282 + 16841493 + 13541006 + 12054669 + 10321309 + 9265613 + 8205464 + 7376979 + 6869707 + 6306408 + 5780870 + 5391505 + 4936183 + 4828892 + 4475075 + 4175051 + 4014029 + 3772281 + 3639683 + 3337046 + 3359885 + 3122091 + 3052837 + 2899569 + 2819004 + 2679041 + 2696232 + 2641414 + 2548421 + 2424922 + 2406511 + 2316436 + 2219825 + 2197580 + 2127596 + 2129931 + 1990152 + 2012337 + 1943915 + 1945710 + 1861399 + 1787626 + 1798167 + 1794245 + 1703450 + 1715666 + 0 := by
      rw [roundedReciprocalGroup_001, roundedReciprocalGroup_002, roundedReciprocalGroup_003, roundedReciprocalGroup_004, roundedReciprocalGroup_005, roundedReciprocalGroup_006, roundedReciprocalGroup_007, roundedReciprocalGroup_008, roundedReciprocalGroup_009, roundedReciprocalGroup_010, roundedReciprocalGroup_011, roundedReciprocalGroup_012, roundedReciprocalGroup_013, roundedReciprocalGroup_014, roundedReciprocalGroup_015, roundedReciprocalGroup_016, roundedReciprocalGroup_017, roundedReciprocalGroup_018, roundedReciprocalGroup_019, roundedReciprocalGroup_020, roundedReciprocalGroup_021, roundedReciprocalGroup_022, roundedReciprocalGroup_023, roundedReciprocalGroup_024, roundedReciprocalGroup_025, roundedReciprocalGroup_026, roundedReciprocalGroup_027, roundedReciprocalGroup_028, roundedReciprocalGroup_029, roundedReciprocalGroup_030, roundedReciprocalGroup_031, roundedReciprocalGroup_032, roundedReciprocalGroup_033, roundedReciprocalGroup_034, roundedReciprocalGroup_035, roundedReciprocalGroup_036, roundedReciprocalGroup_037, roundedReciprocalGroup_038, roundedReciprocalGroup_039, roundedReciprocalGroup_040, roundedReciprocalGroup_041, roundedReciprocalGroup_042, roundedReciprocalGroup_043, roundedReciprocalGroup_044, roundedReciprocalGroup_045, roundedReciprocalGroup_046, roundedReciprocalGroup_047, roundedReciprocalGroup_048, roundedReciprocalGroup_049, roundedReciprocalGroup_050, roundedReciprocalGroup_051]
    _ = 2838580130 := by norm_num

end PrimeFactorUnimodality
