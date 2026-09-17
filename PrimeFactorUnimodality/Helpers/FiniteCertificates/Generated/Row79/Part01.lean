import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Definitions.SelectionRow
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes

/-! Generated segment 1 of the bounded selection row for endpoint 79. -/

set_option autoImplicit false

namespace PrimeFactorUnimodality

set_option linter.style.longLine false in
theorem numericalRow79_2 :
    selectionRowBounded 6 primePrefix2 =
      [1, 0, 0, 0, 0, 0, 0] := by
  rfl

set_option linter.style.longLine false in
theorem numericalRow79_3 :
    selectionRowBounded 6 primePrefix3 =
      [1, 1, 0, 0, 0, 0, 0] := by
  rw [primePrefix3, selectionRowBounded, numericalRow79_2]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow79_5 :
    selectionRowBounded 6 primePrefix5 =
      [2, 3, 1, 0, 0, 0, 0] := by
  rw [primePrefix5, selectionRowBounded, numericalRow79_3]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow79_7 :
    selectionRowBounded 6 primePrefix7 =
      [8, 14, 7, 1, 0, 0, 0] := by
  rw [primePrefix7, selectionRowBounded, numericalRow79_5]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow79_11 :
    selectionRowBounded 6 primePrefix11 =
      [48, 92, 56, 13, 1, 0, 0] := by
  rw [primePrefix11, selectionRowBounded, numericalRow79_7]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow79_13 :
    selectionRowBounded 6 primePrefix13 =
      [480, 968, 652, 186, 23, 1, 0] := by
  rw [primePrefix13, selectionRowBounded, numericalRow79_11]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow79_17 :
    selectionRowBounded 6 primePrefix17 =
      [5760, 12096, 8792, 2884, 462, 35, 1] := by
  rw [primePrefix17, selectionRowBounded, numericalRow79_13]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow79_19 :
    selectionRowBounded 6 primePrefix19 =
      [92160, 199296, 152768, 54936, 10276, 1022, 51] := by
  rw [primePrefix19, selectionRowBounded, numericalRow79_17]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow79_23 :
    selectionRowBounded 6 primePrefix23 =
      [1658880, 3679488, 2949120, 1141616, 239904, 28672, 1940] := by
  rw [primePrefix23, selectionRowBounded, numericalRow79_19]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow79_29 :
    selectionRowBounded 6 primePrefix29 =
      [36495360, 82607616, 68560128, 28064672, 6419504, 870688, 71352] := by
  rw [primePrefix29, selectionRowBounded, numericalRow79_23]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow79_31 :
    selectionRowBounded 6 primePrefix31 =
      [1021870080, 2349508608, 2002291200, 854370944, 207810784, 30798768, 2868544] := by
  rw [primePrefix31, selectionRowBounded, numericalRow79_29]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow79_37 :
    selectionRowBounded 6 primePrefix37 =
      [30656102400, 71507128320, 62418244608, 27633419520, 7088694464, 1131773824, 116855088] := by
  rw [primePrefix37, selectionRowBounded, numericalRow79_31]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow79_41 :
    selectionRowBounded 6 primePrefix41 =
      [1103619686400, 2604912721920, 2318563934208, 1057221347328, 282826420224, 47832552128, 5338556992] := by
  rw [primePrefix41, selectionRowBounded, numericalRow79_37]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow79_43 :
    selectionRowBounded 6 primePrefix43 =
      [44144787456000, 105300128563200, 95347470090240, 44607417827328, 12370278156288, 2196128505344, 261374831808] := by
  rw [primePrefix43, selectionRowBounded, numericalRow79_41]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow79_47 :
    selectionRowBounded 6 primePrefix47 =
      [1854081073152000, 4466750187110400, 4109893872353280, 1968859018838016, 564159100391424, 104607675380736, 13173871441280] := by
  rw [primePrefix47, selectionRowBounded, numericalRow79_43]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow79_53 :
    selectionRowBounded 6 primePrefix53 =
      [85287729364992000, 207324589680230400, 193521868315361280, 94677408738902016, 27920177636843520, 5376112167905280, 710605761679616] := by
  rw [primePrefix53, selectionRowBounded, numericalRow79_47]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow79_59 :
    selectionRowBounded 6 primePrefix59 =
      [4434961926979584000, 10866166392736972800, 10270461742079016960, 5116747122738266112, 1546526645854765056, 307478010367918080, 42327611775245312] := by
  rw [primePrefix59, selectionRowBounded, numericalRow79_53]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow79_61 :
    selectionRowBounded 6 primePrefix61 =
      [257227791764815872000, 634672612705724006400, 606552947433319956480, 307041794860898451456, 94815292582314639360, 19380251247194013696, 2762479493332146176] := by
  rw [primePrefix61, selectionRowBounded, numericalRow79_59]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow79_67 :
    selectionRowBounded 6 primePrefix67 =
      [15433667505888952320000, 38337584554108256256000, 37027849458704921395200, 19029060639087227043840, 5995959349799776813056, 1257630367413955461120, 185129020847122784256] := by
  rw [primePrefix67, selectionRowBounded, numericalRow79_61]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow79_71 :
    selectionRowBounded 6 primePrefix71 =
      [1018622055388670853120000, 2545714248077033865216000, 2482175648828633068339200, 1292945851638461906288640, 414762377725872496705536, 88999563599120837246976, 13476145743324059222016] := by
  rw [primePrefix71, selectionRowBounded, numericalRow79_67]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow79_73 :
    selectionRowBounded 6 primePrefix73 =
      [71303543877206959718400000, 179218619420781041418240000, 176298009666081348648960000, 92988385263520966508544000, 30326312292449536675676160, 6644731829664331103993856, 1032329765631804982788096] := by
  rw [primePrefix73, selectionRowBounded, numericalRow79_71]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow79_79 :
    selectionRowBounded 6 primePrefix79 =
      [5133855159158901099724800000, 12975044142173441941831680000, 12872675315378638144143360000, 6871461748639590937264128000, 2276482870319887607157227520, 508747004028281376163233792, 80972474955154289864736768] := by
  rw [primePrefix79, selectionRowBounded, numericalRow79_73]
  norm_num [selectionRowStep, selectionRowTail]

end PrimeFactorUnimodality
