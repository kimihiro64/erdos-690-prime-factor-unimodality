import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Definitions.SelectionRow
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes

/-! Generated segment 1 of the bounded selection row for endpoint 97. -/

set_option autoImplicit false

namespace PrimeFactorUnimodality

set_option linter.style.longLine false in
theorem numericalRow97_2 :
    selectionRowBounded 7 primePrefix2 =
      [1, 0, 0, 0, 0, 0, 0, 0] := by
  rfl

set_option linter.style.longLine false in
theorem numericalRow97_3 :
    selectionRowBounded 7 primePrefix3 =
      [1, 1, 0, 0, 0, 0, 0, 0] := by
  rw [primePrefix3, selectionRowBounded, numericalRow97_2]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow97_5 :
    selectionRowBounded 7 primePrefix5 =
      [2, 3, 1, 0, 0, 0, 0, 0] := by
  rw [primePrefix5, selectionRowBounded, numericalRow97_3]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow97_7 :
    selectionRowBounded 7 primePrefix7 =
      [8, 14, 7, 1, 0, 0, 0, 0] := by
  rw [primePrefix7, selectionRowBounded, numericalRow97_5]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow97_11 :
    selectionRowBounded 7 primePrefix11 =
      [48, 92, 56, 13, 1, 0, 0, 0] := by
  rw [primePrefix11, selectionRowBounded, numericalRow97_7]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow97_13 :
    selectionRowBounded 7 primePrefix13 =
      [480, 968, 652, 186, 23, 1, 0, 0] := by
  rw [primePrefix13, selectionRowBounded, numericalRow97_11]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow97_17 :
    selectionRowBounded 7 primePrefix17 =
      [5760, 12096, 8792, 2884, 462, 35, 1, 0] := by
  rw [primePrefix17, selectionRowBounded, numericalRow97_13]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow97_19 :
    selectionRowBounded 7 primePrefix19 =
      [92160, 199296, 152768, 54936, 10276, 1022, 51, 1] := by
  rw [primePrefix19, selectionRowBounded, numericalRow97_17]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow97_23 :
    selectionRowBounded 7 primePrefix23 =
      [1658880, 3679488, 2949120, 1141616, 239904, 28672, 1940, 69] := by
  rw [primePrefix23, selectionRowBounded, numericalRow97_19]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow97_29 :
    selectionRowBounded 7 primePrefix29 =
      [36495360, 82607616, 68560128, 28064672, 6419504, 870688, 71352, 3458] := by
  rw [primePrefix29, selectionRowBounded, numericalRow97_23]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow97_31 :
    selectionRowBounded 7 primePrefix31 =
      [1021870080, 2349508608, 2002291200, 854370944, 207810784, 30798768, 2868544, 168176] := by
  rw [primePrefix31, selectionRowBounded, numericalRow97_29]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow97_37 :
    selectionRowBounded 7 primePrefix37 =
      [30656102400, 71507128320, 62418244608, 27633419520, 7088694464, 1131773824, 116855088, 7913824] := by
  rw [primePrefix37, selectionRowBounded, numericalRow97_31]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow97_41 :
    selectionRowBounded 7 primePrefix41 =
      [1103619686400, 2604912721920, 2318563934208, 1057221347328, 282826420224, 47832552128, 5338556992, 401752752] := by
  rw [primePrefix41, selectionRowBounded, numericalRow97_37]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow97_43 :
    selectionRowBounded 7 primePrefix43 =
      [44144787456000, 105300128563200, 95347470090240, 44607417827328, 12370278156288, 2196128505344, 261374831808, 21408667072] := by
  rw [primePrefix43, selectionRowBounded, numericalRow97_41]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow97_47 :
    selectionRowBounded 7 primePrefix47 =
      [1854081073152000, 4466750187110400, 4109893872353280, 1968859018838016, 564159100391424, 104607675380736, 13173871441280, 1160538848832] := by
  rw [primePrefix47, selectionRowBounded, numericalRow97_43]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow97_53 :
    selectionRowBounded 7 primePrefix53 =
      [85287729364992000, 207324589680230400, 193521868315361280, 94677408738902016, 27920177636843520, 5376112167905280, 710605761679616, 66558658487552] := by
  rw [primePrefix53, selectionRowBounded, numericalRow97_47]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow97_59 :
    selectionRowBounded 7 primePrefix59 =
      [4434961926979584000, 10866166392736972800, 10270461742079016960, 5116747122738266112, 1546526645854765056, 307478010367918080, 42327611775245312, 4171656003032320] := by
  rw [primePrefix59, selectionRowBounded, numericalRow97_53]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow97_61 :
    selectionRowBounded 7 primePrefix61 =
      [257227791764815872000, 634672612705724006400, 606552947433319956480, 307041794860898451456, 94815292582314639360, 19380251247194013696, 2762479493332146176, 284283659951119872] := by
  rw [primePrefix61, selectionRowBounded, numericalRow97_59]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow97_67 :
    selectionRowBounded 7 primePrefix67 =
      [15433667505888952320000, 38337584554108256256000, 37027849458704921395200, 19029060639087227043840, 5995959349799776813056, 1257630367413955461120, 185129020847122784256, 19819499090399338496] := by
  rw [primePrefix67, selectionRowBounded, numericalRow97_61]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow97_71 :
    selectionRowBounded 7 primePrefix71 =
      [1018622055388670853120000, 2545714248077033865216000, 2482175648828633068339200, 1292945851638461906288640, 414762377725872496705536, 88999563599120837246976, 13476145743324059222016, 1493215960813479124992] := by
  rw [primePrefix71, selectionRowBounded, numericalRow97_67]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow97_73 :
    selectionRowBounded 7 primePrefix73 =
      [71303543877206959718400000, 179218619420781041418240000, 176298009666081348648960000, 92988385263520966508544000, 30326312292449536675676160, 6644731829664331103993856, 1032329765631804982788096, 118001263000267597971456] := by
  rw [primePrefix73, selectionRowBounded, numericalRow97_71]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow97_79 :
    selectionRowBounded 7 primePrefix79 =
      [5133855159158901099724800000, 12975044142173441941831680000, 12872675315378638144143360000, 6871461748639590937264128000, 2276482870319887607157227520, 508747004028281376163233792, 80972474955154289864736768, 9528420701651072036732928] := by
  rw [primePrefix79, selectionRowBounded, numericalRow97_73]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow97_83 :
    selectionRowBounded 7 primePrefix83 =
      [400440702414394285778534400000, 1017187298248687372562595840000, 1017043718741707217185013760000, 548846691709266731250745344000, 184437125633590824295527874560, 41958749184525834947889463296, 6824600050530315985612701696, 824189289683937908729905152] := by
  rw [primePrefix83, selectionRowBounded, numericalRow97_79]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow97_89 :
    selectionRowBounded 7 primePrefix89 =
      [32836137597980331433839820800000, 83809799158806758835911393280000, 84414772235068679181733724160000, 46022472438901579179746131968000, 15672690993663714323484031057920, 3625054558764709290022463864832, 601575953328011745768131002368, 74408121804613224501464924160] := by
  rw [primePrefix89, selectionRowBounded, numericalRow97_83]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow97_97 :
    selectionRowBounded 7 primePrefix97 =
      [2889580108622269166177904230400000, 7408098463572975108994042429440000, 7512309755844850526828479119360000, 4134392346858407646999393337344000, 1425219279881308439646340865064960, 334677492164958131845460851163136, 56563738451629742917617992073216, 7149490672133975501897044328448] := by
  rw [primePrefix97, selectionRowBounded, numericalRow97_89]
  norm_num [selectionRowStep, selectionRowTail]

end PrimeFactorUnimodality
