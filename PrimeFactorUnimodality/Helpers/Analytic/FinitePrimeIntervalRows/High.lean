import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.Low

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Upper finite Dusart prime-row prefix -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_23159_89693 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_89693 (p := 23159) (q := 23227) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 23227) (q := 23311) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 23311) (q := 23399) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 23399) (q := 23473) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 23473) (q := 23563) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 23563) (q := 23633) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 23633) (q := 23719) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 23719) (q := 23801) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 23801) (q := 23887) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 23887) (q := 23977) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 23977) (q := 24061) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 24061) (q := 24151) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 24151) (q := 24239) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 24239) (q := 24329) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 24329) (q := 24421) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 24421) (q := 24509) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 24509) (q := 24593) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 24593) (q := 24683) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 24683) (q := 24767) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 24767) (q := 24859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 24859) (q := 24953) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 24953) (q := 25037) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 25037) (q := 25127) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 25127) (q := 25219) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 25219) (q := 25309) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 25309) (q := 25391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 25391) (q := 25471) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 25471) (q := 25561) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 25561) (q := 25657) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 25657) (q := 25747) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 25747) (q := 25841) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 25841) (q := 25939) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 25939) (q := 26029) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 26029) (q := 26119) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 26119) (q := 26209) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 26209) (q := 26309) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 26309) (q := 26407) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 26407) (q := 26501) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 26501) (q := 26597) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 26597) (q := 26699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 26699) (q := 26801) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 26801) (q := 26903) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 26903) (q := 26993) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 26993) (q := 27091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 27091) (q := 27191) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 27191) (q := 27283) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 27283) (q := 27367) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 27367) (q := 27457) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 27457) (q := 27551) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 27551) (q := 27653) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 27653) (q := 27751) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 27751) (q := 27851) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 27851) (q := 27953) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 27953) (q := 28057) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 28057) (q := 28163) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 28163) (q := 28229) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 28229) (q := 28319) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 28319) (q := 28411) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 28411) (q := 28517) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 28517) (q := 28621) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 28621) (q := 28729) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 28729) (q := 28837) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 28837) (q := 28933) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 28933) (q := 29033) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 29033) (q := 29137) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 29137) (q := 29243) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 29243) (q := 29347) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 29347) (q := 29453) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 29453) (q := 29537) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 29537) (q := 29641) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 29641) (q := 29753) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 29753) (q := 29867) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 29867) (q := 29959) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 29959) (q := 30071) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 30071) (q := 30181) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 30181) (q := 30293) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 30293) (q := 30403) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 30403) (q := 30517) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 30517) (q := 30631) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 30631) (q := 30727) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 30727) (q := 30841) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 30841) (q := 30949) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 30949) (q := 31063) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 31063) (q := 31181) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 31181) (q := 31277) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 31277) (q := 31397) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 31397) (q := 31517) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 31517) (q := 31627) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 31627) (q := 31741) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 31741) (q := 31859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 31859) (q := 31981) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 31981) (q := 32099) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 32099) (q := 32213) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 32213) (q := 32327) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 32327) (q := 32443) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 32443) (q := 32563) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 32563) (q := 32687) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 32687) (q := 32803) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 32803) (q := 32917) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 32917) (q := 33037) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 33037) (q := 33161) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 33161) (q := 33287) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 33287) (q := 33413) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 33413) (q := 33533) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 33533) (q := 33647) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 33647) (q := 33773) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 33773) (q := 33893) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 33893) (q := 34019) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 34019) (q := 34147) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 34147) (q := 34273) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 34273) (q := 34403) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 34403) (q := 34519) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 34519) (q := 34651) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 34651) (q := 34781) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 34781) (q := 34913) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 34913) (q := 35027) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 35027) (q := 35159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 35159) (q := 35291) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 35291) (q := 35423) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 35423) (q := 35543) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 35543) (q := 35677) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 35677) (q := 35809) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 35809) (q := 35933) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 35933) (q := 36067) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 36067) (q := 36191) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 36191) (q := 36319) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 36319) (q := 36457) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 36457) (q := 36587) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 36587) (q := 36721) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 36721) (q := 36857) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 36857) (q := 36997) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 36997) (q := 37139) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 37139) (q := 37277) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 37277) (q := 37409) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 37409) (q := 37549) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 37549) (q := 37693) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 37693) (q := 37831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 37831) (q := 37967) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 37967) (q := 38083) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 38083) (q := 38219) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 38219) (q := 38351) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 38351) (q := 38461) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 38461) (q := 38603) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 38603) (q := 38749) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 38749) (q := 38891) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 38891) (q := 39023) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 39023) (q := 39163) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 39163) (q := 39313) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 39313) (q := 39461) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 39461) (q := 39607) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 39607) (q := 39749) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 39749) (q := 39901) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 39901) (q := 40039) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 40039) (q := 40189) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 40189) (q := 40343) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 40343) (q := 40493) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 40493) (q := 40639) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 40639) (q := 40787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 40787) (q := 40939) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 40939) (q := 41081) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 41081) (q := 41233) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 41233) (q := 41389) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 41389) (q := 41543) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 41543) (q := 41687) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 41687) (q := 41843) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 41843) (q := 41999) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 41999) (q := 42157) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 42157) (q := 42307) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 42307) (q := 42467) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 42467) (q := 42611) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 42611) (q := 42773) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 42773) (q := 42937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 42937) (q := 43093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 43093) (q := 43237) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 43237) (q := 43403) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 43403) (q := 43543) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 43543) (q := 43691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 43691) (q := 43853) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 43853) (q := 44021) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 44021) (q := 44189) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 44189) (q := 44357) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 44357) (q := 44519) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 44519) (q := 44687) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 44687) (q := 44851) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 44851) (q := 45013) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 45013) (q := 45181) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 45181) (q := 45343) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 45343) (q := 45503) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 45503) (q := 45677) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 45677) (q := 45841) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 45841) (q := 45989) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 45989) (q := 46153) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 46153) (q := 46327) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 46327) (q := 46499) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 46499) (q := 46663) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 46663) (q := 46831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 46831) (q := 46997) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 46997) (q := 47161) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 47161) (q := 47339) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 47339) (q := 47513) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 47513) (q := 47681) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 47681) (q := 47857) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 47857) (q := 48029) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 48029) (q := 48197) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 48197) (q := 48371) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 48371) (q := 48541) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 48541) (q := 48679) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 48679) (q := 48859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 48859) (q := 49043) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 49043) (q := 49223) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 49223) (q := 49411) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 49411) (q := 49597) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 49597) (q := 49787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 49787) (q := 49957) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 49957) (q := 50147) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 50147) (q := 50333) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 50333) (q := 50513) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 50513) (q := 50707) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 50707) (q := 50893) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 50893) (q := 51071) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 51071) (q := 51263) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 51263) (q := 51449) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 51449) (q := 51637) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 51637) (q := 51829) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 51829) (q := 52027) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 52027) (q := 52223) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 52223) (q := 52391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 52391) (q := 52583) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 52583) (q := 52783) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 52783) (q := 52981) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 52981) (q := 53173) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 53173) (q := 53377) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 53377) (q := 53569) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 53569) (q := 53773) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 53773) (q := 53959) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 53959) (q := 54163) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 54163) (q := 54371) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 54371) (q := 54577) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 54577) (q := 54779) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 54779) (q := 54983) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 54983) (q := 55171) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 55171) (q := 55381) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 55381) (q := 55589) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 55589) (q := 55799) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 55799) (q := 56009) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 56009) (q := 56209) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 56209) (q := 56417) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 56417) (q := 56633) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 56633) (q := 56843) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 56843) (q := 57059) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 57059) (q := 57271) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 57271) (q := 57487) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 57487) (q := 57697) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 57697) (q := 57917) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 57917) (q := 58129) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 58129) (q := 58337) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 58337) (q := 58549) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 58549) (q := 58771) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 58771) (q := 58991) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 58991) (q := 59209) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 59209) (q := 59419) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 59419) (q := 59629) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 59629) (q := 59833) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 59833) (q := 60041) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 60041) (q := 60271) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 60271) (q := 60497) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 60497) (q := 60727) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 60727) (q := 60953) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 60953) (q := 61169) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 61169) (q := 61403) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 61403) (q := 61637) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 61637) (q := 61871) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 61871) (q := 62099) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 62099) (q := 62327) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 62327) (q := 62563) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 62563) (q := 62801) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 62801) (q := 63031) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 63031) (q := 63247) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 63247) (q := 63487) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 63487) (q := 63727) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 63727) (q := 63949) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 63949) (q := 64189) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 64189) (q := 64433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 64433) (q := 64679) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 64679) (q := 64927) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 64927) (q := 65173) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 65173) (q := 65423) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 65423) (q := 65657) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 65657) (q := 65899) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 65899) (q := 66137) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 66137) (q := 66383) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 66383) (q := 66629) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 66629) (q := 66883) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 66883) (q := 67139) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 67139) (q := 67391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 67391) (q := 67631) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 67631) (q := 67883) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 67883) (q := 68141) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 68141) (q := 68399) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 68399) (q := 68659) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 68659) (q := 68917) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 68917) (q := 69163) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 69163) (q := 69427) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 69427) (q := 69691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 69691) (q := 69941) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 69941) (q := 70207) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 70207) (q := 70459) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 70459) (q := 70729) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 70729) (q := 70999) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 70999) (q := 71263) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 71263) (q := 71527) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 71527) (q := 71789) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 71789) (q := 72053) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 72053) (q := 72313) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 72313) (q := 72577) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 72577) (q := 72823) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 72823) (q := 73091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 73091) (q := 73369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 73369) (q := 73643) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 73643) (q := 73907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 73907) (q := 74189) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 74189) (q := 74471) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 74471) (q := 74747) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 74747) (q := 75029) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 75029) (q := 75307) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 75307) (q := 75583) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 75583) (q := 75869) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 75869) (q := 76159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 76159) (q := 76441) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 76441) (q := 76733) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 76733) (q := 77023) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 77023) (q := 77317) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 77317) (q := 77611) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 77611) (q := 77899) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 77899) (q := 78193) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 78193) (q := 78487) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 78487) (q := 78787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 78787) (q := 79087) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 79087) (q := 79379) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 79379) (q := 79669) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 79669) (q := 79973) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 79973) (q := 80279) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 80279) (q := 80567) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 80567) (q := 80863) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 80863) (q := 81173) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 81173) (q := 81463) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 81463) (q := 81773) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 81773) (q := 82073) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 82073) (q := 82387) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 82387) (q := 82699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 82699) (q := 83009) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 83009) (q := 83311) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 83311) (q := 83621) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 83621) (q := 83939) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 83939) (q := 84247) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 84247) (q := 84559) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 84559) (q := 84871) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 84871) (q := 85193) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 85193) (q := 85517) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 85517) (q := 85843) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 85843) (q := 86171) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 86171) (q := 86501) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 86501) (q := 86813) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 86813) (q := 87133) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 87133) (q := 87443) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 87443) (q := 87767) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 87767) (q := 88093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 88093) (q := 88427) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 88427) (q := 88747) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 88747) (q := 89087) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 89087) (q := 89417) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_89693 (p := 89417) (q := 89759) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_23159_89693_chain :
    DusartPrimeRowsChain 23159 89693 dusartPrimeRows_23159_89693 := by
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 23159) (q := 23227) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 23227) (q := 23311) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 23311) (q := 23399) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 23399) (q := 23473) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 23473) (q := 23563) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 23563) (q := 23633) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 23633) (q := 23719) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 23719) (q := 23801) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 23801) (q := 23887) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 23887) (q := 23977) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 23977) (q := 24061) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 24061) (q := 24151) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 24151) (q := 24239) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 24239) (q := 24329) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 24329) (q := 24421) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 24421) (q := 24509) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 24509) (q := 24593) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 24593) (q := 24683) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 24683) (q := 24767) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 24767) (q := 24859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 24859) (q := 24953) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 24953) (q := 25037) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 25037) (q := 25127) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 25127) (q := 25219) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 25219) (q := 25309) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 25309) (q := 25391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 25391) (q := 25471) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 25471) (q := 25561) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 25561) (q := 25657) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 25657) (q := 25747) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 25747) (q := 25841) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 25841) (q := 25939) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 25939) (q := 26029) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 26029) (q := 26119) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 26119) (q := 26209) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 26209) (q := 26309) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 26309) (q := 26407) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 26407) (q := 26501) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 26501) (q := 26597) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 26597) (q := 26699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 26699) (q := 26801) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 26801) (q := 26903) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 26903) (q := 26993) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 26993) (q := 27091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 27091) (q := 27191) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 27191) (q := 27283) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 27283) (q := 27367) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 27367) (q := 27457) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 27457) (q := 27551) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 27551) (q := 27653) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 27653) (q := 27751) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 27751) (q := 27851) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 27851) (q := 27953) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 27953) (q := 28057) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 28057) (q := 28163) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 28163) (q := 28229) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 28229) (q := 28319) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 28319) (q := 28411) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 28411) (q := 28517) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 28517) (q := 28621) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 28621) (q := 28729) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 28729) (q := 28837) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 28837) (q := 28933) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 28933) (q := 29033) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 29033) (q := 29137) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 29137) (q := 29243) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 29243) (q := 29347) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 29347) (q := 29453) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 29453) (q := 29537) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 29537) (q := 29641) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 29641) (q := 29753) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 29753) (q := 29867) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 29867) (q := 29959) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 29959) (q := 30071) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 30071) (q := 30181) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 30181) (q := 30293) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 30293) (q := 30403) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 30403) (q := 30517) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 30517) (q := 30631) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 30631) (q := 30727) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 30727) (q := 30841) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 30841) (q := 30949) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 30949) (q := 31063) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 31063) (q := 31181) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 31181) (q := 31277) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 31277) (q := 31397) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 31397) (q := 31517) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 31517) (q := 31627) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 31627) (q := 31741) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 31741) (q := 31859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 31859) (q := 31981) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 31981) (q := 32099) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 32099) (q := 32213) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 32213) (q := 32327) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 32327) (q := 32443) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 32443) (q := 32563) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 32563) (q := 32687) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 32687) (q := 32803) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 32803) (q := 32917) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 32917) (q := 33037) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 33037) (q := 33161) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 33161) (q := 33287) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 33287) (q := 33413) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 33413) (q := 33533) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 33533) (q := 33647) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 33647) (q := 33773) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 33773) (q := 33893) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 33893) (q := 34019) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 34019) (q := 34147) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 34147) (q := 34273) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 34273) (q := 34403) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 34403) (q := 34519) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 34519) (q := 34651) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 34651) (q := 34781) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 34781) (q := 34913) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 34913) (q := 35027) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 35027) (q := 35159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 35159) (q := 35291) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 35291) (q := 35423) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 35423) (q := 35543) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 35543) (q := 35677) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 35677) (q := 35809) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 35809) (q := 35933) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 35933) (q := 36067) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 36067) (q := 36191) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 36191) (q := 36319) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 36319) (q := 36457) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 36457) (q := 36587) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 36587) (q := 36721) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 36721) (q := 36857) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 36857) (q := 36997) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 36997) (q := 37139) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 37139) (q := 37277) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 37277) (q := 37409) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 37409) (q := 37549) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 37549) (q := 37693) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 37693) (q := 37831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 37831) (q := 37967) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 37967) (q := 38083) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 38083) (q := 38219) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 38219) (q := 38351) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 38351) (q := 38461) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 38461) (q := 38603) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 38603) (q := 38749) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 38749) (q := 38891) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 38891) (q := 39023) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 39023) (q := 39163) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 39163) (q := 39313) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 39313) (q := 39461) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 39461) (q := 39607) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 39607) (q := 39749) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 39749) (q := 39901) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 39901) (q := 40039) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 40039) (q := 40189) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 40189) (q := 40343) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 40343) (q := 40493) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 40493) (q := 40639) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 40639) (q := 40787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 40787) (q := 40939) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 40939) (q := 41081) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 41081) (q := 41233) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 41233) (q := 41389) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 41389) (q := 41543) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 41543) (q := 41687) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 41687) (q := 41843) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 41843) (q := 41999) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 41999) (q := 42157) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 42157) (q := 42307) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 42307) (q := 42467) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 42467) (q := 42611) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 42611) (q := 42773) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 42773) (q := 42937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 42937) (q := 43093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 43093) (q := 43237) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 43237) (q := 43403) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 43403) (q := 43543) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 43543) (q := 43691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 43691) (q := 43853) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 43853) (q := 44021) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 44021) (q := 44189) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 44189) (q := 44357) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 44357) (q := 44519) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 44519) (q := 44687) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 44687) (q := 44851) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 44851) (q := 45013) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 45013) (q := 45181) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 45181) (q := 45343) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 45343) (q := 45503) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 45503) (q := 45677) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 45677) (q := 45841) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 45841) (q := 45989) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 45989) (q := 46153) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 46153) (q := 46327) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 46327) (q := 46499) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 46499) (q := 46663) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 46663) (q := 46831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 46831) (q := 46997) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 46997) (q := 47161) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 47161) (q := 47339) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 47339) (q := 47513) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 47513) (q := 47681) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 47681) (q := 47857) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 47857) (q := 48029) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 48029) (q := 48197) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 48197) (q := 48371) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 48371) (q := 48541) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 48541) (q := 48679) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 48679) (q := 48859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 48859) (q := 49043) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 49043) (q := 49223) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 49223) (q := 49411) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 49411) (q := 49597) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 49597) (q := 49787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 49787) (q := 49957) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 49957) (q := 50147) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 50147) (q := 50333) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 50333) (q := 50513) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 50513) (q := 50707) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 50707) (q := 50893) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 50893) (q := 51071) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 51071) (q := 51263) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 51263) (q := 51449) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 51449) (q := 51637) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 51637) (q := 51829) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 51829) (q := 52027) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 52027) (q := 52223) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 52223) (q := 52391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 52391) (q := 52583) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 52583) (q := 52783) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 52783) (q := 52981) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 52981) (q := 53173) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 53173) (q := 53377) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 53377) (q := 53569) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 53569) (q := 53773) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 53773) (q := 53959) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 53959) (q := 54163) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 54163) (q := 54371) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 54371) (q := 54577) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 54577) (q := 54779) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 54779) (q := 54983) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 54983) (q := 55171) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 55171) (q := 55381) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 55381) (q := 55589) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 55589) (q := 55799) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 55799) (q := 56009) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 56009) (q := 56209) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 56209) (q := 56417) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 56417) (q := 56633) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 56633) (q := 56843) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 56843) (q := 57059) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 57059) (q := 57271) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 57271) (q := 57487) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 57487) (q := 57697) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 57697) (q := 57917) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 57917) (q := 58129) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 58129) (q := 58337) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 58337) (q := 58549) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 58549) (q := 58771) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 58771) (q := 58991) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 58991) (q := 59209) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 59209) (q := 59419) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 59419) (q := 59629) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 59629) (q := 59833) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 59833) (q := 60041) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 60041) (q := 60271) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 60271) (q := 60497) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 60497) (q := 60727) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 60727) (q := 60953) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 60953) (q := 61169) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 61169) (q := 61403) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 61403) (q := 61637) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 61637) (q := 61871) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 61871) (q := 62099) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 62099) (q := 62327) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 62327) (q := 62563) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 62563) (q := 62801) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 62801) (q := 63031) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 63031) (q := 63247) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 63247) (q := 63487) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 63487) (q := 63727) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 63727) (q := 63949) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 63949) (q := 64189) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 64189) (q := 64433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 64433) (q := 64679) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 64679) (q := 64927) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 64927) (q := 65173) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 65173) (q := 65423) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 65423) (q := 65657) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 65657) (q := 65899) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 65899) (q := 66137) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 66137) (q := 66383) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 66383) (q := 66629) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 66629) (q := 66883) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 66883) (q := 67139) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 67139) (q := 67391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 67391) (q := 67631) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 67631) (q := 67883) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 67883) (q := 68141) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 68141) (q := 68399) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 68399) (q := 68659) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 68659) (q := 68917) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 68917) (q := 69163) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 69163) (q := 69427) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 69427) (q := 69691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 69691) (q := 69941) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 69941) (q := 70207) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 70207) (q := 70459) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 70459) (q := 70729) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 70729) (q := 70999) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 70999) (q := 71263) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 71263) (q := 71527) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 71527) (q := 71789) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 71789) (q := 72053) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 72053) (q := 72313) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 72313) (q := 72577) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 72577) (q := 72823) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 72823) (q := 73091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 73091) (q := 73369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 73369) (q := 73643) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 73643) (q := 73907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 73907) (q := 74189) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 74189) (q := 74471) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 74471) (q := 74747) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 74747) (q := 75029) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 75029) (q := 75307) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 75307) (q := 75583) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 75583) (q := 75869) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 75869) (q := 76159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 76159) (q := 76441) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 76441) (q := 76733) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 76733) (q := 77023) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 77023) (q := 77317) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 77317) (q := 77611) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 77611) (q := 77899) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 77899) (q := 78193) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 78193) (q := 78487) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 78487) (q := 78787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 78787) (q := 79087) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 79087) (q := 79379) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 79379) (q := 79669) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 79669) (q := 79973) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 79973) (q := 80279) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 80279) (q := 80567) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 80567) (q := 80863) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 80863) (q := 81173) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 81173) (q := 81463) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 81463) (q := 81773) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 81773) (q := 82073) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 82073) (q := 82387) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 82387) (q := 82699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 82699) (q := 83009) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 83009) (q := 83311) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 83311) (q := 83621) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 83621) (q := 83939) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 83939) (q := 84247) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 84247) (q := 84559) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 84559) (q := 84871) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 84871) (q := 85193) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 85193) (q := 85517) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 85517) (q := 85843) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 85843) (q := 86171) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 86171) (q := 86501) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 86501) (q := 86813) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 86813) (q := 87133) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 87133) (q := 87443) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 87443) (q := 87767) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 87767) (q := 88093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 88093) (q := 88427) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 88427) (q := 88747) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 88747) (q := 89087) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 89087) (q := 89417) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    dusartPrimeRow_of_explicit_89693 (p := 89417) (q := 89759) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_89693 : List DusartPrimeRow :=
  dusartPrimeRows_3275_23158 ++ dusartPrimeRows_23159_89693

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_89693_chain :
    DusartPrimeRowsChain 3275 89693 dusartPrimeRows_3275_89693 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_23158_chain dusartPrimeRows_23159_89693_chain


def DusartPrimeRowsCoverBelow (rows : List DusartPrimeRow) : Prop :=
  ∀ x : Real, 3275 ≤ x → x < 89693 + 1 →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x < (row.right : Real) + 1

def DusartPrimeRowsCoverUpTo
    (rows : List DusartPrimeRow) (X : Real) : Prop :=
  ∀ x : Real, 3275 ≤ x → x < X + 1 →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x < (row.right : Real) + 1

theorem dusartPrimeRowsCoverUpTo_of_chain
    {b : Nat} {X : Real} {rows : List DusartPrimeRow}
    (chain : DusartPrimeRowsChain 3275 b rows)
    (hXbound : X ≤ (b : Real)) :
    DusartPrimeRowsCoverUpTo rows X := by
  intro x hx hX
  exact dusartPrimeRowsCover_of_chain chain x hx (by linarith)

theorem dusartPrimeRowsCoverUpTo_append
    {m X : Real} {left right : List DusartPrimeRow}
    (hleft : DusartPrimeRowsCoverUpTo left m)
    (hright : DusartPrimeRowsCoverUpTo right X) :
    DusartPrimeRowsCoverUpTo (left ++ right) X := by
  intro x hx hX
  by_cases hxm : x < m + 1
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hleft x hx hxm
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hright x hx hX
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩

def DusartPrimeRowsCoverFrom
    (rows : List DusartPrimeRow) (A X : Real) : Prop :=
  ∀ x : Real, A ≤ x → x < X + 1 →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x < (row.right : Real) + 1

theorem dusartPrimeRowsCoverUpTo_append_from
    {m X : Real} {left right : List DusartPrimeRow}
    (hleft : DusartPrimeRowsCoverUpTo left m)
    (hright : DusartPrimeRowsCoverFrom right m X) :
    DusartPrimeRowsCoverUpTo (left ++ right) X := by
  intro x hx hX
  by_cases hxm : x < m + 1
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hleft x hx hxm
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hright x
      (by linarith) hX
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_3802 (3802 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_3802_chain (by norm_num)

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_4672_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_4672 (4672 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_4672_chain (by norm_num)

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_4918_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_4918 (4918 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_4918_chain (by norm_num)

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_5166_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_5166 (5166 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_5166_chain (by norm_num)

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_5436_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_5436 (5436 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_5436_chain (by norm_num)

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_5710_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_5710 (5710 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_5710_chain (by norm_num)

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_6006_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_6006 (6006 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_6006_chain (by norm_num)

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_6310_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_6310 (6310 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_6310_chain (by norm_num)

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_6636_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_6636 (6636 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_6636_chain (by norm_num)

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_6976_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_6976 (6976 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_6976_chain (by norm_num)

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_7332_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_7332 (7332 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_7332_chain (by norm_num)

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_7716_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_7716 (7716 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_7716_chain (by norm_num)

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_8110_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_8110 (8110 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_8110_chain (by norm_num)

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_8520_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_8520 (8520 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_8520_chain (by norm_num)

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_8962_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_8962 (8962 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_8962_chain (by norm_num)

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_9418_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_9418 (9418 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_9418_chain (by norm_num)

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_9900_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_9900 (9900 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_9900_chain (by norm_num)

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_10426_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_10426 (10426 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_10426_chain (by norm_num)

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_10938_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_10938 (10938 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_10938_chain (by norm_num)

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_11502_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_11502 (11502 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_11502_chain (by norm_num)

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_12096_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_12096 (12096 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_12096_chain (by norm_num)

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_12712_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_12712 (12712 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_12712_chain (by norm_num)

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_13366_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_13366 (13366 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_13366_chain (by norm_num)

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_14050_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_14050 (14050 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_14050_chain (by norm_num)

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_14766_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_14766 (14766 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_14766_chain (by norm_num)

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_15526_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_15526 (15526 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_15526_chain (by norm_num)

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_16318_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_16318 (16318 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_16318_chain (by norm_num)

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_23158_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_23158 (23158 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_23158_chain (by norm_num)


set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_22026_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_22026 (22026 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_22026_chain (by norm_num)


set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_20958_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_20958 (20958 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_20958_chain (by norm_num)


set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_19936_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_19936 (19936 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_19936_chain (by norm_num)


set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_18958_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_18958 (18958 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_18958_chain (by norm_num)


set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_18040_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_18040 (18040 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_18040_chain (by norm_num)


set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_17158_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_17158 (17158 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_17158_chain (by norm_num)


theorem dusartPrimeRowsCoverBelow_of_chain
    {rows : List DusartPrimeRow}
    (chain : DusartPrimeRowsChain 3275 89693 rows) :
    DusartPrimeRowsCoverBelow rows := by
  intro x hleft hright
  exact dusartPrimeRowsCover_of_chain chain x hleft (by linarith)

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_89693_cover :
    DusartPrimeRowsCoverBelow dusartPrimeRows_3275_89693 := by
  exact dusartPrimeRowsCoverBelow_of_chain
    dusartPrimeRows_3275_89693_chain

theorem dusartPrimeRow_provides
    (row : DusartPrimeRow) {x : Real}
    (left_mem : (row.left : Real) ≤ x)
    (right_mem : x < (row.right : Real) + 1) :
    ∃ q : Nat, q.Prime ∧ x < q ∧
      (q : Real) ≤ x * (1 + 1 / (2 * (Real.log x) ^ 2)) := by
  refine ⟨row.prime, row.prime_prime, ?_, ?_⟩
  · have right_lt_prime : (row.right : Real) < row.prime := by
      exact_mod_cast row.right_lt_prime
    have hstep : ((row.right + 1 : Nat) : Real) ≤ row.prime := by
      exact_mod_cast Nat.succ_le_of_lt row.right_lt_prime
    exact right_mem.trans_le hstep
  · have hbound : (row.prime : Real) ≤ dusartUpper x :=
      row.prime_upper.trans (dusartUpper_monotoneOn
        (show (row.left : Real) ∈ Set.Ici (3275 : Real) by
          change (3275 : Real) ≤ row.left
          exact_mod_cast row.left_large)
        (show x ∈ Set.Ici (3275 : Real) by
          have hleft : (3275 : Real) ≤ row.left := by
            exact_mod_cast row.left_large
          norm_num at ⊢
          linarith [hleft, left_mem]) left_mem)
    have hrewrite : dusartUpper x =
        x * (1 + 1 / (2 * (Real.log x) ^ 2)) := by
      dsimp [dusartUpper]
      field_simp
    exact hrewrite ▸ hbound

theorem hasDusartShortIntervalPrimeBelow_of_rows
    {rows : List DusartPrimeRow}
    (cover : DusartPrimeRowsCoverBelow rows) :
    HasDusartShortIntervalPrimeBelow (89693 : Real) := by
  intro x hx hX
  obtain ⟨row, row_mem, left_mem, right_mem⟩ := cover x hx (by linarith)
  exact dusartPrimeRow_provides row left_mem right_mem

theorem hasDusartShortIntervalPrimeBelow_of_rows_up_to
    {X : Real} {rows : List DusartPrimeRow}
    (cover : DusartPrimeRowsCoverUpTo rows X) :
    HasDusartShortIntervalPrimeBelow X := by
  intro x hx hX
  obtain ⟨row, row_mem, left_mem, right_mem⟩ := cover x hx (by linarith)
  exact dusartPrimeRow_provides row left_mem right_mem

theorem hasDusartShortIntervalPrimeBelow_3275_89693 :
    HasDusartShortIntervalPrimeBelow (89693 : Real) :=
  hasDusartShortIntervalPrimeBelow_of_rows
    dusartPrimeRows_3275_89693_cover

theorem hasDusartShortIntervalPrimeBelow_3275_23158 :
    HasDusartShortIntervalPrimeBelow (23158 : Real) :=
  hasDusartShortIntervalPrimeBelow_of_rows_up_to
    dusartPrimeRows_3275_23158_cover
