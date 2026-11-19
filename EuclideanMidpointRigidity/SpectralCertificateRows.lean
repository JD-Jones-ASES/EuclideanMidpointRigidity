module

public import EuclideanMidpointRigidity.MixedCertificate

/-! # Coefficients for the norm direction used by the interval certificates

Six intervals use the same norm test at `(1, -3/23)`. Its row is independent
of its weight. We check its two numerators and then each component of the row.
-/

@[expose] public section
namespace EuclideanMidpointRigidity.Spectral.CertificateRows
open IntervalPolynomial

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem row_eq (u v : Row) (ha : u.a = v.a) (hb : u.b = v.b) (hc : u.c = v.c)
    (hi : u.internal = v.internal) (hr : u.rhs = v.rhs) : u = v := by
  cases u
  cases v
  simp_all

private def uCoeffs : List ℚ := [mkRat (-9228887) 828, mkRat 215169959 1656, mkRat (-806167819) 1656, mkRat 27421199 36, mkRat (-67016990) 207, mkRat (-128432225) 207, mkRat 72879250 69, mkRat (-37175000) 69]

private def vCoeffs : List ℚ := [mkRat 388805759 9522, mkRat (-1076353672) 4761, mkRat 758674477 4761, mkRat 349773107 414, mkRat (-6808341590) 4761, mkRat 1371642425 4761, mkRat 936603250 1587, mkRat (-424075000) 1587]

def normRow : Row :=
  ⟨[mkRat 45056175931888801 375119424, mkRat (-1050477216587579857) 375119424, mkRat 496726023967452837 18524416, mkRat (-104078249989958110393) 750238848, mkRat 641422225146631996997 1500477696, mkRat (-32717939285527584443) 41679936, mkRat 257725251139766645501 375119424, mkRat 36028676840149221385 93779856, mkRat (-15177523903192549625) 7814988, mkRat 57469134437371401125 23444964, mkRat (-25380767957116386875) 23444964, mkRat (-1816767878288740625) 1953747, mkRat 3370138807290359375 1953747, mkRat (-716606178409375000) 651249, mkRat 182766937656250000 651249],
   [mkRat (-82529621539485359) 93779856, mkRat 315338956881531239 20839968, mkRat (-18506893092645988999) 187559712, mkRat 3071614813484269609 10419984, mkRat (-49788864287065985749) 187559712, mkRat (-17371060563789993701) 20839968, mkRat 136215991559244509983 46889928, mkRat (-35925311500089720715) 10419984, mkRat 5726507906795567075 23444964, mkRat 10981497111217018625 2604996, mkRat (-57551055832745905625) 11722482, mkRat 1001245815268975000 651249, mkRat 2394885532737156250 1953747, mkRat (-251943892756250000) 217083, mkRat 181297363437500000 651249],
   [mkRat 151169918231566081 93779856, mkRat (-104623126598599262) 5861241, mkRat 484504744363932209 7814988, mkRat (-138550874753284277) 46889928, mkRat (-10730565523364868073) 23444964, mkRat 591473327302384262 651249, mkRat 15954890758424031281 93779856, mkRat (-14808426623840767135) 5861241, mkRat 21463422914568904175 7814988, mkRat 998337887631241625 11722482, mkRat (-46613658313985849375) 23444964, mkRat 2085966106436065625 1953747, mkRat 367079605241984375 1953747, mkRat (-198595011621875000) 651249, mkRat 44959901406250000 651249],
   [mkRat 6928869937211370142569 911918829544838440000, mkRat 19843504200368538561 155943515821572964],
   [mkRat 839523 1157776, mkRat 52371 1447220, mkRat 486 1809025]⟩

private theorem u_checked :
    plus (firstNumerator.map ((1:ℚ)^2*·)) (denominator.map ((2*1*(-3/23:ℚ))*·)) = uCoeffs := by
  decide +kernel

private theorem v_checked :
    plus (secondNumerator.map ((1:ℚ)^2*·)) (denominator.map ((-3/23:ℚ)^2*·)) = vCoeffs := by
  decide +kernel

private theorem norm_checked (q : ℚ) : (⟨1,-3/23,q⟩ : NormTest).row = normRow := by
  simp only [NormTest.row, u_checked, v_checked]
  apply row_eq
  all_goals
    simp only [Row.scale, normRow, uCoeffs, vCoeffs, Rat.mkRat_eq_div, times, plus,
      List.map_cons, List.map_nil, List.cons.injEq, and_true]
    repeat' apply And.intro
    all_goals as_aux_lemma => norm_num

def weightedRows (weights : List ℚ) (bounds : List Row) : Row :=
  (((weights.zip physicalRows).map (fun (w,u) ↦ Row.scale w u)) ++ bounds).foldr Row.add Row.zero

theorem no_test (w : MixedCertificate) (h : w.tests = []) :
    w.combined = weightedRows w.weights [] := by
  simp only [MixedCertificate.combined, weightedRows, h, List.map_nil]

theorem one_test (w : MixedCertificate) (q : ℚ) (h : w.tests = [⟨1,-3/23,q⟩]) :
    w.combined = weightedRows w.weights [normRow.scale q] := by
  simp only [MixedCertificate.combined, weightedRows, h, List.map_cons, List.map_nil, norm_checked]

end EuclideanMidpointRigidity.Spectral.CertificateRows
