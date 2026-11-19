module

public import EuclideanMidpointRigidity.SpectralTable

/-! # Rational combinations of the nine equations and the cubic norm tests -/

@[expose] public section
namespace EuclideanMidpointRigidity.Spectral
open IntervalPolynomial

structure NormTest where
  x : ℚ
  z : ℚ
  weight : ℚ

/-- Test the norm at `x f₁ + t z f₂`, with `r = t²`. The denominator of the
external channel is included in each numerator. -/
def NormTest.row (t : NormTest) : Row :=
  let x := t.x
  let z := t.z
  let k : ℚ := 219375/86354
  let U := plus (firstNumerator.map (x^2*·)) (denominator.map ((2*x*z)*·))
  let V := plus (secondNumerator.map (x^2*·)) (denominator.map (z^2*·))
  let P := (650/153)*k*x^2-2*k*x*z+z^2
  let J := -k*x^2+2*x*z-(159/1300)*z^2
  Row.scale (1/(x^2+z^2)^2)
    ⟨times U U, (times U V).map (2*·), times V V, [J^2,P^2],
      [3*x^4/4,11*x^2*z^2/5,24*z^4/25]⟩

structure MixedCertificate where
  weights : List ℚ
  tests : List NormTest
  ratio : RatioWitness
  aSign : SignWitness
  cSign : SignWitness
  detSign : SignWitness

def MixedCertificate.combined (w : MixedCertificate) : Row :=
  let physical := (w.weights.zip physicalRows).map (fun (y,u) ↦ u.scale y)
  let bounds := w.tests.map (fun t ↦ t.row.scale t.weight)
  (physical ++ bounds).foldr Row.add Row.zero

def MixedCertificate.validWeights (w : MixedCertificate) : Bool :=
  decide (w.weights.length = 9 ∧ w.weights.getLastD 0 ≤ 0) &&
    w.tests.all fun t ↦ decide (0 < t.weight ∧ 0 < t.x^2+t.z^2)

def MixedCertificate.verify (w : MixedCertificate) : Bool :=
  let u := w.combined
  w.validWeights && w.ratio.verify u && w.aSign.verify u.a &&
    w.cSign.verify u.c && w.detSign.verify u.determinant

theorem MixedCertificate.excludes {w : MixedCertificate} (hw : w.verify = true)
    {ι : Type*} [Fintype ι] {x L H : ι → ℝ} {r h σ : ℝ}
    (hx : ∀ i, -1 ≤ x i ∧ x i ≤ 1/2) (hr : 0 ≤ r) (hh : 0 ≤ h) (hσ : 0 ≤ σ)
    (hlo : w.ratio.lo*(1+r) ≤ r) (hhi : r ≤ w.ratio.hi*(1+r)) :
    ¬ (∑ i, w.combined.atChannel (x i) (L i) (H i)) + eval w.combined.internal r * h ≤
      eval w.combined.rhs r + (w.weights.getLastD 0 : ℝ)*σ := by
  simp only [verify, Bool.and_eq_true] at hw
  obtain ⟨⟨⟨⟨hw,hrat⟩,ha⟩,hc⟩,hd⟩ := hw
  simp only [validWeights, Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨hin,hR⟩ := RatioWitness.signs hrat hr hlo hhi
  exact excludes_spectral_sum (fun i ↦ Row.channel_nonnegative ha hc hd
    (hx i).1 (hx i).2 (L i) (H i)) hin.le hh hR (by exact_mod_cast hw.1.2) hσ

end EuclideanMidpointRigidity.Spectral
