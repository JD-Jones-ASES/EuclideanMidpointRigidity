module

public import EuclideanMidpointRigidity.MixedCertificate
public import EuclideanMidpointRigidity.ChannelOverlap
public import EuclideanMidpointRigidity.MixedEigenbasis

/-! # Normalized norm tests on the actual gradient plane -/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity.Spectral.NormTest
open IntervalPolynomial MixedChannel LiftedSection

def divisor (T : NormTest) : ℝ := ((T.x:ℝ)^2+(T.z:ℝ)^2)^2

def raw (T : NormTest) (v : MixedChannel) : ℝ :=
  ((T.x:ℝ)^2*v.q+2*(T.x:ℝ)*T.z*v.l+(T.z:ℝ)^2*v.h)^2/T.divisor

theorem regular_evaluation (T : NormTest) (s L H : ℝ) :
    T.row.atChannel s L H=
      ((T.x:ℝ)^2*(eval firstNumerator s*L+eval secondNumerator s*H)+
        (2*(T.x:ℝ)*T.z*L+(T.z:ℝ)^2*H)*eval denominator s)^2/T.divisor := by
  simp only [row,Row.atChannel,Row.scale,eval_scale,eval_times,eval_plus,divisor]
  push_cast
  ring

theorem raw_eq (T : NormTest) {v : MixedChannel} {s : ℝ} (hv : v.Equations s) (hd : regularDenominator s≠0) :
    T.raw v=T.row.atChannel s (v.l/regularDenominator s) (v.h/regularDenominator s) := by
  have h := cubic_transport hv
  rw [denominator_eq] at h
  rw [T.regular_evaluation,denominator_eq]
  unfold raw
  congr 2
  linear_combination (norm := (field_simp [hd]; ring)) ((T.x:ℝ)^2/(regularDenominator s))*h

theorem scalar_evaluations (T : NormTest) (r : ℝ) :
    let a : ℝ := T.x
    let b : ℝ := T.z
    let k := ResonantPlane.k
    let P := (650/153)*k*a^2-2*k*a*b+b^2
    let J := -k*a^2+2*a*b-(159/1300)*b^2
    eval T.row.internal r=(r*P^2+J^2)/T.divisor ∧
    eval T.row.rhs r=((3/4)*a^4+(11/5)*r*a^2*b^2+(24/25)*r^2*b^4)/T.divisor := by
  simp only [row,Row.scale,eval_scale,eval,divisor,ResonantPlane.k]
  push_cast
  constructor <;> ring

theorem geometric_bound {d : ℕ} {S : LiftedSection d} {p : Space d} (hm : S.IsMixed p)
    (hmax : ∀ z : Space d, ‖z‖=1 → inner ℝ (K (S.field p) z z) z≤S.a p)
    {ι : Type*} [Fintype ι] (B : SpectralFrame S p ι) (T : NormTest) (hT : 0<T.x^2+T.z^2) :
    let r := (S.ratio p)^2
    let n := inner ℝ (S.x p) (K (S.cubic p) (S.y p) (S.y p))
    (∑ j, T.raw (S.channel p (B.w j)))+eval T.row.internal r*(r*n^2)≤eval T.row.rhs r := by
  have hd₀ : 0<(T.x:ℝ)^2+(T.z:ℝ)^2 := by exact_mod_cast hT
  have hd : 0<T.divisor := sq_pos_of_pos hd₀
  have h := B.norm_inequality hm hmax (T.x:ℝ) (T.z:ℝ)
  dsimp only at h ⊢
  have hi := (div_le_div_iff_of_pos_right hd).mpr h
  rw [(T.scalar_evaluations _).1,(T.scalar_evaluations _).2]
  unfold raw
  simp only [add_div,Finset.sum_div] at hi
  linear_combination hi

end EuclideanMidpointRigidity.Spectral.NormTest

