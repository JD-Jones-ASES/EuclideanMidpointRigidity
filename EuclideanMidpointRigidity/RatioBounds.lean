module

public import EuclideanMidpointRigidity.SpectralForm

/-! # Signs of the internal coefficient and the right side on a ratio interval -/

@[expose] public section
namespace EuclideanMidpointRigidity.Spectral
open IntervalPolynomial

structure RatioWitness where
  lo : ℚ
  hi : ℚ
  n₀ : ℚ
  n₁ : ℚ
  b₀ : ℚ
  b₁ : ℚ
  b₂ : ℚ

def RatioWitness.linear (q : RatioWitness) (s : ℚ) :=
  q.n₀*(1-s)+q.n₁*s

def RatioWitness.quadratic (q : RatioWitness) (s t : ℚ) :=
  q.b₀*(1-s)*(1-t) + q.b₁*(s*(1-t)+t*(1-s))/2 + q.b₂*s*t

def RatioWitness.verify (q : RatioWitness) (u : Row) : Bool :=
  decide (trim u.internal = trim [q.n₀,q.n₁] ∧ trim u.rhs = trim [q.b₀,q.b₁,q.b₂] ∧
    q.lo < q.hi ∧ 0 < q.linear q.lo ∧ 0 < q.linear q.hi ∧
    q.quadratic q.lo q.lo < 0 ∧ q.quadratic q.lo q.hi < 0 ∧ q.quadratic q.hi q.hi < 0)

private theorem mix_pos {u v a b : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : 0 < u+v)
    (ha : 0 < a) (hb : 0 < b) : 0 < u*a+v*b := by
  have hm := mul_pos huv (lt_min ha hb)
  linarith only [hm, mul_le_mul_of_nonneg_left (min_le_left a b) hu,
    mul_le_mul_of_nonneg_left (min_le_right a b) hv]

private theorem mix_neg {u v a b c : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : 0 < u+v)
    (ha : a < 0) (hb : b < 0) (hc : c < 0) : u^2*a + 2*u*v*b + v^2*c < 0 := by
  let m := max a (max b c)
  have hm : m < 0 := max_lt ha (max_lt hb hc)
  have hmax := mul_neg_of_pos_of_neg (sq_pos_of_pos huv) hm
  have h₁ := mul_le_mul_of_nonneg_left (le_max_left a (max b c)) (sq_nonneg u)
  have h₂ := mul_le_mul_of_nonneg_left ((le_max_left b c).trans (le_max_right a _))
    (show 0 ≤ 2*u*v by positivity)
  have h₃ := mul_le_mul_of_nonneg_left ((le_max_right b c).trans (le_max_right a _)) (sq_nonneg v)
  dsimp [m] at hmax
  linarith only [hmax,h₁,h₂,h₃]

theorem RatioWitness.signs {q : RatioWitness} {row : Row} (hc : q.verify row = true)
    {r : ℝ} (hr : 0 ≤ r) (hl : q.lo*(1+r) ≤ r) (hu : r ≤ q.hi*(1+r)) :
    0 < eval row.internal r ∧ eval row.rhs r < 0 := by
  obtain ⟨hn,hb,hlh,hn₁,hn₂,hb₁,hb₂,hb₃⟩ := of_decide_eq_true hc
  let u := q.hi*(1+r)-r
  let v := r-q.lo*(1+r)
  have h₀ : 0 ≤ u := sub_nonneg.mpr hu
  have h₁ : 0 ≤ v := sub_nonneg.mpr hl
  have hwidth : 0 < (q.hi:ℝ) - q.lo := sub_pos.mpr (by exact_mod_cast hlh)
  have hsum : 0 < u+v := by
    have h := mul_pos hwidth (show 0 < 1+r by linarith)
    dsimp [u,v]
    linarith only [h]
  have hn' := mix_pos h₀ h₁ hsum (by exact_mod_cast hn₁ : (0:ℝ) < q.linear q.lo)
    (by exact_mod_cast hn₂ : (0:ℝ) < q.linear q.hi)
  have hb' := mix_neg h₀ h₁ hsum (by exact_mod_cast hb₁ : (q.quadratic q.lo q.lo:ℝ) < 0)
    (by exact_mod_cast hb₂ : (q.quadratic q.lo q.hi:ℝ) < 0)
    (by exact_mod_cast hb₃ : (q.quadratic q.hi q.hi:ℝ) < 0)
  rw [← eval_trim row.internal, hn, eval_trim, ← eval_trim row.rhs, hb, eval_trim]
  simp only [eval, mul_zero, add_zero]
  dsimp [u,v,linear,quadratic] at hn' hb'
  push_cast at hn' hb'
  constructor
  · apply pos_of_mul_pos_right (a := (q.hi:ℝ)-q.lo) _ hwidth.le
    linarith only [hn']
  · apply neg_of_mul_neg_right (a := ((q.hi:ℝ)-q.lo)^2) _ (sq_nonneg _)
    linarith only [hb']

end EuclideanMidpointRigidity.Spectral
