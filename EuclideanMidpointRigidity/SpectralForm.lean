module

public import EuclideanMidpointRigidity.IntervalPolynomial

/-! # The spectral and ratio inequalities used in the maximum calculation -/

@[expose] public section
namespace EuclideanMidpointRigidity.Spectral
open IntervalPolynomial

/-- Each external eigendirection contributes `A L² + B L H + C H²`.
The internal coefficient and the right side are polynomials in the squared
gradient ratio. -/
structure Row where
  a : List ℚ
  b : List ℚ
  c : List ℚ
  internal : List ℚ
  rhs : List ℚ

def Row.zero : Row := ⟨[],[],[],[],[]⟩

def Row.add (u v : Row) : Row :=
  ⟨plus u.a v.a, plus u.b v.b, plus u.c v.c,
    plus u.internal v.internal, plus u.rhs v.rhs⟩

def Row.scale (w : ℚ) (u : Row) : Row :=
  ⟨u.a.map (w*·), u.b.map (w*·), u.c.map (w*·), u.internal.map (w*·), u.rhs.map (w*·)⟩

def Row.determinant (u : Row) : List ℚ :=
  plus ((times u.a u.c).map (4*·)) ((times u.b u.b).map ((-1)*·))

def Row.atChannel (u : Row) (x L H : ℝ) : ℝ :=
  eval u.a x * L^2 + eval u.b x * L*H + eval u.c x * H^2

theorem Row.channel_nonnegative {u : Row} {wa wc wd : SignWitness}
    (hA : wa.verify u.a = true) (hC : wc.verify u.c = true)
    (hD : wd.verify u.determinant = true) {x : ℝ} (hl : -1 ≤ x) (hr : x ≤ 1/2)
    (L H : ℝ) : 0 ≤ u.atChannel x L H := by
  have ha := wa.sound hA hl hr
  have hc := wc.sound hC hl hr
  have hd := wd.sound hD hl hr
  simp only [determinant, eval_plus, eval_scale, eval_times] at hd
  norm_num at hd
  unfold atChannel
  by_cases hz : eval u.a x = 0
  · rw [hz] at hd ⊢
    have hb : eval u.b x = 0 := by nlinarith [sq_nonneg (eval u.b x)]
    rw [hb]
    simpa using mul_nonneg hc (sq_nonneg H)
  · have hpos := lt_of_le_of_ne ha (Ne.symm hz)
    have he :
        4*eval u.a x * (eval u.a x * L^2 + eval u.b x * L*H + eval u.c x * H^2) =
        (2*eval u.a x*L + eval u.b x*H)^2 +
          (4*eval u.a x*eval u.c x - (eval u.b x)^2)*H^2 := by ring
    have hdet : 0 ≤ 4*eval u.a x*eval u.c x - (eval u.b x)^2 := by linarith only [hd]
    exact nonneg_of_mul_nonneg_right
      (he.symm ▸ add_nonneg (sq_nonneg _) (mul_nonneg hdet (sq_nonneg H))) (by positivity)

/-- The internal term is nonnegative and the right side is strictly negative.
Adding any finite number of positive semidefinite spectral terms is impossible. -/
theorem excludes_spectral_sum {ι : Type*} [Fintype ι] {u : Row}
    {x L H : ι → ℝ} {r h σ y : ℝ}
    (hchan : ∀ i, 0 ≤ u.atChannel (x i) (L i) (H i))
    (hin : 0 ≤ eval u.internal r) (hh : 0 ≤ h)
    (hrhs : eval u.rhs r < 0) (hy : y ≤ 0) (hσ : 0 ≤ σ) :
    ¬ (∑ i, u.atChannel (x i) (L i) (H i)) + eval u.internal r * h ≤
      eval u.rhs r + y*σ := by
  have hsum := Finset.sum_nonneg (s := Finset.univ) (fun i _ ↦ hchan i)
  linarith [mul_nonneg hin hh, mul_nonpos_of_nonpos_of_nonneg hy hσ]

end EuclideanMidpointRigidity.Spectral
