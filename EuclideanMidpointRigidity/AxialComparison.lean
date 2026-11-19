module

public import EuclideanMidpointRigidity.AxialResponse
public import EuclideanMidpointRigidity.ResponsePolynomials
public import EuclideanMidpointRigidity.ScalarGreenEstimate

/-! # Comparing the actual scalar response with its scaled polynomial -/

public section
noncomputable section
open Set Filter
open scoped Topology
namespace EuclideanMidpointRigidity.Endpoint

theorem scaled_line_mem {h t : ℝ} (hh : 0≤h) (ht : t ∈ Icc (-1:ℝ) 1) : h*t ∈ Icc (-h) h := by
  exact ⟨by simpa using mul_le_mul_of_nonneg_left ht.1 hh,by simpa using mul_le_mul_of_nonneg_left ht.2 hh⟩

theorem scaled_midpoint_mem {h : ℝ} (hh : 0<h) : Real.log (Real.cosh h)/h ∈ Icc (-1:ℝ) 1 := by
  have hb := chordParameter_bounds hh.le (show (1/2:ℝ) ∈ Icc 0 1 by norm_num)
  rw [chordParameter_half] at hb
  exact ⟨(le_div_iff₀ hh).mpr (by simpa using hb.1),(div_le_iff₀ hh).mpr (by simpa using hb.2)⟩

theorem dirichlet_polynomial_comparison {f : ℝ → ℝ} {a b c d : ℝ} (hf : HasFourCoefficients f a b c d) (η : ℝ) :
    ∃ M : ℝ, 0≤M ∧ ∀ᶠ h in 𝓝[>] (0:ℝ), VanishingResponse η h f →
      |(responsePolynomial η a b c d h).eval (Real.log (Real.cosh h)/h)|≤M*h^7 := by
  obtain ⟨ρ,K,hρ,hK,hf⟩ := hf
  obtain ⟨L,hL,hl⟩ := polynomial_interval_bound (v₄ η a b c d).derivative
  let M := K+|η| * L
  have hM : 0≤M := by dsimp [M]; positivity
  refine ⟨8*M,by positivity,?_⟩
  have near : ∀ᶠ h in 𝓝 (0:ℝ), |h*η|<1/4 :=
    (continuous_id.mul continuous_const).abs.continuousAt (Iio_mem_nhds (by norm_num : |0*η|<(1:ℝ)/4))
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hρ),mem_nhdsWithin_of_mem_nhds near] with h hpos hsmall hη
  intro ⟨X,V,hsol,hmid⟩
  have hh : 0<h := hpos
  let p := responsePolynomial η a b c d h
  let y := fun t ↦ X (h*t)-p.eval t
  let v := fun t ↦ h*V (h*t)-p.derivative.eval t
  let g := fun t ↦ h^2*(f (h*t)-sourceTaylor a b c d (h*t))+h^7*η*(v₄ η a b c d).derivative.eval t
  have dh (t : ℝ) : HasDerivAt (fun s ↦ h*s) h t := by simpa using (hasDerivAt_id t).const_mul h
  have dy (t : ℝ) (ht : t ∈ Icc (-1:ℝ) 1) : HasDerivAt y (v t) t := by
    have H := ((hsol.position _ (scaled_line_mem hh.le ht)).comp t (dh t)).fun_sub (p.hasDerivAt t)
    convert H using 1 <;> first | rfl | dsimp [v]; ring
  have dv (t : ℝ) (ht : t ∈ Icc (-1:ℝ) 1) : HasDerivAt v (h*η*v t+g t) t := by
    have H := (((hsol.velocity _ (scaled_line_mem hh.le ht)).comp t (dh t)).const_mul h).fun_sub (p.derivative.hasDerivAt t)
    change HasDerivAt v (h*((η*V (h*t)+f (h*t))*h)-p.derivative.derivative.eval t) t at H
    convert H using 1
    change _=h*((η*V (h*t)+f (h*t))*h)-p.derivative.derivative.eval t
    have he := responsePolynomial_equation η a b c d h t
    change p.derivative.derivative.eval t=_ at he
    rw [he]
    dsimp only [v,g,p]
    ring
  have hg (t : ℝ) (ht : t ∈ Icc (-1:ℝ) 1) : |g t|≤M*h^7 := by
    have ht' := scaled_line_mem hh.le ht
    have hab : |h*t|≤h := abs_le.mpr ht'
    have hsource := (hf _ (hab.trans_lt hsmall)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hab 5) hK)
    apply (abs_add_le _ _).trans
    simp only [abs_mul,abs_of_nonneg (pow_nonneg hh.le 2),abs_of_nonneg (pow_nonneg hh.le 7)]
    calc
      _ ≤ h^2*(K*h^5)+(h^7*|η|)*L := add_le_add (mul_le_mul_of_nonneg_left hsource (sq_nonneg _))
        (mul_le_mul_of_nonneg_left (hl t ht) (by positivity))
      _ = _ := by dsimp [M]; ring
  have hlft : y (-1)=0 := by simp only [y,p,mul_neg_one,hsol.left,responsePolynomial_endpoint _ _ _ _ _ _ _ (Or.inl rfl),sub_self]
  have hrgt : y 1=0 := by simp only [y,p,mul_one,hsol.right,responsePolynomial_endpoint _ _ _ _ _ _ _ (Or.inr rfl),sub_self]
  let z := Real.log (Real.cosh h)/h
  have hz : h*z=Real.log (Real.cosh h) := by dsimp [z]; field_simp
  have H := scalar_dirichlet_small_drift hη.le dy dv hg hlft hrgt z (scaled_midpoint_mem hh)
  change |X (h*z)-p.eval z|≤_ at H
  rw [hz,hmid,zero_sub,abs_neg] at H
  simpa only [mul_assoc] using H

end EuclideanMidpointRigidity.Endpoint

