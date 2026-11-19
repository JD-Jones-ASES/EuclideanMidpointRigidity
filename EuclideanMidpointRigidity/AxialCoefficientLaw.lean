module

public import EuclideanMidpointRigidity.AxialComparison
public import EuclideanMidpointRigidity.UniformPolynomial

/-! # Fourth and sixth identities for genuine scalar midpoint responses -/

public section
noncomputable section
open Set Filter
open scoped Topology
namespace EuclideanMidpointRigidity.Endpoint

private theorem midpoint_evaluation_error (η a b c d : ℝ) :
    ∃ M : ℝ, 0≤M ∧ ∀ᶠ h in 𝓝[>] (0:ℝ),
      let p := responsePolynomial η a b c d h
      |p.eval (h/2-h^3/12)-p.eval (Real.log (Real.cosh h)/h)|≤M*h^7 := by
  obtain ⟨ρ,K,hρ,hK,hlog⟩ := log_cosh_coefficients
  obtain ⟨L,hL,hder⟩ := responsePolynomial_slope_bound η a b c d
  refine ⟨L*K,by positivity,?_⟩
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hρ),
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1))] with h hpos hsmall hsmall₁
  have hh : 0<h := hpos
  have h₁ : h≤1 := hsmall₁.le
  let z := Real.log (Real.cosh h)/h
  let t := h/2-h^3/12
  let p := responsePolynomial η a b c d h
  have hz : z ∈ Icc (-1:ℝ) 1 := scaled_midpoint_mem hh
  have ht : t ∈ Icc (-1:ℝ) 1 := by
    have hb : h^3≤1 := pow_le_one₀ hh.le h₁
    dsimp only [t]; constructor <;> nlinarith only [hh,h₁,hb,pow_nonneg hh.le 3]
  have hlog' := hlog h (by rwa [abs_of_pos hh])
  rw [abs_of_pos hh] at hlog'
  have he : Real.log (Real.cosh h)-sourceTaylor 0 (1/2) 0 (-1/12) h=h*(z-t) := by
    dsimp [z,t,sourceTaylor]; field_simp; ring
  rw [he,abs_mul,abs_of_pos hh] at hlog'
  have hdist : |t-z|≤K*h^4 := by
    rw [abs_sub_comm]
    apply le_of_mul_le_mul_left (a := h) _ hh
    nlinarith only [hlog']
  have hd := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x (_ : x ∈ Icc (-1:ℝ) 1) ↦ (p.hasDerivAt x).hasDerivWithinAt)
    (fun x hx ↦ (show ‖p.derivative.eval x‖≤L*h^3 from hder h ⟨hh.le,h₁⟩ x hx))
    (convex_Icc (-1:ℝ) 1) hz ht
  change |p.eval t-p.eval z|≤_
  rw [Real.norm_eq_abs,Real.norm_eq_abs] at hd
  exact (hd.trans (mul_le_mul_of_nonneg_left hdist (by positivity))).trans_eq (by ring)

theorem vanishing_response_coefficients {f : ℝ → ℝ} {a b c d η : ℝ} (hf : HasFourCoefficients f a b c d)
    (hvan : ∀ᶠ h in 𝓝[>] (0:ℝ), VanishingResponse η h f) : fourth η a b=0 ∧ sixth η a b c d=0 := by
  obtain ⟨A,hA,ha⟩ := dirichlet_polynomial_comparison hf η
  obtain ⟨B,hB,hb⟩ := midpoint_evaluation_error η a b c d
  obtain ⟨r,hr,he⟩ := responsePolynomial_midpoint η a b c d
  obtain ⟨L,hL⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0:ℝ) 1) hr.continuousOn
  let V := fourth η a b
  let W := sixth η a b c d
  have bound : ∀ᶠ h in 𝓝[>] (0:ℝ), |h^4*V+h^6*W|≤(A+B+L)*h^7 := by
    filter_upwards [ha,hb,hvan,self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1))] with h hsol herr hvan hpos hsmall
    have hh : 0<h := hpos
    let p := responsePolynomial η a b c d h
    let t := h/2-h^3/12
    let z := Real.log (Real.cosh h)/h
    have hterms : h^4*V+h^6*W=(p.eval t-p.eval z)+p.eval z-h^8*r h := by
      rw [sub_add_cancel]; dsimp only [p,t,V,W]; rw [he]; ring
    have hlr : |r h|≤L := hL h ⟨hh.le,hsmall.le⟩
    have rem : |h^8*r h|≤L*h^7 := by
      rw [abs_mul,abs_of_nonneg (pow_nonneg hh.le 8),mul_comm]
      exact mul_le_mul hlr (pow_le_pow_of_le_one hh.le hsmall.le (by decide : 7≤8)) (pow_nonneg hh.le _) ((abs_nonneg _).trans hlr)
    rw [hterms]
    apply (abs_sub _ _).trans
    apply (add_le_add (abs_add_le _ _) (le_refl _)).trans
    change _≤_
    have hv := add_le_add (add_le_add herr (hsol hvan)) rem
    exact hv.trans_eq (by ring)
  obtain ⟨δ,hδ,hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp bound
  have hcs := horner_coefficients_zero ([0,0,0,0,V,0,W] : List ℝ) (M := A+B+L) hδ (by
    intro h hh hd
    have hbound := hb (show h ∈ Ioo 0 δ from ⟨hh,hd⟩)
    change |h^4*V+h^6*W|≤(A+B+L)*h^7 at hbound
    change |horner [0,0,0,0,V,0,W] h|≤(A+B+L)*h^7
    rwa [show horner [0,0,0,0,V,0,W] h=h^4*V+h^6*W by simp only [horner,smul_eq_mul]; ring])
  exact ⟨hcs V (by simp),hcs W (by simp)⟩

end EuclideanMidpointRigidity.Endpoint

