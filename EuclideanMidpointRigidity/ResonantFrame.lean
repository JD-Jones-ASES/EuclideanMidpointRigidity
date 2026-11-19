module

public import EuclideanMidpointRigidity.MixedCubic
public import EuclideanMidpointRigidity.Resonances

/-! # The frame determined by the two nonzero components of the amplitude gradient -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

def negativeComponent (C : E → Coeff) (e : E → E) (p : E) : E :=
  (13/7:ℝ) • K (fderiv ℝ C p (e p)) (e p) (e p)

def positiveComponent (C : E → Coeff) (e : E → E) (p : E) : E :=
  gradient (sectionValue C e) p-negativeComponent C e p

set_option backward.isDefEq.respectTransparency false in
theorem contDiffAt_negativeComponent {C : E → Coeff} {e : E → E} {p : E}
    (hC : ContDiffAt ℝ ∞ C p) (he : ContDiffAt ℝ ∞ e p) :
    ContDiffAt ℝ ∞ (negativeComponent C e) p := by
  let inc : Coeff →L[ℝ] (E →L[ℝ] E →L[ℝ] E) := (cubicSubspace d).subtypeL
  have hJ : ContDiffAt ℝ ∞ (fderiv ℝ C) p := hC.fderiv_right (by simp)
  have hi := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) («E» := Coeff)
    (F := E →L[ℝ] E →L[ℝ] E) inc
  have hprod : ContDiffAt ℝ ∞ (fun q ↦ K (fderiv ℝ C q (e q)) (e q) (e q)) p :=
    (((hi.contDiffAt.comp p (hJ.clm_apply he)).clm_apply he).clm_apply he)
  exact hprod.const_smul (13/7:ℝ)

set_option backward.isDefEq.respectTransparency false in
theorem contDiffAt_positiveComponent {Ω : Set E} {C : E → Coeff} {e : E → E} (hΩ : IsOpen Ω)
    (hC : ContDiffOn ℝ ∞ C Ω) (he : ContDiffOn ℝ ∞ e Ω) {p : E} (hp : p ∈ Ω) :
    ContDiffAt ℝ ∞ (positiveComponent C e) p := by
  let riesz : (E →L[ℝ] ℝ) →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hA := (contDiffOn_sectionValue hC he).contDiffAt (hΩ.mem_nhds hp)
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ (sectionValue C e)) p := hA.fderiv_right (by simp)
  have hg : ContDiffAt ℝ ∞ (gradient (sectionValue C e)) p := riesz.contDiff.contDiffAt.comp p hD
  exact hg.sub (contDiffAt_negativeComponent (hC.contDiffAt (hΩ.mem_nhds hp))
    (he.contDiffAt (hΩ.mem_nhds hp)))

theorem component_eigenvalues {Ω : Set E} {C : E → Coeff} {e : E → E} (hΩ : IsOpen Ω)
    (hC : ContDiffOn ℝ ∞ C Ω) (he : ContDiffOn ℝ ∞ e Ω) (hm : QuarticOn Ω C)
    (hunit : ∀ q ∈ Ω, ‖e q‖=1) {p : E} (hp : p ∈ Ω)
    (hc : K (C p) (e p) (e p)=sectionValue C e p • e p) :
    K (C p) (e p) (negativeComponent C e p)=((-1/2:ℝ)*sectionValue C e p) • negativeComponent C e p ∧
    K (C p) (e p) (positiveComponent C e p)=((1/5:ℝ)*sectionValue C e p) • positiveComponent C e p := by
  obtain ⟨h₁,h₂⟩ := critical_axis_resonances hc
    (hm hp)
    (fun l ↦ (sectionValue_gradient hΩ hC he hunit hp hc l).symm)
  constructor
  · simp only [negativeComponent,K_smul_right,h₁]
    module
  · rw [show (1/5:ℝ)*sectionValue C e p=sectionValue C e p/5 by ring]
    exact h₂

theorem axial_eigenvectors_orthogonal {c : Coeff} {e x y : E} {b s : ℝ} (hbs : b≠s)
    (hx : K c e x=b • x) (hy : K c e y=s • y) : ⟪x,y⟫_ℝ=0 := by
  have h := K_selfAdjoint c e x y
  rw [hx,hy,real_inner_smul_left,real_inner_smul_right] at h
  exact (mul_eq_zero.mp (show (b-s)*⟪x,y⟫_ℝ=0 by linarith only [h])).resolve_left (sub_ne_zero.mpr hbs)

/-- Normalize only at the base point. Constant multiples of the smooth components
extend these unit vectors through the point, including at repeated eigenvalues. -/
theorem mixed_resonant_frame {Ω : Set E} {C : E → Coeff} {e : E → E} (hΩ : IsOpen Ω)
    (hC : ContDiffOn ℝ ∞ C Ω) (he : ContDiffOn ℝ ∞ e Ω) (hm : MidpointJetEquations Ω C)
    (hunit : ∀ q ∈ Ω, ‖e q‖=1) (hc : ∀ q ∈ Ω, K (C q) (e q) (e q)=sectionValue C e q • e q)
    (ha : ∀ q ∈ Ω, sectionValue C e q≠0) {p : E} (hp : p ∈ Ω)
    (hstep : fderiv ℝ e p (e p)=liftStep (sectionValue C e p) (fderiv ℝ C p) (e p))
    (h₁ : negativeComponent C e p≠0) (h₂ : positiveComponent C e p≠0) :
    let a := sectionValue C e p
    let u := ‖negativeComponent C e p‖
    let v := ‖positiveComponent C e p‖
    let x := u⁻¹ • negativeComponent C e p
    let y := v⁻¹ • positiveComponent C e p
    let plane := ResonantPlane.ofJet (a⁻¹ • C p) (fderiv ℝ C p) (e p) x y u v
    ‖x‖=1 ∧ ‖y‖=1 ∧ ⟪x,y⟫_ℝ=0 ∧ ⟪e p,x⟫_ℝ=0 ∧ ⟪e p,y⟫_ℝ=0 ∧
      plane.LowRows ∧ plane.scalarSixth=0 ∧ 86354*u*plane.t112+219375*v*plane.t122=0 := by
  let u := ‖negativeComponent C e p‖
  let v := ‖positiveComponent C e p‖
  let x := fun q ↦ u⁻¹ • negativeComponent C e q
  let y := fun q ↦ v⁻¹ • positiveComponent C e q
  let a := sectionValue C e p
  have hu : 0<u := norm_pos_iff.mpr h₁
  have hv : 0<v := norm_pos_iff.mpr h₂
  have hs (q : E) (hq : q ∈ Ω) := component_eigenvalues hΩ hC he hm.quartic hunit hq (hc q hq)
  have hx : ∀ᶠ q in 𝓝 p, K (C q) (e q) (x q)=((-1/2:ℝ)*sectionValue C e q) • x q := by
    filter_upwards [hΩ.mem_nhds hp] with q hq
    rw [show x q=u⁻¹ • negativeComponent C e q from rfl,K_smul_right,(hs q hq).1,smul_comm]
  have hy : ∀ᶠ q in 𝓝 p, K (C q) (e q) (y q)=((1/5:ℝ)*sectionValue C e q) • y q := by
    filter_upwards [hΩ.mem_nhds hp] with q hq
    rw [show y q=v⁻¹ • positiveComponent C e q from rfl,K_smul_right,(hs q hq).2,smul_comm]
  have hdx : DifferentiableAt ℝ x p := ((contDiffAt_negativeComponent
    (hC.contDiffAt (hΩ.mem_nhds hp)) (he.contDiffAt (hΩ.mem_nhds hp))).const_smul u⁻¹).differentiableAt (by simp)
  have hdy : DifferentiableAt ℝ y p := ((contDiffAt_positiveComponent
    hΩ hC he hp).const_smul v⁻¹).differentiableAt (by simp)
  have hg : gradient (sectionValue C e) p=u • x p+v • y p := by
    simp [x,y,smul_smul,hu.ne',hv.ne',positiveComponent]
  have hU : K (fderiv ℝ C p (e p)) (e p) (e p)=(7/13*u) • x p := by
    simp only [x,negativeComponent,smul_smul]
    have heq : (7/13*u)*(u⁻¹*(13/7))=1 := by field_simp
    rw [heq,one_smul]
  obtain ⟨low,six⟩ := mixed_plane_of_sections hΩ hC he hm hunit hc ha hp hstep hdx hdy hx hy hg hU
  have hap := ha p hp
  refine ⟨norm_smul_inv_norm h₁,norm_smul_inv_norm h₂,
    axial_eigenvectors_orthogonal (by intro h; apply hap; linarith only [h]) hx.self_of_nhds hy.self_of_nhds,
    axial_eigenvectors_orthogonal (by intro h; apply hap; linarith only [h]) (hc p hp) hx.self_of_nhds,
    axial_eigenvectors_orthogonal (by intro h; apply hap; linarith only [h]) (hc p hp) hy.self_of_nhds,
    low,six,ResonantPlane.mixed_cubic_relation low hu hv six⟩

end EuclideanMidpointRigidity
