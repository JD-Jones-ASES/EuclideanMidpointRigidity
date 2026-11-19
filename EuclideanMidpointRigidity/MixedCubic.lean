module

public import EuclideanMidpointRigidity.EigenvalueTangency
public import EuclideanMidpointRigidity.GradientSixth
public import EuclideanMidpointRigidity.ResonantPlane

/-! # The scalar sixth-order constraint on the two resonant cubic components -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

private theorem scalarSixth_of_gradient {D c : Coeff} {J : E →L[ℝ] Coeff}
    {e x y g : E} {a u v : ℝ} (ha : a≠0) (hD : D=a • c)
    (hg : g=u • x+v • y) (hU : K (J e) e e=(7/13*u) • x)
    (hs : let U := K (J e) e e
          let R := K (J U) e e
          let Z := K (J e) e U
          a*(217*⟪U,R⟫_ℝ+231*⟪g,R⟫_ℝ-918*⟪g,Z⟫_ℝ)-340*⟪g,K D U U⟫_ℝ=0) :
    (ResonantPlane.ofJet c J e x y u v).scalarSixth=0 := by
  dsimp only at hs
  simp only [hD,hg,hU,map_smul,K_smul_coeff,K_smul_left,K_smul_right,inner_add_left,
    real_inner_smul_left,real_inner_smul_right] at hs
  have hr : ∀ w : E, ⟪w,K (J x) e e⟫_ℝ=⟪K (J x) e e,w⟫_ℝ := fun _ ↦ real_inner_comm _ _
  have hz : ∀ w : E, ⟪w,K (J e) e x⟫_ℝ=⟪K (J e) e x,w⟫_ℝ := fun _ ↦ real_inner_comm _ _
  simp only [hr,hz] at hs
  apply (mul_eq_zero.mp (show a*(ResonantPlane.ofJet c J e x y u v).scalarSixth=0 by
    dsimp only [ResonantPlane.scalarSixth,ResonantPlane.ofJet]
    linear_combination hs)).resolve_left ha

private theorem normalize_tangent {D c : Coeff} {J : E →L[ℝ] Coeff}
    {e x f q : E} {a u : ℝ} (ha : a≠0) (hD : D=a • c)
    (hq : q=liftStep a J e) (hU : K (J e) e e=(7/13*u) • x)
    (ht : ⟪K (J e) e f,f⟫_ℝ= -⟪K D q f,f⟫_ℝ) :
    ⟪K (J e) e f,f⟫_ℝ= -(7/26)*u*⟪x,K c f f⟫_ℝ := by
  rw [ht,hq,liftStep,hU,hD]
  simp only [K_smul_coeff,K_smul_left,real_inner_smul_left,K_symm c x f,K_selfAdjoint c f x f]
  field_simp
  ring

/-- Only differentiability at the point and persistence of the eigenvalues are
needed of the two auxiliary vector fields. Their other values may have arbitrary lengths. -/
theorem mixed_plane_of_sections {Ω : Set E} {C : E → Coeff} {e x y : E → E} (hΩ : IsOpen Ω)
    (hC : ContDiffOn ℝ ∞ C Ω) (he : ContDiffOn ℝ ∞ e Ω) (hm : MidpointJetEquations Ω C)
    (hunit : ∀ q ∈ Ω, ‖e q‖=1) (hc : ∀ q ∈ Ω, K (C q) (e q) (e q)=sectionValue C e q • e q)
    (ha : ∀ q ∈ Ω, sectionValue C e q≠0) {p : E} (hp : p ∈ Ω)
    (hstep : fderiv ℝ e p (e p)=liftStep (sectionValue C e p) (fderiv ℝ C p) (e p))
    (hdx : DifferentiableAt ℝ x p) (hdy : DifferentiableAt ℝ y p)
    (hx : ∀ᶠ q in 𝓝 p, K (C q) (e q) (x q)=((-1/2:ℝ)*sectionValue C e q) • x q)
    (hy : ∀ᶠ q in 𝓝 p, K (C q) (e q) (y q)=((1/5:ℝ)*sectionValue C e q) • y q)
    {u v : ℝ} (hg : gradient (sectionValue C e) p=u • x p+v • y p)
    (hU : K (fderiv ℝ C p (e p)) (e p) (e p)=(7/13*u) • x p) :
    let c := (sectionValue C e p)⁻¹ • C p
    let plane := ResonantPlane.ofJet c (fderiv ℝ C p) (e p) (x p) (y p) u v
    plane.LowRows ∧ plane.scalarSixth=0 := by
  let a := sectionValue C e p
  let c := a⁻¹ • C p
  have hap : a≠0 := ha _ hp
  have hD : C p=a • c := by simp [c,smul_smul,hap]
  have hE := hm.quartic hp
  have hEn (w : E) : obstruction c (fderiv ℝ C p) w=0 := by
    rw [show c=a⁻¹ • C p from rfl,obstruction_smul_coeff,hE,smul_zero]
  have hcn : K c (e p) (e p)=(1:ℝ) • e p := by
    simp only [c,K_smul_coeff,hc p hp,smul_smul]
    change (a⁻¹*a) • e p=_
    rw [inv_mul_cancel₀ hap]
  have hn (f : E) (b : ℝ) (h : K (C p) (e p) f=(b*a) • f) : K c (e p) f=b • f := by
    simp only [c,K_smul_coeff,h,smul_smul]
    rw [mul_left_comm,inv_mul_cancel₀ hap,mul_one]
  have hprof (l : E) : ⟪K (fderiv ℝ C p l) (e p) (e p),e p⟫_ℝ=⟪u • x p+v • y p,l⟫_ℝ := by
    rw [← hg,sectionValue_gradient hΩ hC he hunit hp (hc _ hp)]
  have ht₁ := eigen_section_tangent hΩ hC he hm.quartic hunit hp (hc _ hp) hap hdx hx
  have ht₂ := eigen_section_tangent hΩ hC he hm.quartic hunit hp (hc _ hp) hap hdy hy
  refine ⟨ResonantPlane.lowRows_of_jet hcn hEn (hn _ _ hx.self_of_nhds) (hn _ _ hy.self_of_nhds)
    hU hprof (normalize_tangent hap hD hstep hU ht₁) (normalize_tangent hap hD hstep hU ht₂),?_⟩
  exact scalarSixth_of_gradient hap hD hg hU (gradient_sixth_equation hΩ hC he hm hunit hc ha hp hstep)

end EuclideanMidpointRigidity
