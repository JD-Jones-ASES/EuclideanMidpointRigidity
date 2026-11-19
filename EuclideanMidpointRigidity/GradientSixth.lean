module

public import EuclideanMidpointRigidity.CriticalScalarSixth
public import EuclideanMidpointRigidity.SectionHessian
public import EuclideanMidpointRigidity.SectionJetTransport

/-! # The first-jet scalar sixth equation on a section following the critical lift -/

@[expose] public section
noncomputable section
open Set
open scoped ContDiff InnerProductSpace
namespace EuclideanMidpointRigidity

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

private theorem first_jet_elimination {a gY uY hess gV gR uR gZ gK h : ℝ} (ha : a≠0)
    (hy : gY=gV+(2*a)⁻¹*gR+(2*(2*a)⁻¹)*gZ)
    (ht : 7*(hess+gY)=26*uY)
    (hv : 2*(gZ+(2*a)⁻¹*gK+(a/5*gY-13*a/10*uY))+a*gY=0)
    (hh : 6*a*hess=13*uR-10*gR) (h₆ : 17*gV=32*h)
    (h₄ : 3*a*h+5*gR-2*uR=0) :
    a*(217*uR+231*gR-918*gZ)-340*gK=0 := by
  have hys : 2*a*gY=2*a*gV+gR+2*gZ := by
    field_simp [ha] at hy
    linarith only [hy]
  have hvs : 20*a*gZ+10*gK+14*a^2*gY-26*a^2*uY=0 := by
    field_simp [ha] at hv
    linarith only [hv]
  have hmix : 42*a^2*gV+91*a*gR+162*a*gZ-91*a*uR+60*gK=0 := by
    linear_combination 6*hvs - (6*a^2)*ht - (21*a)*hys + (7*a)*hh
  linear_combination (-17/3)*hmix + (14*a^2)*h₆ + (448/3*a)*h₄

theorem gradient_sixth_equation {Ω : Set E} {C : E → Coeff} {e : E → E} (hΩ : IsOpen Ω)
    (hC : ContDiffOn ℝ ∞ C Ω) (he : ContDiffOn ℝ ∞ e Ω) (hm : MidpointJetEquations Ω C)
    (hunit : ∀ x ∈ Ω, ‖e x‖=1) (hc : ∀ x ∈ Ω, K (C x) (e x) (e x)=sectionValue C e x • e x)
    (ha : ∀ x ∈ Ω, sectionValue C e x≠0) {p : E} (hp : p ∈ Ω)
    (hstep : fderiv ℝ e p (e p)=liftStep (sectionValue C e p) (fderiv ℝ C p) (e p)) :
    let a := sectionValue C e p
    let g := gradient (sectionValue C e) p
    let z := e p
    let J := fderiv ℝ C p
    let U := K (J z) z z
    let R := K (J U) z z
    let Z := K (J z) z U
    a*(217*⟪U,R⟫_ℝ+231*⟪g,R⟫_ℝ-918*⟪g,Z⟫_ℝ)-340*⟪g,K (C p) U U⟫_ℝ=0 := by
  let A := sectionValue C e
  let a := A p
  let g := gradient A p
  let z := e p
  let q := fderiv ℝ e p z
  let J := fderiv ℝ C p
  let H := fderiv ℝ (fderiv ℝ C) p
  let U := K (J z) z z
  let V := K (H z z) z z
  let R := K (J U) z z
  let Z := K (J z) z U
  let k := (2*a)⁻¹
  let Y := V+K (J q) z z+K (J z) q z+K (J z) z q
  have hq : q=k • U := hstep
  have hg (l : E) : ⟪K (J l) z z,z⟫_ℝ=⟪g,l⟫_ℝ :=
    (sectionValue_gradient hΩ hC he hunit hp (hc p hp) l).symm
  have hY : Y=V+k • R+(2*k) • Z := by
    dsimp only [Y,R,Z]
    rw [hq]
    simp only [map_smul,K_smul_coeff,K_smul_left,K_smul_right,K_symm (J z) U z]
    module
  have hy := congrArg (fun w : E ↦ ⟪g,w⟫_ℝ) hY
  simp only [inner_add_right,real_inner_smul_right] at hy
  obtain ⟨ht,hv⟩ := section_jet_transport hΩ hC he hm.quartic hunit hc ha hp
  change 7*(fderiv ℝ (fderiv ℝ A) p z U+fderiv ℝ A p Y)=26*⟪U,Y⟫_ℝ at ht
  rw [← inner_gradient_left] at ht
  change (2:ℝ) • (Z + K (C p) q U + K (C p) z Y) + a • Y=0 at hv
  have hB : K (C p) z g=(a/5) • g-(13*a/10) • U :=
    critical_gradient_product (hc p hp) (hm.quartic hp) hg
  have hvg := congrArg (fun w : E ↦ ⟪g,w⟫_ℝ) hv
  simp only [inner_add_right,real_inner_smul_right,inner_zero_right,hq,K_smul_left,
    ← K_selfAdjoint (C p) z g Y,hB,inner_sub_left,real_inner_smul_left] at hvg
  have hh := section_axial_hessian hΩ hC he hm.quartic hunit hc ha hp
  have h₆ := critical_sixth_scalar hΩ hC hm hp (ha p hp) z (hc p hp)
  change 17*⟪K (J V) z z,z⟫_ℝ=32*⟪K (H z U) z z,z⟫_ℝ at h₆
  rw [hg V] at h₆
  have h₄ := first_prolongation_scalar hΩ (hC.of_le (by simp)) hm.quartic hp a z U (hc p hp)
  change 3*a*⟪K (H U z) z z,z⟫_ℝ+5*⟪K (J R) z z,z⟫_ℝ-2*⟪R,U⟫_ℝ=0 at h₄
  have hs : H U z=H z U := ((hC.contDiffAt (hΩ.mem_nhds hp)).isSymmSndFDerivAt (by simp)) U z
  rw [hs,hg R,show ⟪R,U⟫_ℝ=⟪U,R⟫_ℝ from real_inner_comm _ _] at h₄
  exact first_jet_elimination (ha p hp) hy ht hvg hh h₆ h₄

end EuclideanMidpointRigidity
