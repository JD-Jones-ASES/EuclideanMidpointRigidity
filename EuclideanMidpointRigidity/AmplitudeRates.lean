module

public import EuclideanMidpointRigidity.ChannelGeometry
public import EuclideanMidpointRigidity.MixedNorm

/-! # Derivatives of the two resonant gradient lengths -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity

theorem stationary_inner_derivative {d : ℕ} {x y : Space d → Space d} {p : Space d} {c : ℝ}
    (hx : DifferentiableAt ℝ x p) (hy : DifferentiableAt ℝ y p)
    (hc : ∀ᶠ q in 𝓝 p, ⟪x q,y q⟫_ℝ=c) (l : Space d) :
    ⟪fderiv ℝ x p l,y p⟫_ℝ+⟪x p,fderiv ℝ y p l⟫_ℝ=0 := by
  let line := fun t : ℝ ↦ p+t • l
  have h₀ : line 0=p := by simp [line]
  have hd : HasDerivAt line l 0 := by simpa [line] using ((hasDerivAt_id (0:ℝ)).smul_const l).const_add p
  have dx := hx.hasFDerivAt.comp_hasDerivAt_of_eq 0 hd h₀.symm
  have dy := hy.hasFDerivAt.comp_hasDerivAt_of_eq 0 hd h₀.symm
  have hn : ∀ᶠ t in 𝓝 (0:ℝ), ⟪x (line t),y (line t)⟫_ℝ=c := hd.continuousAt (h₀ ▸ hc)
  have h := (dx.inner ℝ dy).unique ((hasDerivAt_const (0:ℝ) c).congr_of_eventuallyEq hn)
  simpa only [Function.comp_apply,h₀,add_comm] using h

namespace ResonantPlane

theorem amplitude_rates {p : ResonantPlane} (h : p.LowRows) (hs : p.scalarSixth=0)
    (hu : 0<p.u) (hv : 0<p.v) {du dv w : ℝ}
    (hw : (7/10)*w=p.z12+(7/26)*p.u*p.t112)
    (h₁ : du= -p.u*p.r11/2-5*p.v*p.r21/3-p.v*w)
    (h₂ : dv= -p.u*p.r12/2-5*p.v*p.r22/3+p.u*w) :
    du= -(1261750/734009)*p.v^2*p.t122 ∧ dv=(4164755/4490408)*p.u*p.v*p.t122 := by
  have sol := h.solve
  have mix := mixed_cubic_relation h hu hv hs
  rw [sol.z12] at hw
  rw [sol.r11,sol.r21] at h₁
  rw [sol.r12,sol.r22] at h₂
  constructor
  · linear_combination h₁ - (10/7*p.v)*hw + (5*106034/(193851*86354)*p.v)*mix
  · linear_combination h₂ + (10/7*p.u)*hw - (5*65920/(395304*86354)*p.u)*mix

end ResonantPlane

namespace LiftedSection
variable {d : ℕ}
local notation "E" => Space d
variable (S : LiftedSection d)

def n (p : E) : ℝ := ⟪S.x p,K (S.cubic p) (S.y p) (S.y p)⟫_ℝ

theorem frame_derivatives {p : E} (hm : S.IsMixed p) :
    ⟪fderiv ℝ S.x p (S.axis p),S.x p⟫_ℝ=0 ∧ ⟪fderiv ℝ S.y p (S.axis p),S.y p⟫_ℝ=0 ∧
      ⟪fderiv ℝ S.x p (S.axis p),S.y p⟫_ℝ= -⟪fderiv ℝ S.y p (S.axis p),S.x p⟫_ℝ := by
  obtain ⟨_,_,hx,hy⟩ := S.smooth_frame hm
  have hd (q : E) (hq : S.IsMixed q) := S.plane_data hq
  have hxx := stationary_inner_derivative (hx.differentiableAt (by simp)) (hx.differentiableAt (by simp))
    ((S.eventually_mixed hm).mono fun q hq ↦ show ⟪S.x q,S.x q⟫_ℝ=1 by
      rw [real_inner_self_eq_norm_sq,(hd q hq).1]; norm_num) (S.axis p)
  have hyy := stationary_inner_derivative (hy.differentiableAt (by simp)) (hy.differentiableAt (by simp))
    ((S.eventually_mixed hm).mono fun q hq ↦ show ⟪S.y q,S.y q⟫_ℝ=1 by
      rw [real_inner_self_eq_norm_sq,(hd q hq).2.1]; norm_num) (S.axis p)
  have hxy := stationary_inner_derivative (hx.differentiableAt (by simp)) (hy.differentiableAt (by simp))
    ((S.eventually_mixed hm).mono fun q hq ↦ (hd q hq).2.2.1) (S.axis p)
  rw [show ⟪S.x p,fderiv ℝ S.x p (S.axis p)⟫_ℝ=_ from real_inner_comm _ _] at hxx
  rw [show ⟪S.y p,fderiv ℝ S.y p (S.axis p)⟫_ℝ=_ from real_inner_comm _ _] at hyy
  rw [show ⟪S.x p,fderiv ℝ S.y p (S.axis p)⟫_ℝ=_ from real_inner_comm _ _] at hxy
  exact ⟨by linarith only [hxx],by linarith only [hyy],by linarith only [hxy]⟩

theorem amplitude_rates {p : E} (hm : S.IsMixed p) :
    S.a p*fderiv ℝ S.u p (S.axis p)= -(1261750/734009)*(S.v p)^2*S.n p ∧
      S.a p*fderiv ℝ S.v p (S.axis p)=(4164755/4490408)*S.u p*S.v p*S.n p := by
  obtain ⟨hu,hv,hx,hy⟩ := S.smooth_frame hm
  obtain ⟨hxn,hyn,hxy,hex,hey,low,six,_⟩ := S.plane_data hm
  obtain ⟨hx₀,hy₀,hmv⟩ := S.frame_derivatives hm
  let W := S.a p*⟪fderiv ℝ S.y p (S.axis p),S.x p⟫_ℝ
  have hr (l : E) := gradient_frame_transport S.isOpen S.smooth S.smoothAxis S.equations.quartic S.unit S.critical
    (fun q hq ↦ (S.positive q hq).ne') hm.1 (hx.differentiableAt (by simp)) (hy.differentiableAt (by simp))
    (hu.differentiableAt (by simp)) (hv.differentiableAt (by simp))
    ((S.eventually_mixed hm).mono fun _ hq ↦ S.split_gradient hq) l
  have h₁ := hr (S.x p)
  have h₂ := hr (S.y p)
  have hyx : ⟪S.y p,S.x p⟫_ℝ=0 := inner_eq_zero_symm.mp hxy
  have hxx : ⟪S.x p,S.x p⟫_ℝ=1 := by rw [real_inner_self_eq_norm_sq,hxn]; norm_num
  have hyy : ⟪S.y p,S.y p⟫_ℝ=1 := by rw [real_inner_self_eq_norm_sq,hyn]; norm_num
  simp only [hx₀,hy₀,hxx,hyy,hxy,hyx,hmv,mul_zero,mul_one,add_zero,zero_add] at h₁ h₂
  have ex := (S.eigenvectors hm.1).1
  have ey := (S.eigenvectors hm.1).2
  have ax (l : E) := axis_section_coordinate S.isOpen S.smooth S.smoothAxis S.critical hm.1 hex ex l
  have ay (l : E) := axis_section_coordinate S.isOpen S.smooth S.smoothAxis S.critical hm.1 hey ey l
  have hnear : ∀ᶠ q in 𝓝 p, q ∈ S.domain := S.isOpen.mem_nhds hm.1
  have hrw := eigen_rotation_coordinate S.isOpen S.smooth S.smoothAxis hm.1 (hy.differentiableAt (by simp))
    (hnear.mono fun q hq ↦ (S.eigenvectors hq).2) ex hyx (S.axis p)
  rw [S.acceleration hm,K_smul_left,real_inner_smul_left] at hrw
  have hcyc : ⟪K (S.field p) (S.x p) (S.y p),S.x p⟫_ℝ=⟪S.y p,K (S.field p) (S.x p) (S.x p)⟫_ℝ :=
    K_selfAdjoint _ _ _ _
  have hZ : ⟪K (fderiv ℝ S.field p (S.axis p)) (S.axis p) (S.y p),S.x p⟫_ℝ=
      ⟪K (fderiv ℝ S.field p (S.axis p)) (S.axis p) (S.x p),S.y p⟫_ℝ := by rw [K_selfAdjoint,real_inner_comm]
  rw [hcyc,hZ] at hrw
  apply ResonantPlane.amplitude_rates low six (norm_pos_iff.mpr hm.2.1) (norm_pos_iff.mpr hm.2.2) (w := W)
  · dsimp only [ResonantPlane.ofJet,W,cubic]
    simp only [K_smul_coeff,real_inner_smul_right]
    change (1/5- -1/2)*S.a p*_=_ at hrw
    linear_combination hrw
  · dsimp only [ResonantPlane.ofJet,W]
    rw [← ax,← ay]
    simp only [a]
    linear_combination sectionValue S.field S.axis p*h₁
  · dsimp only [ResonantPlane.ofJet,W]
    rw [← ax,← ay]
    simp only [a]
    linear_combination sectionValue S.field S.axis p*h₂

end LiftedSection
end EuclideanMidpointRigidity
