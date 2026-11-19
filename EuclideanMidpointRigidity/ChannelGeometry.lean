module

public import EuclideanMidpointRigidity.LiftedSection
public import EuclideanMidpointRigidity.FrameTransport
public import EuclideanMidpointRigidity.MixedChannel

/-! # The actual first-jet equations in each external eigendirection -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity.LiftedSection

variable {d : ℕ}
local notation "E" => Space d
variable (S : LiftedSection d)

def rotation (p : E) (f : E → E) (w : E) : ℝ :=
  S.a p/S.u p*⟪fderiv ℝ f p (S.axis p),w⟫_ℝ

def channel (p w : E) : MixedChannel :=
  MixedChannel.ofJet (S.cubic p) (S.jet p) (S.axis p) (S.x p) (S.y p) w (S.ratio p)
    (S.rotation p S.x w) (S.ratio p*S.rotation p S.y w)

theorem acceleration {p : E} (hm : S.IsMixed p) :
    fderiv ℝ S.axis p (S.axis p)=(7/26*S.u p/S.a p) • S.x p := by
  rw [S.lift _ hm.1,liftStep,S.axial_jet hm,smul_smul]
  change ((2*S.a p)⁻¹*(7/13*S.u p)) • S.x p=_
  congr 1
  ring

theorem rotation_equation {p : E} (hm : S.IsMixed p) {f : E → E} (hf : DifferentiableAt ℝ f p)
    {b s : ℝ} (heig : ∀ᶠ q in 𝓝 p, K (S.field q) (S.axis q) (f q)=(b*S.a q) • f q)
    {w : E} (hw : K (S.field p) (S.axis p) w=(s*S.a p) • w) (hfw : ⟪f p,w⟫_ℝ=0) :
    (b-s)*S.rotation p f w=⟪K (S.jet p (S.axis p)) (S.axis p) (f p),w⟫_ℝ+
      7/26*⟪w,K (S.cubic p) (S.x p) (f p)⟫_ℝ := by
  have h := eigen_rotation_coordinate S.isOpen S.smooth S.smoothAxis hm.1 hf heig hw hfw (S.axis p)
  rw [S.acceleration hm,K_smul_left,real_inner_smul_left] at h
  change (b-s)*S.a p*_=_ at h
  simp only [rotation,jet,cubic,smul_apply,K_smul_coeff,real_inner_smul_left,real_inner_smul_right]
  rw [show ⟪w,K (S.field p) (S.x p) (f p)⟫_ℝ=⟪K (S.field p) (S.x p) (f p),w⟫_ℝ from real_inner_comm _ _]
  have hu : S.u p≠0 := (norm_pos_iff.mpr hm.2.1).ne'
  have ha : S.a p≠0 := (S.positive _ hm.1).ne'
  linear_combination (norm := (field_simp [hu,ha]; ring)) (S.u p)⁻¹*h

theorem channel_equations {p : E} (hm : S.IsMixed p) {w : E} {s : ℝ}
    (hw : K (S.field p) (S.axis p) w=(s*S.a p) • w)
    (hxw : ⟪S.x p,w⟫_ℝ=0) (hyw : ⟪S.y p,w⟫_ℝ=0) :
    (S.channel p w).Equations s := by
  obtain ⟨hu,hv,hx,hy⟩ := S.smooth_frame hm
  have hne : S.u p≠0 := (norm_pos_iff.mpr hm.2.1).ne'
  have ex := (S.eigenvectors hm.1).1
  have ey := (S.eigenvectors hm.1).2
  obtain ⟨_,_,_,hex,hey,_,_,_⟩ := S.plane_data hm
  obtain ⟨hU,hg⟩ := S.normalized_jet_data hm
  have hx' := hx.differentiableAt (by simp)
  have hy' := hy.differentiableAt (by simp)
  have hnear : ∀ᶠ q in 𝓝 p, q ∈ S.domain := S.isOpen.mem_nhds hm.1
  have rot₁ := S.rotation_equation hm hx'
    (hnear.mono fun q hq ↦ (S.eigenvectors hq).1) hw hxw
  have rot₂ := S.rotation_equation hm hy'
    (hnear.mono fun q hq ↦ (S.eigenvectors hq).2) hw hyw
  refine ⟨MixedChannel.lowRows_of_jet (S.normalized_axis hm.1) (S.normalized_obstruction hm.1)
    (S.normalized_eigenvector hm.1 ex) (S.normalized_eigenvector hm.1 ey)
    (S.normalized_eigenvector hm.1 hw) hU hg _ _,rot₁,?_,?_⟩
  · dsimp only [channel,MixedChannel.ofJet]
    linear_combination S.ratio p*rot₂
  · have hF := gradient_frame_transport S.isOpen S.smooth S.smoothAxis S.equations.quartic S.unit S.critical
      (fun q hq ↦ (S.positive q hq).ne') hm.1 hx' hy' (hu.differentiableAt (by simp)) (hv.differentiableAt (by simp))
      ((S.eventually_mixed hm).mono fun _ hq ↦ S.split_gradient hq) w
    simp only [hxw,hyw,mul_zero,add_zero] at hF
    have h₁ := axis_section_coordinate S.isOpen S.smooth S.smoothAxis S.critical hm.1 hex ex w
    have h₂ := axis_section_coordinate S.isOpen S.smooth S.smoothAxis S.critical hm.1 hey ey w
    change S.a p*(1-2*(-1/2:ℝ))*_= _ at h₁
    change S.a p*(1-2*(1/5:ℝ))*_= _ at h₂
    dsimp only [channel,MixedChannel.ofJet,rotation,ratio,jet]
    simp only [smul_apply,K_smul_coeff,real_inner_smul_left,← h₁,← h₂]
    linear_combination (norm := (field_simp [hne]; ring)) (S.a p/(S.u p)^2)*hF

/-- Differentiated criticality makes the two missing null-output jet entries
zero. Hence a null direction carries neither a cubic nor a rotation term. -/
theorem null_channel {p : E} (hm : S.IsMixed p) {w : E}
    (hw : K (S.field p) (S.axis p) w=((1/2:ℝ)*S.a p) • w)
    (hew : ⟪S.axis p,w⟫_ℝ=0) (hxw : ⟪S.x p,w⟫_ℝ=0) (hyw : ⟪S.y p,w⟫_ℝ=0) :
    let v := S.channel p w
    v.q=0 ∧ v.l=0 ∧ v.h=0 ∧ v.r1w=0 ∧ v.rw1=0 ∧ v.z1w=0 ∧
      v.r2w=0 ∧ v.rw2=0 ∧ v.z2w=0 ∧ v.rot1=0 ∧ v.rot2=0 := by
  have hr (l : E) : ⟪K (S.jet p l) (S.axis p) (S.axis p),w⟫_ℝ=0 := by
    have h := axis_section_coordinate S.isOpen S.smooth S.smoothAxis S.critical hm.1 hew hw l
    norm_num at h
    simp [jet,smul_apply,real_inner_smul_left,← h]
  have h₁ : (S.channel p w).rw1=0 := hr _
  have h₂ : (S.channel p w).rw2=0 := by simp only [channel,MixedChannel.ofJet,hr,mul_zero]
  obtain ⟨q,l,h,a,b,c,d,i,j⟩ := MixedChannel.zero_at_half (S.channel_equations hm hw hxw hyw) h₁ h₂
  exact ⟨q,l,h,a,h₁,b,c,h₂,d,i,j⟩

end EuclideanMidpointRigidity.LiftedSection
