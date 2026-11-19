module

public import EuclideanMidpointRigidity.ResonantDerivative
public import EuclideanMidpointRigidity.ChannelEntries

/-! # Angular velocities and the contractions of a moving resonant frame -/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology ContDiff InnerProductSpace
namespace EuclideanMidpointRigidity.LiftedSection
open Quartic
variable {d : ℕ} (S : LiftedSection d)
local notation "E" => Space d

def omega (p : E) := (10/7)*((S.core p).z12+(7/26)*(S.core p).m)

theorem rate_coordinate {f : E → E} {p : E} (hf : DifferentiableAt ℝ f p) (w : E) :
    ⟪S.rate f p,w⟫_ℝ=S.rotation p f w := by
  rw [rate,(S.along_axis hf).deriv,real_inner_smul_left,rotation]

theorem internal_rotations {p : E} (hm : S.IsMixed p) :
    S.rotation p S.x (S.axis p)= -7/26 ∧ S.rotation p S.y (S.axis p)=0 ∧
    S.rotation p S.x (S.x p)=0 ∧ S.rotation p S.y (S.y p)=0 ∧
    S.rotation p S.x (S.y p)= -S.omega p ∧ S.rotation p S.y (S.x p)=S.omega p := by
  obtain ⟨_,_,hx,hy⟩ := S.smooth_frame hm
  have dx := hx.differentiableAt (by simp)
  have dy := hy.differentiableAt (by simp)
  have de := (S.smoothAxis.contDiffAt (S.isOpen.mem_nhds hm.1)).differentiableAt (by simp)
  have near := S.eventually_mixed hm
  have xe := stationary_inner_derivative de dx (near.mono fun q hq ↦ (S.plane_data hq).2.2.2.1) (S.axis p)
  have ye := stationary_inner_derivative de dy (near.mono fun q hq ↦ (S.plane_data hq).2.2.2.2.1) (S.axis p)
  obtain ⟨xx,yy,xy⟩ := S.frame_derivatives hm
  obtain ⟨hn,_,hor,_,_,_,_,_⟩ := S.plane_data hm
  have yx := inner_eq_zero_symm.mp hor
  have h := S.rotation_equation hm dy (near.mono fun q hq ↦ (S.eigenvectors hq.1).2) (S.eigenvectors hm.1).1 yx
  have z : ⟪K (S.jet p (S.axis p)) (S.axis p) (S.y p),S.x p⟫_ℝ=(S.core p).z12 :=
    jetEntry_swap₂ _ _ _ _ _
  have m : ⟪S.x p,K (S.cubic p) (S.x p) (S.y p)⟫_ℝ=(S.core p).m := by
    rw [real_inner_comm]
    exact cubicEntry_swap₂ _ _ _ _
  rw [z,m] at h
  have oy : S.rotation p S.y (S.x p)=S.omega p := by unfold omega; linarith only [h]
  rw [S.acceleration hm,real_inner_smul_left,real_inner_self_eq_norm_sq,hn,one_pow,mul_one,
    show ⟪S.axis p,fderiv ℝ S.x p (S.axis p)⟫_ℝ=_ from real_inner_comm _ _] at xe
  rw [S.acceleration hm,real_inner_smul_left,hor,mul_zero,zero_add,
    show ⟪S.axis p,fderiv ℝ S.y p (S.axis p)⟫_ℝ=_ from real_inner_comm _ _] at ye
  have hu : S.u p≠0 := (norm_pos_iff.mpr hm.2.1).ne'
  have ha : S.a p≠0 := (S.positive _ hm.1).ne'
  refine ⟨?_,?_,?_,?_,?_,oy⟩
  · unfold rotation
    linear_combination (norm := (field_simp [ha,hu] <;> ring)) (S.a p/S.u p)*xe
  · simp only [rotation,ye,mul_zero]
  · simp only [rotation,xx,mul_zero]
  · simp only [rotation,yy,mul_zero]
  · rw [← oy]
    simp only [rotation,xy,mul_neg]

namespace SpectralFrame
variable {S : LiftedSection d} {p : Space d}
variable {ι : Type*} [Fintype ι]
variable (B : SpectralFrame S p ι)

theorem contract_rate {f : E → E} (hf : DifferentiableAt ℝ f p) (z w : E) :
    let c := S.cubic p
    cubicEntry c z w (S.rate f p)=cubicEntry c z w (S.axis p)*S.rotation p f (S.axis p)+
      cubicEntry c z w (S.x p)*S.rotation p f (S.x p)+cubicEntry c z w (S.y p)*S.rotation p f (S.y p)+
      ∑ i, cubicEntry c z w (B.w i)*S.rotation p f (B.w i) := by
  have h := B.basis.sum_inner_mul_inner (K (S.cubic p) z w) (S.rate f p)
  rw [Fintype.sum_sum_type,Fin.sum_univ_three] at h
  simp only [B.internal,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at h
  let k := K (S.cubic p) z w
  let v := S.rate f p
  change ⟪k,S.axis p⟫_ℝ*⟪S.axis p,v⟫_ℝ+⟪k,S.x p⟫_ℝ*⟪S.x p,v⟫_ℝ+
    ⟪k,S.y p⟫_ℝ*⟪S.y p,v⟫_ℝ+(∑ i, ⟪k,B.w i⟫_ℝ*⟪B.w i,v⟫_ℝ)=⟪k,v⟫_ℝ at h
  have hv (w : E) : ⟪w,v⟫_ℝ=S.rotation p f w := (real_inner_comm _ _).trans (S.rate_coordinate hf w)
  change ⟪k,v⟫_ℝ=_
  rw [← h]
  simp only [hv]
  rfl

end SpectralFrame
end EuclideanMidpointRigidity.LiftedSection

