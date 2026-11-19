module

public import EuclideanMidpointRigidity.PersistentIdempotent
public import EuclideanMidpointRigidity.FixedFactorRows

/-! # A nonzero space of fixed directions on a ball -/

@[expose] public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d

set_option backward.isDefEq.respectTransparency false

/-- Directions annihilating the spatial derivative in both the spatial and cubic slots. -/
def fixedDirections (C : E → T) (W : Set E) : Submodule ℝ E where
  carrier := {z | ∀ p ∈ W, fderiv ℝ C p z=0 ∧ ∀ l v, K (fderiv ℝ C p l) z v=0}
  zero_mem' := by simp [K]
  add_mem' := by
    intro a b ha hb p hp
    obtain ⟨h₁,h₂⟩ := ha p hp
    obtain ⟨h₃,h₄⟩ := hb p hp
    exact ⟨(LinearMap.ker (fderiv ℝ C p).toLinearMap).add_mem h₁ h₃, fun l v ↦ by rw [K_add_left,h₂,h₄,add_zero]⟩
  smul_mem' := by
    intro a b hb p hp
    obtain ⟨h₁,h₂⟩ := hb p hp
    exact ⟨(LinearMap.ker (fderiv ℝ C p).toLinearMap).smul_mem a h₁, fun l v ↦ by rw [K_smul_left,h₂,smul_zero]⟩

theorem HorizontalPatch.nonzero_fixed_directions {S : LiftedSection d} (H : HorizontalPatch S) (hne : S.domain.Nonempty) :
    ∃ p ∈ S.domain, ∃ r : ℝ, 0<r ∧ ball p r ⊆ S.domain ∧ ∃ z ∈ fixedDirections S.field (ball p r), z≠0 := by
  obtain ⟨p,hp,r,hr,hsub,hin⟩ := H.fixed_stationary_axis hne
  have hnear : ∀ᶠ x in 𝓝 p, x ∈ ball p r := ball_mem_nhds p hr
  obtain ⟨s,hs,hball⟩ := Metric.mem_nhds_iff.mp (hnear.and (H.persistent_idempotent hp hr hsub hin))
  let U := ball p s
  let a := S.a p
  let e := S.axis p
  let u := S.idempotent p
  have ha : 0<a := S.positive p hp
  have he : ‖e‖=1 := S.unit p hp
  have hne' : e≠0 := norm_ne_zero_iff.mp (he.trans_ne one_ne_zero)
  have hue : a • u=e := by simp only [u,LiftedSection.idempotent,a,smul_smul,mul_inv_cancel₀ ha.ne',one_smul,e]
  have hU : U ⊆ S.domain := fun _ hx ↦ hsub (hball hx).1
  have hId (x : E) (hx : x ∈ U) : K (S.field x) u u=u := (hball hx).2
  have hprod (x : E) (hx : x ∈ U) : K (S.field x) e e=a • e := by
    rw [← hue,K_smul_left,K_smul_right,hId x hx]
  have hval (x : E) (hx : x ∈ U) : sectionValue S.field (fun _ ↦ e) x=a := by
    simp only [sectionValue,hprod x hx,real_inner_smul_left,real_inner_self_eq_norm_sq,he,one_pow,mul_one]
  have hz (x : E) (hx : x ∈ U) : fderiv ℝ S.field x u=0 := hin _ (hball hx).1
  let S' : LiftedSection d := ⟨U,S.field,fun _ ↦ e,isOpen_ball,S.smooth.mono hU,contDiffOn_const,S.equations.mono hU,
    fun _ _ ↦ he,fun x hx ↦ by rw [hval x hx]; exact hprod x hx,fun x hx ↦ (hval x hx).symm ▸ ha,by
      intro x hx
      have h := congrArg (fun v : E ↦ fderiv ℝ S.field x v) hue
      simp only [map_smul,hz x hx,smul_zero] at h
      simp [liftStep,h.symm,K]⟩
  obtain ⟨b,hb⟩ := (S.equations.mono hU).amplitude_constant isOpen_ball (convex_ball _ _).isPreconnected (S.smooth.mono hU)
  have hamp : amplitude (S.field p)=a := amplitude_eq_of_unit_max he ha.le (H.maximizes p hp) rfl
  have hm (x : E) (hx : x ∈ U) : S'.Maximizes x := by
    intro v hv
    change ⟪K (S.field x) v v,v⟫_ℝ≤sectionValue S.field (fun _ ↦ e) x
    rw [← directionProfile_apply,hval x hx,← hamp,hb p (mem_ball_self hs),← hb x hx]
    exact directionProfile_le_amplitude (by simp [mem_closedBall,dist_zero_right,hv]) _
  have hF (x : E) (hx : x ∈ U) : Nonempty (FixedAxis.SliceFrame (S.field x) u) := by
    have hh := S'.idempotent_frame hx (hm x hx)
    change Nonempty (FixedAxis.SliceFrame (S.field x) ((sectionValue S.field (fun _ ↦ e) x)⁻¹ • e)) at hh
    rwa [hval x hx] at hh
  refine ⟨p,hp,s,hs,hU,u,fun x hx ↦ ⟨hz x hx,?_⟩,?_⟩
  · exact FixedAxis.constant_slice isOpen_ball (S.smooth.mono hU) (S.equations.mono hU).quartic hId hz hF hx
  · intro hu
    exact hne' (by simpa [hu] using hue.symm)

end EuclideanMidpointRigidity

