module

public import EuclideanMidpointRigidity.EndpointFamily

/-! # The midpoint identity on smooth endpoint families -/

@[expose] public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d
local notation "H" => E × E
local notation "P" => PhaseCurve d

def middleParameter : UnitInterval := ⟨midpointTime,by constructor <;> norm_num [midpointTime]⟩

namespace SmoothEndpointFamily
variable {C : Space d → Cubic d} {σ r : ℝ} {p : Space d} (F : SmoothEndpointFamily C σ p r)

def source (q : H) : AccelerationCurve d := F.force.comp (F.phase q)
def position (q : H) := bvpPosition q.1 q.2 (F.source q)
def velocity (q : H) := bvpVelocity q.1 q.2 (F.source q)

theorem phase_eq {q : H} (hq : q ∈ F.domain) (t : UnitInterval) :
    (F.position q t,F.velocity q t)=F.phase q t := by
  simpa only [position,velocity,source,bvpPosition,bvpVelocity,ContinuousMap.add_apply,affinePhase,
    ContinuousMap.coe_mk,Prod.mk_add_mk,greenOperator_apply] using
    (congrArg (fun y : P ↦ y t) (F.equation q hq)).symm

theorem short {q : H} (hq : q ∈ F.domain) :
    IsShortGeodesic C σ p r q.1 q.2 (F.position q) (F.velocity q) := by
  refine ⟨⟨fun t _ ↦ hasDerivAt_bvpPosition _ _ _ t,?_⟩,bvpPosition_zero _ _ _,bvpPosition_one _ _ _,?_⟩
  · intro t ht
    have h := hasDerivAt_bvpVelocity q.1 q.2 (F.source q) t
    rw [pathExtend_mem _ t ht] at h
    have hacc := (F.forceGerm q hq ⟨t,ht⟩).self_of_nhds
    change F.force (F.phase q ⟨t,ht⟩)=geodesicForce C σ (F.phase q ⟨t,ht⟩) at hacc
    rw [← F.phase_eq hq ⟨t,ht⟩] at hacc
    change HasDerivAt (F.velocity q) ((F.force.comp (F.phase q)) ⟨t,ht⟩) t at h
    have hforce : (F.force.comp (F.phase q)) ⟨t,ht⟩= -σ • K (C (F.position q t)) (F.velocity q t) (F.velocity q t) := by
      change F.force (F.phase q ⟨t,ht⟩)=_
      rw [← F.phase_eq hq ⟨t,ht⟩]
      exact hacc
    rwa [hforce] at h
  · intro t ht
    have h := (ContinuousMap.dist_apply_le_dist (f := F.phase q) (g := ContinuousMap.const UnitInterval (p,0)) ⟨t,ht⟩).trans_lt (F.small q hq)
    rw [← F.phase_eq hq ⟨t,ht⟩] at h
    change max (dist (F.position q t) p) (dist (F.velocity q t) 0)<r at h
    simpa only [dist_eq_norm,sub_zero] using max_lt_iff.mp h

theorem midpoint_eq {Ω : Set E} {W : Set H} {A : E → E → E}
    (hA : IsCanonicalLocalMidpoint Ω C σ p r W A) {q : H} (hq : q ∈ F.domain) (hw : q ∈ W) :
    (F.phase q middleParameter).1=A q.1 q.2 := by
  obtain ⟨γ,v,_,ha,hu⟩ := hA.2.2.2.2 q.1 q.2 hw
  rw [← F.phase_eq hq middleParameter,ha]
  exact (hu _ _ (F.short hq) _ middleParameter.property).1

end SmoothEndpointFamily

theorem smooth_midpoint_families {Ω : Set E} {C : E → Cubic d} (hΩ : IsOpen Ω) (hC : ContDiffOn ℝ ∞ C Ω)
    (hmid : LocalMidpointInvariance Ω C) {p : E} (hp : p ∈ Ω) :
    ∃ (r s : ℝ) (F : SmoothEndpointFamily C 1 p r) (G : SmoothEndpointFamily C (-1) p s) (U : Set H),
      IsOpen U ∧ (p,p) ∈ U ∧ U ⊆ F.domain ∧ U ⊆ G.domain ∧
      ∀ q ∈ U, (F.phase q middleParameter).1+(G.phase q middleParameter).1=q.1+q.2 := by
  obtain ⟨r,s,W,A,B,hA,hB,hg⟩ := hmid p hp
  obtain ⟨F⟩ := exists_smooth_endpoint_family hΩ hC hp 1 hA.1
  obtain ⟨G⟩ := exists_smooth_endpoint_family hΩ hC hp (-1) hB.1
  let U := (W ∩ F.domain) ∩ G.domain
  refine ⟨r,s,F,G,U,(hA.2.2.1.inter F.isOpen).inter G.isOpen,⟨⟨hA.2.2.2.1,F.center⟩,G.center⟩,
    fun _ h ↦ h.1.2,fun _ h ↦ h.2,?_⟩
  intro q hq
  rw [F.midpoint_eq hA hq.1.2 hq.1.1,G.midpoint_eq hB hq.2 hq.1.1]
  exact hg _ _ hq.1.1

end EuclideanMidpointRigidity

