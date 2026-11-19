module

public import EuclideanMidpointRigidity.GeodesicBVP
public import EuclideanMidpointRigidity.SmoothDirichlet
public import EuclideanMidpointRigidity.SmoothFieldExtension

/-! # Smooth families of short geodesics parametrized by their endpoints -/

@[expose] public section
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d
local notation "H" => E × E
local notation "P" => PhaseCurve d

def geodesicForce (C : E → Cubic d) (σ : ℝ) (z : H) := -σ • K (C z.1) z.2 z.2

set_option backward.isDefEq.respectTransparency false in
theorem contDiff_geodesicForce {C : E → Cubic d} (hC : ContDiff ℝ ∞ C) (σ : ℝ) :
    ContDiff ℝ ∞ (geodesicForce C σ) := by
  let inc : Cubic d →L[ℝ] (E →L[ℝ] E →L[ℝ] E) := (cubicSubspace d).subtypeL
  have hi := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) («E» := Cubic d) (F := E →L[ℝ] E →L[ℝ] E) inc
  have h : ContDiff ℝ ∞ (fun z : H ↦ inc (C z.1)) := (hi.comp hC).comp contDiff_fst
  exact (((h.clm_apply contDiff_snd).clm_apply contDiff_snd).const_smul (-σ))

def affinePhaseMap : H →L[ℝ] P := by
  let L : H →ₗ[ℝ] P := {
    toFun := fun q ↦ affinePhase q.1 q.2
    map_add' := by
      intro a b
      ext t : 1
      apply Prod.ext <;> simp [affinePhase] <;> module
    map_smul' := by
      intro r a
      ext t : 1
      apply Prod.ext <;> simp [affinePhase,smul_sub,smul_add,smul_comm r] }
  exact LinearMap.toContinuousLinearMap L

@[simp] theorem affinePhaseMap_apply (q : H) : affinePhaseMap q=affinePhase q.1 q.2 := rfl

@[simp] theorem affinePhase_diagonal (p : E) : affinePhase p p=ContinuousMap.const UnitInterval (p,(0:E)) := by
  ext t : 1; simp [affinePhase]

structure SmoothEndpointFamily (C : E → Cubic d) (σ : ℝ) (p : E) (r : ℝ) where
  domain : Set H
  isOpen : IsOpen domain
  center : (p,p) ∈ domain
  phase : H → P
  smooth : ContDiffOn ℝ ∞ phase domain
  rest : phase (p,p)=ContinuousMap.const UnitInterval (p,0)
  force : C(H,E)
  smoothForce : ContDiff ℝ ∞ (force : H → E)
  forceGerm : ∀ q ∈ domain, ∀ t : UnitInterval, (force : H → E) =ᶠ[𝓝 (phase q t)] geodesicForce C σ
  equation : ∀ q ∈ domain, phase q=affinePhase q.1 q.2+greenOperator (force.comp (phase q))
  regular : ∀ q ∈ domain, (fderiv ℝ (dirichletInput greenOperator force) (phase q)).IsInvertible
  small : ∀ q ∈ domain, dist (phase q) (ContinuousMap.const UnitInterval (p,0))<r

set_option backward.isDefEq.respectTransparency false in
theorem exists_smooth_endpoint_family {Ω : Set E} (hΩ : IsOpen Ω) {C : E → Cubic d}
    (hC : ContDiffOn ℝ ∞ C Ω) {p : E} (hp : p ∈ Ω) (σ : ℝ) {r : ℝ} (hr : 0<r) :
    Nonempty (SmoothEndpointFamily C σ p r) := by
  obtain ⟨g,hg,heq⟩ := local_smooth_representative hΩ hC hp
  obtain ⟨W,hWg,hW,hpW⟩ := _root_.mem_nhds_iff.mp heq
  obtain ⟨ε,hε,hεW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hpW)
  let ρ := min r ε
  have hρ : 0<ρ := lt_min hr hε
  let u : P := ContinuousMap.const UnitInterval (p,0)
  let f : C(H,E) := ⟨geodesicForce g σ,(contDiff_geodesicForce hg σ).continuous⟩
  have hf : ContDiff ℝ ∞ (f : H → E) := contDiff_geodesicForce hg σ
  have hfp : f (p,0)=0 := by simp [f,geodesicForce,K]
  have hDf : fderiv ℝ (f : H → E) (p,0)=0 :=
    (hasStrictFDerivAt_acceleration_zero (hg.contDiffAt.of_le (by simp)) σ).hasFDerivAt.fderiv
  obtain ⟨V,s,hV,hV₀,hs₀,hs,hsol⟩ := smooth_green_response greenOperator f hf hfp hDf isOpen_ball (mem_ball_self hρ : u ∈ ball u ρ)
  let D := (affinePhaseMap : H → P) ⁻¹' V
  have hD : IsOpen D := hV.preimage affinePhaseMap.continuous
  have hpp : affinePhaseMap (p,p)=u := by rw [affinePhaseMap_apply,affinePhase_diagonal]
  have hpD : (p,p) ∈ D := by change affinePhaseMap (p,p) ∈ V; rwa [hpp]
  let Y := s ∘ affinePhaseMap
  have hYs : ContDiffOn ℝ ∞ Y D := hs.comp affinePhaseMap.contDiff.contDiffOn (fun _ h ↦ h)
  have hYr : Y (p,p)=u := by change s (affinePhaseMap (p,p))=u; rw [hpp]; exact hs₀
  refine ⟨⟨D,hD,hpD,Y,hYs,hYr,f,hf,?_,fun q hq ↦ (hsol _ hq).2.1,
    fun q hq ↦ (hsol _ hq).2.2,fun q hq ↦ lt_of_lt_of_le (hsol _ hq).1 (min_le_left _ _)⟩⟩
  intro q hq t
  have hd := (ContinuousMap.dist_apply_le_dist (f := Y q) (g := u) t).trans_lt (show dist (Y q) u<ρ from (hsol _ hq).1)
  have hfst : dist (Y q t).1 p≤dist (Y q t) (p,0) := le_max_left _ _
  have hx : (Y q t).1 ∈ W := hεW (hfst.trans_lt (hd.trans_le (min_le_right _ _)))
  have hn : ∀ᶠ z in 𝓝 (Y q t), z.1 ∈ W := continuous_fst.continuousAt (hW.mem_nhds hx)
  filter_upwards [hn] with z hz
  change -σ • K (g z.1) z.2 z.2= -σ • K (C z.1) z.2 z.2
  rw [show g z.1=C z.1 from hWg hz]

end EuclideanMidpointRigidity

