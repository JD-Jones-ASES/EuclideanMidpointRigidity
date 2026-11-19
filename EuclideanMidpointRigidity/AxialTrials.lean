module

public import EuclideanMidpointRigidity.ShiftedPhase
public import EuclideanMidpointRigidity.AxialObservation
public import EuclideanMidpointRigidity.StationaryAxis

/-! # The force and its derivative on straight trial paths through nearby centers -/

@[expose] public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
open Endpoint
namespace RealizedChord
variable {d : ℕ} {Ω W : Set (Space d)} {C : Space d → Cubic d} {σ r : ℝ} {p u : Space d} {h : ℝ}
  {B : Space d →L[ℝ] Space d} {F : SmoothEndpointFamily C σ p r}
local notation "E" => Space d
local notation "P" => PhaseCurve d
variable (J : RealizedChord Ω C σ p u h B F)
include J
set_option backward.isDefEq.respectTransparency false

theorem trial_data (hW : IsOpen W) (hc : Convex ℝ W) (hC : ContDiffOn ℝ ∞ C W) (hp : p ∈ W)
    (hi : ∀ t : UnitInterval, axialPosition p u h t ∈ W) (inactive : ∀ x ∈ W, fderiv ℝ C x u=0) :
    let q := chordEnds p u h
    ∀ᶠ v in 𝓝 (0:E), ∀ t : UnitInterval,
      F.force (F.shiftPath q v t)= -σ • ((chordSpeed h t)^2 • K (C (p+v)) u u) ∧
      ∀ Y : P, pathForceDerivative F.force F.smoothForce (F.shiftPath q v) Y t=
        -σ • ((chordSpeed h t)^2 • K (fderiv ℝ C (p+v) (Y t).1) u u+
          (2*chordSpeed h t) • K (C (p+v)) u (Y t).2) := by
  let q := chordEnds p u h
  have hv : Tendsto (F.shiftPath q) (𝓝 0) (𝓝 (F.phase q)) := F.shiftPath_zero q ▸ (F.continuous_shiftPath q).continuousAt
  have hm : range (F.phase q) ⊆ Prod.fst ⁻¹' W := by
    rintro _ ⟨t,rfl⟩
    rw [J.path_eq]
    exact hi t
  have hn := hv (ContinuousMap.eventually_range_subset (hW.preimage continuous_fst) hm)
  have hp' : ∀ᶠ v in 𝓝 (0:E), p+v ∈ W := (continuous_const.add continuous_id).continuousAt (hW.mem_nhds (by simpa using hp : p+0 ∈ W))
  filter_upwards [F.eventually_force_germ J.mem,hn,hp'] with v hg hm hpv
  intro t
  let k := chordSpeed h t
  let s := chordParameter h t
  have eq : F.shiftPath q v t=(p+v+s • u,k • u) := by
    rw [F.shiftPath_apply,J.path_eq]
    simp only [axialPosition,axialVelocity,Prod.mk_add_mk,add_zero,s,k]
    abel
  have hpos := hm (mem_range_self t)
  rw [eq] at hpos
  have hf := stationary_field_jet hW hc hC inactive hpv hpos
  have h₁ := (hg t).self_of_nhds
  have h₂ := (hg t).fderiv_eq (𝕜 := ℝ)
  constructor
  · change F.force (F.shiftPath q v t)=_
    rw [h₁,eq]
    simp only [geodesicForce,K_smul_left,K_smul_right,smul_smul,hf.1,k,pow_two]
  · intro Y
    rw [pathForceDerivative_apply,h₂,eq,fderiv_geodesicForce_apply σ _ _ (hC.contDiffAt (hW.mem_nhds hpos))]
    simp only [firstForceJet,firstProduct,Prod.fst,Prod.snd,hf.1,hf.2,k,K_smul_left,K_smul_right,smul_smul,pow_two]

theorem trial_comparison (hW : IsOpen W) (hc : Convex ℝ W) (hC : ContDiffOn ℝ ∞ C W) (hp : p ∈ W)
    (hi : ∀ t : UnitInterval, axialPosition p u h t ∈ W) (inactive : ∀ x ∈ W, fderiv ℝ C x u=0) (j : E × E) :
    let q := chordEnds p u h
    ∃ L : ℝ, 0≤L ∧ ∀ᶠ v in 𝓝 (0:E), ‖F.shiftResponse q v j-F.variation (q+(v,v)) j‖≤
      L*‖K (C (p+v)) u u-K (C p) u u‖ := by
  let q := chordEnds p u h
  have hD := J.trial_data hW hc hC hp hi inactive
  have h₀ (t : UnitInterval) : F.force (F.phase q t)= -σ • ((chordSpeed h t)^2 • K (C p) u u) := by
    simpa only [F.shiftPath_zero,add_zero] using (hD.self_of_nhds t).1
  obtain ⟨K₀,hK,hb⟩ := F.shifted_comparison J.mem j
  let w := chordWeight h J.positive
  refine ⟨K₀*(|σ| * ‖w‖),by positivity,?_⟩
  filter_upwards [hb,hD] with v hv hs
  apply hv.trans
  rw [mul_assoc K₀]
  apply mul_le_mul_of_nonneg_left _ hK
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  change ‖F.force (F.shiftPath q v t)-F.force (F.phase q t)‖≤_
  rw [(hs t).1,h₀,← smul_sub,← smul_sub,norm_smul,norm_smul,Real.norm_eq_abs,abs_neg]
  have hw : ‖(chordSpeed h t)^2‖≤‖w‖ := w.norm_coe_le_norm t
  calc
    _ ≤ |σ| * (‖w‖*‖K (C (p+v)) u u-K (C p) u u‖) := by gcongr
    _ = _ := by ring

end RealizedChord
end EuclideanMidpointRigidity

