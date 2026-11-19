module

public import EuclideanMidpointRigidity.InverseComparison
public import EuclideanMidpointRigidity.TranslatedMidpoints

/-! # Comparing endpoint derivatives with derivatives at a translated trial path -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.SmoothEndpointFamily
variable {d : ℕ} {C : Space d → Cubic d} {σ r : ℝ} {p : Space d} (F : SmoothEndpointFamily C σ p r)
local notation "E" => Space d
local notation "H" => E × E
local notation "P" => PhaseCurve d
local notation "Q" => AccelerationCurve d
set_option backward.isDefEq.respectTransparency false

def shiftPath (q : H) (v : E) : P := F.phase q+translationPhase v
def shiftJacobian (q : H) (v : E) : P →L[ℝ] P := fderiv ℝ (dirichletInput greenOperator F.force) (F.shiftPath q v)
def shiftResponse (q : H) (v : E) (j : H) : P := (F.shiftJacobian q v).inverse (affinePhaseMap j)

theorem shiftPath_apply (q : H) (v : E) (t : UnitInterval) : F.shiftPath q v t=F.phase q t+(v,0) := rfl

theorem continuous_shiftPath (q : H) : Continuous (F.shiftPath q) := by
  have ht : Continuous (translationPhase (d := d)) := by
    change Continuous (fun v : E ↦ ContinuousMap.const UnitInterval (v,(0:E)))
    fun_prop
  exact continuous_const.add ht

@[simp] theorem shiftPath_zero (q : H) : F.shiftPath q 0=F.phase q := by
  ext t : 1; rw [F.shiftPath_apply]; simp

theorem continuous_shiftJacobian (q : H) : Continuous (F.shiftJacobian q) :=
  ((contDiff_dirichletInput greenOperator F.force F.smoothForce).continuous_fderiv (by simp)).comp (F.continuous_shiftPath q)

theorem shiftJacobian_zero {q : H} (hq : q ∈ F.domain) : (F.shiftJacobian q 0).IsInvertible := by
  change (fderiv ℝ _ (F.shiftPath q 0)).IsInvertible
  rw [F.shiftPath_zero]
  exact F.regular q hq

theorem eventually_shift_regular {q : H} (hq : q ∈ F.domain) : ∀ᶠ v in 𝓝 (0:E), (F.shiftJacobian q v).IsInvertible :=
  (F.continuous_shiftJacobian q).continuousAt (ContinuousLinearMap.isOpen_setOfPred_isInvertible.mem_nhds (F.shiftJacobian_zero hq))

theorem continuousAt_shiftInverse {q : H} (hq : q ∈ F.domain) :
    ContinuousAt (fun v ↦ (F.shiftJacobian q v).inverse) 0 :=
  ((F.shiftJacobian_zero hq).contDiffAt_map_inverse (n := (∞ : WithTop ℕ∞))).continuousAt.comp (F.continuous_shiftJacobian q).continuousAt

theorem shiftResponse_zero {q : H} (hq : q ∈ F.domain) (j : H) : F.shiftResponse q 0 j=F.variation q j := by
  apply (F.shiftJacobian_zero hq).injective
  rw [shiftResponse,(F.shiftJacobian_zero hq).self_apply_inverse]
  have h := F.variation_equation hq j
  change affinePhaseMap j=fderiv ℝ (dirichletInput greenOperator F.force) (F.shiftPath q 0) (F.variation q j)
  rw [F.shiftPath_zero,dirichletInput_derivative]
  change _=F.variation q j-greenOperator (F.linearForce q (F.variation q j))
  exact (sub_eq_iff_eq_add.mpr h).symm

theorem eventually_force_germ {q : H} (hq : q ∈ F.domain) :
    ∀ᶠ v in 𝓝 (0:E), ∀ t : UnitInterval, (F.force : H → E) =ᶠ[𝓝 (F.shiftPath q v t)] geodesicForce C σ := by
  let U := interior {z : H | F.force z=geodesicForce C σ z}
  have hU : range (F.phase q) ⊆ U := by
    rintro _ ⟨t,rfl⟩
    exact mem_interior_iff_mem_nhds.mpr (F.forceGerm q hq t)
  have hn : Tendsto (F.shiftPath q) (𝓝 0) (𝓝 (F.phase q)) := F.shiftPath_zero q ▸ (F.continuous_shiftPath q).continuousAt
  filter_upwards [hn (ContinuousMap.eventually_range_subset isOpen_interior hU)] with v hv
  exact fun t ↦ mem_interior_iff_mem_nhds.mp (hv (mem_range_self t))

/-- The force defect controls the discrepancy of the endpoint derivative on nearby trial paths. -/
theorem shifted_comparison {q : H} (hq : q ∈ F.domain) (j : H) :
    ∃ K : ℝ, 0≤K ∧ ∀ᶠ v in 𝓝 (0:E),
      ‖F.shiftResponse q v j-F.variation (q+(v,v)) j‖≤
        K*‖F.force.comp (F.shiftPath q v)-F.force.comp (F.phase q)‖ := by
  let f := dirichletInput greenOperator F.force
  obtain ⟨K,hK,U,hU,hb⟩ := inverse_derivative_comparison (contDiff_dirichletInput greenOperator F.force F.smoothForce) (F.regular q hq) (affinePhaseMap j)
  let q' := fun v : E ↦ q+(v,v)
  have hq' : Continuous q' := continuous_const.add (continuous_id.prodMk continuous_id)
  have h₀ : q' 0=q := by simp [q']
  have ht : Tendsto (F.shiftPath q) (𝓝 0) (𝓝 (F.phase q)) := F.shiftPath_zero q ▸ (F.continuous_shiftPath q).continuousAt
  have ha : Tendsto q' (𝓝 0) (𝓝 q) := h₀ ▸ hq'.continuousAt
  have hs := (F.smooth.continuousOn.continuousAt (F.isOpen.mem_nhds hq)).tendsto.comp ha
  refine ⟨K*‖(greenOperator : Q →L[ℝ] P)‖,mul_nonneg hK (ContinuousLinearMap.opNorm_nonneg _),?_⟩
  filter_upwards [ht hU,hs hU,ha (F.isOpen.mem_nhds hq)] with v hv hw hd
  have he (y : H) (hy : y ∈ F.domain) : f (F.phase y)=affinePhaseMap y := sub_eq_iff_eq_add.mpr (F.equation y hy)
  have hv' : f (F.shiftPath q v)-f (F.phase (q' v))= -greenOperator (F.force.comp (F.shiftPath q v)-F.force.comp (F.phase q)) := by
    rw [he _ hd,map_sub]
    change F.phase q+translationPhase v-greenOperator _-affinePhaseMap (q+(v,v))=_
    rw [map_add,affinePhaseMap_apply (v,v),affinePhase_diagonal]
    change F.phase q+translationPhase v-_-((affinePhase q.1 q.2)+translationPhase v)=_
    linear_combination (norm := abel) F.equation q hq
  have hh := hb _ hv _ hw
  change ‖F.shiftResponse q v j-(fderiv ℝ f (F.phase (q' v))).inverse (affinePhaseMap j)‖≤K*‖f (F.shiftPath q v)-f (F.phase (q' v))‖ at hh
  have hx : (fderiv ℝ f (F.phase (q' v))).inverse (affinePhaseMap j)=F.variation (q' v) j := by
    rw [← F.shiftResponse_zero hd j]
    simp [shiftResponse,shiftJacobian,f]
  rw [hv',norm_neg,hx] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left (greenOperator.le_opNorm _) hK).trans_eq (mul_assoc _ _ _).symm)

end EuclideanMidpointRigidity.SmoothEndpointFamily

