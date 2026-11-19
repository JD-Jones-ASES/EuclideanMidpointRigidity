module

public import EuclideanMidpointRigidity.MaximumEnvelope
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Sequences

/-! # Maximizing axes as limits of unconstrained polynomial extrema -/

@[expose] public section
noncomputable section
open Set Filter Metric
open scoped Topology InnerProductSpace
namespace EuclideanMidpointRigidity

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

def radialObjective (c : Coeff) (z : E) : ℝ := directionProfile z c-‖z‖^4

theorem directionProfile_smul (c : Coeff) (s : ℝ) (e : E) :
    directionProfile (s • e) c=s^3*directionProfile e c := by
  simp only [directionProfile_apply,K_smul_left,K_smul_right,real_inner_smul_left,real_inner_smul_right]
  ring

theorem directionProfile_le_radial (c : Coeff) (v : E) :
    directionProfile v c ≤ amplitude c*‖v‖^3 := by
  have h := cubic_diagonal_norm_bound c (amplitude c) (amplitude_nonneg c) (by
    intro w hw
    rw [← directionProfile_apply]
    exact directionProfile_le_amplitude (by simp [mem_closedBall,dist_zero_right,hw]) c) v
  rw [directionProfile_apply]
  calc
    _ ≤ ‖K c v v‖*‖v‖ := real_inner_le_norm _ _
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right h (norm_nonneg v)]

theorem continuous_radialObjective (c : Coeff) : Continuous (radialObjective c) :=
  (continuous_directionProfile.comp (Continuous.prodMk_right c)).sub (continuous_norm.pow _)

theorem normalized_radial_max {c : Coeff} (ha : 0<amplitude c) {z : E}
    (hm : ∀ v, radialObjective c v ≤ radialObjective c z) :
    z≠0 ∧ ‖‖z‖⁻¹ • z‖=1 ∧ directionProfile (‖z‖⁻¹ • z) c=amplitude c := by
  obtain ⟨e,hu,he⟩ := exists_unit_max_of_pos ha
  have hs (r : ℝ) (hr : 0≤r) :
      radialObjective c (r • e)=r^3*amplitude c-r^4 := by
    simp [radialObjective,directionProfile_smul,he,norm_smul,abs_of_nonneg hr,hu]
  have h₀ : z≠0 := by
    rintro rfl
    have h := hm ((amplitude c / 2) • e)
    rw [hs _ (by positivity)] at h
    have hz : radialObjective c 0=0 := by simp [radialObjective,directionProfile_apply,K]
    rw [hz] at h
    nlinarith only [h,pow_pos ha 4]
  have hn := norm_pos_iff.mpr h₀
  have hu' : ‖‖z‖⁻¹ • z‖=1 := by simp [norm_smul,hn.ne']
  refine ⟨h₀,hu',?_⟩
  have h := hm (‖z‖ • e)
  rw [hs _ hn.le] at h
  have he' : directionProfile z c=amplitude c*‖z‖^3 := by
    apply le_antisymm (directionProfile_le_radial c z)
    dsimp only [radialObjective] at h
    rw [mul_comm (amplitude c)]
    linarith only [h]
  rw [directionProfile_smul,he']
  field_simp

/-- A nonnegative penalty vanishing at the origin can be sent to zero along
a sequence of global maximizers in a common compact ball. -/
theorem radial_perturbation_limit (c : Coeff) (L : E → ℝ) (hL : Continuous L)
    (hpos : ∀ z, 0≤L z) (hzero : L 0=0) :
    ∃ (w : E) (t : ℕ → ℝ) (z : ℕ → E), Tendsto t atTop (𝓝 0) ∧ (∀ j, 0<t j) ∧
      Tendsto z atTop (𝓝 w) ∧ (∀ j v, radialObjective c v-t j*L v ≤ radialObjective c (z j)-t j*L (z j)) ∧
      ∀ v, radialObjective c v ≤ radialObjective c w := by
  let s : ℕ → ℝ := fun j ↦ 1/((j:ℝ)+1)
  have hs (j : ℕ) : 0<s j := by dsimp [s]; positivity
  have hst : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let B := closedBall (0:E) (amplitude c+1)
  have hB : IsCompact B := isCompact_closedBall _ _
  have h₀ : (0:E) ∈ B := mem_closedBall_self (by linarith [amplitude_nonneg c])
  let P := fun j z ↦ radialObjective c z-s j*L z
  have hex (j : ℕ) : ∃ z ∈ B, ∀ v, P j v ≤ P j z := by
    have hc : Continuous (P j) := (continuous_radialObjective c).sub (continuous_const.mul hL)
    obtain ⟨z,hz,hm⟩ := hB.exists_isMaxOn ⟨0,h₀⟩ hc.continuousOn
    refine ⟨z,hz,fun v ↦ ?_⟩
    by_cases hv : v ∈ B
    · exact isMaxOn_iff.mp hm v hv
    · apply le_trans _ (isMaxOn_iff.mp hm 0 h₀)
      have hnorm : amplitude c+1<‖v‖ := by simpa [B,mem_closedBall,dist_zero_right] using hv
      have hdiff : 0≤‖v‖-amplitude c := by linarith
      have hpow : 0≤‖v‖^3 := by positivity
      have hpr := directionProfile_le_radial c v
      have hz₀ : P j 0=0 := by simp [P,radialObjective,directionProfile_apply,K,hzero]
      rw [hz₀]
      dsimp only [P,radialObjective]
      nlinarith only [mul_nonneg hdiff hpow,hpr,mul_nonneg (hs j).le (hpos v)]
  choose u hu hmax using hex
  obtain ⟨w,_,φ,hφ,hlim⟩ := hB.tendsto_subseq hu
  have ht := hst.comp hφ.tendsto_atTop
  refine ⟨w,s ∘ φ,u ∘ φ,ht,fun j ↦ hs _,hlim,fun j v ↦ hmax _ _,?_⟩
  intro v
  have hleft := (tendsto_const_nhds (x := radialObjective c v)).sub (ht.mul_const (L v))
  have hright := ((continuous_radialObjective c).continuousAt.tendsto.comp hlim).sub
    (ht.mul (hL.continuousAt.tendsto.comp hlim))
  simpa only [zero_mul,sub_zero] using le_of_tendsto_of_tendsto' hleft hright (fun j ↦ hmax (φ j) v)

end EuclideanMidpointRigidity

