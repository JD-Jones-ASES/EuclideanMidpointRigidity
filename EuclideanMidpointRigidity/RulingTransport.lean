module

public import EuclideanMidpointRigidity.RulingCoefficients

/-! # Derivatives of the normalized slice and the direction field along a ruling -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 140000
namespace EuclideanMidpointRigidity.LiftedSection
variable {d : ℕ} (S : LiftedSection d)
local notation "E" => Space d
local notation "Op" => E →L[ℝ] E

theorem hasDerivAt_normalized_cubic {p : E} (hp : p ∈ S.domain) (hm : ∀ q ∈ S.domain, S.Maximizes q) (l : E) :
    HasDerivAt (S.cubic ∘ displacementLine p l) (S.normalizedJet p l) 0 := by
  let line := displacementLine p l
  have ha : ContDiffAt ℝ ∞ S.a p := (contDiffOn_sectionValue S.smooth S.smoothAxis).contDiffAt (S.isOpen.mem_nhds hp)
  have dc := differentiableAlongLine ((S.smooth.contDiffAt (S.isOpen.mem_nhds hp)).differentiableAt (by simp)) l
  have da := differentiableAlongLine (ha.differentiableAt (by simp)) l
  rw [S.stationary_value hp hm,zero_apply] at da
  have hn : (S.a ∘ displacementLine p l) 0≠0 := by
    rw [Function.comp_apply,displacementLine_zero]; exact (S.positive p hp).ne'
  have di := da.fun_inv hn
  simp only [neg_zero,zero_div] at di
  have h := di.fun_smul dc
  change HasDerivAt (S.cubic ∘ displacementLine p l)
    (((S.a (displacementLine p l 0))⁻¹) • fderiv ℝ S.field p l + (0:ℝ) • S.field (displacementLine p l 0)) 0 at h
  simpa only [displacementLine_zero,zero_smul,add_zero,normalizedJet,smul_apply] using h

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_axisSlice {p : E} (hp : p ∈ S.domain) (hm : ∀ q ∈ S.domain, S.Maximizes q) :
    HasDerivAt (S.axisSlice ∘ displacementLine p (S.axis p)) (S.sliceRate p) 0 := by
  let e := S.axis p
  let line := displacementLine p e
  let inc : Cubic d →L[ℝ] (E →L[ℝ] Op) := (cubicSubspace d).subtypeL
  have dc := S.hasDerivAt_normalized_cubic hp hm e
  change HasDerivAt (S.cubic ∘ line) (S.normalizedJet p e) 0 at dc
  have hi := ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) («E» := Cubic d) (F := E →L[ℝ] Op)
    (x := (S.cubic ∘ line) 0) inc
  have dj : HasDerivAt (inc ∘ (S.cubic ∘ line)) (inc (S.normalizedJet p e)) 0 :=
    HasFDerivAt.comp_hasDerivAt («E» := E →L[ℝ] Op) (F := Cubic d) 0 hi dc
  have de := differentiableAlongLine ((S.smoothAxis.contDiffAt (S.isOpen.mem_nhds hp)).differentiableAt (by simp)) (S.axis p)
  rw [S.straight_axis hp hm] at de
  have h := dj.clm_apply de
  simp only [Function.comp_apply,line,displacementLine_zero,map_zero,add_zero] at h
  exact h

theorem hasDerivAt_axisSlope {p : E} (hp : p ∈ S.domain) (hm : ∀ q ∈ S.domain, S.Maximizes q) :
    let A := fderiv ℝ S.axis p
    HasDerivAt (fderiv ℝ S.axis ∘ displacementLine p (S.axis p)) (-(A.comp A)) 0 := by
  dsimp only
  have he := S.smoothAxis.contDiffAt (S.isOpen.mem_nhds hp)
  have hA : ContDiffAt ℝ 1 (fderiv ℝ S.axis) p := he.fderiv_right (by simp)
  have h := differentiableAlongLine (hA.differentiableAt (by norm_num)) (S.axis p)
  have hr : fderiv ℝ (fderiv ℝ S.axis) p (S.axis p)= -((fderiv ℝ S.axis p).comp (fderiv ℝ S.axis p)) := by
    ext l : 1
    exact S.axis_riccati hp hm l
  rwa [hr] at h

end EuclideanMidpointRigidity.LiftedSection

