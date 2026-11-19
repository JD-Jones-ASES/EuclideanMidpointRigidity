module

public import EuclideanMidpointRigidity.AxialTrials

/-! # Linear measurements of the derivative of a fixed axial product -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity
open Endpoint
variable {d : ℕ}
local notation "E" => Space d
local notation "Op" => E →L[ℝ] E
local notation "H" => E × E
local notation "P" => PhaseCurve d
local notation "Q" => AccelerationCurve d
set_option backward.isDefEq.respectTransparency false

namespace OrientedEndpointChart
variable {Ω : Set (Space d)} {C : Space d → Cubic d} {p u : Space d} {h : ℝ} {B : Space d →L[ℝ] Space d} (D : OrientedEndpointChart C p)

def observation (u : E) (h : ℝ) (hh : 0<h) (j : H) (v : E) : Op →L[ℝ] E :=
  midpointEvaluation.comp (((D.plus.shiftJacobian (chordEnds p u h) v).inverse).comp
    (greenOperator.comp (weightedPosition h hh (D.minus.shiftResponse (chordEnds p (-u) h) v j))))

variable (J : RealizedChord Ω C 1 p u h B D.plus) (N : RealizedChord Ω C (-1) p (-u) h B D.minus)
include J N

theorem observation_continuous (j : H) : ContinuousAt (D.observation u h J.positive j) 0 := by
  have hm : ContinuousAt (fun v ↦ D.minus.shiftResponse (chordEnds p (-u) h) v j) 0 :=
    (D.minus.continuousAt_shiftInverse N.mem).clm_apply continuousAt_const
  exact continuousAt_const.clm_comp ((D.plus.continuousAt_shiftInverse J.mem).clm_comp
    (continuousAt_const.clm_comp ((weightedPosition h J.positive).continuous.continuousAt.comp hm)))

theorem observation_kernel (hΩ : IsOpen Ω) (hC : ContDiffOn ℝ ∞ C Ω) {z o : E} {b c : ℝ} (hz : B z=b • z) (ho : B o=c • o)
    (M : Op) (hm : D.observation u h J.positive ((centeredProfile (1-2*b) h).ends h z) 0 M=0) :
    VanishingResponse (1-2*c) h (fun s ↦ ⟪o,M z⟫_ℝ*centeredCoordinate (1-2*b) h s) := by
  let q := chordEnds p u h
  let q' := chordEnds p (-u) h
  let T := centeredProfile (1-2*b) h
  let j := T.ends h z
  let Z := D.minus.shiftResponse q' 0 j
  let src := weightedPosition h J.positive Z M
  let Y := (D.plus.shiftJacobian q 0).inverse (greenOperator src)
  have hh := (D.plus.shiftJacobian_zero J.mem).self_apply_inverse (greenOperator src)
  change fderiv ℝ (dirichletInput greenOperator D.plus.force) (D.plus.shiftPath q 0) Y=greenOperator src at hh
  rw [D.plus.shiftPath_zero,dirichletInput_derivative] at hh
  change Y-greenOperator (D.plus.linearForce q Y)=greenOperator src at hh
  have he : Y=greenOperator (src+D.plus.linearForce q Y) := by rw [map_add]; exact sub_eq_iff_eq_add.mp hh
  have eqn (t : UnitInterval) : ⟪o,src t⟫_ℝ=(chordSpeed h t)^2*(⟪o,M z⟫_ℝ*centeredCoordinate (1-2*b) h (chordParameter h t)) := by
    rw [show src=weightedPosition h J.positive Z M from rfl,weightedPosition_apply]
    dsimp only [Z]
    rw [D.minus.shiftResponse_zero N.mem]
    dsimp only [j,ChordProfile.ends]
    rw [N.profile hΩ hC z hz T t]
    simp only [centeredProfile,real_inner_smul_right,map_smul,T,Prod.fst]
    ring
  obtain ⟨X,V,hsol,hval⟩ := J.forced_projection hΩ hC ho Y src he (fun s ↦ ⟪o,M z⟫_ℝ*centeredCoordinate (1-2*b) h s) eqn
  change midpointEvaluation Y=0 at hm
  exact ⟨X,V,hsol,by rw [hval,hm,inner_zero_right]⟩

theorem observation_difference {W : Set E} (hW : IsOpen W) (hc : Convex ℝ W) (hC : ContDiffOn ℝ ∞ C W) (hp : p ∈ W)
    (hi : ∀ t : UnitInterval, axialPosition p u h t ∈ W) (hn : ∀ t : UnitInterval, axialPosition p (-u) h t ∈ W)
    (hz : ∀ x ∈ W, fderiv ℝ C x u=0) (j : H) :
    let q := chordEnds p u h
    let q' := chordEnds p (-u) h
    ∀ᶠ v in 𝓝 (0:E), (2:ℝ) • D.observation u h J.positive j v (Horizontal.spatialSlice (fderiv ℝ C (p+v)) u)=
      midpointEvaluation (D.minus.shiftResponse q' v j-D.plus.shiftResponse q v j) := by
  let q := chordEnds p u h
  let q' := chordEnds p (-u) h
  have hz' (x : E) (hx : x ∈ W) : fderiv ℝ C x (-u)=0 := by simp [hz x hx]
  filter_upwards [J.trial_data hW hc hC hp hi hz,N.trial_data hW hc hC hp hn hz',
    D.plus.eventually_shift_regular J.mem,D.minus.eventually_shift_regular N.mem] with v a b hA hB
  let A := D.plus.shiftJacobian q v
  let Z := D.minus.shiftResponse q' v j
  let X := D.plus.shiftResponse q v j
  let R := Horizontal.spatialSlice (fderiv ℝ C (p+v)) u
  let F := weightedPosition h J.positive Z R
  have hforce : pathForceDerivative D.minus.force D.minus.smoothForce (D.minus.shiftPath q' v) Z-
      pathForceDerivative D.plus.force D.plus.smoothForce (D.plus.shiftPath q v) Z=(2:ℝ) • F := by
    ext t : 1
    simp only [ContinuousMap.sub_apply,ContinuousMap.smul_apply]
    change pathForceDerivative D.minus.force D.minus.smoothForce (D.minus.shiftPath q' v) Z t-
      pathForceDerivative D.plus.force D.plus.smoothForce (D.plus.shiftPath q v) Z t=(2:ℝ) • weightedPosition h J.positive Z R t
    rw [(a t).2 Z,(b t).2 Z,weightedPosition_apply]
    change _=(2:ℝ) • (chordSpeed h t^2 • K (fderiv ℝ C (p+v) (Z t).1) u u)
    simp only [K_neg_left,K_neg_right,neg_neg,one_smul,neg_smul,smul_neg]
    module
  have hZ := hB.self_apply_inverse (affinePhaseMap j)
  have hX := hA.self_apply_inverse (affinePhaseMap j)
  change (D.minus.shiftJacobian q' v) Z=affinePhaseMap j at hZ
  change A X=affinePhaseMap j at hX
  have hdiff : A (Z-X)=(2:ℝ) • greenOperator F := by
    rw [map_sub,hX,← hZ]
    dsimp only [A,SmoothEndpointFamily.shiftJacobian]
    rw [dirichletInput_derivative greenOperator D.plus.force D.plus.smoothForce,dirichletInput_derivative greenOperator D.minus.force D.minus.smoothForce]
    change (Z-greenOperator _)-(Z-greenOperator _)=(2:ℝ) • greenOperator F
    rw [← map_smul,← hforce,map_sub]
    abel_nf
    rw [add_comm]
    rfl
  have hId := congrArg A.inverse hdiff
  rw [hA.inverse_apply_self,map_smul] at hId
  change (2:ℝ) • midpointEvaluation (A.inverse (greenOperator F))=midpointEvaluation (Z-X)
  rw [hId,map_smul]

end OrientedEndpointChart
end EuclideanMidpointRigidity

