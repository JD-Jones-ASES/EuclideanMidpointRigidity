module

public import EuclideanMidpointRigidity.ForcedChord
public import EuclideanMidpointRigidity.FirstTiltCoefficients
public import EuclideanMidpointRigidity.TripleResponses

/-! # Linear responses to the spatial derivative of an axial product -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff InnerProductSpace Topology
namespace EuclideanMidpointRigidity
open Endpoint
variable {d : ℕ}
local notation "E" => Space d
local notation "Op" => E →L[ℝ] E
local notation "P" => PhaseCurve d
local notation "Q" => AccelerationCurve d

def chordWeight (h : ℝ) (hh : 0<h) : C(UnitInterval,ℝ) :=
  ⟨fun t ↦ (chordSpeed h t)^2,(continuousOn_iff_continuous_domRestrict.mp
    (HasDerivAt.continuousOn fun t ht ↦ hasDerivAt_chordSpeed hh.le ht)).pow 2⟩

def weightedPosition (h : ℝ) (hh : 0<h) : P →L[ℝ] Op →L[ℝ] Q := by
  let w := chordWeight h hh
  let a := fun (Y : P) (M : Op) ↦ (⟨fun t ↦ w t • M (Y t).1,
    w.continuous.smul (M.continuous.comp (continuous_fst.comp Y.continuous))⟩ : Q)
  let L := LinearMap.mk₂ ℝ a
    (by intro X Y M; ext t : 1; simp [a,map_add,smul_add])
    (by intro r X M; ext t : 1; simp [a,smul_comm r])
    (by intro X L M; ext t : 1; simp [a,smul_add])
    (by intro r X M; ext t : 1; simp [a,smul_comm r])
  refine LinearMap.mkContinuous₂ («E» := P) (F := Op) (G := Q) (σ₁₃ := RingHom.id ℝ) (σ₂₃ := RingHom.id ℝ) L ‖w‖ ?_
  intro Y M
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  change ‖w t • M (Y t).1‖≤_
  rw [norm_smul]
  have hY : ‖(Y t).1‖≤‖Y‖ := (norm_fst_le (Y t)).trans (Y.norm_coe_le_norm t)
  calc
    _ ≤ ‖w‖*(‖M‖*‖Y‖) := mul_le_mul (w.norm_coe_le_norm t)
      ((M.le_opNorm _).trans (mul_le_mul_of_nonneg_left hY (norm_nonneg _))) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by ring

theorem weightedPosition_apply (h : ℝ) (hh : 0<h) (Y : P) (M : Op) (t : UnitInterval) :
    weightedPosition h hh Y M t=(chordSpeed h t)^2 • M (Y t).1 := rfl

def Endpoint.centeredProfile (k h : ℝ) : ChordProfile k where
  value := centeredCoordinate k h
  slope s := Real.exp (k*s)
  first s := (rateCoordinate_diff k s).sub_const _
  second s := by simpa only [mul_comm k] using exp_line_diff k s

theorem Endpoint.centered_ends (k h : ℝ) (w : E) :
    ((centeredProfile k h).ends h w).swap= -((centeredProfile k h).ends h w) := by
  apply Prod.ext <;> dsimp [ChordProfile.ends,centeredProfile,centeredCoordinate] <;> module

end EuclideanMidpointRigidity

