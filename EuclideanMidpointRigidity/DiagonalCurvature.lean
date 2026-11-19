module

public import EuclideanMidpointRigidity.CurvatureChords
public import EuclideanMidpointRigidity.TiltElimination

/-! # The endpoint law eliminates the diagonal of the remaining curvature term -/

public section
noncomputable section
open Set
open scoped ContDiff InnerProductSpace
namespace EuclideanMidpointRigidity.HorizontalPatch
open Endpoint FixedAxis
variable {d : ℕ} {S : LiftedSection d} (H : HorizontalPatch S)
local notation "E" => Space d
set_option backward.isDefEq.respectTransparency false

include H in
theorem diagonal_curvature {p : E} (hp : p ∈ S.domain) (a : E) {y z w : E} {b : ℝ}
    (hr : Resonant b) (hy : K (S.field p) (S.idempotent p) y=b • y)
    (hz : K (S.field p) (S.idempotent p) z=(2*b) • z) (hw : K (S.field p) (S.idempotent p) w=b • w) :
    (H.freeze hp [] H.inactive_one).component a y y z w=0 := by
  let u := S.idempotent p
  let D := directional S.field (fderiv ℝ S.axis p a)
  let A := fun t : ℝ ↦ TiltData.atPoint D (p+t • u) u y y z w
  let r := ⟪w,K (directions D [y] p) y z⟫_ℝ
  let P := H.freeze hp [] H.inactive_one
  have hz' : directions D [z] p=0 := by
    have hn : ¬Resonant (2*b) := by rcases hr with hb|hb <;> rw [hb] <;> norm_num [Resonant]
    change directional (directional S.field (fderiv ℝ S.axis p a)) z p=0
    rw [H.translated_curvature hp,P.support hz hn,neg_zero]
  simp only [S.idempotent_slice] at hy hz hw
  obtain ⟨W,hW,h₀,hL,hS,hI⟩ := H.curvature_chords hp a y z w hy hz hw
  have hD : ThirdTiltLaws.DiagonalData W A r := by
    refine ⟨hS [y,y,z] u u,hS [y,z] u y,hS [y,y] u z,fun _ _ ↦ rfl,?_⟩
    intro t ht
    have hi (l : E) : directions D [l] (p+t • u)=directions D [l] p := hI t ht l
    simp only [A,TiltData.atPoint,hi,hz',r]
    simp [K]
  have he : r=0 := by
    rcases hr with hb|hb
    · have hL' : ThirdTiltLaws W (2:ℚ) (3:ℚ) A := by
        convert hL using 1 <;> norm_num [hb]
      exact ThirdTiltLaws.eliminate rates_two_three hL' hD hW h₀
    · have hL' : ThirdTiltLaws W (3/5:ℚ) (1/5:ℚ) A := by
        convert hL using 1 <;> norm_num [hb]
      exact ThirdTiltLaws.eliminate rates_three_one_fifths hL' hD hW h₀
  change ⟪w,K (directional (directional S.field (fderiv ℝ S.axis p a)) y p) y z⟫_ℝ=0 at he
  rw [H.translated_curvature hp,K_neg_coeff,inner_neg_right,neg_eq_zero,real_inner_comm] at he
  exact he

end EuclideanMidpointRigidity.HorizontalPatch

