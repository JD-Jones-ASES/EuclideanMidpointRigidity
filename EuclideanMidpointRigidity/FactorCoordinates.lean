module

public import EuclideanMidpointRigidity.MaximumEnvelope
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! # Euclidean coordinates and restriction of a symmetric cubic to a subspace -/

@[expose] public section
noncomputable section
open Set
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity.OrthogonalFactor
variable {d : ℕ} (V : Submodule ℝ (Space d))
local notation "E" => Space d
local notation "F" => Space (Module.finrank ℝ V)
set_option backward.isDefEq.respectTransparency false

def coordinates := (stdOrthonormalBasis ℝ V).repr

def inclusion : F →L[ℝ] E :=
  V.subtypeL.comp (coordinates V).symm.toContinuousLinearEquiv.toContinuousLinearMap

def projection : E →L[ℝ] F :=
  (coordinates V).toContinuousLinearEquiv.toContinuousLinearMap.comp V.orthogonalProjectionOnto

theorem projection_inclusion (v : F) : projection V (inclusion V v)=v := by
  change (coordinates V) (V.orthogonalProjectionOnto ((coordinates V).symm v : V))=v
  rw [V.orthogonalProjectionOnto_mem_subspace_eq_self,LinearIsometryEquiv.apply_symm_apply]

theorem inclusion_projection (x : E) : inclusion V (projection V x)=V.starProjection x := by
  exact congrArg ((↑) : V → E) ((coordinates V).symm_apply_apply (V.orthogonalProjectionOnto x))

theorem inclusion_mem (v : F) : inclusion V v ∈ V := ((coordinates V).symm v).property

theorem inclusion_norm (v : F) : ‖inclusion V v‖=‖v‖ := (coordinates V).symm.norm_map v

theorem projection_norm (v : E) : ‖projection V v‖≤‖v‖ := by
  change ‖(coordinates V) (V.orthogonalProjectionOnto v)‖≤‖v‖
  rw [LinearIsometryEquiv.norm_map]
  exact V.norm_orthogonalProjectionOnto_apply_le v

theorem projection_inner (x : E) (v : F) : ⟪projection V x,v⟫_ℝ=⟪x,inclusion V v⟫_ℝ := by
  change ⟪(coordinates V) (V.orthogonalProjectionOnto x),v⟫_ℝ=_
  rw [LinearIsometryEquiv.inner_map_eq_flip]
  exact V.inner_orthogonalProjectionOnto_eq_of_mem_right _ _

theorem projection_zero_of_orthogonal {x : E} (hx : x ∈ Vᗮ) : projection V x=0 := by
  change (coordinates V) (V.orthogonalProjectionOnto x)=0
  rw [V.orthogonalProjectionOnto_apply_of_mem_orthogonal hx,map_zero]

def restrictBilinear (c : Cubic d) : F →L[ℝ] F →L[ℝ] F :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a ↦ (projection V).comp ((c.val (inclusion V a)).comp (inclusion V))
      map_add' := by intro a b; ext v : 1; simp only [map_add,add_apply,ContinuousLinearMap.comp_apply]
      map_smul' := by intro r a; ext v : 1; simp only [map_smul,smul_apply,ContinuousLinearMap.comp_apply,RingHom.id_apply] }

def restriction : Cubic d →L[ℝ] Cubic (Module.finrank ℝ V) := by
  haveI : FiniteDimensional ℝ (Cubic d) := FiniteDimensional.finiteDimensional_submodule (K := ℝ) (V := E →L[ℝ] E →L[ℝ] E) (cubicSubspace d)
  let L : Cubic d →ₗ[ℝ] Cubic (Module.finrank ℝ V) :=
    { toFun := fun c ↦ ⟨restrictBilinear V c,fun a b ↦ congrArg (projection V) (K_symm c _ _),fun a b e ↦ by
          change ⟪projection V (K c (inclusion V a) (inclusion V b)),e⟫_ℝ=
            ⟪b,projection V (K c (inclusion V a) (inclusion V e))⟫_ℝ
          rw [projection_inner,real_inner_comm _ b,projection_inner,K_selfAdjoint]; exact real_inner_comm _ _⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        exact ContinuousLinearMap.ext fun x ↦ ContinuousLinearMap.ext fun y ↦ map_add (projection V) _ _
      map_smul' := by
        intro r a
        apply Subtype.ext
        exact ContinuousLinearMap.ext fun x ↦ ContinuousLinearMap.ext fun y ↦ map_smul (projection V) r _ }
  exact L.toContinuousLinearMap

theorem restriction_product (c : Cubic d) (a b : F) :
    K (restriction V c) a b=projection V (K c (inclusion V a) (inclusion V b)) := rfl

end EuclideanMidpointRigidity.OrthogonalFactor

