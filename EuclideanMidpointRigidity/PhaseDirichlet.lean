module

public import EuclideanMidpointRigidity.GeodesicBVP

/-! # Recovering phase paths and endpoint data from a Dirichlet equation -/

@[expose] public section
noncomputable section
open Set
namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d
local notation "P" => PhaseCurve d
local notation "Q" => AccelerationCurve d

theorem green_phase_eq {y : P} {a : Q} {L R : E} (hy : y=affinePhase L R+greenOperator a) (t : UnitInterval) :
    (bvpPosition L R a t,bvpVelocity L R a t)=y t := by
  simpa only [bvpPosition,bvpVelocity,ContinuousMap.add_apply,affinePhase,ContinuousMap.coe_mk,
    Prod.mk_add_mk,greenOperator_apply] using (congrArg (fun z : P ↦ z t) hy).symm

/-- Any solution of the forced second-order equation with these endpoint values gives
the same continuous phase path as the Green operator. -/
theorem green_phase_of_derivatives {y : P} {a : Q} {L R : E} {x v : ℝ → E}
    (hphase : ∀ t : UnitInterval, y t=(x t,v t))
    (hx : ∀ t ∈ UnitInterval, HasDerivAt x (v t) t)
    (hv : ∀ t ∈ UnitInterval, HasDerivAt v (pathExtend a t) t) (h₀ : x 0=L) (h₁ : x 1=R) :
    y=affinePhase L R+greenOperator a := by
  let X := fun t ↦ x t-bvpPosition L R a t
  let V := fun t ↦ v t-bvpVelocity L R a t
  have dX (t : ℝ) (ht : t ∈ UnitInterval) : HasDerivAt X (V t) t :=
    (hx t ht).fun_sub (hasDerivAt_bvpPosition L R a t)
  have dV (t : ℝ) (ht : t ∈ UnitInterval) : HasDerivAt V 0 t := by
    simpa only [V,sub_self] using (hv t ht).fun_sub (hasDerivAt_bvpVelocity L R a t)
  have hX₀ : X 0=0 := by simp [X,h₀]
  have hX₁ : X 1=0 := by simp [X,h₁]
  ext t : 1
  rw [hphase]
  apply Prod.ext
  · change x t=bvpPosition L R a t
    exact sub_eq_zero.mp (dirichlet_unique X V dX dV hX₀ hX₁ t t.property)
  · change v t=bvpVelocity L R a t
    have hb := dirichlet_velocity_bound X V (fun _ ↦ 0) 0 dX dV (by simp) hX₀ hX₁ t t.property
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)))

end EuclideanMidpointRigidity

