module

public import EuclideanMidpointRigidity.SixthRecursion

/-! # Evaluation of the full sixth-order formal midpoint coefficient -/

@[expose] public section
namespace EuclideanMidpointRigidity.Jet
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

theorem positive_boundary_equations : boundaryEquations 1 = true := by decide +kernel

theorem negative_boundary_equations : boundaryEquations (-1) = true := by decide +kernel

theorem quartic_recursion : same (midpointCoefficient 4) quartic = true := by decide +kernel

theorem sixth_recursion : same (midpointCoefficient 6) (affineSixth ++ higherSixth) = true := by
  decide +kernel

theorem sixth_value {V : Type*} [AddCommGroup V] [Module ℝ V] (f : Tree → V) :
    value (midpointCoefficient 6) f 0 = value affineSixth f 0 + value higherSixth f 0 := by
  rw [same_sound sixth_recursion]
  simp [value]

end EuclideanMidpointRigidity.Jet
