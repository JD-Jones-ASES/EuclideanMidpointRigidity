module

public import EuclideanMidpointRigidity.Basic

/-! # Operator bounds for a Euclidean cubic -/

@[expose] public section

namespace EuclideanMidpointRigidity

variable {d : ℕ}
local notation "E" => Space d

theorem norm_K_le_opNorm (c : Cubic d) (u v : E) :
    ‖K c u v‖ ≤ ‖c‖ * ‖u‖ * ‖v‖ :=
  ((c.val u).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (c.val.le_opNorm u) (norm_nonneg v))

/-- A common upper bound used in the Dirichlet estimates. -/
theorem norm_K_le (c : Cubic d) (u v : E) :
    ‖K c u v‖ ≤ 8 * ‖c‖ * ‖u‖ * ‖v‖ := by
  apply (norm_K_le_opNorm c u v).trans
  nlinarith [mul_nonneg (mul_nonneg (norm_nonneg c) (norm_nonneg u)) (norm_nonneg v)]

theorem K_diagonal_sub (c a : Cubic d) (v w : E) :
    K c v v - K a w w =
      K (c-a) v v + K a (v-w) v + K a w (v-w) := by
  simp [K, map_sub]

theorem norm_K_diagonal_sub_le (c a : Cubic d) (v w : E) :
    ‖K c v v - K a w w‖ ≤
      8 * ‖c-a‖ * ‖v‖ ^ 2 + 8 * ‖a‖ * (‖v‖ + ‖w‖) * ‖v-w‖ := by
  rw [K_diagonal_sub]
  calc
    _ ≤ ‖K (c-a) v v‖ + ‖K a (v-w) v‖ + ‖K a w (v-w)‖ := norm_add₃_le
    _ ≤ 8 * ‖c-a‖ * ‖v‖ * ‖v‖ + 8 * ‖a‖ * ‖v-w‖ * ‖v‖ +
        8 * ‖a‖ * ‖w‖ * ‖v-w‖ :=
      add_le_add (add_le_add (norm_K_le _ _ _) (norm_K_le _ _ _)) (norm_K_le _ _ _)
    _ = _ := by ring

end EuclideanMidpointRigidity
