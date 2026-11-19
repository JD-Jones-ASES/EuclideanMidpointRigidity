module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Tactic

/-! # Real symmetric cubic tensors in Euclidean space -/

@[expose] public section

noncomputable section

open Set Metric
open scoped ContDiff InnerProductSpace

namespace EuclideanMidpointRigidity

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Raising the last index identifies a symmetric cubic with a symmetric
bilinear product whose left multiplication operators are self-adjoint. -/
def cubicSubspace (d : ℕ) :
    Submodule ℝ (Space d →L[ℝ] Space d →L[ℝ] Space d) where
  carrier := {B | (∀ u v, B u v = B v u) ∧
    ∀ u v w, ⟪B u v, w⟫_ℝ = ⟪v, B u w⟫_ℝ}
  zero_mem' := by simp
  add_mem' := by
    rintro B D ⟨hB, hB'⟩ ⟨hD, hD'⟩
    exact ⟨fun u v ↦ by simp [hB u v, hD u v],
      fun u v w ↦ by simp [inner_add_left, inner_add_right, hB', hD']⟩
  smul_mem' := by
    rintro a B ⟨hB, hB'⟩
    exact ⟨fun u v ↦ by simp [hB u v],
      fun u v w ↦ by simp [real_inner_smul_left, real_inner_smul_right, hB']⟩

abbrev Cubic (d : ℕ) : Type := cubicSubspace d

section
set_option backward.isDefEq.respectTransparency false

instance cubicNormedAddCommGroup (d : ℕ) : NormedAddCommGroup (Cubic d) :=
  Submodule.normedAddCommGroup (𝕜 := ℝ) (E := Space d →L[ℝ] Space d →L[ℝ] Space d)
    (cubicSubspace d)

instance cubicNormedSpace (d : ℕ) : NormedSpace ℝ (Cubic d) :=
  Submodule.normedSpace (𝕜 := ℝ) (R := ℝ) (E := Space d →L[ℝ] Space d →L[ℝ] Space d)
    (cubicSubspace d)

end

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

/-- The Christoffel tensor with one index raised by the Euclidean metric. -/
def K (c : Coeff) (u v : E) : E := c.val u v

noncomputable abbrev midpointTime : ℝ := 1 / 2

/-- The vector-valued quartic in Theorem 9.2 of Nielsen and Okamura. -/
def obstruction (c : Coeff) (J : E →L[ℝ] Coeff) (h : E) : E :=
  2 • K c h (K (J h) h h) + 5 • K (J (K c h h)) h h - 4 • K (J h) h (K c h h)

theorem K_symm (c : Coeff) (u v : E) : K c u v = K c v u := c.property.1 u v

theorem K_selfAdjoint (c : Coeff) (u v w : E) :
    ⟪K c u v, w⟫_ℝ = ⟪v, K c u w⟫_ℝ := c.property.2 u v w

@[simp] theorem K_add_coeff (c a : Coeff) (u v : E) :
    K (c + a) u v = K c u v + K a u v := rfl

@[simp] theorem K_sub_coeff (c a : Coeff) (u v : E) :
    K (c - a) u v = K c u v - K a u v := rfl

@[simp] theorem K_neg_coeff (c : Coeff) (u v : E) : K (-c) u v = -K c u v := rfl

@[simp] theorem K_smul_coeff (r : ℝ) (c : Coeff) (u v : E) :
    K (r • c) u v = r • K c u v := rfl

@[simp] theorem K_add_left (c : Coeff) (u v w : E) :
    K c (u + v) w = K c u w + K c v w := by simp [K]

@[simp] theorem K_add_right (c : Coeff) (u v w : E) :
    K c u (v + w) = K c u v + K c u w := by simp [K]

@[simp] theorem K_smul_left (c : Coeff) (r : ℝ) (u v : E) :
    K c (r • u) v = r • K c u v := by simp [K]

@[simp] theorem K_smul_right (c : Coeff) (r : ℝ) (u v : E) :
    K c u (r • v) = r • K c u v := by simp [K]

@[simp] theorem K_neg_left (c : Coeff) (u v : E) : K c (-u) v = -K c u v := by simp [K]

@[simp] theorem K_neg_right (c : Coeff) (u v : E) : K c u (-v) = -K c u v := by simp [K]

end EuclideanMidpointRigidity
