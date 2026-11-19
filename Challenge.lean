module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-! # Nielsen–Okamura Conjecture 9.1 in Euclidean space -/

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

/-- An affinely parametrized geodesic for the connection with coefficient `σ K`. -/
def IsGeodesicSegment (C : E → Coeff) (σ : ℝ) (γ v : ℝ → E) : Prop :=
  (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt γ (v t) t) ∧
  (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt v (-σ • K (C (γ t)) (v t) (v t)) t)

/-- Position and velocity stay in a small neighborhood of the zero-velocity phase. -/
def IsShortGeodesic (C : E → Coeff) (σ : ℝ) (p : E) (r : ℝ)
    (P Q : E) (γ v : ℝ → E) : Prop :=
  IsGeodesicSegment C σ γ v ∧ γ 0 = P ∧ γ 1 = Q ∧
    ∀ t ∈ Icc (0 : ℝ) 1, ‖γ t - p‖ < r ∧ ‖v t‖ < r

/-- The midpoint of the unique short geodesic for each pair of nearby endpoints. -/
def IsCanonicalLocalMidpoint (Ω : Set E) (C : E → Coeff) (σ : ℝ)
    (p : E) (r : ℝ) (W : Set (E × E)) (A : E → E → E) : Prop :=
  0 < r ∧ ball p r ⊆ Ω ∧ IsOpen W ∧ (p, p) ∈ W ∧
  ∀ P Q, (P, Q) ∈ W → ∃ γ v,
    IsShortGeodesic C σ p r P Q γ v ∧ A P Q = γ midpointTime ∧
    ∀ γ' v', IsShortGeodesic C σ p r P Q γ' v' →
      ∀ t ∈ Icc (0 : ℝ) 1, γ' t = γ t ∧ v' t = v t

/-- The canonical midpoints of the dual connections are complementary near the diagonal. -/
def LocalMidpointInvariance (Ω : Set E) (C : E → Coeff) : Prop :=
  ∀ p ∈ Ω, ∃ rPlus rMinus W APlus AMinus,
    IsCanonicalLocalMidpoint Ω C 1 p rPlus W APlus ∧
    IsCanonicalLocalMidpoint Ω C (-1) p rMinus W AMinus ∧
    ∀ P Q, (P, Q) ∈ W → APlus P Q + AMinus P Q = P + Q

/-- Nielsen–Okamura Conjecture 9.1. A smooth symmetric cubic with complementary
dual geodesic midpoints on a connected open Euclidean domain is constant. -/
theorem euclidean_midpoint_rigidity (Ω : Set E) (C : E → Coeff)
    (openΩ : IsOpen Ω) (connectedΩ : IsPreconnected Ω)
    (smoothC : ContDiffOn ℝ ∞ C Ω) (complementary : LocalMidpointInvariance Ω C) :
    ∃ c : Coeff, ∀ p ∈ Ω, C p = c := by
  sorry

end EuclideanMidpointRigidity
