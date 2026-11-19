module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Tactic

/-! # Taylor coefficients of the scalar endpoint equation

Write the physical line coordinate as `s = h*x`, with endpoints `x = ±1`.
For a source vanishing at zero, let `f₁,…,f₄` be its ordinary Taylor coefficients.
The coefficient of `h^(j+2)` in the Dirichlet solution is the polynomial `vⱼ`.
It has zero boundary values and second derivative `η*vⱼ₋₁' + fⱼ*x^j`.
The midpoint in these coordinates is `log(cosh h)/h = h/2 - h³/12 + O(h⁵)`.
-/

@[expose] public section
noncomputable section

namespace EuclideanMidpointRigidity.Endpoint
open Polynomial

def v₁ (f₁ : ℝ) : ℝ[X] := C (f₁/6) * (X^3-X)

def v₂ (η f₁ f₂ : ℝ) : ℝ[X] :=
  C (η*f₁/24 + f₂/12) * (X^4-1) - C (η*f₁/12) * (X^2-1)

def v₃ (η f₁ f₂ f₃ : ℝ) : ℝ[X] :=
  C (η^2*f₁/120 + η*f₂/60 + f₃/20) * (X^5-X) -
    C (η^2*f₁/36) * (X^3-X)

def v₄ (η f₁ f₂ f₃ f₄ : ℝ) : ℝ[X] :=
  C (η^3*f₁/720 + η^2*f₂/360 + η*f₃/120 + f₄/30) * (X^6-1) -
    C (η^3*f₁/144) * (X^4-1) +
    C (7*η^3*f₁/720 - η^2*f₂/120 - η*f₃/40) * (X^2-1)

/-- These polynomials solve all four forced coefficient equations. -/
theorem coefficient_equations (η f₁ f₂ f₃ f₄ : ℝ) :
    (v₁ f₁).derivative.derivative = C f₁ * X ∧
    (v₂ η f₁ f₂).derivative.derivative = C η * (v₁ f₁).derivative + C f₂ * X^2 ∧
    (v₃ η f₁ f₂ f₃).derivative.derivative =
      C η * (v₂ η f₁ f₂).derivative + C f₃ * X^3 ∧
    (v₄ η f₁ f₂ f₃ f₄).derivative.derivative =
      C η * (v₃ η f₁ f₂ f₃).derivative + C f₄ * X^4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext n <;>
    simp only [coeff_derivative, v₁, v₂, v₃, v₄, coeff_add, coeff_sub, coeff_C_mul,
      coeff_X_pow, coeff_X, coeff_one] <;>
    (by_cases h : n < 6
     · interval_cases n <;> norm_num <;> ring
     · split_ifs <;> first | omega | simp_all)

theorem coefficient_endpoints (η f₁ f₂ f₃ f₄ x : ℝ) (hx : x = -1 ∨ x = 1) :
    (v₁ f₁).eval x = 0 ∧ (v₂ η f₁ f₂).eval x = 0 ∧
    (v₃ η f₁ f₂ f₃).eval x = 0 ∧ (v₄ η f₁ f₂ f₃ f₄).eval x = 0 := by
  rcases hx with rfl | rfl <;> norm_num [v₁, v₂, v₃, v₄]

/-- Evaluation of the order-four term at the scaled midpoint. -/
def fourth (η f₁ f₂ : ℝ) : ℝ :=
  (v₁ f₁).coeff 1 / 2 + (v₂ η f₁ f₂).coeff 0

/-- Only five monomials contribute at order six. -/
def sixth (η f₁ f₂ f₃ f₄ : ℝ) : ℝ :=
  -(v₁ f₁).coeff 1 / 12 + (v₁ f₁).coeff 3 / 8 +
    (v₂ η f₁ f₂).coeff 2 / 4 + (v₃ η f₁ f₂ f₃).coeff 1 / 2 +
    (v₄ η f₁ f₂ f₃ f₄).coeff 0

theorem fourth_eq (η f₁ f₂ : ℝ) :
    fourth η f₁ f₂ = (f₁*(η-2) - 2*f₂)/24 := by
  norm_num [fourth, v₁, v₂, coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one]
  ring

theorem sixth_eq (η f₁ f₂ f₃ f₄ : ℝ) :
    sixth η f₁ f₂ f₃ f₄ =
      ((-3*η^3+7*η^2-15*η+25)*f₁ + (4*η^2-6*η)*f₂ +
        (12*η-18)*f₃ - 24*f₄)/720 := by
  simp only [sixth, v₁, v₂, v₃, v₄, coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one]
  norm_num
  ring

/-- For the source `exp(κ*s)*sin(ω*s)`, a nonzero real frequency leaves a
nonzero Dirichlet midpoint coefficient by degree six. -/
theorem oscillatory_coefficients (η κ ω : ℝ) (hκ : 0 ≤ κ) (hω : ω ≠ 0) :
    fourth η ω (κ*ω) ≠ 0 ∨
      sixth η ω (κ*ω) ((3*κ^2*ω-ω^3)/6) ((κ^3*ω-κ*ω^3)/6) ≠ 0 := by
  rw [fourth_eq, sixth_eq]
  by_cases hη : η = 2*κ+2
  · right
    subst η
    have hpos : 0 < 21*κ^2+42*κ+ω^2+1 := by positivity
    have hn := mul_ne_zero hω (ne_of_gt hpos)
    intro h
    apply hn
    linarith only [h]
  · left
    have hn := mul_ne_zero hω (sub_ne_zero.mpr hη)
    intro h
    apply hn
    linarith only [h]

end EuclideanMidpointRigidity.Endpoint
