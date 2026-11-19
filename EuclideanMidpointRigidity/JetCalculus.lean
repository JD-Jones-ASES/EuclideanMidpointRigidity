module

public import EuclideanMidpointRigidity.JetTrees
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # Differentiation and evaluation of the time polynomials -/

@[expose] public section
namespace EuclideanMidpointRigidity.Jet

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem value_append (p q : TimePolynomial) (f : Tree → V) (t : ℝ) :
    value (p++q) f t = value p f t+value q f t := by simp [value]

theorem value_atTime (p : TimePolynomial) (f : Tree → V) (s : ℚ) (t : ℝ) :
    value (atTime p s) f t = value p f (s:ℝ) := by
  rw [atTime,value_collect]
  induction p with
  | nil => rfl
  | cons m ms ih =>
    exact congrArg₂ (·+·) (show ({m with power := 0, coeff := m.coeff*s^m.power}:Term).value f t =
      m.value f (s:ℝ) by simp [Term.value]) ih

private theorem hasDerivAt_term (m : Term) (f : Tree → V) (t : ℝ) :
    HasDerivAt (m.value f) (((m.coeff:ℝ)*m.power*t^(m.power-1)) • f m.tree) t := by
  have h := ((hasDerivAt_pow m.power t).const_mul (m.coeff:ℝ)).smul_const (f m.tree)
  change HasDerivAt (fun x : ℝ ↦ ((m.coeff:ℝ)*x^m.power) • f m.tree) _ t
  simpa only [mul_assoc] using h

theorem hasDerivAt_value (p : TimePolynomial) (f : Tree → V) (t : ℝ) :
    HasDerivAt (value p f) (value (differentiate p) f t) t := by
  induction p with
  | nil => exact hasDerivAt_const _ _
  | cons m ms ih =>
    have h := (hasDerivAt_term m f t).fun_add ih
    change HasDerivAt (fun x ↦ m.value f x + value ms f x) _ t
    by_cases hz : m.power = 0
    · simpa [differentiate, hz] using h
    · simp only [differentiate, List.filterMap_cons, hz, reduceIte]
      change HasDerivAt _ (({m with power := m.power-1, coeff := m.coeff*m.power}:Term).value f t +
        value (differentiate ms) f t) t
      simpa [Term.value] using h

end EuclideanMidpointRigidity.Jet
