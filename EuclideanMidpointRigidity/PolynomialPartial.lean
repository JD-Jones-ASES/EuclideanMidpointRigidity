module

public import EuclideanMidpointRigidity.SmoothPolynomialFamily
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

/-! # Formal partial derivatives as real directional derivatives -/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity
variable {n : ℕ}

def coordinateStep (z : Fin n → ℝ) (i : Fin n) (t : ℝ) (j : Fin n) : ℝ :=
  z j+t*(if j=i then 1 else 0)

@[simp] theorem coordinateStep_zero (z : Fin n → ℝ) (i : Fin n) : coordinateStep z i 0=z := by
  funext j
  simp [coordinateStep]

theorem hasDerivAt_coordinateStep (z : Fin n → ℝ) (i j : Fin n) :
    HasDerivAt (fun t ↦ coordinateStep z i t j) (if j=i then 1 else 0) 0 := by
  simpa [coordinateStep] using (((hasDerivAt_id (0:ℝ)).mul_const (if j=i then (1:ℝ) else 0)).const_add (z j))

theorem hasDerivAt_eval_coordinate (f : MvPolynomial (Fin n) ℝ) (z : Fin n → ℝ) (i : Fin n) :
    HasDerivAt (fun t ↦ MvPolynomial.eval (coordinateStep z i t) f)
      (MvPolynomial.eval z (MvPolynomial.pderiv i f)) 0 := by
  induction f using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const (0:ℝ) a
  | add f g hf hg =>
    simpa only [map_add] using hf.fun_add hg
  | mul_X f j hf =>
    have h := hf.fun_mul (hasDerivAt_coordinateStep z i j)
    by_cases hij : j=i
    · subst j
      simpa [MvPolynomial.pderiv_mul,mul_comm,add_comm] using h
    · simpa [MvPolynomial.pderiv_mul,hij,coordinateStep,mul_comm] using h

end EuclideanMidpointRigidity

