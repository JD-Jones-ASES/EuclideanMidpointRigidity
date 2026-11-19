module

public import EuclideanMidpointRigidity.EndpointCoefficients
public import EuclideanMidpointRigidity.AxialTaylor
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! # The scaled Dirichlet polynomial and its midpoint expansion -/

@[expose] public section
noncomputable section
open Set Polynomial
namespace EuclideanMidpointRigidity.Endpoint

def responsePolynomial (η a b c d h : ℝ) : ℝ[X] :=
  C (h^3)*v₁ a+C (h^4)*v₂ η a b+C (h^5)*v₃ η a b c+C (h^6)*v₄ η a b c d

theorem responsePolynomial_endpoint (η a b c d h x : ℝ) (hx : x= -1 ∨ x=1) :
    (responsePolynomial η a b c d h).eval x=0 := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := coefficient_endpoints η a b c d x hx
  simp [responsePolynomial,h₁,h₂,h₃,h₄]

theorem responsePolynomial_equation (η a b c d h x : ℝ) :
    let p := responsePolynomial η a b c d h
    p.derivative.derivative.eval x=h*η*p.derivative.eval x+h^2*sourceTaylor a b c d (h*x)-
      h^7*η*(v₄ η a b c d).derivative.eval x := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := coefficient_equations η a b c d
  simp only [responsePolynomial,derivative_add,derivative_C_mul,h₁,h₂,h₃,h₄,eval_add,eval_mul,
    eval_C,eval_X,eval_pow,sourceTaylor]
  ring

theorem polynomial_interval_bound (p : ℝ[X]) : ∃ L : ℝ, 0≤L ∧ ∀ x ∈ Icc (-1:ℝ) 1, |p.eval x|≤L := by
  obtain ⟨x,_,hx⟩ := isCompact_Icc.exists_isMaxOn (show (Icc (-1:ℝ) 1).Nonempty from ⟨0,by norm_num⟩)
    p.continuous.continuousOn.abs
  exact ⟨_,abs_nonneg _,fun t ht ↦ hx ht⟩

theorem responsePolynomial_slope_bound (η a b c d : ℝ) :
    ∃ L : ℝ, 0≤L ∧ ∀ h ∈ Icc (0:ℝ) 1, ∀ x ∈ Icc (-1:ℝ) 1,
      |(responsePolynomial η a b c d h).derivative.eval x|≤L*h^3 := by
  obtain ⟨L₁,h₁,e₁⟩ := polynomial_interval_bound (v₁ a).derivative
  obtain ⟨L₂,h₂,e₂⟩ := polynomial_interval_bound (v₂ η a b).derivative
  obtain ⟨L₃,h₃,e₃⟩ := polynomial_interval_bound (v₃ η a b c).derivative
  obtain ⟨L₄,h₄,e₄⟩ := polynomial_interval_bound (v₄ η a b c d).derivative
  refine ⟨L₁+L₂+L₃+L₄,by positivity,?_⟩
  intro h hh x hx
  have hp (n : ℕ) (hn : 3≤n) (v L : ℝ) (hv : |v|≤L) : |h^n*v|≤L*h^3 := by
    rw [abs_mul,abs_of_nonneg (pow_nonneg hh.1 n),mul_comm]
    exact mul_le_mul hv (pow_le_pow_of_le_one hh.1 hh.2 hn) (pow_nonneg hh.1 _) ((abs_nonneg _).trans hv)
  simp only [responsePolynomial,derivative_add,derivative_C_mul,eval_add,eval_mul,eval_C]
  apply (abs_add_le _ _).trans
  apply (add_le_add (abs_add_le _ _) (le_refl _)).trans
  apply (add_le_add (add_le_add (abs_add_le _ _) (le_refl _)) (le_refl _)).trans
  simp only [add_mul]
  exact add_le_add (add_le_add (add_le_add (hp 3 (by decide) _ _ (e₁ x hx)) (hp 4 (by decide) _ _ (e₂ x hx)))
    (hp 5 (by decide) _ _ (e₃ x hx))) (hp 6 (by decide) _ _ (e₄ x hx))

/-- The polynomial evaluated at the cubic approximation of the physical midpoint
has a continuous remainder after its two possible coefficients. -/
theorem responsePolynomial_midpoint (η a b c d : ℝ) :
    ∃ r : ℝ → ℝ, Continuous r ∧ ∀ h : ℝ,
      (responsePolynomial η a b c d h).eval (h/2-h^3/12)=
        h^4*fourth η a b+h^6*sixth η a b c d+h^8*r h := by
  let A := a/6
  let B := η*a/24+b/12
  let D := η*a/12
  let F := η^2*a/120+η*b/60+c/20
  let G := η^2*a/36
  let H := η^3*a/720+η^2*b/360+η*c/120+d/30
  let I := η^3*a/144
  let J := 7*η^3*a/720-η^2*b/120-η*c/40
  let r := fun h : ℝ ↦
    let g := 1/2-h^2/12;
    -(A*(g^2+g/2+1/4)-D*(g+1/2)-F+G)/12+
      B*g^4-G*g^3+J*g^2+h^2*(F*g^5-I*g^4)+h^4*H*g^6
  refine ⟨r,by dsimp [r]; fun_prop,?_⟩
  intro h
  simp only [responsePolynomial,eval_add,eval_sub,eval_mul,eval_pow,eval_C,eval_X,eval_one,v₁,v₂,v₃,v₄,
    fourth_eq,sixth_eq,r,A,B,D,F,G,H,I,J]
  ring

end EuclideanMidpointRigidity.Endpoint

