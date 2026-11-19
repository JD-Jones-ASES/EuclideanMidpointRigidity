module

public import EuclideanMidpointRigidity.TiltedOddJet
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Real exponential solutions of the third-order line equation -/

public section
noncomputable section
open Set
open scoped ContDiff
namespace EuclideanMidpointRigidity.Endpoint

theorem smooth_line_derivative {W : Set ℝ} {f : ℝ → ℝ} (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W) (n : ℕ) :
    ContDiffOn ℝ ∞ (iteratedDeriv n f) W := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv_of_isOpen hW (by simp)

theorem hasDerivAt_line_derivative {W : Set ℝ} {f : ℝ → ℝ} (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    {x : ℝ} (hx : x ∈ W) (n : ℕ) : HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n+1) f x) x := by
  rw [iteratedDeriv_succ]
  exact (((smooth_line_derivative hW hf n).contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp)).hasDerivAt

theorem exponential_form_of_third {W : Set ℝ} {f : ℝ → ℝ} {r p : ℝ} (hW : IsOpen W) (hc : IsPreconnected W)
    (hf : ContDiffOn ℝ ∞ f W) (hp : p ∈ W) (hr : r≠0) (hode : ∀ x ∈ W, iteratedDeriv 3 f x=r^2*iteratedDeriv 1 f x) :
    ∃ a b c : ℝ, ∀ x ∈ W, f x=a+b*Real.exp (r*x)+c*Real.exp (-(r*x)) := by
  let g := iteratedDeriv 1 f
  let k := iteratedDeriv 2 f
  let A := fun x ↦ r^2*f x-k x
  let B := fun x ↦ Real.exp (-(r*x))*(k x+r*g x)
  let C := fun x ↦ Real.exp (r*x)*(k x-r*g x)
  have constancy (F : ℝ → ℝ) (hF : ∀ x ∈ W, HasDerivAt F 0 x) : ∀ x ∈ W, F x=F p :=
    fun x hx ↦ hW.is_const_of_deriv_eq_zero hc (fun y hy ↦ (hF y hy).differentiableAt.differentiableWithinAt)
      (fun y hy ↦ (hF y hy).deriv) hx hp
  have d0 (x : ℝ) (hx : x ∈ W) : HasDerivAt f (g x) x := by simpa [g] using hasDerivAt_line_derivative hW hf hx 0
  have d1 (x : ℝ) (hx : x ∈ W) : HasDerivAt g (k x) x := hasDerivAt_line_derivative hW hf hx 1
  have d2 (x : ℝ) (hx : x ∈ W) : HasDerivAt k (r^2*g x) x := (hode x hx) ▸ hasDerivAt_line_derivative hW hf hx 2
  have dplus (x : ℝ) : HasDerivAt (fun s ↦ Real.exp (r*s)) (Real.exp (r*x)*r) x := by
    simpa only [Function.comp_def,id_eq,mul_one] using (Real.hasDerivAt_exp (r*x)).comp x ((hasDerivAt_id x).const_mul r)
  have dminus (x : ℝ) : HasDerivAt (fun s ↦ Real.exp (-(r*s))) (Real.exp (-(r*x))*(-r)) x := by
    simpa only [Function.comp_def,id_eq,mul_one] using (Real.hasDerivAt_exp (-(r*x))).comp x ((hasDerivAt_id x).const_mul r).fun_neg
  have hA := constancy A (fun x hx ↦ by convert ((d0 x hx).const_mul (r^2)).fun_sub (d2 x hx) using 1 <;> first | rfl | ring)
  have hB := constancy B (fun x hx ↦ by
    convert (dminus x).fun_mul ((d2 x hx).fun_add ((d1 x hx).const_mul r)) using 1 <;> first | rfl | ring)
  have hC := constancy C (fun x hx ↦ by
    convert (dplus x).fun_mul ((d2 x hx).fun_sub ((d1 x hx).const_mul r)) using 1 <;> first | rfl | ring)
  refine ⟨A p/r^2,B p/(2*r^2),C p/(2*r^2),?_⟩
  intro x hx
  rw [← hA x hx,← hB x hx,← hC x hx]
  dsimp only [A,B,C]
  rw [Real.exp_neg]
  field_simp [hr,(Real.exp_pos (r*x)).ne']
  <;> ring

end EuclideanMidpointRigidity.Endpoint

