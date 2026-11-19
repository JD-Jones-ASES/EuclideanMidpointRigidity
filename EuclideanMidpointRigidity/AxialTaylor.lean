module

public import EuclideanMidpointRigidity.SpatialTaylorBound
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Taylor estimates for the axial source and the physical midpoint -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.Endpoint

def sourceTaylor (a b c d x : ℝ) := a*x+b*x^2+c*x^3+d*x^4

def HasFourCoefficients (f : ℝ → ℝ) (a b c d : ℝ) : Prop :=
  ∃ ρ M : ℝ, 0<ρ ∧ 0≤M ∧ ∀ x, |x|<ρ → |f x-sourceTaylor a b c d x|≤M*|x|^5

theorem hasFourCoefficients_of_derivatives {W : Set ℝ} {f : ℝ → ℝ} (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    (hp : 0 ∈ W) {a b c d : ℝ} (h₀ : f 0=0) (h₁ : iteratedDeriv 1 f 0=a)
    (h₂ : iteratedDeriv 2 f 0=2*b) (h₃ : iteratedDeriv 3 f 0=6*c) (h₄ : iteratedDeriv 4 f 0=24*d) :
    HasFourCoefficients f a b c d := by
  obtain ⟨ρ,M,hρ,hM,hb⟩ := exists_spatialTaylor_bound hW hf hp 4
  refine ⟨ρ,M,hρ,hM,?_⟩
  intro x hx
  have ht : spatialTaylor f 4 0 x=sourceTaylor a b c d x := by
    simp only [spatialTaylor,Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,
      iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
      iteratedDeriv_zero,h₀,h₁,h₂,h₃,h₄,smul_eq_mul,sourceTaylor]
    norm_num [Nat.factorial]
    ring
  simpa only [zero_add,Real.norm_eq_abs,ht] using hb x hx

theorem log_cosh_coefficients : HasFourCoefficients (fun x : ℝ ↦ Real.log (Real.cosh x)) 0 (1/2) 0 (-1/12) := by
  let m := fun x : ℝ ↦ Real.log (Real.cosh x)
  let T := Real.tanh
  have hm : ContDiff ℝ ∞ m := Real.contDiff_cosh.log (fun x ↦ (Real.cosh_pos x).ne')
  have d₁ (x : ℝ) : HasDerivAt m (T x) x := by
    simpa only [m,T,Real.tanh_eq_sinh_div_cosh] using (Real.hasDerivAt_cosh x).log (Real.cosh_pos x).ne'
  have d₂ (x : ℝ) : HasDerivAt T (1-(T x)^2) x := by
    have h := (Real.hasDerivAt_sinh x).fun_div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
    rw [show T=fun u ↦ Real.sinh u/Real.cosh u from funext Real.tanh_eq_sinh_div_cosh]
    convert h using 1
    field_simp [(Real.cosh_pos x).ne']
  have d₃ (x : ℝ) : HasDerivAt (fun u ↦ 1-(T u)^2) (-2*T x*(1-(T x)^2)) x := by
    convert ((d₂ x).fun_pow 2).const_sub 1 using 1 <;> first | rfl | ring
  have t₀ : T 0=0 := Real.tanh_zero
  have d₄ : HasDerivAt (fun u ↦ -2*T u*(1-(T u)^2)) (-2) 0 := by
    simpa only [t₀,zero_pow (by norm_num : 2≠0),sub_zero,mul_one,mul_zero,zero_mul,add_zero] using
      ((d₂ 0).const_mul (-2)).fun_mul (d₃ 0)
  have h₁ : iteratedDeriv 1 m=T := by rw [iteratedDeriv_one]; exact funext fun x ↦ (d₁ x).deriv
  have h₂ : iteratedDeriv 2 m=fun x ↦ 1-(T x)^2 := by rw [iteratedDeriv_succ,h₁]; exact funext fun x ↦ (d₂ x).deriv
  have h₃ : iteratedDeriv 3 m=fun x ↦ -2*T x*(1-(T x)^2) := by rw [iteratedDeriv_succ,h₂]; exact funext fun x ↦ (d₃ x).deriv
  apply hasFourCoefficients_of_derivatives isOpen_univ hm.contDiffOn (mem_univ 0)
  · simp [m]
  · rw [h₁,t₀]
  · norm_num [h₂,t₀]
  · norm_num [h₃,t₀]
  · change iteratedDeriv 4 m 0=_
    rw [iteratedDeriv_succ,h₃,d₄.deriv]
    norm_num

end EuclideanMidpointRigidity.Endpoint

