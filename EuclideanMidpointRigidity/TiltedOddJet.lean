module

public import EuclideanMidpointRigidity.AxialTaylor
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Taylor coefficients of a reflected source with exponential tilt -/

@[expose] public section
noncomputable section
open Set
open scoped ContDiff
namespace EuclideanMidpointRigidity.Endpoint

def oddTilt (κ : ℝ) (f : ℝ → ℝ) (p s : ℝ) := Real.exp (κ*s)*(f (p+s)-f (p-s))

theorem oddTilt_coefficients {W : Set ℝ} {f : ℝ → ℝ} (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    {p : ℝ} (hp : p ∈ W) (κ : ℝ) :
    let a := iteratedDeriv 1 f p
    let c := iteratedDeriv 3 f p
    HasFourCoefficients (oddTilt κ f p) (2*a) (2*κ*a) (κ^2*a+c/3) ((κ^3*a+κ*c)/3) := by
  let u := fun s : ℝ ↦ p+s
  let v := fun s : ℝ ↦ p-s
  let D := u ⁻¹' W ∩ v ⁻¹' W
  have hu : ContDiff ℝ ∞ u := contDiff_const.add contDiff_id
  have hv : ContDiff ℝ ∞ v := contDiff_const.sub contDiff_id
  have hD : IsOpen D := (hW.preimage hu.continuous).inter (hW.preimage hv.continuous)
  have h₀ : 0 ∈ D := by simp [D,u,v,hp]
  have h₁ : ContDiffOn ℝ ∞ (f ∘ u) D := hf.comp hu.contDiffOn (fun _ hx ↦ hx.1)
  have h₂ : ContDiffOn ℝ ∞ (f ∘ v) D := hf.comp hv.contDiffOn (fun _ hx ↦ hx.2)
  let F := (f ∘ u)-(f ∘ v)
  let G := fun s : ℝ ↦ Real.exp (κ*s)
  have hF : ContDiffOn ℝ ∞ F D := h₁.sub h₂
  have hG : ContDiff ℝ ∞ G := by dsimp [G]; fun_prop
  have hsol : ContDiffOn ℝ ∞ (oddTilt κ f p) D := hG.contDiffOn.mul hF
  have dF (n : ℕ) : iteratedDeriv n F 0=(1-(-1:ℝ)^n)*iteratedDeriv n f p := by
    rw [show F=(f ∘ u)-(f ∘ v) from rfl,iteratedDeriv_sub ((h₁.contDiffAt (hD.mem_nhds h₀)).of_le (by simp))
      ((h₂.contDiffAt (hD.mem_nhds h₀)).of_le (by simp))]
    change iteratedDeriv n (fun s ↦ f (p+s)) 0-iteratedDeriv n (fun s ↦ f (p-s)) 0=_
    simp only [iteratedDeriv_comp_const_add,iteratedDeriv_comp_const_sub,add_zero,sub_zero,smul_eq_mul]
    ring
  have dG (n : ℕ) : iteratedDeriv n G 0=κ^n := by simp [G,iteratedDeriv_exp_const_mul]
  have calcD (n : ℕ) : iteratedDeriv n (oddTilt κ f p) 0=
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*κ^i*((1-(-1:ℝ)^(n-i))*iteratedDeriv (n-i) f p) := by
    change iteratedDeriv n (G*F) 0=_
    rw [iteratedDeriv_mul (hG.contDiffAt.of_le (by simp)) ((hF.contDiffAt (hD.mem_nhds h₀)).of_le (by simp))]
    simp only [dG,dF]
  apply hasFourCoefficients_of_derivatives hD hsol h₀
  · simp [oddTilt]
  all_goals rw [calcD] <;> norm_num [Finset.sum_range_succ,Nat.choose] <;> ring

end EuclideanMidpointRigidity.Endpoint

