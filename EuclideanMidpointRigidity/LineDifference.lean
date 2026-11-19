module

public import EuclideanMidpointRigidity.ExponentialLine

/-! # A four-point difference annihilating the three translation modes -/

@[expose] public section
noncomputable section
open Set
open scoped ContDiff
namespace EuclideanMidpointRigidity.Endpoint

def differenceWeight (t : ℝ) := 1+Real.exp t+Real.exp (-t)

def lineDifference (t : ℝ) (f : ℝ → ℝ) (x : ℝ) :=
  f (x+3*t)-f x-differenceWeight t*(f (x+2*t)-f (x+t))

def differenceDomain (W : Set ℝ) (t : ℝ) : Set ℝ :=
  ((W ∩ (fun x ↦ x+t) ⁻¹' W) ∩ (fun x ↦ x+2*t) ⁻¹' W) ∩ (fun x ↦ x+3*t) ⁻¹' W

theorem isOpen_differenceDomain {W : Set ℝ} (hW : IsOpen W) (t : ℝ) : IsOpen (differenceDomain W t) :=
  ((hW.inter (hW.preimage (continuous_id.add continuous_const))).inter
    (hW.preimage (continuous_id.add continuous_const))).inter (hW.preimage (continuous_id.add continuous_const))

theorem smooth_lineDifference {W : Set ℝ} {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f W) (t : ℝ) :
    ContDiffOn ℝ ∞ (lineDifference t f) (differenceDomain W t) := by
  have shift (a : ℝ) (hm : ∀ x ∈ differenceDomain W t, x+a ∈ W) :
      ContDiffOn ℝ ∞ (fun x ↦ f (x+a)) (differenceDomain W t) :=
    hf.comp (contDiff_id.add contDiff_const).contDiffOn hm
  exact ((shift (3*t) fun _ hx ↦ hx.2).sub (hf.mono (fun _ hx ↦ hx.1.1.1))).sub
    (contDiffOn_const.mul ((shift (2*t) fun _ hx ↦ hx.1.2).sub (shift t fun _ hx ↦ hx.1.1.2)))

theorem iteratedDeriv_lineDifference {W : Set ℝ} {f : ℝ → ℝ} {x t : ℝ}
    (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W) (hx : x ∈ differenceDomain W t) (n : ℕ) :
    iteratedDeriv n (lineDifference t f) x=lineDifference t (iteratedDeriv n f) x := by
  let g := fun a : ℝ ↦ fun y ↦ f (y+a)
  have hs (a : ℝ) (ha : x+a ∈ W) : ContDiffAt ℝ n (g a) x :=
    ((hf.contDiffAt (hW.mem_nhds ha)).of_le (by simp)).comp x (contDiffAt_id.add contDiffAt_const)
  have h₀ : ContDiffAt ℝ n f x := (hf.contDiffAt (hW.mem_nhds hx.1.1.1)).of_le (by simp)
  have h₁ := hs t hx.1.1.2
  have h₂ := hs (2*t) hx.1.2
  have h₃ := hs (3*t) hx.2
  have ha : ContDiffAt ℝ n (g (3*t)-f) x := h₃.sub h₀
  have hb : ContDiffAt ℝ n (g (2*t)-g t) x := h₂.sub h₁
  have hz : ContDiffAt ℝ n (fun y ↦ differenceWeight t*((g (2*t)-g t) y)) x := contDiffAt_const.mul hb
  change iteratedDeriv n ((g (3*t)-f)-(fun y ↦ differenceWeight t*((g (2*t)-g t) y))) x=_
  rw [iteratedDeriv_sub ha hz,iteratedDeriv_sub h₃ h₀,
    iteratedDeriv_const_mul_field,iteratedDeriv_sub h₂ h₁]
  simp only [g,iteratedDeriv_comp_add_const,lineDifference]

theorem lineDifference_exponential {W : Set ℝ} {f : ℝ → ℝ} {x t a b c : ℝ}
    (hx : x ∈ differenceDomain W t) (he : ∀ z ∈ W, f z=a+b*Real.exp z+c*Real.exp (-z)) :
    lineDifference t f x=0 := by
  rw [lineDifference,he _ hx.2,he _ hx.1.1.1,he _ hx.1.2,he _ hx.1.1.2]
  have he₂ : Real.exp (2*t)=(Real.exp t)^2 := by rw [two_mul,Real.exp_add,pow_two]
  have he₃ : Real.exp (3*t)=(Real.exp t)^3 := by rw [show 3*t=2*t+t by ring,Real.exp_add,he₂]; ring
  simp only [differenceWeight,Real.exp_neg,Real.exp_add,he₂,he₃]
  field_simp [(Real.exp_pos x).ne',(Real.exp_pos t).ne']
  <;> ring

end EuclideanMidpointRigidity.Endpoint

