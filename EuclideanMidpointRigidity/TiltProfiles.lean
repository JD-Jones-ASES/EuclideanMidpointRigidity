module

public import EuclideanMidpointRigidity.ChordParameter

/-! # Scalar Jacobi profiles for translated and tilted endpoints -/

@[expose] public section
noncomputable section
open Set
namespace EuclideanMidpointRigidity.Endpoint

structure ChordProfile (κ : ℝ) where
  value : ℝ → ℝ
  slope : ℝ → ℝ
  first : ∀ s, HasDerivAt value (slope s) s
  second : ∀ s, HasDerivAt slope (κ*slope s) s

def tiltFactor (κ h : ℝ) := if κ=0 then (2*h)⁻¹ else κ/(Real.exp (κ*h)-Real.exp (-κ*h))
def tiltValue (κ h s : ℝ) := if κ=0 then (s+h)/(2*h) else
  (Real.exp (κ*s)-Real.exp (-κ*h))/(Real.exp (κ*h)-Real.exp (-κ*h))

def rightTilt (κ h : ℝ) : ChordProfile κ where
  value := tiltValue κ h
  slope := fun s ↦ tiltFactor κ h*Real.exp (κ*s)
  first s := by
    by_cases hκ : κ=0
    · subst κ
      rw [show tiltValue 0 h=fun s ↦ (s+h)/(2*h) by funext s; simp [tiltValue]]
      simp only [tiltFactor,ite_true,zero_mul,Real.exp_zero,mul_one]
      simpa only [id_eq,one_div] using ((hasDerivAt_id s).add_const h).div_const (2*h)
    · have he := (Real.hasDerivAt_exp (κ*s)).comp s ((hasDerivAt_id s).const_mul κ)
      have hd := (he.sub_const (Real.exp (-κ*h))).div_const (Real.exp (κ*h)-Real.exp (-κ*h))
      rw [show tiltValue κ h=fun s ↦ (Real.exp (κ*s)-Real.exp (-κ*h))/(Real.exp (κ*h)-Real.exp (-κ*h)) by funext s; simp [tiltValue,hκ]]
      simp only [tiltFactor,ite_eq_right hκ]
      convert hd using 1 <;> first | rfl | ring
  second s := by
    have he := (Real.hasDerivAt_exp (κ*s)).comp s ((hasDerivAt_id s).const_mul κ)
    convert he.const_mul (tiltFactor κ h) using 1 <;> first | rfl | ring

def ChordProfile.complement {κ : ℝ} (J : ChordProfile κ) : ChordProfile κ where
  value := fun s ↦ 1-J.value s
  slope := fun s ↦ -J.slope s
  first s := (J.first s).const_sub 1
  second s := by simpa only [mul_neg] using (J.second s).fun_neg

theorem tiltFactor_ne_zero {κ h : ℝ} (hh : 0<h) : tiltFactor κ h≠0 := by
  by_cases hκ : κ=0
  · simp [tiltFactor,hκ,hh.ne']
  · have hne : Real.exp (κ*h)≠Real.exp (-κ*h) := by
      intro he
      have heq := Real.exp_injective he
      exact mul_ne_zero hκ hh.ne' (by linarith : κ*h=0)
    exact by simpa only [tiltFactor,ite_eq_right hκ] using div_ne_zero hκ (sub_ne_zero.mpr hne)

@[simp] theorem tiltValue_left (κ h : ℝ) : tiltValue κ h (-h)=0 := by
  by_cases hκ : κ=0 <;> simp [tiltValue,hκ]

@[simp] theorem tiltValue_right (κ : ℝ) {h : ℝ} (hh : 0<h) : tiltValue κ h h=1 := by
  by_cases hκ : κ=0
  · rw [tiltValue,ite_eq_left hκ,← two_mul,div_self (mul_ne_zero (by norm_num) hh.ne')]
  · have hfac := tiltFactor_ne_zero (κ := κ) hh
    rw [tiltFactor,ite_eq_right hκ] at hfac
    have hden : Real.exp (κ*h)-Real.exp (-κ*h)≠0 := fun hz ↦ hfac (by rw [hz,div_zero])
    simpa only [tiltValue,ite_eq_right hκ] using div_self hden

theorem ChordProfile.time_derivatives {κ h : ℝ} (J : ChordProfile κ) (hh : 0≤h) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun s ↦ J.value (chordParameter h s)) (chordSpeed h t*J.slope (chordParameter h t)) t ∧
    HasDerivAt (fun s ↦ chordSpeed h s*J.slope (chordParameter h s))
      ((κ-1)*(chordSpeed h t)^2*J.slope (chordParameter h t)) t := by
  have hd := hasDerivAt_chordParameter hh ht
  refine ⟨?_,?_⟩
  · simpa only [Function.comp_def,mul_comm] using (J.first _).comp t hd
  · have h₂ := (hasDerivAt_chordSpeed hh ht).fun_mul ((J.second _).comp t hd)
    simp only [Function.comp_apply] at h₂
    convert h₂ using 1 <;> first | rfl | ring

end EuclideanMidpointRigidity.Endpoint

