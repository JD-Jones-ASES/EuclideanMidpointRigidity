module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic

/-! # The affine time parameter on a straight axial geodesic -/

@[expose] public section
noncomputable section
open Set
namespace EuclideanMidpointRigidity.Endpoint

def chordDensity (h t : ℝ) := Real.exp (-h)+t*(Real.exp h-Real.exp (-h))
def chordParameter (h t : ℝ) := Real.log (chordDensity h t)
def chordSpeed (h t : ℝ) := (Real.exp h-Real.exp (-h))/chordDensity h t

theorem chordDensity_bounds {h t : ℝ} (hh : 0≤h) (ht : t ∈ Icc (0:ℝ) 1) :
    Real.exp (-h)≤chordDensity h t ∧ chordDensity h t≤Real.exp h := by
  have he : Real.exp (-h)≤Real.exp h := Real.exp_le_exp.mpr (by linarith)
  dsimp only [chordDensity]
  constructor
  · linarith only [mul_nonneg ht.1 (sub_nonneg.mpr he)]
  · nlinarith only [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr he)]

theorem chordParameter_bounds {h t : ℝ} (hh : 0≤h) (ht : t ∈ Icc (0:ℝ) 1) :
    -h≤chordParameter h t ∧ chordParameter h t≤h := by
  obtain ⟨hl,hu⟩ := chordDensity_bounds hh ht
  have hp := (Real.exp_pos (-h)).trans_le hl
  exact ⟨by simpa only [Real.log_exp,chordParameter] using Real.log_le_log (Real.exp_pos _) hl,
    by simpa only [Real.log_exp,chordParameter] using Real.log_le_log hp hu⟩

@[simp] theorem chordParameter_zero (h : ℝ) : chordParameter h 0= -h := by simp [chordParameter,chordDensity]
@[simp] theorem chordParameter_one (h : ℝ) : chordParameter h 1=h := by simp [chordParameter,chordDensity]
theorem chordParameter_half (h : ℝ) : chordParameter h (1/2)=Real.log (Real.cosh h) := by
  unfold chordParameter chordDensity; rw [Real.cosh_eq]; congr 1; ring

theorem hasDerivAt_chordDensity (h t : ℝ) : HasDerivAt (chordDensity h) (Real.exp h-Real.exp (-h)) t := by
  change HasDerivAt (fun t : ℝ ↦ Real.exp (-h)+t*(Real.exp h-Real.exp (-h))) _ t
  simpa only [id_eq,one_mul] using ((hasDerivAt_id t).mul_const (Real.exp h-Real.exp (-h))).const_add (Real.exp (-h))

theorem hasDerivAt_chordParameter {h t : ℝ} (hh : 0≤h) (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt (chordParameter h) (chordSpeed h t) t := by
  have hp := (Real.exp_pos (-h)).trans_le (chordDensity_bounds hh ht).1
  exact (hasDerivAt_chordDensity h t).log hp.ne'

theorem hasDerivAt_chordSpeed {h t : ℝ} (hh : 0≤h) (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt (chordSpeed h) (-(chordSpeed h t)^2) t := by
  have hp := (Real.exp_pos (-h)).trans_le (chordDensity_bounds hh ht).1
  have hd := (hasDerivAt_const t (Real.exp h-Real.exp (-h))).fun_div (hasDerivAt_chordDensity h t) hp.ne'
  change HasDerivAt (fun s ↦ (Real.exp h-Real.exp (-h))/chordDensity h s) _ t
  convert hd using 1 <;> first | rfl | (simp only [chordSpeed,zero_mul,zero_sub,div_pow]; ring)

theorem chordSpeed_bounds {h t : ℝ} (hh : 0≤h) (ht : t ∈ Icc (0:ℝ) 1) :
    0≤chordSpeed h t ∧ chordSpeed h t≤Real.exp (2*h)-1 := by
  obtain ⟨hl,_⟩ := chordDensity_bounds hh ht
  have he := Real.exp_le_exp.mpr (show -h≤h by linarith)
  have hp := (Real.exp_pos (-h)).trans_le hl
  refine ⟨div_nonneg (sub_nonneg.mpr he) hp.le,?_⟩
  change _/chordDensity h t≤_
  calc
    _ ≤ (Real.exp h-Real.exp (-h))/Real.exp (-h) :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr he) (Real.exp_pos _) hl
    _ = Real.exp (2*h)-1 := by
      rw [show 2*h=h-(-h) by ring,Real.exp_sub]
      field_simp

end EuclideanMidpointRigidity.Endpoint

