module

public import EuclideanMidpointRigidity.ChordParameter

/-! # Returning from signed line position to affine geodesic time -/

@[expose] public section
noncomputable section
open Set
namespace EuclideanMidpointRigidity.Endpoint

def chordTime (h s : ℝ) := (Real.exp s-Real.exp (-h))/(Real.exp h-Real.exp (-h))
def chordTimeSpeed (h s : ℝ) := Real.exp s/(Real.exp h-Real.exp (-h))

theorem chordDifference_pos {h : ℝ} (hh : 0<h) : 0<Real.exp h-Real.exp (-h) :=
  sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))

theorem chordTime_mem {s h : ℝ} (hh : 0<h) (hs : s ∈ Icc (-h) h) : chordTime h s ∈ Icc (0:ℝ) 1 := by
  have hd := chordDifference_pos hh
  refine ⟨div_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hs.1)) hd.le,?_⟩
  exact (div_le_one hd).mpr (sub_le_sub_right (Real.exp_le_exp.mpr hs.2) _)

@[simp] theorem chordTime_left (h : ℝ) : chordTime h (-h)=0 := by simp [chordTime]
@[simp] theorem chordTime_right {h : ℝ} (hh : 0<h) : chordTime h h=1 := div_self (chordDifference_pos hh).ne'

theorem hasDerivAt_chordTime (h s : ℝ) : HasDerivAt (chordTime h) (chordTimeSpeed h s) s :=
  ((Real.hasDerivAt_exp s).sub_const (Real.exp (-h))).div_const _
theorem hasDerivAt_chordTimeSpeed (h s : ℝ) : HasDerivAt (chordTimeSpeed h) (chordTimeSpeed h s) s :=
  (Real.hasDerivAt_exp s).div_const _

theorem chordDensity_at_time {h : ℝ} (hh : 0<h) (s : ℝ) : chordDensity h (chordTime h s)=Real.exp s := by
  unfold chordDensity chordTime
  rw [div_mul_cancel₀ _ (chordDifference_pos hh).ne']
  ring

theorem chordParameter_at_time {h : ℝ} (hh : 0<h) (s : ℝ) : chordParameter h (chordTime h s)=s := by
  rw [chordParameter,chordDensity_at_time hh,Real.log_exp]

theorem chordSpeed_timeSpeed {h : ℝ} (hh : 0<h) (s : ℝ) :
    chordSpeed h (chordTime h s)*chordTimeSpeed h s=1 := by
  rw [chordSpeed,chordTimeSpeed,chordDensity_at_time hh]
  field_simp [(chordDifference_pos hh).ne',(Real.exp_pos s).ne']

theorem chordTime_midpoint {h : ℝ} (hh : 0<h) : chordTime h (Real.log (Real.cosh h))=1/2 := by
  rw [chordTime,Real.exp_log (Real.cosh_pos _),Real.cosh_eq]
  field_simp [(chordDifference_pos hh).ne']
  ring

end EuclideanMidpointRigidity.Endpoint

