module

public import EuclideanMidpointRigidity.Basic
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # The geodesic acceleration near the zero section -/

@[expose] public section

namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d

set_option backward.isDefEq.respectTransparency false in
/-- The velocity enters quadratically, so the Lipschitz constant of the
acceleration can be made arbitrarily small near the zero section. -/
theorem hasStrictFDerivAt_acceleration_zero {C : E → Cubic d} {p : E}
    (hC : ContDiffAt ℝ 1 C p) (σ : ℝ) :
    HasStrictFDerivAt (𝕜 := ℝ) (fun z : E × E ↦ -σ • K (C z.1) z.2 z.2) 0 (p, 0) := by
  let z₀ : E × E := (p, 0)
  let inc : Cubic d →L[ℝ] (E →L[ℝ] E →L[ℝ] E) := (cubicSubspace d).subtypeL
  have hinc := ContinuousLinearMap.hasStrictFDerivAt (𝕜 := ℝ) («E» := Cubic d)
    (F := E →L[ℝ] E →L[ℝ] E) (x := C p) inc
  have hc := (hinc.comp p
    (hC.hasStrictFDerivAt_fderiv one_ne_zero)).comp z₀ (hasStrictFDerivAt_fst (𝕜 := ℝ))
  have hv := hasStrictFDerivAt_snd (𝕜 := ℝ) (p := z₀)
  apply (((hc.clm_apply hv).clm_apply hv).const_smul (-σ)).congr_fderiv
  apply ContinuousLinearMap.ext
  intro z
  simp [z₀, inc]

end EuclideanMidpointRigidity
