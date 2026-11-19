module

public import EuclideanMidpointRigidity.CriticalAxis
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Spatial derivatives of the product evaluated on moving vectors -/

@[expose] public section
noncomputable section
open scoped ContDiff
namespace EuclideanMidpointRigidity

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

def firstProduct (C : E → Coeff) (x l u v : E) : E := K (fderiv ℝ C x l) u v

def secondProduct (C : E → Coeff) (x l m u v : E) : E :=
  K (fderiv ℝ (fderiv ℝ C) x l m) u v

def thirdProduct (C : E → Coeff) (x k l m u v : E) : E :=
  K (fderiv ℝ (fderiv ℝ (fderiv ℝ C)) x k l m) u v

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_firstProduct (C : E → Coeff) {t : ℝ} {x l u v : ℝ → E}
    {x' l' u' v' : E} (hc : ContDiffAt ℝ ∞ C (x t)) (hx : HasDerivAt x x' t)
    (hl : HasDerivAt l l' t) (hu : HasDerivAt u u' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s ↦ firstProduct C (x s) (l s) (u s) (v s))
      (secondProduct C (x t) x' (l t) (u t) (v t) + firstProduct C (x t) l' (u t) (v t) +
       firstProduct C (x t) (l t) u' (v t) + firstProduct C (x t) (l t) (u t) v') t := by
  have hJ : ContDiffAt ℝ 1 (fderiv ℝ C) (x t) := hc.fderiv_right (by simp)
  have hj := (hJ.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t hx
  simpa only [firstProduct,secondProduct,Function.comp_apply,K_add_coeff] using
    hasDerivAt_K (hj.clm_apply hl) hu hv

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_secondProduct (C : E → Coeff) {t : ℝ} {x l m u v : ℝ → E}
    {x' l' m' u' v' : E} (hc : ContDiffAt ℝ ∞ C (x t)) (hx : HasDerivAt x x' t)
    (hl : HasDerivAt l l' t) (hm : HasDerivAt m m' t) (hu : HasDerivAt u u' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s ↦ secondProduct C (x s) (l s) (m s) (u s) (v s))
      (thirdProduct C (x t) x' (l t) (m t) (u t) (v t) +
       secondProduct C (x t) l' (m t) (u t) (v t) + secondProduct C (x t) (l t) m' (u t) (v t) +
       secondProduct C (x t) (l t) (m t) u' (v t) + secondProduct C (x t) (l t) (m t) (u t) v') t := by
  have hJ : ContDiffAt ℝ 2 (fderiv ℝ C) (x t) := hc.fderiv_right (by simp)
  have hH : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ C)) (x t) := hJ.fderiv_right (by norm_num)
  have hh := (hH.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t hx
  simpa only [firstProduct,secondProduct,thirdProduct,Function.comp_apply,K_add_coeff,
    ContinuousLinearMap.add_apply] using hasDerivAt_K ((hh.clm_apply hl).clm_apply hm) hu hv

end EuclideanMidpointRigidity
