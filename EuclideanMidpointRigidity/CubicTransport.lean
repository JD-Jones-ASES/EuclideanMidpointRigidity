module

public import EuclideanMidpointRigidity.DirectionalDerivatives
public import EuclideanMidpointRigidity.LineFamilyOperations
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Transporting a cubic Taylor polynomial on a convex domain -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]

def cubicTranslate (C : E → V) (w : E) (x : E) (s : ℝ) :=
  C x+s • directions C [w] x+(s^2/2) • directions C [w,w] x+(s^3/6) • directions C [w,w,w] x

theorem cubicTranslate_zero (C : E → V) (w x : E) : cubicTranslate C w x 0=C x := by simp [cubicTranslate]

def cubicTranslateFamily {W : Set E} {C : E → V} (hW : IsOpen W) (hC : ContDiffOn ℝ ∞ C W) (w : E) :
    AnalyticLineFamily W (cubicTranslate C w) := by
  let j := fun xs : List E ↦ AnalyticLineFamily.spatial (directions.smooth hW hC xs)
  let t := AnalyticLineFamily.time W
  let t₂ := t.map (fun s ↦ s^2/2) ((contDiff_id.pow 2).div_const 2)
  let t₃ := t.map (fun s ↦ s^3/6) ((contDiff_id.pow 3).div_const 6)
  exact (((AnalyticLineFamily.spatial hC).add (t.smul (j [w]))).add (t₂.smul (j [w,w]))).add (t₃.smul (j [w,w,w]))

theorem cubicTranslate_transport {W : Set E} {C : E → V} (hW : IsOpen W) (hc : Convex ℝ W)
    (hC : ContDiffOn ℝ ∞ C W) (w : E) (hz : ∀ x ∈ W, directions C [w,w,w,w] x=0)
    {x : E} {t : ℝ} (hx : x ∈ W) (ht : x+t • w ∈ W) (s : ℝ) :
    cubicTranslate C w (x+t • w) (s-t)=cubicTranslate C w x s := by
  let X := fun a : ℝ ↦ x+a • (t • w)
  let f := fun a : ℝ ↦ s-a*t
  have hX (a : ℝ) (ha : a ∈ Icc 0 1) : X a ∈ W := by
    have h := hc hx ht (sub_nonneg.mpr ha.2) ha.1 (sub_add_cancel 1 a)
    convert h using 1; dsimp [X]; module
  have hd (a : ℝ) (ha : a ∈ Icc 0 1) (xs : List E) :
      HasDerivAt (fun b ↦ directions C xs (X b)) (t • directions C (w::xs) (X a)) a := by
    have hh := (((directions.smooth hW hC xs).contDiffAt (hW.mem_nhds (hX a ha))).differentiableAt (by simp)).hasFDerivAt
    have hl : HasDerivAt X (t • w) a := by simpa [X] using ((hasDerivAt_id a).smul_const (t • w)).const_add x
    simpa only [map_smul,directions,directional,Function.comp_def] using hh.comp_hasDerivAt a hl
  have df (a : ℝ) : HasDerivAt f (-t) a := by
    simpa [f] using ((hasDerivAt_id a).mul_const t).const_sub s
  let G := fun a ↦ cubicTranslate C w (X a) (f a)
  have dG (a : ℝ) (ha : a ∈ Icc 0 1) : HasDerivAt G 0 a := by
    have h₁ := (hd a ha []).add ((df a).smul (hd a ha [w]))
    have h₂ := h₁.add ((((df a).pow 2).div_const 2).smul (hd a ha [w,w]))
    have hh := h₂.add ((((df a).pow 3).div_const 6).smul (hd a ha [w,w,w]))
    convert hh using 1
    · funext b
      rfl
    · rw [hz _ (hX a ha),smul_zero,smul_zero]
      simp only [smul_smul,Pi.pow_apply]
      norm_num; module
  have hh := constant_of_has_deriv_right_zero (HasDerivAt.continuousOn dG)
    (fun a ha ↦ (dG a (Ico_subset_Icc_self ha)).hasDerivWithinAt) 1 (right_mem_Icc.mpr (by norm_num))
  simpa only [G,X,f,one_smul,zero_smul,add_zero,one_mul,zero_mul,sub_zero] using hh

end EuclideanMidpointRigidity

