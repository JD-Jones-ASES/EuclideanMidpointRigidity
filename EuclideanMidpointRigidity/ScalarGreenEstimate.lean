module

public import EuclideanMidpointRigidity.GreenOperator
public import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-! # A uniform Dirichlet error estimate on the scaled axial interval -/

public section
noncomputable section
open Set
namespace EuclideanMidpointRigidity.Endpoint

theorem scalar_dirichlet_small_drift {y v f : ℝ → ℝ} {k R : ℝ} (hk : |k|≤1/4)
    (dy : ∀ t ∈ Icc (-1:ℝ) 1, HasDerivAt y (v t) t)
    (dv : ∀ t ∈ Icc (-1:ℝ) 1, HasDerivAt v (k*v t+f t) t)
    (hf : ∀ t ∈ Icc (-1:ℝ) 1, |f t|≤R) (hl : y (-1)=0) (hr : y 1=0) :
    ∀ t ∈ Icc (-1:ℝ) 1, |y t|≤8*R := by
  let T := Icc (-1:ℝ) 1
  have hne : T.Nonempty := ⟨0,by norm_num [T]⟩
  obtain ⟨c,hc,hm⟩ := isCompact_Icc.exists_isMaxOn hne (HasDerivAt.continuousOn dv).abs
  have hV (t : ℝ) (ht : t ∈ T) : |v t|≤|v c| := hm ht
  obtain ⟨z,hz,dz⟩ := exists_hasDerivAt_eq_zero (by norm_num : (-1:ℝ)<1)
    (HasDerivAt.continuousOn dy) (hl.trans hr.symm) (fun x hx ↦ dy x (Ioo_subset_Icc_self hx))
  have hTz : z ∈ T := Ioo_subset_Icc_self hz
  have diam {a b : ℝ} (ha : a ∈ T) (hb : b ∈ T) : ‖a-b‖≤2 := by
    rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨by linarith [ha.1,hb.2],by linarith [ha.2,hb.1]⟩
  have hd (t : ℝ) (ht : t ∈ T) : ‖k*v t+f t‖≤|k| * |v c|+R := by
    rw [Real.norm_eq_abs]
    exact (abs_add_le _ _).trans (add_le_add (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hV t ht) (abs_nonneg _)) (hf t ht))
  have hR : 0≤R := (abs_nonneg (f c)).trans (hf c hc)
  have slope := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (fun t ht ↦ (dv t ht).hasDerivWithinAt) hd
    (convex_Icc (-1:ℝ) 1) hTz hc
  rw [dz,sub_zero,Real.norm_eq_abs] at slope
  have hvc := slope.trans (mul_le_mul_of_nonneg_left (diam hc hTz) (by positivity))
  have hb : |v c|≤4*R := by nlinarith only [hvc,mul_le_mul_of_nonneg_right hk (abs_nonneg (v c))]
  intro t ht
  have hpos := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (fun s hs ↦ (dy s hs).hasDerivWithinAt)
    (fun s hs ↦ (show ‖v s‖≤|v c| from hV s hs)) (convex_Icc (-1:ℝ) 1) (left_mem_Icc.mpr (by norm_num)) ht
  rw [hl,sub_zero,Real.norm_eq_abs] at hpos
  have hdist := diam ht (left_mem_Icc.mpr (by norm_num) : (-1:ℝ) ∈ T)
  linarith only [hpos.trans (mul_le_mul_of_nonneg_left hdist (abs_nonneg _)),hb]

end EuclideanMidpointRigidity.Endpoint

