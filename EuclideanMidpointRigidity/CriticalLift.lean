module

public import EuclideanMidpointRigidity.CriticalAxis
public import EuclideanMidpointRigidity.TensorBounds
public import Mathlib.Analysis.ODE.Gronwall

/-! # Transporting a critical direction at its initial eigenvalue

Fix the nonzero initial value `a`. Along `x' = e` and
`e' = (DₑK)(e,e)/(2a)`, the defect `K(e,e) - a e` solves a homogeneous
linear equation. Its zero initial condition propagates through multiple
spherical critical points as well.
-/

@[expose] public section
noncomputable section
open Set
open scoped ContDiff InnerProductSpace
namespace EuclideanMidpointRigidity

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

def liftStep (a : ℝ) (J : E →L[ℝ] Coeff) (e : E) : E := (2*a)⁻¹ • K (J e) e e
def liftDefect (a : ℝ) (c : Coeff) (e : E) : E := K c e e-a • e
def liftDefectRate (a : ℝ) (J : E →L[ℝ] Coeff) (e v : E) : E :=
  (2*a)⁻¹ • ((4:ℝ) • K (J e) e v - (5:ℝ) • K (J v) e e)

theorem critical_lift_rate {a : ℝ} (ha : a≠0) {c : Coeff} {J : E →L[ℝ] Coeff} {e : E}
    (hE : obstruction c J e=0) :
    K (J e) e e + K c (liftStep a J e) e + K c e (liftStep a J e) - a • liftStep a J e =
      liftDefectRate a J e (liftDefect a c e) := by
  let U := K (J e) e e
  let v := liftDefect a c e
  let k : ℝ := (2*a)⁻¹
  have hk : 2*a*k=1 := mul_inv_cancel₀ (mul_ne_zero (by norm_num) ha)
  have hU : (1:ℝ) • U=(2*a*k) • U := by rw [hk]
  have h : (2:ℝ) • K c e U + a • U + (5:ℝ) • K (J v) e e - (4:ℝ) • K (J e) e v = 0 := by
    dsimp only [v,liftDefect,U]
    simp only [sub_eq_add_neg,map_add,map_neg,map_smul,K_add_coeff,K_neg_coeff,K_smul_coeff,
      K_add_right,K_neg_right,K_smul_right]
    simp only [obstruction,← Nat.cast_smul_eq_nsmul ℝ] at hE
    push_cast at hE
    linear_combination (norm := module) hE
  rw [K_symm c (liftStep a J e) e]
  change U + K c e (k • U) + K c e (k • U) - a • (k • U) =
    k • ((4:ℝ) • K (J e) e v - (5:ℝ) • K (J v) e e)
  simp only [K_smul_right]
  linear_combination (norm := module) k • h + hU

theorem norm_liftDefectRate (a : ℝ) (J : E →L[ℝ] Coeff) (e v : E) :
    ‖liftDefectRate a J e v‖ ≤ (|(2*a)⁻¹| * (9*‖J‖*‖e‖^2))*‖v‖ := by
  have h₁ : ‖K (J e) e v‖ ≤ (‖J‖*‖e‖)*‖e‖*‖v‖ :=
    (norm_K_le_opNorm _ _ _).trans (by gcongr; exact J.le_opNorm e)
  have h₂ : ‖K (J v) e e‖ ≤ (‖J‖*‖v‖)*‖e‖*‖e‖ :=
    (norm_K_le_opNorm _ _ _).trans (by gcongr; exact J.le_opNorm v)
  rw [liftDefectRate,norm_smul,Real.norm_eq_abs]
  calc
    _ ≤ |(2*a)⁻¹| * (‖(4:ℝ) • K (J e) e v‖+‖(5:ℝ) • K (J v) e e‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (abs_nonneg _)
    _ ≤ |(2*a)⁻¹| * (4*((‖J‖*‖e‖)*‖e‖*‖v‖)+5*((‖J‖*‖v‖)*‖e‖*‖e‖)) := by
      simp only [norm_smul,Real.norm_ofNat]
      gcongr
    _ = _ := by ring

theorem critical_lift_preserves {Ω : Set E} {C : E → Coeff} (hΩ : IsOpen Ω)
    (hC : ContDiffOn ℝ ∞ C Ω) (hE : ∀ x ∈ Ω, ∀ e, obstruction (C x) (fderiv ℝ C x) e=0)
    {a b₀ b₁ : ℝ} (ha : a≠0) (x e : ℝ → E) (hxΩ : MapsTo x (Icc b₀ b₁) Ω)
    (hx : ∀ t ∈ Icc b₀ b₁, HasDerivAt x (e t) t)
    (he : ∀ t ∈ Icc b₀ b₁, HasDerivAt e (liftStep a (fderiv ℝ C (x t)) (e t)) t)
    (hstart : K (C (x b₀)) (e b₀) (e b₀)=a • e b₀) :
    ∀ t ∈ Icc b₀ b₁, K (C (x t)) (e t) (e t)=a • e t := by
  let D := fun t ↦ liftDefect a (C (x t)) (e t)
  let J := fun t ↦ fderiv ℝ C (x t)
  let R := fun t ↦ liftDefectRate a (J t) (e t) (D t)
  have hD (t : ℝ) (ht : t ∈ Icc b₀ b₁) : HasDerivAt D (R t) t := by
    have hc := ((hC.contDiffAt (hΩ.mem_nhds (hxΩ ht))).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (hx t ht)
    have h := (hasDerivAt_K hc (he t ht) (he t ht)).fun_sub ((he t ht).fun_const_smul a)
    dsimp only [R,J,D]
    rw [← critical_lift_rate ha (hE (x t) (hxΩ ht) (e t))]
    exact h
  have hJ : ContinuousOn J (Icc b₀ b₁) := by
    intro t ht
    exact ((hC.contDiffAt (hΩ.mem_nhds (hxΩ ht))).continuousAt_fderiv (by simp)).comp_continuousWithinAt
      (hx t ht).continuousAt.continuousWithinAt
  have hec : ContinuousOn e (Icc b₀ b₁) := fun t ht ↦ (he t ht).continuousAt.continuousWithinAt
  have hbound : ContinuousOn (fun t ↦ |(2*a)⁻¹| * (9*‖J t‖*‖e t‖^2)) (Icc b₀ b₁) :=
    continuousOn_const.mul ((continuousOn_const.mul hJ.norm).mul (hec.norm.pow 2))
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hbound
  have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (f := D) (f' := R) (K := B)
    (fun t ht ↦ (hD t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hD t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (show D b₀=0 from sub_eq_zero.mpr hstart) (by
      intro t ht
      have hb := (le_abs_self _).trans (hB t (Ico_subset_Icc_self ht))
      exact (norm_liftDefectRate a (J t) (e t) (D t)).trans
        (mul_le_mul_of_nonneg_right hb (norm_nonneg _)))
  exact fun t ht ↦ sub_eq_zero.mp (hz t ht)

end EuclideanMidpointRigidity
