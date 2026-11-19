module

public import EuclideanMidpointRigidity.CriticalLift

/-! # The value derivative and speed along a spherical critical branch -/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology InnerProductSpace
namespace EuclideanMidpointRigidity

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

theorem critical_axial_orthogonal {c : Coeff} {J : E →L[ℝ] Coeff} {e : E} {a : ℝ}
    (ha : a≠0) (he : K c e e=a • e) (h₄ : obstruction c J e=0) :
    ⟪K (J e) e e,e⟫_ℝ=0 := by
  let U := K (J e) e e
  have h := congrArg (fun y : E ↦ ⟪y,e⟫_ℝ) (critical_axis_eigenrelation he h₄)
  change ⟪(2:ℝ) • K c e U + a • U,e⟫_ℝ = ⟪0,e⟫_ℝ at h
  simp only [inner_add_left,real_inner_smul_left,K_selfAdjoint,he,real_inner_smul_right,inner_zero_left] at h
  exact (mul_eq_zero.mp (show a*⟪U,e⟫_ℝ=0 by linarith only [h])).resolve_left ha

/-- Along a unit critical section, differentiating the cubic value uses
only the spatial variation of the field. -/
theorem hasDerivAt_critical_value {c : ℝ → Coeff} {e : ℝ → E} {t a : ℝ} {c' : Coeff} {e' : E}
    (hc : HasDerivAt c c' t) (he : HasDerivAt e e' t) (hunit : ∀ᶠ s in 𝓝 t, ‖e s‖=1)
    (hcrit : K (c t) (e t) (e t)=a • e t) :
    HasDerivAt (fun s ↦ ⟪K (c s) (e s) (e s),e s⟫_ℝ) ⟪K c' (e t) (e t),e t⟫_ℝ t := by
  have hs : ∀ᶠ s in 𝓝 t, ⟪e s,e s⟫_ℝ=1 := hunit.mono fun s h ↦ by
    rw [real_inner_self_eq_norm_sq,h,one_pow]
  have hd : HasDerivAt (fun s ↦ ⟪e s,e s⟫_ℝ) 0 t :=
    (hasDerivAt_const t (1:ℝ)).congr_of_eventuallyEq hs
  have htan := (he.inner ℝ he).unique hd
  have hcomm : ⟪e t,e'⟫_ℝ=⟪e',e t⟫_ℝ := real_inner_comm _ _
  have h₀ : ⟪e',e t⟫_ℝ=0 := by rw [hcomm] at htan; linarith
  have hcross : ⟪K (c t) (e t) e',e t⟫_ℝ=0 := by
    rw [K_selfAdjoint,hcrit,real_inner_smul_right,h₀,mul_zero]
  have h := (hasDerivAt_K hc he he).inner ℝ he
  simpa only [inner_add_left,K_symm (c t) e' (e t),hcross,hcrit,
    real_inner_smul_left,hcomm,h₀,mul_zero,add_zero,zero_add] using h

/-- Every lifted critical axis with nonzero frozen eigenvalue has constant
speed, including at a multiple spherical critical point. -/
theorem critical_lift_speed {a b₀ b₁ : ℝ} (ha : a≠0) (c : ℝ → Coeff)
    (J : ℝ → E →L[ℝ] Coeff) (e : ℝ → E)
    (hcrit : ∀ t ∈ Icc b₀ b₁, K (c t) (e t) (e t)=a • e t)
    (hE : ∀ t ∈ Icc b₀ b₁, obstruction (c t) (J t) (e t)=0)
    (he : ∀ t ∈ Icc b₀ b₁, HasDerivAt e (liftStep a (J t) (e t)) t) :
    ∀ t ∈ Icc b₀ b₁, ‖e t‖=‖e b₀‖ := by
  let f := fun t ↦ ⟪e t,e t⟫_ℝ-⟪e b₀,e b₀⟫_ℝ
  have hdf (t : ℝ) (ht : t ∈ Icc b₀ b₁) : HasDerivAt f 0 t := by
    have h := critical_axial_orthogonal ha (hcrit t ht) (hE t ht)
    have h' : ⟪e t,K (J t (e t)) (e t) (e t)⟫_ℝ=0 := (real_inner_comm _ _).trans h
    simpa only [f,liftStep,real_inner_smul_left,real_inner_smul_right,h,h',mul_zero,add_zero] using
      (((he t ht).inner ℝ (he t ht)).sub_const ⟪e b₀,e b₀⟫_ℝ)
  have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (f := f) (f' := fun _ ↦ 0) (K := 0)
    (fun t ht ↦ (hdf t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hdf t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (show f b₀=0 by simp [f]) (by simp)
  intro t ht
  have h := sub_eq_zero.mp (hz t ht)
  simp only [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (e t),norm_nonneg (e b₀)]

end EuclideanMidpointRigidity
