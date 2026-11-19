module

public import EuclideanMidpointRigidity.CriticalAxis

/-! # The first two test-vector coefficients of the quartic at a critical axis -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

theorem first_quartic_test {c : Coeff} {J : E →L[ℝ] Coeff} {e : E} {a : ℝ}
    (he : K c e e=a • e) (hE : ∀ h, obstruction c J h=0) (z : E) :
    let B := K c e
    let R := fun l ↦ K (J l) e e
    let Z := K (J e) e
    let U := R e
    (2:ℝ) • K c z U + (2:ℝ) • B (R z) + (4:ℝ) • B (Z z) +
      (10:ℝ) • R (B z) + (6*a) • Z z - (4*a) • R z - (8:ℝ) • Z (B z) = 0 := by
  let y := fun t : ℝ ↦ e+t • z
  have hy : HasDerivAt y z 0 := by simpa [y] using ((hasDerivAt_id (0:ℝ)).smul_const z).const_add e
  have h₀ : y 0=e := by simp [y]
  have hj := J.hasFDerivAt.comp_hasDerivAt 0 hy
  have hq := hasDerivAt_K (hasDerivAt_const (0:ℝ) c) hy hy
  have hu := hasDerivAt_K hj hy hy
  have ht₁ := (hasDerivAt_K (hasDerivAt_const (0:ℝ) c) hy hu).fun_const_smul (2:ℝ)
  have ht₂ := (hasDerivAt_K (J.hasFDerivAt.comp_hasDerivAt 0 hq) hy hy).fun_const_smul (5:ℝ)
  have ht₃ := (hasDerivAt_K hj hy hq).fun_const_smul (4:ℝ)
  have hd := (ht₁.fun_add ht₂).fun_sub ht₃
  have hz : HasDerivAt (fun t ↦ obstruction c J (y t)) 0 0 := by
    simpa only [hE] using hasDerivAt_const (0:ℝ) (0:E)
  have hh := hd.unique (by simpa [obstruction,← Nat.cast_smul_eq_nsmul ℝ] using hz)
  have hzero (u v : E) : K (0:Coeff) u v=0 := rfl
  simp only [Function.comp_apply,h₀,he,hzero,zero_add,map_add,map_smul,K_add_coeff,K_add_right,
    K_smul_coeff,K_smul_right,K_symm _ z e] at hh
  dsimp only
  linear_combination (norm := module) hh

private theorem second_quartic_test {c : Coeff} {J : E →L[ℝ] Coeff} {e : E} {a : ℝ}
    (he : K c e e=a • e) (hE : ∀ h, obstruction c J h=0) (z : E) :
    let B := K c e
    let R := fun l ↦ K (J l) e e
    let Z := K (J e) e
    let k := K c z z
    (2:ℝ) • K c z (R z+(2:ℝ) • Z z) +
      (2:ℝ) • B (K (J e) z z + (2:ℝ) • K (J z) e z) +
      (5:ℝ) • R k + (20:ℝ) • K (J (B z)) e z + (5*a) • K (J e) z z -
      (4*a) • K (J z) e z - (8:ℝ) • K (J z) e (B z) -
      (8:ℝ) • K (J e) z (B z) - (4:ℝ) • Z k = 0 := by
  have h₁ := hE (e+z)
  have h₂ := hE (e-z)
  have h₃ := hE e
  have h₄ := hE z
  dsimp only
  simp only [obstruction,sub_eq_add_neg,map_add,map_neg,map_smul,K_add_coeff,K_add_left,
    K_add_right,K_neg_coeff,K_neg_left,K_neg_right,K_smul_coeff,K_smul_right,
    K_symm _ z e,he,← Nat.cast_smul_eq_nsmul ℝ] at h₁ h₂ h₃ h₄ ⊢
  push_cast at h₁ h₂ h₃ h₄
  linear_combination (norm := module) (1/2:ℝ) • h₁ + (1/2:ℝ) • h₂ - h₃ - h₄

private theorem inner_axis_pair (c : Coeff) (e x y : E) :
    ⟪K c x y,e⟫_ℝ=⟪K c e x,y⟫_ℝ := by
  rw [K_selfAdjoint,K_symm c x e,real_inner_comm]

theorem second_quartic_normal_test {c : Coeff} {J : E →L[ℝ] Coeff} {e : E} {a : ℝ}
    (he : K c e e=a • e) (hE : ∀ h, obstruction c J h=0) (z : E) :
    let B := K c e
    let R := fun l ↦ K (J l) e e
    let Z := K (J e) e
    let U := R e
    let k := K c z z
    20*⟪R (B z),z⟫_ℝ-6*⟪B z,R z⟫_ℝ+(7*a)*⟪Z z,z⟫_ℝ-
      4*⟪Z z,B z⟫_ℝ+5*⟪R k,e⟫_ℝ-4*⟪U,k⟫_ℝ=0 := by
  have h := congrArg (fun w : E ↦ ⟪w,e⟫_ℝ) (second_quartic_test he hE z)
  dsimp only at h ⊢
  simp only [inner_add_left,inner_sub_left,inner_zero_left,real_inner_smul_left,
    inner_axis_pair _ e,he,inner_add_right,real_inner_smul_right,real_inner_smul_left] at h
  rw [show ⟪e,K (J e) z z⟫_ℝ=⟪K (J e) z z,e⟫_ℝ from real_inner_comm _ _,
    show ⟪e,K (J z) e z⟫_ℝ=⟪K (J z) e z,e⟫_ℝ from real_inner_comm _ _] at h
  simp only [inner_axis_pair _ e] at h
  rw [show ⟪K c e z,K (J e) e z⟫_ℝ=⟪K (J e) e z,K c e z⟫_ℝ from real_inner_comm _ _,
    show ⟪K (J z) e e,K c e z⟫_ℝ=⟪K c e z,K (J z) e e⟫_ℝ from real_inner_comm _ _] at h
  linear_combination (norm := ring_nf) h

end EuclideanMidpointRigidity
