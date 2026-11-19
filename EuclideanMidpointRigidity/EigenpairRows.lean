module

public import EuclideanMidpointRigidity.QuarticTestRows

/-! # The three quartic equations for a pair of axial eigenvectors -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

/-- Project the first test coefficient onto a second eigenvector. The two
eigenvalues may coincide, so the same equation also gives the diagonal row. -/
theorem eigenpair_vector_row {c : Coeff} {J : E →L[ℝ] Coeff} {e x y : E} {a b s : ℝ}
    (hc : K c e e=a • e) (hE : ∀ l, obstruction c J l=0)
    (hx : K c e x=b • x) (hy : K c e y=s • y) :
    let U := K (J e) e e
    (2*s+10*b-4*a)*⟪K (J x) e e,y⟫_ℝ+(4*s+6*a-8*b)*⟪K (J e) e x,y⟫_ℝ+
      2*⟪U,K c x y⟫_ℝ=0 := by
  have h := congrArg (fun w : E ↦ ⟪w,y⟫_ℝ) (first_quartic_test hc hE x)
  dsimp only at h ⊢
  simp only [inner_add_left,inner_sub_left,inner_zero_left,real_inner_smul_left,hx,map_smul,
    K_smul_coeff,K_smul_right,K_selfAdjoint c e _ y,hy,real_inner_smul_right,
    K_selfAdjoint c x _ y] at h
  linarith only [h]

/-- Polarizing the second normal test gives the third pair equation, valid
also at spectral values where a solved rational coordinate formula has a pole. -/
theorem eigenpair_normal_row {c : Coeff} {J : E →L[ℝ] Coeff} {e g x y : E} {a b s : ℝ}
    (hc : K c e e=a • e) (hE : ∀ l, obstruction c J l=0)
    (hg : ∀ l, ⟪K (J l) e e,e⟫_ℝ=⟪g,l⟫_ℝ)
    (hx : K c e x=b • x) (hy : K c e y=s • y) :
    let U := K (J e) e e
    (20*b-6*s)*⟪K (J x) e e,y⟫_ℝ + (20*s-6*b)*⟪K (J y) e e,x⟫_ℝ +
      (14*a-4*(b+s))*⟪K (J e) e x,y⟫_ℝ + 10*⟪g,K c x y⟫_ℝ - 8*⟪U,K c x y⟫_ℝ=0 := by
  have h := second_quartic_normal_test hc hE (x+y)
  have h₁ := second_quartic_normal_test hc hE x
  have h₂ := second_quartic_normal_test hc hE y
  dsimp only at h h₁ h₂ ⊢
  have hz : ⟪K (J e) e y,x⟫_ℝ=⟪K (J e) e x,y⟫_ℝ := by
    rw [K_selfAdjoint,real_inner_comm]
  simp only [K_add_left,K_add_right,map_add,K_add_coeff,inner_add_left,inner_add_right,
    K_symm c y x,hx,hy,map_smul,K_smul_coeff,real_inner_smul_left,real_inner_smul_right,hg,hz,
    show ⟪x,K (J y) e e⟫_ℝ=⟪K (J y) e e,x⟫_ℝ from real_inner_comm _ _,
    show ⟪y,K (J x) e e⟫_ℝ=⟪K (J x) e e,y⟫_ℝ from real_inner_comm _ _] at h h₁ h₂
  linear_combination h-h₁-h₂

end EuclideanMidpointRigidity
