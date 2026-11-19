module

public import EuclideanMidpointRigidity.CriticalAxis

/-! # The two first-derivative eigenspaces at a critical axis -/

@[expose] public section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

/-- The gradient of the fixed-axis cubic profile is the sum of two eigenvectors.
The first is explicitly `(13/7) U`, where `U = (J e)(e,e)`. The statement
allows either vector to vanish. -/
theorem critical_axis_resonances {c : Coeff} {J : E →L[ℝ] Coeff} {e g : E} {a : ℝ}
    (he : K c e e = a • e) (hE : ∀ h, obstruction c J h = 0)
    (hg : ∀ v, ⟪K (J v) e e,e⟫_ℝ = ⟪g,v⟫_ℝ) :
    let U := K (J e) e e
    let V := g - (13/7 : ℝ) • U
    K c e U = (-a/2) • U ∧ K c e V = (a/5) • V := by
  let U := K (J e) e e
  have hu := critical_axis_eigenrelation he (hE e)
  change (2:ℝ) • K c e U + a • U = 0 at hu
  have hU : K c e U = (-a/2) • U := by
    linear_combination (norm := module) (1/2:ℝ) • hu
  refine ⟨hU,?_⟩
  change K c e (g-(13/7:ℝ) • U) = (a/5) • (g-(13/7:ℝ) • U)
  apply ext_inner_right ℝ
  intro v
  have ht := critical_axis_test_relation he hE v
  dsimp only at ht
  rw [hg, hg] at ht
  have hB : ⟪K c e v,U⟫_ℝ = (-a/2)*⟪U,v⟫_ℝ := by
    rw [K_selfAdjoint, hU, real_inner_smul_right, real_inner_comm U v]
  change 11*a*⟪U,v⟫_ℝ - 4*⟪K c e v,U⟫_ℝ + 10*⟪g,K c e v⟫_ℝ - 2*a*⟪g,v⟫_ℝ = 0 at ht
  rw [hB, ← K_selfAdjoint c e g v] at ht
  simp only [sub_eq_add_neg, K_add_right, K_neg_right, K_smul_right, hU,
    inner_add_left, inner_neg_left, real_inner_smul_left]
  linarith only [ht]

/-- Distinct resonant eigenvalues give orthogonal gradient components,
including at a multiple spherical maximum. -/
theorem critical_axis_resonances_orthogonal {c : Coeff} {J : E →L[ℝ] Coeff}
    {e g : E} {a : ℝ} (ha : a ≠ 0) (he : K c e e = a • e)
    (hE : ∀ h, obstruction c J h = 0)
    (hg : ∀ v, ⟪K (J v) e e,e⟫_ℝ = ⟪g,v⟫_ℝ) :
    let U := K (J e) e e
    ⟪U,g-(13/7:ℝ) • U⟫_ℝ = 0 := by
  let U := K (J e) e e
  let V := g-(13/7:ℝ) • U
  obtain ⟨hU,hV⟩ := critical_axis_resonances he hE hg
  have h := K_selfAdjoint c e U V
  change K c e U = (-a/2) • U at hU
  change K c e V = (a/5) • V at hV
  rw [hU,hV,real_inner_smul_left,real_inner_smul_right] at h
  change ⟪U,V⟫_ℝ = 0
  apply (mul_eq_zero.mp (show a*⟪U,V⟫_ℝ=0 by linarith only [h])).resolve_left ha

end EuclideanMidpointRigidity
