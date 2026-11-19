module

public import EuclideanMidpointRigidity.CriticalSixthReduction
public import EuclideanMidpointRigidity.CriticalBranch

/-! # Scalar contractions of the prolonged quartic and full sixth equation -/

@[expose] public section
noncomputable section
open Set
open scoped ContDiff InnerProductSpace
namespace EuclideanMidpointRigidity

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

private theorem last_slot (c : Coeff) (e v : E) :
    ⟪K c e v,e⟫_ℝ=⟪K c e e,v⟫_ℝ := by rw [K_selfAdjoint,real_inner_comm]

theorem first_prolongation_scalar {Ω : Set E} {C : E → Coeff} (hΩ : IsOpen Ω)
    (hC : ContDiffOn ℝ 2 C Ω) (hm : QuarticOn Ω C) {p : E} (hp : p ∈ Ω)
    (a : ℝ) (e l : E) (he : K (C p) e e=a • e) :
    let J := fderiv ℝ C p
    let H := fderiv ℝ (fderiv ℝ C) p
    let U := K (J e) e e
    let R := K (J l) e e
    3*a*⟪K (H l e) e e,e⟫_ℝ + 5*⟪K (J R) e e,e⟫_ℝ - 2*⟪R,U⟫_ℝ=0 := by
  have h := congrArg (fun w : E ↦ ⟪w,e⟫_ℝ) (prolongation_of_quartic hΩ hC hm hp l e)
  dsimp only at h ⊢
  simp only [inner_add_left,inner_zero_left,contract_obstruction,he,map_smul,K_smul_coeff,
    real_inner_smul_left] at h
  rw [show ⟪e,K (fderiv ℝ (fderiv ℝ C) p l e) e e⟫_ℝ=
    ⟪K (fderiv ℝ (fderiv ℝ C) p l e) e e,e⟫_ℝ from real_inner_comm _ _] at h
  linarith only [h]

theorem critical_sixth_scalar {Ω : Set E} {C : E → Coeff} (hΩ : IsOpen Ω)
    (hC : ContDiffOn ℝ ∞ C Ω) (hm : MidpointJetEquations Ω C) {p : E} (hp : p ∈ Ω)
    {a : ℝ} (ha : a≠0) (e : E) (he : K (C p) e e=a • e) :
    let J := fderiv ℝ C p
    let H := fderiv ℝ (fderiv ℝ C) p
    let U := K (J e) e e
    let V := K (H e e) e e
    17*⟪K (J V) e e,e⟫_ℝ = 32*⟪K (H e U) e e,e⟫_ℝ := by
  let J := fderiv ℝ C p
  let H := fderiv ℝ (fderiv ℝ C) p
  let T := fderiv ℝ (fderiv ℝ (fderiv ℝ C)) p
  let U := K (J e) e e
  let V := K (H e e) e e
  let W := K (T e e e) e e
  have hU : ⟪U,e⟫_ℝ=0 := critical_axial_orthogonal ha he
    (hm.quartic hp e)
  have h₆ := congrArg (fun w : E ↦ ⟪w,e⟫_ℝ) (critical_sixth_vector hΩ hC hm hp e a he)
  change ⟪a • W,e⟫_ℝ=⟪a^3 • U + (4:ℝ) • K (J V) e e - (8:ℝ) • K (J e) e V +
    (10:ℝ) • K (H e e) e U - (14:ℝ) • K (H e U) e e,e⟫_ℝ at h₆
  simp only [inner_add_left,inner_sub_left,real_inner_smul_left,hU,mul_zero,zero_add,
    last_slot (J e) e V,last_slot (H e e) e U] at h₆
  have h₂ := congrArg (fun w : E ↦ ⟪w,e⟫_ℝ)
    (second_prolongation_of_quartic hΩ hC hm.quartic hp e e)
  change ⟪obstruction (C p) (T e e) e + (2:ℝ) • obstruction (J e) (H e) e +
    obstruction (H e e) J e,e⟫_ℝ=⟪0,e⟫_ℝ at h₂
  simp only [inner_add_left,real_inner_smul_left,inner_zero_left,contract_obstruction,he,
    map_smul,K_smul_coeff] at h₂
  change 5*(a*⟪W,e⟫_ℝ)-2*(a*⟪e,W⟫_ℝ) +
    2*(5*⟪K (H e U) e e,e⟫_ℝ-2*⟪U,V⟫_ℝ) +
    (5*⟪K (J V) e e,e⟫_ℝ-2*⟪V,U⟫_ℝ)=0 at h₂
  rw [show ⟪e,W⟫_ℝ=⟪W,e⟫_ℝ from real_inner_comm _ _,
    show ⟪V,U⟫_ℝ=⟪U,V⟫_ℝ from real_inner_comm _ _] at h₂
  change a*⟪W,e⟫_ℝ = 4*⟪K (J V) e e,e⟫_ℝ-8*⟪U,V⟫_ℝ+
    10*⟪V,U⟫_ℝ-14*⟪K (H e U) e e,e⟫_ℝ at h₆
  rw [show ⟪V,U⟫_ℝ=⟪U,V⟫_ℝ from real_inner_comm _ _] at h₆
  change 17*⟪K (J V) e e,e⟫_ℝ = 32*⟪K (H e U) e e,e⟫_ℝ
  linarith only [h₆,h₂]

end EuclideanMidpointRigidity
