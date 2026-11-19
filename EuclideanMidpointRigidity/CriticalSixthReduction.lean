module

public import EuclideanMidpointRigidity.MidpointJetEquations
public import EuclideanMidpointRigidity.FieldJets
public import EuclideanMidpointRigidity.SecondProlongation

/-! # The vector sixth equation at a critical axis, after two quartic derivatives -/

@[expose] public section
noncomputable section
open Set
open scoped ContDiff
namespace EuclideanMidpointRigidity
open Jet

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

attribute [local irreducible] listForm fieldDerivatives

set_option maxHeartbeats 1000000 in
private theorem higher_sixth_at_axis (C : E → Coeff) (p e : E) (a : ℝ)
    (hc : ContDiffAt ℝ ∞ C p) (he : K (C p) e e=a • e) :
    let J := fderiv ℝ C p
    let H := fderiv ℝ (fderiv ℝ C) p
    let T := fderiv ℝ (fderiv ℝ (fderiv ℝ C)) p
    let U := K (J e) e e
    let V := K (H e e) e e
    let W := K (T e e e) e e
    (360:ℝ) • value higherSixth (Tree.realize (fieldDerivatives C p) e) 0 =
      (4:ℝ) • K (C p) e W - (8:ℝ) • K (J e) e V + (14:ℝ) • K (J V) e e -
      (2:ℝ) • K (H e e) e U + (6:ℝ) • K (H e U) e e + a • W := by
  let D := fieldDerivatives C p
  have hsp : listForm D [e,e,a • e] = a • listForm D [e,e,e] := listForm_middle_smul D [e,e] [] a e
  dsimp only [D] at hsp
  dsimp only
  rw [higherSixth,value_literal]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Tree.realize,field_nil,
    field_single,field_pair C p hc,field_triple_diagonal,he,hsp,K_smul_coeff,K_smul_right]
  push_cast
  module

/-- The source in the critical vector equation is `a³ U`. Both higher
spatial jets and the three undifferentiated cubic factors contribute. -/
theorem critical_sixth_vector {Ω : Set E} {C : E → Coeff} (hΩ : IsOpen Ω)
    (smooth : ContDiffOn ℝ ∞ C Ω) (hm : MidpointJetEquations Ω C) {p : E} (hp : p ∈ Ω)
    (e : E) (a : ℝ) (he : K (C p) e e=a • e) :
    let J := fderiv ℝ C p
    let H := fderiv ℝ (fderiv ℝ C) p
    let T := fderiv ℝ (fderiv ℝ (fderiv ℝ C)) p
    let U := K (J e) e e
    let V := K (H e e) e e
    let W := K (T e e e) e e
    a • W = a^3 • U + (4:ℝ) • K (J V) e e - (8:ℝ) • K (J e) e V +
      (10:ℝ) • K (H e e) e U - (14:ℝ) • K (H e U) e e := by
  have h₄ := hm.quartic hp e
  have h₆ := hm.sixth hp e
  have hA := critical_affine_sixth C p e a he h₄
  have hR := higher_sixth_at_axis C p e a (smooth.contDiffAt (hΩ.mem_nhds hp)) he
  have h₂ := second_prolongation_of_quartic hΩ smooth hm.quartic hp e e
  dsimp only at h₆ h₂ hR ⊢
  simp only [obstruction,he,map_smul,K_smul_coeff,K_smul_right,← Nat.cast_smul_eq_nsmul ℝ] at h₂
  push_cast at h₂
  linear_combination (norm := module) hA + hR - (360:ℝ) • h₆ + (2:ℝ) • h₂

end EuclideanMidpointRigidity
