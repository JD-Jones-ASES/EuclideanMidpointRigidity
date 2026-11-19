module

public import EuclideanMidpointRigidity.TaylorModel
public import EuclideanMidpointRigidity.CriticalAxis

/-! # The affine sixth-order source at a critical direction -/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity.Jet

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

private theorem realize_product_default (D : Derivatives d) (z : E)
    (ps : List Tree) (u v fallback : Tree) (hs : ps.length ≤ 4) :
    ((product ps u v).getD fallback).realize D z =
      K (listForm D (ps.map (Tree.realize D z))) (u.realize D z) (v.realize D z) := by
  obtain ⟨w,hw⟩ := product_exists ps u v hs
  simpa only [hw,Option.getD_some] using product_realize hw D z

theorem canonical_realize (t : Tree) (D : Derivatives d) (z : E) :
    (canonical t).realize D z = t.realize D z := by
  induction t <;> simp [canonical, realize_product_default, Tree.realize, *]

theorem value_literal (rows : List (ℚ × Tree)) (D : Derivatives d) (z : E) (t : ℝ) :
    value (literal rows) (Tree.realize D z) t =
      (rows.map (fun q ↦ (q.1:ℝ) • q.2.realize D z)).sum := by
  simp [literal,value,Term.value,List.map_map,Function.comp_def,canonical_realize]

theorem field_nil (C : E → Coeff) (p : E) : listForm (fieldDerivatives C p) [] = C p := by
  simpa only [List.replicate_zero,fieldDerivatives,iteratedFDeriv_zero_apply] using
    listForm_replicate (fieldDerivatives C p) 0 (0:E)

theorem field_single (C : E → Coeff) (p u : E) :
    listForm (fieldDerivatives C p) [u] = fderiv ℝ C p u := by
  simpa only [List.replicate_one,fieldDerivatives,iteratedFDeriv_one_apply] using
    listForm_replicate (fieldDerivatives C p) 1 u

/-- At a critical axis satisfying the quartic, the axial derivative enters
the scaled affine part of the sixth-order expression with coefficient `a³`. -/
theorem critical_affine_sixth (C : E → Coeff) (p e : E) (a : ℝ)
    (he : K (C p) e e = a • e) (hE : obstruction (C p) (fderiv ℝ C p) e=0) :
    (360:ℝ) • value affineSixth (Tree.realize (fieldDerivatives C p) e) 0 =
      a^3 • K (fderiv ℝ C p e) e e := by
  let U := K (fderiv ℝ C p e) e e
  have hj : K (fderiv ℝ C p e) e e=U := rfl
  have hB : K (C p) e U = (-a/2) • U := by
    have hu := critical_axis_eigenrelation he hE
    change (2:ℝ) • K (C p) e U + a • U = 0 at hu
    linear_combination (norm := module) (1/2:ℝ) • hu
  rw [affineSixth,value_scale,value_literal]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Tree.realize,field_nil,
    field_single,K_smul_left,K_smul_right,map_smul,K_smul_coeff,he,hj,hB]
  push_cast
  module

end EuclideanMidpointRigidity.Jet
