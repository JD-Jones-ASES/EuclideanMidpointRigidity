module

public import EuclideanMidpointRigidity.CubicNorm
public import EuclideanMidpointRigidity.ResonantPlane

/-! # The norm inequalities in the mixed resonant plane -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity

namespace ResonantPlane

def k : ℝ := 219375/86354

theorem ratio_coordinates {p : ResonantPlane} (hl : p.LowRows) (hs : p.scalarSixth=0)
    (hu : 0<p.u) (hv : 0<p.v) {t : ℝ} (ht : p.v=t*p.u) :
    p.t111=(650/153)*k*t^2*p.t122 ∧ p.t112= -k*t*p.t122 ∧
      t*p.t222= -(159/1300)*p.t122 := by
  have hm := mixed_cubic_relation hl hu hv hs
  have hd := hl.solve
  have hx := hd.t111
  have hy := hd.t222
  rw [ht] at hm hx hy
  have h₁ : p.t112= -k*t*p.t122 := by
    apply (mul_left_inj' hu.ne').mp
    unfold k
    linear_combination hm / 86354
  refine ⟨?_,h₁,?_⟩
  · apply (mul_left_inj' hu.ne').mp
    rw [h₁] at hx
    linear_combination hx
  · apply (mul_left_inj' hu.ne').mp
    linear_combination hy

end ResonantPlane

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

private theorem quadratic_components (c : Coeff) (w x y : E) (α β t : ℝ) :
    let Y := α • x+(t*β) • y
    ⟪w,K c Y Y⟫_ℝ=α^2*⟪w,K c x x⟫_ℝ+2*t*α*β*⟪w,K c x y⟫_ℝ+
      t^2*β^2*⟪w,K c y y⟫_ℝ := by
  simp only [K_add_left,K_add_right,K_smul_left,K_smul_right,K_symm c y x,
    inner_add_right,real_inner_smul_right]
  ring

/-- The external vectors may be any orthonormal completion, or any subfamily
of one. The three internal components use the same cubic as every external term. -/
theorem mixed_norm_inequality {ι : Type*} [Fintype ι] (outside : ι → E)
    {c : Coeff} {e x y : E} {t n : ℝ}
    (hon : Orthonormal ℝ (Sum.elim ![e,x,y] outside))
    (hdiag : ∀ w : E, ‖w‖=1 → ⟪K c w w,w⟫_ℝ≤1)
    (hbx : K c e x=(-1/2:ℝ) • x) (hby : K c e y=(1/5:ℝ) • y)
    (h111 : ⟪x,K c x x⟫_ℝ=(650/153)*ResonantPlane.k*t^2*n)
    (h112 : ⟪y,K c x x⟫_ℝ= -ResonantPlane.k*t*n)
    (h122 : ⟪x,K c y y⟫_ℝ=n) (h222 : t*⟪y,K c y y⟫_ℝ= -(159/1300)*n)
    (α β : ℝ) :
    let r := t^2
    let h := r*n^2
    let P := (650/153)*ResonantPlane.k*α^2-2*ResonantPlane.k*α*β+β^2
    let J := -ResonantPlane.k*α^2+2*α*β-(159/1300)*β^2
    (∑ i, (α^2*⟪outside i,K c x x⟫_ℝ+2*α*β*(t*⟪outside i,K c x y⟫_ℝ)+
      β^2*(t^2*⟪outside i,K c y y⟫_ℝ))^2)+(r*P^2+J^2)*h ≤
      (3/4)*α^4+(11/5)*r*α^2*β^2+(24/25)*r^2*β^4 := by
  classical
  let Y := α • x+(t*β) • y
  let r := t^2
  let h := r*n^2
  let P := (650/153)*ResonantPlane.k*α^2-2*ResonantPlane.k*α*β+β^2
  let J := -ResonantPlane.k*α^2+2*α*β-(159/1300)*β^2
  have hx : ‖x‖=1 := hon.norm_eq_one (Sum.inl (1 : Fin 3))
  have hy : ‖y‖=1 := hon.norm_eq_one (Sum.inl (2 : Fin 3))
  have hxy : ⟪x,y⟫_ℝ=0 := hon.inner_eq_zero (i := Sum.inl (1 : Fin 3)) (j := Sum.inl 2)
    (fun h ↦ (by decide : (1 : Fin 3)≠2) (Sum.inl.inj h))
  have hxx : ⟪x,x⟫_ℝ=1 := by rw [real_inner_self_eq_norm_sq,hx]; norm_num
  have hyy : ⟪y,y⟫_ℝ=1 := by rw [real_inner_self_eq_norm_sq,hy]; norm_num
  have hY : ‖Y‖^2=α^2+r*β^2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [Y,inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
      hxx,hyy,hxy,show ⟪y,x⟫_ℝ=0 by rw [real_inner_comm,hxy]]
    dsimp only [r]
    ring
  have tri (l m : E) : ⟪e,K c l m⟫_ℝ=⟪K c e l,m⟫_ℝ := by rw [← K_selfAdjoint,K_symm c l e]
  have he : ⟪e,K c Y Y⟫_ℝ= -α^2/2+r*β^2/5 := by
    rw [quadratic_components,tri,tri,tri,hbx,hby]
    simp only [real_inner_smul_left,hxx,hxy,hyy]
    dsimp only [r]
    ring
  have h₁ : ⟪x,K c Y Y⟫_ℝ=r*n*P := by
    rw [quadratic_components,h111,h122,show ⟪x,K c x y⟫_ℝ=⟪y,K c x x⟫_ℝ by
      rw [← K_selfAdjoint,real_inner_comm],h112]
    dsimp only [r,P]
    ring
  have h₂ : ⟪y,K c Y Y⟫_ℝ=t*n*J := by
    rw [quadratic_components,h112,show ⟪y,K c x y⟫_ℝ=⟪x,K c y y⟫_ℝ by
      rw [K_symm c x y,← K_selfAdjoint,real_inner_comm],h122]
    dsimp only [J]
    linear_combination t*β^2*h222
  have hout (i : ι) : ⟪outside i,K c Y Y⟫_ℝ=
      α^2*⟪outside i,K c x x⟫_ℝ+2*α*β*(t*⟪outside i,K c x y⟫_ℝ)+
      β^2*(t^2*⟪outside i,K c y y⟫_ℝ) := by rw [quadratic_components]; ring
  have hnorm := cubic_diagonal_norm_bound c 1 (by norm_num) hdiag Y
  rw [one_mul,hY] at hnorm
  have hb := hon.sum_inner_products_le (s := Finset.univ) (K c Y Y)
  simp only [Fintype.sum_sum_type,Fin.sum_univ_three,Sum.elim_inl,Sum.elim_inr,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Real.norm_eq_abs,sq_abs] at hb
  change ⟪e,K c Y Y⟫_ℝ^2+⟪x,K c Y Y⟫_ℝ^2+⟪y,K c Y Y⟫_ℝ^2+
    (∑ i, ⟪outside i,K c Y Y⟫_ℝ^2) ≤ ‖K c Y Y‖^2 at hb
  rw [he,h₁,h₂] at hb
  simp only [hout] at hb
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  change _+(r*P^2+J^2)*h ≤ _
  dsimp only [h,r] at hb hsq ⊢
  linarith only [hb,hsq]

end EuclideanMidpointRigidity
