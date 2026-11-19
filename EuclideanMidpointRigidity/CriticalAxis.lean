module

public import EuclideanMidpointRigidity.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # The quartic equation at a critical direction of the cubic -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

/-- Contracting the quartic with the test vector uses symmetry of both cubics. -/
theorem contract_obstruction (c : Coeff) (J : E →L[ℝ] Coeff) (h : E) :
    ⟪obstruction c J h, h⟫_ℝ =
      5 * ⟪K (J (K c h h)) h h, h⟫_ℝ - 2 * ⟪K c h h, K (J h) h h⟫_ℝ := by
  simp only [obstruction, inner_sub_left, inner_add_left, ← Nat.cast_smul_eq_nsmul ℝ, real_inner_smul_left]
  rw [K_selfAdjoint c h (K (J h) h h) h,
      K_selfAdjoint (J h) h (K c h h) h, real_inner_comm (K (J h) h h) (K c h h)]
  push_cast
  ring

/-- At a critical axis, the axial derivative of the raised cubic product
lies in the eigenspace with eigenvalue `-a/2`. -/
theorem critical_axis_eigenrelation {c : Coeff} {J : E →L[ℝ] Coeff} {e : E} {a : ℝ}
    (he : K c e e = a • e) (hE : obstruction c J e = 0) :
    (2 : ℝ) • K c e (K (J e) e e) + a • K (J e) e e = 0 := by
  simp only [obstruction, he, map_smul, K_smul_coeff, K_smul_right] at hE
  linear_combination (norm := module) hE

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_K {C : ℝ → Coeff} {u v : ℝ → E} {t : ℝ} {C' : Coeff} {u' v' : E}
    (hc : HasDerivAt C C' t) (hu : HasDerivAt u u' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s ↦ K (C s) (u s) (v s))
      (K C' (u t) (v t) + K (C t) u' (v t) + K (C t) (u t) v') t := by
  let inc : Coeff →L[ℝ] (E →L[ℝ] E →L[ℝ] E) := (cubicSubspace d).subtypeL
  have hinc := ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) («E» := Coeff)
    (F := E →L[ℝ] E →L[ℝ] E) (x := C t) inc
  have hc' : HasDerivAt (inc ∘ C) (inc C') t :=
    HasFDerivAt.comp_hasDerivAt («E» := E →L[ℝ] E →L[ℝ] E) (F := Coeff) t hinc hc
  exact ((hc'.clm_apply hu).clm_apply hv)

private theorem triangular_pair (c : Coeff) (e v : E) :
    ⟪K c v e, e⟫_ℝ = ⟪K c e e, v⟫_ℝ := by
  rw [K_symm c v e, K_selfAdjoint, real_inner_comm]

/-- Directional derivative of the scalar contraction at a critical axis.
The spatial derivative slot in `J` is independent of its three cubic slots. -/
theorem critical_axis_test_relation {c : Coeff} {J : E →L[ℝ] Coeff} {e : E} {a : ℝ}
    (he : K c e e = a • e) (hE : ∀ h, obstruction c J h = 0) (v : E) :
    let U := K (J e) e e
    let g := fun l ↦ ⟪K (J l) e e, e⟫_ℝ
    11*a*⟪U,v⟫_ℝ - 4*⟪K c e v,U⟫_ℝ + 10*g (K c e v) - 2*a*g v = 0 := by
  let y := fun t : ℝ ↦ e + t • v
  have hy : HasDerivAt y v 0 := by
    simpa [y] using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add e
  have hy0 : y 0 = e := by simp [y]
  let q := fun t ↦ K c (y t) (y t)
  let u := fun t ↦ K (J (y t)) (y t) (y t)
  have hq : HasDerivAt q ((2 : ℝ) • K c e v) 0 := by
    convert! hasDerivAt_K (hasDerivAt_const (0:ℝ) c) hy hy using 1
    simp only [hy0, K_symm c v e, two_smul]
    simp [K]
  have hq0 : q 0 = a • e := by simp [q, hy0, he]
  have hu : HasDerivAt u
      (K (J v) e e + K (J e) v e + K (J e) e v) 0 := by
    simpa only [u, Function.comp_apply, hy0] using
      (hasDerivAt_K (J.hasFDerivAt.comp_hasDerivAt 0 hy) hy hy)
  let s := fun t ↦ ⟪K (J (q t)) (y t) (y t), y t⟫_ℝ
  have hs := (hasDerivAt_K (J.hasFDerivAt.comp_hasDerivAt 0 hq) hy hy).inner ℝ hy
  have ht := hq.inner ℝ hu
  have hdiff := (hs.const_mul 5).sub (ht.const_mul 2)
  have hzero : (fun t ↦ 5*s t - 2*⟪q t,u t⟫_ℝ) = fun _ ↦ (0:ℝ) := by
    funext t
    change 5*⟪K (J (K c (y t) (y t))) (y t) (y t), y t⟫_ℝ -
      2*⟪K c (y t) (y t), K (J (y t)) (y t) (y t)⟫_ℝ = 0
    rw [← contract_obstruction, hE, inner_zero_left]
  have hz : HasDerivAt (fun t ↦ 5*s t - 2*⟪q t,u t⟫_ℝ) 0 0 := by
    rw [hzero]
    exact hasDerivAt_const _ _
  have hval := hdiff.unique hz
  dsimp only
  simp only [Function.comp_apply, hy0, hq0, u, K_smul_coeff, map_smul, inner_add_left,
    inner_add_right, real_inner_smul_left, K_symm (J e) e v,
    triangular_pair] at hval
  rw [real_inner_comm (K (J v) e e) e, real_inner_comm (K (J e) v e) e,
    triangular_pair (J e) e v] at hval
  linarith only [hval]

/-- The spatial derivative in the direction `U = (J e)(e,e)` at an active axis. -/
theorem critical_axis_source {c : Coeff} {J : E →L[ℝ] Coeff} {e : E} {a : ℝ}
    (ha : a ≠ 0) (he : K c e e = a • e) (hE : ∀ h, obstruction c J h = 0) :
    let U := K (J e) e e
    7*⟪K (J U) e e,e⟫_ℝ = 13*⟪U,U⟫_ℝ := by
  let U := K (J e) e e
  have hu : (2 : ℝ) • K c e U + a • U = 0 := critical_axis_eigenrelation he (hE e)
  have h₁ := congrArg (fun z : E ↦ ⟪z,U⟫_ℝ) hu
  have h₂ := congrArg (fun z : E ↦ ⟪K (J z) e e,e⟫_ℝ) hu
  simp only [inner_add_left, real_inner_smul_left, inner_zero_left] at h₁
  simp [inner_add_left, real_inner_smul_left, K] at h₂
  have ht := critical_axis_test_relation he hE U
  change 11*a*⟪U,U⟫_ℝ - 4*⟪K c e U,U⟫_ℝ +
    10*⟪K (J (K c e U)) e e,e⟫_ℝ - 2*a*⟪K (J U) e e,e⟫_ℝ = 0 at ht
  change 2*⟪K (J (K c e U)) e e,e⟫_ℝ + a*⟪K (J U) e e,e⟫_ℝ = 0 at h₂
  apply mul_left_cancel₀ ha
  change a*(7*⟪K (J U) e e,e⟫_ℝ) = a*(13*⟪U,U⟫_ℝ)
  linarith only [ht, h₁, h₂]

/-- The first spatial prolongation fixes the axial second derivative at a
critical point of nonzero value. The second jet can otherwise be arbitrary. -/
theorem critical_axis_second_derivative {c : Coeff} {J H : E →L[ℝ] Coeff}
    {e : E} {a : ℝ} (ha : a ≠ 0) (he : K c e e = a • e)
    (hE : ∀ h, obstruction c J h = 0)
    (h₁ : obstruction c H e + obstruction (J e) J e = 0) :
    7*a*⟪K (H e) e e,e⟫_ℝ = -17*⟪K (J e) e e,K (J e) e e⟫_ℝ := by
  have hsource := critical_axis_source ha he hE
  have hsum := congrArg (fun z : E ↦ ⟪z,e⟫_ℝ) h₁
  simp only [inner_add_left, inner_zero_left, contract_obstruction, he,
    map_smul, K_smul_coeff, real_inner_smul_left] at hsum
  rw [real_inner_comm (K (H e) e e) e] at hsum
  dsimp only at hsource
  linarith only [hsum, hsource]

end EuclideanMidpointRigidity
