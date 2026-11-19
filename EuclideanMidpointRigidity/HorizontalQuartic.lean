module

public import EuclideanMidpointRigidity.CriticalAxis
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Horizontal transport from the quartic at arbitrary test vectors -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity.Horizontal
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d

private theorem triangle (c : T) (h v : E) : ⟪K c v h,h⟫_ℝ=⟪K c h h,v⟫_ℝ := by
  rw [K_symm c v h,K_selfAdjoint,real_inner_comm]

theorem quartic_test {c : T} {J : E →L[ℝ] T} (hQ : ∀ w, obstruction c J w=0) (h v : E) :
    10*⟪K (J (K c h v)) h h,h⟫_ℝ+15*⟪K (J (K c h h)) h h,v⟫_ℝ-
    4*⟪K c h v,K (J h) h h⟫_ℝ-2*⟪K c h h,K (J v) h h⟫_ℝ-4*⟪K c h h,K (J h) v h⟫_ℝ=0 := by
  let y := fun t : ℝ ↦ h+t • v
  have hy : HasDerivAt y v 0 := by simpa [y] using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add h
  have hy₀ : y 0=h := by simp [y]
  let q := fun t ↦ K c (y t) (y t)
  have dq : HasDerivAt q ((2:ℝ) • K c h v) 0 := by
    convert! hasDerivAt_K (hasDerivAt_const (0:ℝ) c) hy hy using 1
    simp only [hy₀,K_symm c v h,two_smul]; simp [K]
  let u := fun t ↦ K (J (y t)) (y t) (y t)
  have du : HasDerivAt u (K (J v) h h+K (J h) v h+K (J h) h v) 0 := by
    simpa only [u,Function.comp_apply,hy₀] using hasDerivAt_K (J.hasFDerivAt.comp_hasDerivAt 0 hy) hy hy
  let s := fun t ↦ ⟪K (J (q t)) (y t) (y t),y t⟫_ℝ
  have ds := (hasDerivAt_K (J.hasFDerivAt.comp_hasDerivAt 0 dq) hy hy).inner ℝ hy
  have dt := dq.inner ℝ du
  have dh := (ds.const_mul 5).sub (dt.const_mul 2)
  have he : HasDerivAt (fun t ↦ 5*s t-2*⟪q t,u t⟫_ℝ) 0 0 := by
    have hz (t : ℝ) : 5*s t-2*⟪q t,u t⟫_ℝ=0 := by
      rw [← contract_obstruction,hQ,inner_zero_left]
    simp_rw [hz]; exact hasDerivAt_const _ _
  have eq := dh.unique he
  simp only [Function.comp_apply,q,u,hy₀,K_smul_coeff,map_smul,inner_add_left,inner_add_right,real_inner_smul_left,
    K_symm (J (K c h h)) h v,K_symm (J h) h v,triangle] at eq
  linarith only [eq]

def doubleShift (c : T) (h : E) (a : ℝ) (v : E) := (2:ℝ) • K c h v+a • v
def tenShift (c : T) (h : E) (a : ℝ) (v : E) := (10:ℝ) • K c h v-(2*a) • v
def elevenShift (c : T) (h : E) (a : ℝ) (v : E) := (11*a) • v-(4:ℝ) • K c h v

def spatialSlice (J : E →L[ℝ] T) (h : E) : E →L[ℝ] E :=
  ((ContinuousLinearMap.apply ℝ E h).comp ((ContinuousLinearMap.apply ℝ (E →L[ℝ] E) h).comp (cubicSubspace d).subtypeL)).comp J

def transport (c : T) (h : E) (a : ℝ) (l : E) := tenShift c h a (doubleShift c h a l)

def correction (c : T) (J : E →L[ℝ] T) (h : E) (a : ℝ) (l : E) :=
  let v := doubleShift c h a l
  let w := elevenShift c h a l
  (spatialSlice J h).adjoint ((5:ℝ) • w-(15:ℝ) • v)-(4:ℝ) • K (J h) h w+
    (2:ℝ) • K (J v) h h+(4:ℝ) • K (J h) h v

private theorem vector_row {c : T} {J : E →L[ℝ] T} (h : E) (a : ℝ) (δ : E) (hk : K c h h=a • h+δ)
    (hQ : obstruction c J h=0) :
    doubleShift c h a (K (J h) h h)= -(5:ℝ) • K (J δ) h h+(4:ℝ) • K (J h) h δ := by
  unfold obstruction at hQ
  rw [hk] at hQ
  simp only [map_add,map_smul,K_add_coeff,K_smul_coeff,K_add_right,K_smul_right] at hQ
  dsimp only [doubleShift]
  linear_combination (norm := module) hQ

private theorem scalar_row {c : T} {J : E →L[ℝ] T} (h v : E) (a : ℝ) (δ : E) (hk : K c h h=a • h+δ)
    (hQ : ∀ w, obstruction c J w=0) :
    ⟪K (J (tenShift c h a v)) h h,h⟫_ℝ+⟪elevenShift c h a v,K (J h) h h⟫_ℝ+
      15*⟪K (J δ) h h,v⟫_ℝ-2*⟪δ,K (J v) h h⟫_ℝ-4*⟪δ,K (J h) h v⟫_ℝ=0 := by
  have e := quartic_test hQ h v
  rw [hk] at e
  simp only [map_add,map_smul,K_add_coeff,K_smul_coeff,inner_add_left,real_inner_smul_left] at e
  have hp : ⟪h,K (J h) v h⟫_ℝ=⟪v,K (J h) h h⟫_ℝ := by
    calc
      _ = ⟪K (J h) v h,h⟫_ℝ := real_inner_comm _ _
      _ = ⟪K (J h) h h,v⟫_ℝ := triangle _ _ _
      _ = _ := real_inner_comm _ _
  rw [hp,real_inner_comm (K (J v) h h) h,real_inner_comm v (K (J h) h h)] at e
  simp only [tenShift,elevenShift,map_sub,map_smul,K_sub_coeff,K_smul_coeff,inner_sub_left,real_inner_smul_left,
    K_symm (J h) h v]
  linarith only [e]

theorem transport_identity {c : T} {J : E →L[ℝ] T} (hQ : ∀ w, obstruction c J w=0) (h : E) (a : ℝ) (l : E) :
    ⟪K (J (transport c h a l)) h h,h⟫_ℝ=⟪K c h h-a • h,correction c J h a l⟫_ℝ := by
  let δ := K c h h-a • h
  let v := doubleShift c h a l
  let w := elevenShift c h a l
  have hk : K c h h=a • h+δ := by dsimp only [δ]; abel
  have r₁ := vector_row h a δ hk (hQ h)
  have r₂ := scalar_row h v a δ hk hQ
  have he (z : E) : ⟪elevenShift c h a v,z⟫_ℝ=⟪w,doubleShift c h a z⟫_ℝ := by
    dsimp only [v,w,elevenShift,doubleShift]
    simp only [K_add_right,K_smul_right,inner_sub_left,inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right]
    simp only [K_selfAdjoint c h]
    ring
  rw [he,r₁] at r₂
  change ⟪K (J (tenShift c h a v)) h h,h⟫_ℝ=⟪δ,(spatialSlice J h).adjoint ((5:ℝ) • w-(15:ℝ) • v)-(4:ℝ) • K (J h) h w+
    (2:ℝ) • K (J v) h h+(4:ℝ) • K (J h) h v⟫_ℝ
  simp only [inner_add_right,inner_sub_right,real_inner_smul_right,ContinuousLinearMap.adjoint_inner_right] at r₂ ⊢
  change ⟪K (J (tenShift c h a v)) h h,h⟫_ℝ=5*⟪K (J δ) h h,w⟫_ℝ-15*⟪K (J δ) h h,v⟫_ℝ-
    4*⟪δ,K (J h) h w⟫_ℝ+2*⟪δ,K (J v) h h⟫_ℝ+4*⟪δ,K (J h) h v⟫_ℝ
  rw [← K_selfAdjoint (J h) h δ w,real_inner_comm w (K (J h) h δ),real_inner_comm w (K (J δ) h h)]
  linarith only [r₂]

end EuclideanMidpointRigidity.Horizontal

