module

public import EuclideanMidpointRigidity.FixedFactorRows
public import EuclideanMidpointRigidity.HorizontalInvariants

/-! # Algebra of a constant slice with spatially inactive image -/

public section
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity.FixedAxis
open Quartic
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d
set_option backward.isDefEq.respectTransparency false

private theorem scalar_row_rate {c : T} {J : E →L[ℝ] T} {u : E}
    (h : ∀ y, ⟪K (J y) y y,K c u y⟫_ℝ=0) (y l : E) :
    jetEntry J l y y (K c u y)+2*jetEntry J y y (K c u y) l+jetEntry J y y y (K c u l)=0 := by
  let X := fun t : ℝ ↦ y+t • l
  have dx : HasDerivAt X l 0 := by simpa only [X,one_smul,id_eq] using ((hasDerivAt_id (0:ℝ)).smul_const l).const_add y
  have h₀ : X 0=y := by simp [X]
  have ht := (hasDerivAt_K (J.hasFDerivAt.comp_hasDerivAt 0 dx) dx dx).inner ℝ ((c.val u).hasFDerivAt.comp_hasDerivAt 0 dx)
  have H := ht.unique ((hasDerivAt_const (0:ℝ) (0:ℝ)).congr_of_eventuallyEq (Eventually.of_forall fun t ↦ h (X t)))
  rw [add_comm] at H
  change ⟪K (J l) (X 0) (X 0)+K (J (X 0)) l (X 0)+K (J (X 0)) (X 0) l,K c u (X 0)⟫_ℝ+
    ⟪K (J (X 0)) (X 0) (X 0),K c u l⟫_ℝ=0 at H
  simp only [h₀,inner_add_left] at H
  change jetEntry J l y y (K c u y)+jetEntry J y l y (K c u y)+jetEntry J y y l (K c u y)+jetEntry J y y y (K c u l)=0 at H
  simp only [jetEntry_swap₁,jetEntry_swap₂] at H ⊢
  linarith only [H]

theorem slice_decoupling {c : T} {J : E →L[ℝ] T} {u : E} (hQ : ∀ v, obstruction c J v=0)
    (hu : J u=0) (hJ : ∀ l v, K (J l) u v=0) (hB : ∀ v, J (K c u v)=0) (y l : E) :
    jetEntry J y y y (K c u l)=0 ∧ jetEntry J l y y (K c u y)=0 := by
  let B := c.val u
  let U := K (J y) y y
  have rate := scalar_row_rate (fun v ↦ (factor_rows hQ hu hJ v v).1) y
  have row (o : E) : 2*jetEntry J y y y (B o)-8*jetEntry J y y (B y) o=0 := by
    have h := (factor_rows hQ hu hJ y o).2
    change 2*jetEntry J y y y (B o)+10*jetEntry J (B y) y y o-8*jetEntry J y y (B y) o=0 at h
    have he : jetEntry J (B y) y y o=0 := by
      change cubicEntry (J (K c u y)) y y o=0
      rw [hB]; simp [cubicEntry,K]
    simpa only [he,mul_zero,add_zero] using h
  have zero (o : E) : jetEntry J (B o) y y (B y)=0 := by
    change cubicEntry (J (K c u o)) y y (B y)=0
    rw [hB]; simp [cubicEntry,K]
  have active (o : E) : jetEntry J y y y (B (B o))=0 := by
    have h := rate (B o)
    change jetEntry J (B o) y y (B y)+2*jetEntry J y y (B y) (B o)+jetEntry J y y y (B (B o))=0 at h
    rw [zero] at h
    linarith only [h,row (B o)]
  have hU : B U=0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    exact (K_selfAdjoint c u U (B U)).trans (active U)
  have hr (v : E) : jetEntry J y y y (B v)=0 := by
    change ⟪U,K c u v⟫_ℝ=0
    rw [← K_selfAdjoint c u U v]
    change ⟪B U,v⟫_ℝ=0
    rw [hU,inner_zero_left]
  refine ⟨hr l,?_⟩
  have h := rate l
  change jetEntry J l y y (B y)+2*jetEntry J y y (B y) l+jetEntry J y y y (B l)=0 at h
  change jetEntry J l y y (B y)=0
  linarith only [h,hr l,row l]

/-- In the image of the slice, the square field satisfies the vector Killing equation. -/
theorem square_killing {c : T} {J : E →L[ℝ] T} {u : E} (hQ : ∀ v, obstruction c J v=0)
    (hu : J u=0) (hJ : ∀ l v, K (J l) u v=0) (hB : ∀ v, J (K c u v)=0) (l v : E) :
    jetEntry J l (K c u v) (K c u v) l=0 := by
  let a := K c u v
  let X := fun t : ℝ ↦ l+t • a
  have dx : HasDerivAt X a 0 := by simpa only [X,one_smul,id_eq] using ((hasDerivAt_id (0:ℝ)).smul_const a).const_add l
  have h₀ : X 0=l := by simp [X]
  have dt := (hasDerivAt_K (J.hasFDerivAt.comp_hasDerivAt 0 dx) dx dx).inner ℝ (hasDerivAt_const (0:ℝ) a)
  have h := dt.unique ((hasDerivAt_const (0:ℝ) (0:ℝ)).congr_of_eventuallyEq
    (Eventually.of_forall fun t ↦ (slice_decoupling hQ hu hJ hB (X t) v).1))
  have ha : J a=0 := hB v
  have hzero (x y : E) : K (0:T) x y=0 := rfl
  simp only [Function.comp_apply,h₀,ha,hzero,zero_add,inner_zero_right,inner_add_left] at h
  change jetEntry J l a l a+jetEntry J l l a a=0 at h
  change jetEntry J l a a l=0
  simp only [jetEntry_swap₁,jetEntry_swap₂] at h ⊢
  linarith only [h]

end EuclideanMidpointRigidity.FixedAxis

