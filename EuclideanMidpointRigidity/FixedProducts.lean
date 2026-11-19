module

public import EuclideanMidpointRigidity.FixedDirections
public import EuclideanMidpointRigidity.WeightedKillingOrder
public import EuclideanMidpointRigidity.PolynomialCoordinate
public import EuclideanMidpointRigidity.SliceDecoupling
public import EuclideanMidpointRigidity.KillingSquare

/-! # Products with a fixed direction remain fixed -/

public section
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity
open Quartic FixedAxis
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d
set_option backward.isDefEq.respectTransparency false

theorem fixed_slice_constant {W : Set E} {C : E → T} (hW : IsOpen W) (hv : IsPreconnected W) (hC : ContDiffOn ℝ ∞ C W)
    {u : E} (hu : u ∈ fixedDirections C W) {p x : E} (hp : p ∈ W) (hx : x ∈ W) :
    sliceMap u (C x)=sliceMap u (C p) := by
  let L := sliceMap u
  have hd (y : E) (hy : y ∈ W) : HasFDerivAt (𝕜 := ℝ) (L ∘ C) 0 y := by
    have h := L.hasFDerivAt.comp y ((hC.contDiffAt (hW.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
    have he : L.comp (fderiv ℝ C y)=0 := by
      ext l v : 2
      exact (hu y hy).2 l v
    rwa [he] at h
  exact hW.is_const_of_fderiv_eq_zero hv (fun y hy ↦ (hd y hy).differentiableAt.differentiableWithinAt)
    (fun {y} hy ↦ (hd y hy).fderiv) hx hp

private theorem kernel_entry {j : T} (B : E →L[ℝ] E) (h : ∀ y, cubicEntry j y y (B y)=0) {z : E} (hz : B z=0) (v : E) :
    cubicEntry j z z (B v)=0 := by
  let X := fun t : ℝ ↦ z+t • v
  have dx : HasDerivAt X v 0 := by simpa only [X,one_smul,id_eq] using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add z
  have h₀ : X 0=z := by simp [X]
  have dt := (hasDerivAt_K (hasDerivAt_const (0:ℝ) j) dx dx).inner ℝ (B.hasFDerivAt.comp_hasDerivAt 0 dx)
  have he := dt.unique ((hasDerivAt_const (0:ℝ) (0:ℝ)).congr_of_eventuallyEq (Eventually.of_forall fun t ↦ h (X t)))
  simpa only [Function.comp_apply,h₀,hz,inner_zero_right,add_zero,cubicEntry] using he

theorem fixed_product {W : Set E} {C : E → T} (hW : IsOpen W) (hv : Convex ℝ W) (hC : ContDiffOn ℝ ∞ C W)
    (hQ : MidpointJetEquations W C) {u : E} (hu : u ∈ fixedDirections C W) {p : E} (hp : p ∈ W) (v : E) :
    K (C p) u v ∈ fixedDirections C W := by
  let B := sliceMap u (C p)
  have hB (x : E) (hx : x ∈ W) (l : E) : K (C x) u l=B l :=
    DFunLike.congr_fun (fixed_slice_constant hW hv.isPreconnected hC hu hp hx) l
  have hkill (x : E) (hx : x ∈ W) (y : E) : directionProfile y (fderiv ℝ C x (B y))=0 :=
    hB x hx y ▸ weighted_killing (hQ.quartic hx) (hu x hx).1 (hu x hx).2 y
  have hsp (x : E) (hx : x ∈ W) (a : E) : fderiv ℝ C x (B a)=0 :=
    polynomial_coordinate_stationary hW hv hC hQ (B a) (fun _ hy ↦ weighted_killing_order hW hC B hkill hy a) hx
  have hs (x : E) (hx : x ∈ W) (a : E) : fderiv ℝ C x (K (C x) u a)=0 := by rw [hB x hx,hsp x hx]
  have sq (x : E) (hx : x ∈ W) (l a : E) : K (fderiv ℝ C x l) (B a) (B a)=0 := by
    let b := B a
    let L := (ContinuousLinearMap.apply ℝ E b).comp (sliceMap b)
    let N := L ∘ C
    have hd (y : E) (hy : y ∈ W) : fderiv ℝ N y=L.comp (fderiv ℝ C y) :=
      (L.hasFDerivAt.comp y ((hC.contDiffAt (hW.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt).fderiv
    have hk (y : E) (hy : y ∈ W) (w : E) : ⟪fderiv ℝ N y w,w⟫_ℝ=0 := by
      rw [hd y hy]
      change jetEntry (fderiv ℝ C y) w (B a) (B a) w=0
      rw [← hB y hy]
      exact square_killing (hQ.quartic hy) (hu y hy).1 (hu y hy).2 (hs y hy) w a
    have ha (y : E) (hy : y ∈ W) : fderiv ℝ N y (N y)=0 := by
      rw [hd y hy]
      change K (fderiv ℝ C y (K (C y) b b)) b b=0
      have eq := hQ.quartic hy b
      have hb : fderiv ℝ C y b=0 := hsp y hy a
      have hzero (v w : E) : K (0:T) v w=0 := rfl
      simp only [obstruction,hb,hzero,show ∀ v, K (C y) v 0=0 from fun _ ↦ map_zero _,nsmul_zero,zero_add,sub_zero] at eq
      have eq' : (5:ℝ) • K (fderiv ℝ C y (K (C y) b b)) b b=0 := by simpa only [← Nat.cast_smul_eq_nsmul ℝ,Nat.cast_ofNat] using eq
      exact (smul_eq_zero.mp eq').resolve_left (by norm_num)
    have h := DFunLike.congr_fun (parallel_killing_vector hW (L.contDiff.comp_contDiffOn hC) hk ha hx) l
    rw [hd x hx] at h
    exact h
  intro x hx
  refine ⟨hsp x hx v,?_⟩
  intro l w
  let j := fderiv ℝ C x l
  have pair (a b : E) : K j (B a) (B b)=0 := by
    have h := sq x hx l (a+b)
    simp only [map_add,K_add_left,K_add_right,sq x hx l,zero_add,add_zero,K_symm _ (B b) (B a)] at h
    have hh : (2:ℝ) • K j (B a) (B b)=0 := by rwa [two_smul]
    exact (smul_eq_zero.mp hh).resolve_left (by norm_num)
  have hc (y : E) : cubicEntry j y y (B y)=0 := by
    rw [← hB x hx]
    exact (slice_decoupling (hQ.quartic hx) (hu x hx).1 (hu x hx).2 (hs x hx) y l).2
  have diag (y : E) : ⟪K j (B v) y,y⟫_ℝ=0 := by
    obtain ⟨_,⟨a,rfl⟩,z,hz,he⟩ := B.toLinearMap.range.exists_add_mem_mem_orthogonal y
    have hk : B z=0 := by
      apply (inner_self_eq_zero (𝕜 := ℝ)).mp
      have h := (Submodule.mem_orthogonal _ _).mp hz (B (B z)) ⟨B z,rfl⟩
      exact (K_selfAdjoint (C p) u (B z) z).symm.trans h
    have hzz : ⟪K j (B v) z,z⟫_ℝ=0 := (inner_slot j z z (B v)).symm.trans (kernel_entry B hc hk v)
    have hza : ⟪K j (B v) z,B a⟫_ℝ=0 := by rw [K_selfAdjoint,pair,inner_zero_right]
    change y=B a+z at he
    rw [he,K_add_right,pair,zero_add,inner_add_right,hza,hzz,add_zero]
  have h := diag (w+K j (B v) w)
  let n := K j (B v) w
  change ⟪K j (B v) (w+n),w+n⟫_ℝ=0 at h
  rw [K_add_right,inner_add_left,inner_add_right,inner_add_right,diag,diag,zero_add,add_zero,
    K_selfAdjoint j (B v) n w] at h
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  change ⟪n,n⟫_ℝ=0
  change ⟪n,n⟫_ℝ+⟪n,n⟫_ℝ=0 at h
  linarith only [h]

end EuclideanMidpointRigidity

