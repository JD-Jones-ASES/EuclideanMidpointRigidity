module

public import EuclideanMidpointRigidity.KillingCubics

/-! # A Euclidean Killing vector field with zero acceleration is parallel -/

public section
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d
set_option backward.isDefEq.respectTransparency false

private theorem skew_of_diagonal (L : E →L[ℝ] E) (h : ∀ v, ⟪L v,v⟫_ℝ=0) (a b : E) :
    ⟪L a,b⟫_ℝ+⟪L b,a⟫_ℝ=0 := by
  have he := h (a+b)
  simp only [map_add,inner_add_left,inner_add_right,h,zero_add,add_zero] at he
  simpa only [add_comm] using he

theorem parallel_killing_vector {W : Set E} {N : E → E} (hW : IsOpen W) (hN : ContDiffOn ℝ ∞ N W)
    (hk : ∀ x ∈ W, ∀ v, ⟪fderiv ℝ N x v,v⟫_ℝ=0) (ha : ∀ x ∈ W, fderiv ℝ N x (N x)=0)
    {p : E} (hp : p ∈ W) : fderiv ℝ N p=0 := by
  let J := fderiv ℝ N
  let H := fderiv ℝ J p
  have hn := hN.contDiffAt (hW.mem_nhds hp)
  have hj : HasFDerivAt J H p := ((hn.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hsym (v w : E) : H v w=H w v := hn.isSymmSndFDerivAt (by simp) v w
  have hdiag (v a : E) : ⟪H v a,a⟫_ℝ=0 := by
    let L := (innerSL ℝ a).comp (ContinuousLinearMap.apply ℝ E a)
    have he : L ∘ J =ᶠ[𝓝 p] (fun _ ↦ 0) :=
      (show ∀ᶠ x in 𝓝 p, x ∈ W from hW.mem_nhds hp).mono fun x hx ↦ (real_inner_comm _ _).trans (hk x hx a)
    have hz := (L.hasFDerivAt.comp p hj).unique ((hasFDerivAt_const (0:ℝ) p).congr_of_eventuallyEq he)
    exact (real_inner_comm _ _).trans (DFunLike.congr_fun hz v)
  have hs (v : E) : H v v=0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    let w := H v v
    have h := skew_of_diagonal (H v) (hdiag v) v w
    rw [hsym v w,hdiag,add_zero] at h
    exact h
  have hH (v w : E) : H v w=0 := by
    have hh := hs (v+w)
    simp only [map_add,add_apply,hs,zero_add,add_zero,← hsym v w] at hh
    have he : (2:ℝ) • H v w=0 := by rwa [two_smul]
    exact (smul_eq_zero.mp he).resolve_left (by norm_num)
  have he : (fun x ↦ J x (N x)) =ᶠ[𝓝 p] (fun _ ↦ 0) :=
    (show ∀ᶠ x in 𝓝 p, x ∈ W from hW.mem_nhds hp).mono fun x hx ↦ ha x hx
  have hz := (hj.clm_apply (hn.differentiableAt (by simp)).hasFDerivAt).unique ((hasFDerivAt_const (0:E) p).congr_of_eventuallyEq he)
  ext v : 1
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  have h := DFunLike.congr_fun hz v
  change J p (J p v)+H v (N p)=0 at h
  rw [hH,add_zero] at h
  have h' := skew_of_diagonal (J p) (hk p hp) v (J p v)
  simpa only [h,inner_zero_left,add_zero] using h'

end EuclideanMidpointRigidity

