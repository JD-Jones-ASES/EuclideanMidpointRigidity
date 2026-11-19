module

public import EuclideanMidpointRigidity.DirectionalDerivatives

/-! # The leading derivative of a product when the lower derivatives vanish -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.directions
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem directional_apply {A : E → F →L[ℝ] G} {v : E → F} {p : E}
    (hA : DifferentiableAt ℝ A p) (hv : DifferentiableAt ℝ v p) (w : E) :
    directional (fun x ↦ A x (v x)) w p=directional A w p (v p)+A p (directional v w p) := by
  simp only [directional,fderiv_clm_apply hA hv,add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply]
  abel

theorem leading_apply {W : Set E} (hW : IsOpen W) {p : E} (hp : p ∈ W)
    (xs : List E) {A : E → F →L[ℝ] G} {v : E → F} (hA : ContDiffOn ℝ ∞ A W) (hv : ContDiffOn ℝ ∞ v W)
    (hzero : ∀ ys : List E, ys.length<xs.length → directions A ys p=0) :
    directions (fun x ↦ A x (v x)) xs p=directions A xs p (v p) := by
  induction xs using List.reverseRecOn generalizing A v with
  | nil => rfl
  | append_singleton xs w ih =>
    let A' := directional A w
    let v' := directional v w
    have hsA : ContDiffOn ℝ ∞ A' W := smooth hW hA [w]
    have hsv : ContDiffOn ℝ ∞ v' W := smooth hW hv [w]
    have he : directional (fun x ↦ A x (v x)) w =ᶠ[𝓝 p] (fun x ↦ A' x (v x)+A x (v' x)) :=
      (show ∀ᶠ x in 𝓝 p, x ∈ W from hW.mem_nhds hp).mono fun x hx ↦
        directional_apply ((hA.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp))
          ((hv.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp)) w
    have hA' (ys : List E) (hy : ys.length<xs.length) : directions A' ys p=0 := by
      change directions (directions A [w]) ys p=0
      rw [← append]
      exact hzero _ (by simpa using hy)
    have hlow (ys : List E) (hy : ys.length≤xs.length) : directions A ys p=0 :=
      hzero ys (by simpa using Nat.lt_succ_of_le hy)
    rw [append,append]
    change directions (directional (fun x ↦ A x (v x)) w) xs p=directions A' xs p (v p)
    rw [(congr_germ he xs).eq_of_nhds,add hW (hsA.clm_apply hv) (hA.clm_apply hsv) xs hp]
    dsimp only
    rw [ih hsA hv hA',ih hA hsv (fun ys hy ↦ hlow ys hy.le),hlow xs le_rfl,zero_apply,add_zero]

end EuclideanMidpointRigidity.directions

