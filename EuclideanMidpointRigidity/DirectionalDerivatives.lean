module

public import EuclideanMidpointRigidity.FieldJets

/-! # Iterated derivatives in a list of constant spatial directions -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

def directional (f : E → F) (w : E) (p : E) := fderiv ℝ f p w

def directions (f : E → F) : List E → E → F
  | [] => f
  | w::ws => directional (directions f ws) w

namespace directions

theorem append (f : E → F) (xs ys : List E) : directions f (xs++ys)=directions (directions f ys) xs := by
  induction xs with
  | nil => rfl
  | cons w xs ih => simp only [List.cons_append,directions,ih]

theorem congr_germ {p : E} {f g : E → F} (h : f =ᶠ[𝓝 p] g) (xs : List E) :
    directions f xs =ᶠ[𝓝 p] directions g xs := by
  induction xs with
  | nil => exact h
  | cons w ws ih => exact (ih.fderiv (𝕜 := ℝ)).mono fun _ he ↦ DFunLike.congr_fun he w

theorem smooth {W : Set E} {f : E → F} (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W) (xs : List E) :
    ContDiffOn ℝ ∞ (directions f xs) W := by
  induction xs with
  | nil => exact hf
  | cons w ws ih => exact (ih.fderiv_of_isOpen hW (by simp)).clm_apply contDiffOn_const

theorem linear_map {W : Set E} {f : E → F} (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    (L : F →L[ℝ] G) (xs : List E) : EqOn (directions (L ∘ f) xs) (L ∘ directions f xs) W := by
  induction xs with
  | nil => exact fun _ _ ↦ rfl
  | cons w ws ih =>
    intro p hp
    have hn := (show ∀ᶠ q in 𝓝 p, q ∈ W from hW.mem_nhds hp).mono fun _ h ↦ ih h
    have hd := L.hasFDerivAt.comp p (((smooth hW hf ws).contDiffAt (hW.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
    exact DFunLike.congr_fun ((Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hn).trans hd.fderiv) w

theorem add {W : Set E} {f g : E → F} (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W) (hg : ContDiffOn ℝ ∞ g W)
    (xs : List E) : EqOn (directions (fun x ↦ f x+g x) xs) (fun x ↦ directions f xs x+directions g xs x) W := by
  induction xs with
  | nil => exact fun _ _ ↦ rfl
  | cons w ws ih =>
    intro p hp
    have hn := (show ∀ᶠ q in 𝓝 p, q ∈ W from hW.mem_nhds hp).mono fun _ h ↦ ih h
    have df := (((smooth hW hf ws).contDiffAt (hW.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
    have dg := (((smooth hW hg ws).contDiffAt (hW.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
    exact DFunLike.congr_fun ((Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hn).trans (df.fun_add dg).fderiv) w

theorem perm {W : Set E} {f : E → F} (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    {xs ys : List E} (h : xs.Perm ys) : EqOn (directions f xs) (directions f ys) W := by
  induction h with
  | nil => exact fun _ _ ↦ rfl
  | cons w h ih =>
    intro p hp
    have hn := (show ∀ᶠ q in 𝓝 p, q ∈ W from hW.mem_nhds hp).mono fun _ h ↦ ih h
    exact DFunLike.congr_fun (Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hn) w
  | swap a b xs =>
    intro p hp
    let g := directions f xs
    let H := fderiv ℝ (fderiv ℝ g) p
    have hg : ContDiffAt ℝ ∞ g p := (smooth hW hf xs).contDiffAt (hW.mem_nhds hp)
    have he (v w : E) : directional (directional g v) w p=H w v := by
      let L := ContinuousLinearMap.apply ℝ F v
      have hF := L.hasFDerivAt.comp p ((hg.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
      exact DFunLike.congr_fun hF.fderiv w
    change directional (directional g a) b p=directional (directional g b) a p
    rw [he,he]; exact (hg.isSymmSndFDerivAt (by simp)) b a
  | trans h₁ h₂ ih₁ ih₂ => exact fun x hx ↦ (ih₁ hx).trans (ih₂ hx)

theorem zero (xs : List E) : directions (fun _ : E ↦ (0:F)) xs=fun _ ↦ 0 := by
  induction xs with
  | nil => rfl
  | cons w ws ih => funext p; simp [directions,ih,directional]

end directions
end EuclideanMidpointRigidity

