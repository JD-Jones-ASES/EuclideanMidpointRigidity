module

public import EuclideanMidpointRigidity.SpatialInverse
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! # A uniform comparison for the inverse derivative at two nearby paths -/

public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem local_inverse_comparison {f : X → Y} {g : X → Z} {p : X} (hf : ContDiffAt ℝ ∞ f p)
    (hreg : (fderiv ℝ f p).IsInvertible) (hg : ContDiffAt ℝ ∞ g p) :
    ∃ K : ℝ, 0≤K ∧ ∃ U ∈ 𝓝 p, ∀ x ∈ U, ∀ y ∈ U, ‖g x-g y‖≤K*‖f x-f y‖ := by
  obtain ⟨e,he⟩ := hreg
  have hd : HasFDerivAt f (e : X →L[ℝ] Y) p := he ▸ (hf.differentiableAt (by simp)).hasFDerivAt
  have hn : (∞ : WithTop ℕ∞)≠0 := by simp
  let Φ := hf.toOpenPartialHomeomorph f hd hn
  let G := hf.localInverse hd hn
  have hp : p ∈ Φ.source := hf.mem_toOpenPartialHomeomorph_source hd hn
  have hG : ContDiffAt ℝ ∞ G (f p) := hf.to_localInverse hd hn
  have hGp : G (f p)=p := hf.localInverse_apply_image hd hn
  have hgg : ContDiffAt ℝ ∞ (g ∘ G) (f p) := (hGp ▸ hg).comp _ hG
  obtain ⟨K,U,hU,hL⟩ := (hgg.hasStrictFDerivAt_fderiv (by simp)).exists_lipschitzOnWith
  refine ⟨K,K.coe_nonneg,Φ.source ∩ f ⁻¹' U,inter_mem (Φ.open_source.mem_nhds hp) (hf.continuousAt hU),?_⟩
  intro x hx y hy
  have ex : G (f x)=x := Φ.left_inv hx.1
  have ey : G (f y)=y := Φ.left_inv hy.1
  simpa only [Function.comp_apply,ex,ey] using (lipschitzOnWith_iff_norm_sub_le.mp hL) hx.2 hy.2

theorem inverse_derivative_comparison {f : X → Y} {p : X} (hf : ContDiff ℝ ∞ f)
    (hreg : (fderiv ℝ f p).IsInvertible) (b : Y) :
    ∃ K : ℝ, 0≤K ∧ ∃ U ∈ 𝓝 p, ∀ x ∈ U, ∀ y ∈ U,
      ‖(fderiv ℝ f x).inverse b-(fderiv ℝ f y).inverse b‖≤K*‖f x-f y‖ := by
  apply local_inverse_comparison hf.contDiffAt hreg
  exact (hreg.contDiffAt_map_inverse.comp p (hf.fderiv_right (by simp)).contDiffAt).clm_apply contDiffAt_const

end EuclideanMidpointRigidity

