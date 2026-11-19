module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Topology.Compactness.Lindelof

/-! # Smooth implicit graphs on open sets -/

public section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- On an open regular locus the implicit solution is smooth on an open
base neighborhood. Its graph contains every solution in a product neighborhood. -/
theorem smooth_implicit_patch {f : E × F → G} {O : Set (E × F)} (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O) (hinv : ∀ v ∈ O, (fderiv ℝ f v ∘L .inr ℝ E F).IsInvertible)
    {u : E × F} (hu : u ∈ O) :
    ∃ (V : Set E) (D : Set (E × F)) (s : E → F), IsOpen V ∧ IsOpen D ∧ u ∈ D ∧
      ContDiffOn ℝ ∞ s V ∧ (∀ x ∈ V, f (x,s x)=f u) ∧
      ∀ y ∈ D, y.1 ∈ V ∧ (f y=f u → s y.1=y.2) := by
  have hc := hf.contDiffAt (hO.mem_nhds hu)
  have h₁ : (∞ : ℕ∞ω)≠0 := by decide
  let s := hc.implicitFunction h₁ (hinv u hu)
  have hs : s u.1=u.2 := hc.implicitFunction_apply_self h₁ _
  have hsc : ContDiffAt ℝ ∞ s u.1 := hc.contDiffAt_implicitFunction h₁ _
  have hgraph : Tendsto (fun x ↦ (x,s x)) (𝓝 u.1) (𝓝 u) := by
    simpa only [id_eq,hs,Prod.mk.eta] using (tendsto_id (x := 𝓝 u.1)).prodMk_nhds hsc.continuousAt
  obtain ⟨D,hD,hDo,huD⟩ := mem_nhds_iff.mp (hc.eventually_apply_eq_iff_implicitFunction h₁ (hinv u hu))
  have hnear : ∀ᶠ x in 𝓝 u.1, (x,s x) ∈ O ∩ D ∧ f (x,s x)=f u :=
    (hgraph.eventually ((hO.inter hDo).mem_nhds ⟨hu,huD⟩)).and
      (hc.eventually_apply_implicitFunction h₁ (hinv u hu))
  obtain ⟨V,hV,hVo,huV⟩ := mem_nhds_iff.mp hnear
  refine ⟨V,D ∩ Prod.fst ⁻¹' V,s,hVo,hDo.inter (hVo.preimage continuous_fst),⟨huD,huV⟩,?_,
    fun x hx ↦ (hV hx).2,?_⟩
  · intro x hx
    let v := (x,s x)
    have hvO : v ∈ O := (hV hx).1.1
    have hvD : v ∈ D := (hV hx).1.2
    have hcv := hf.contDiffAt (hO.mem_nhds hvO)
    let g := hcv.implicitFunction h₁ (hinv v hvO)
    have hgs : g x=s x := hcv.implicitFunction_apply_self h₁ _
    have hgc : ContDiffAt ℝ ∞ g x := hcv.contDiffAt_implicitFunction h₁ _
    have ht : Tendsto (fun y ↦ (y,g y)) (𝓝 x) (𝓝 v) := by
      simpa only [id_eq,hgs,v] using (tendsto_id (x := 𝓝 x)).prodMk_nhds hgc.continuousAt
    apply ContDiffAt.contDiffWithinAt
    apply hgc.congr_of_eventuallyEq
    filter_upwards [ht.eventually (hDo.mem_nhds hvD),
      hcv.eventually_apply_implicitFunction h₁ (hinv v hvO)] with y hy he
    exact (hD hy).mp (he.trans (hV hx).2)
  · intro y hy
    exact ⟨hy.2,(hD hy.1).mp⟩

end EuclideanMidpointRigidity

