module

public import EuclideanMidpointRigidity.SpatialInverse
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! # A smooth spatial inverse with a two-sided identity near each point -/

public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem smooth_inverse_germs {W : Set E} (hW : IsOpen W) {f : E → F} (hf : ContDiffOn ℝ ∞ f W)
    {p : E} (hp : p ∈ W) (hinv : (fderiv ℝ f p).IsInvertible) :
    ∃ (V : Set F) (r : F → E), IsOpen V ∧ f p ∈ V ∧ r (f p)=p ∧ ContDiffOn ℝ ∞ r V ∧
      ∀ q ∈ V, r q ∈ W ∧ f (r q)=q ∧ (r ∘ f) =ᶠ[𝓝 (r q)] id := by
  obtain ⟨L,hL⟩ := hinv
  have hc := hf.contDiffAt (hW.mem_nhds hp)
  have hd : HasFDerivAt f (L : E →L[ℝ] F) p := hL ▸ (hc.differentiableAt (by simp)).hasFDerivAt
  let P := hc.toOpenPartialHomeomorph f hd (by simp)
  have hP : p ∈ P.source := hc.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hi : InjOn f P.source := P.injOn
  obtain ⟨V,r,hV,hpV,hrp,hr,hs⟩ := smooth_spatial_inverse (hW.inter P.open_source) (hf.mono inter_subset_left)
    ⟨hp,hP⟩ ⟨L,hL⟩
  refine ⟨V,r,hV,hpV,hrp,hr,?_⟩
  intro q hq
  obtain ⟨hw,he,_⟩ := hs q hq
  refine ⟨hw.1,he,?_⟩
  have hn : ∀ᶠ y in 𝓝 (r q), f y ∈ V := (hf.contDiffAt (hW.mem_nhds hw.1)).continuousAt (hV.mem_nhds (he.symm ▸ hq))
  filter_upwards [hn,P.open_source.mem_nhds hw.2] with y hv hy
  exact hi (hs _ hv).1.2 hy (hs _ hv).2.1

end EuclideanMidpointRigidity

