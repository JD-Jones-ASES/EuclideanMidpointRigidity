module

public import EuclideanMidpointRigidity.SmoothFlow
public import EuclideanMidpointRigidity.SmoothFieldExtension

/-! # A smooth flow for a vector field on an open domain -/

public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]

theorem smooth_local_flow {W : Set E} (hW : IsOpen W) {f : E → E} (hf : ContDiffOn ℝ ∞ f W)
    {p : E} (hp : p ∈ W) :
    ∃ (V : Set (E × ℝ)) (Φ : E × ℝ → E), IsOpen V ∧ (p,0) ∈ V ∧ ContDiffOn ℝ ∞ Φ V ∧
      MapsTo Φ V W ∧ (∀ y, (y,0) ∈ V → Φ (y,0)=y) ∧
      ∀ q ∈ V, HasDerivAt (fun r ↦ Φ (q.1,r)) (f (Φ q)) q.2 := by
  obtain ⟨g,hg,heq⟩ := local_smooth_representative hW hf hp
  obtain ⟨U,hUeq,hU,hpU⟩ := mem_nhds_iff.mp (heq.and (hW.mem_nhds hp))
  obtain ⟨V,Φ,hV,hpV,hs,h₀,hd⟩ := smooth_autonomous_flow (⟨g,hg.continuous⟩ : C(E,E)) hg p
  let D := V ∩ Φ ⁻¹' U
  have hD : IsOpen D := hs.continuousOn.isOpen_inter_preimage hV hU
  refine ⟨D,Φ,hD,⟨hpV,by change Φ (p,0) ∈ U; rwa [h₀ p hpV]⟩,hs.mono inter_subset_left,
    fun q hq ↦ (hUeq hq.2).2,fun y hy ↦ h₀ y hy.1,?_⟩
  intro q hq
  rw [← (hUeq hq.2).1]
  exact hd q hq.1

end EuclideanMidpointRigidity

