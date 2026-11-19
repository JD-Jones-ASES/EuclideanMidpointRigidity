module

public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.LocallyClosed

/-! # Open patches of a countable locally closed cover -/

public section
open Set Topology
namespace EuclideanMidpointRigidity

/-- A countable locally closed cover of a nonempty open set contains an
open subpatch. This applies to smooth parameter families with changing rank. -/
theorem exists_subpatch_of_locallyClosed_cover {X ι : Type*} [TopologicalSpace X]
    [BaireSpace X] [Countable ι] {W : Set X} (hW : IsOpen W) (hn : W.Nonempty)
    (T : ι → Set X) (hT : ∀ i, IsLocallyClosed (T i)) (hcover : W ⊆ ⋃ i, T i) :
    ∃ (i : ι) (V : Set X), IsOpen V ∧ V.Nonempty ∧ V ⊆ W ∧ V ⊆ T i := by
  let _ : BaireSpace W := hW.baireSpace
  let _ : Nonempty W := hn.to_subtype
  let F := fun i ↦ ((↑) : W → X) ⁻¹' closure (T i)
  have hF (i : ι) : IsClosed (F i) := isClosed_closure.preimage continuous_subtype_val
  have hc : ⋃ i, F i=univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hcover x.property)
    exact mem_iUnion.mpr ⟨i,subset_closure hi⟩
  obtain ⟨i,hi⟩ := nonempty_interior_of_iUnion_of_closed hF hc
  let U := ((↑) : W → X) '' interior (F i)
  have hU : IsOpen U := hW.isOpenMap_subtype_val _ isOpen_interior
  have hUW : U ⊆ W := by rintro x ⟨w,_,rfl⟩; exact w.property
  have hUF : U ⊆ closure (T i) := by
    rintro _ ⟨w,hw,rfl⟩
    exact (show w ∈ F i from interior_subset hw)
  obtain ⟨x,hx⟩ := hi.image ((↑) : W → X)
  obtain ⟨y,hy,ht⟩ := mem_closure_iff.mp (hUF hx) U hU hx
  refine ⟨i,U ∩ coborder (T i),hU.inter (hT i).isOpen_coborder,
    ⟨y,hy,subset_coborder ht⟩,fun _ h ↦ hUW h.1,?_⟩
  intro w hw
  exact mem_coborder_iff_imp.mp hw.2 (hUF hw.1)

end EuclideanMidpointRigidity

