module

public import EuclideanMidpointRigidity.ParameterPatches
public import EuclideanMidpointRigidity.SmoothLinearSystems
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Choosing one smooth polynomial certificate from countably many linear systems -/

public section
open Set Metric Topology
open scoped ContDiff
namespace EuclideanMidpointRigidity

private theorem isClosed_bounded_solutions {X I : Type*} [TopologicalSpace X] {m : ℕ}
    (A : Fin m → I → X → ℝ) (b : I → X → ℝ) (hA : ∀ j i, Continuous (A j i))
    (hb : ∀ i, Continuous (b i)) (N : ℕ) :
    IsClosed {x : X | ∃ v ∈ closedBall (0 : Fin m → ℝ) (N:ℝ), ∀ i,
      ∑ j, v j*A j i x=b i x} := by
  let B := closedBall (0 : Fin m → ℝ) (N:ℝ)
  let _ : CompactSpace B := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let F := fun i ↦ {p : X × B | ∑ j, (p.2.val j)*A j i p.1=b i p.1}
  have hF (i : I) : IsClosed (F i) := by
    apply isClosed_eq _ ((hb i).comp continuous_fst)
    apply continuous_finsetSum
    intro j _
    exact (((continuous_apply j).comp continuous_subtype_val).comp continuous_snd).mul
      ((hA j i).comp continuous_fst)
  have hrel : {x : X | ∃ v ∈ B, ∀ i, ∑ j, v j*A j i x=b i x} =
      Prod.fst '' (⋂ i, F i) := by
    ext x
    constructor
    · rintro ⟨v,hv,h⟩
      exact ⟨(x,⟨v,hv⟩),mem_iInter.mpr h,rfl⟩
    · rintro ⟨⟨x,v⟩,h,rfl⟩
      exact ⟨v,v.property,mem_iInter.mp h⟩
  rw [show closedBall (0 : Fin m → ℝ) (N:ℝ)=B from rfl,hrel]
  exact isClosedMap_fst_of_compactSpace _ (isClosed_iInter hF)

/-- Whenever at least one system admits a solution at every point, a
single system admits a smooth solution on some nonempty open subpatch. -/
theorem smooth_certificate_on_subpatch {X I τ : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [BaireSpace X] [Countable τ] (m : τ → ℕ) (A : (k : τ) → Fin (m k) → I → X → ℝ)
    (b : τ → I → X → ℝ) {W : Set X} (hW : IsOpen W) (hn : W.Nonempty)
    (hA : ∀ k j i, ContDiffOn ℝ ∞ (A k j i) W) (hb : ∀ k i, ContDiffOn ℝ ∞ (b k i) W)
    (hs : ∀ x ∈ W, ∃ k, ∃ v : Fin (m k) → ℝ, ∀ i, ∑ j, v j*A k j i x=b k i x) :
    ∃ (k : τ) (V : Set X) (v : Fin (m k) → X → ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ W ∧
      (∀ j, ContDiffOn ℝ ∞ (v j) V) ∧ ∀ x ∈ V, ∀ i, ∑ j, v j x*A k j i x=b k i x := by
  let _ : BaireSpace W := hW.baireSpace
  let _ : Nonempty W := hn.to_subtype
  let T := fun c : τ × ℕ ↦ {x : W | ∃ v ∈ closedBall (0 : Fin (m c.1) → ℝ) (c.2:ℝ),
    ∀ i, ∑ j, v j*A c.1 j i x=b c.1 i x}
  have hT (c : τ × ℕ) : IsClosed (T c) := isClosed_bounded_solutions
    (fun j i (x : W) ↦ A c.1 j i x) (fun i (x : W) ↦ b c.1 i x)
    (fun j i ↦ (hA c.1 j i).continuousOn.domRestrict) (fun i ↦ (hb c.1 i).continuousOn.domRestrict) c.2
  have hcover : univ ⊆ ⋃ c, T c := by
    intro x _
    obtain ⟨k,v,hv⟩ := hs x x.property
    obtain ⟨N,hN⟩ := exists_nat_ge ‖v‖
    exact mem_iUnion.mpr ⟨(k,N),v,by simpa [mem_closedBall,dist_zero_right] using hN,hv⟩
  obtain ⟨⟨k,N⟩,U,hU,hUn,_,hUT⟩ := exists_subpatch_of_locallyClosed_cover isOpen_univ
    (univ_nonempty (α := W)) T (fun c ↦ (hT c).isLocallyClosed) hcover
  let V := ((↑) : W → X) '' U
  have hV : IsOpen V := hW.isOpenMap_subtype_val _ hU
  have hVW : V ⊆ W := by rintro _ ⟨x,_,rfl⟩; exact x.property
  have hsolve (x : X) (hx : x ∈ V) : ∃ v : Fin (m k) → ℝ, ∀ i, ∑ j, v j*A k j i x=b k i x := by
    obtain ⟨w,hw,rfl⟩ := hx
    obtain ⟨v,_,hv⟩ := hUT hw
    exact ⟨v,hv⟩
  obtain ⟨V',v,hV',hn',hsub,hv,he⟩ := smooth_linear_solution_on_subpatch (m k) (A k) (b k)
    hV (hUn.image _) (fun j i ↦ (hA k j i).mono hVW) (fun i ↦ (hb k i).mono hVW) hsolve
  exact ⟨k,V',v,hV',hn',hsub.trans hVW,hv,he⟩

end EuclideanMidpointRigidity

