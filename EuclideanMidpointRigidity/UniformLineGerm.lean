module

public import EuclideanMidpointRigidity.ParameterPatches
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Tactic

/-! # A uniform strip of agreement on a subpatch of a pointwise line germ -/

public section
noncomputable section
open Set Filter Metric
open scoped Topology
namespace EuclideanMidpointRigidity

theorem uniform_line_germ_subpatch {Y Z : Type*} [TopologicalSpace Y] [BaireSpace Y] [TopologicalSpace Z] [T2Space Z]
    {W : Set Y} (hW : IsOpen W) (hn : W.Nonempty) {δ : ℝ} (hδ : 0<δ) (f g : Y → ℝ → Z)
    (hf : ∀ s ∈ ball (0:ℝ) δ, ContinuousOn (fun y ↦ f y s) W)
    (hg : ∀ s ∈ ball (0:ℝ) δ, ContinuousOn (fun y ↦ g y s) W)
    (he : ∀ y ∈ W, f y =ᶠ[𝓝 (0:ℝ)] g y) :
    ∃ (U : Set Y) (r : ℝ), IsOpen U ∧ U.Nonempty ∧ U ⊆ W ∧ 0<r ∧ r≤δ ∧
      ∀ y ∈ U, ∀ s ∈ ball (0:ℝ) r, f y s=g y s := by
  let _ : BaireSpace W := hW.baireSpace
  let _ : Nonempty W := hn.to_subtype
  let r := fun n : ℕ ↦ min δ (1/(n+1:ℝ))
  let T := fun n : ℕ ↦ {y : W | ∀ s ∈ ball (0:ℝ) (r n), f y.val s=g y.val s}
  have hT (n : ℕ) : IsClosed (T n) := by
    have e : T n=⋂ s : ball (0:ℝ) (r n), {y : W | f y.val s.val=g y.val s.val} := by ext y; simp [T]
    rw [e]
    apply isClosed_iInter
    intro s
    have hs : s.val ∈ ball (0:ℝ) δ := ball_subset_ball (min_le_left _ _) s.property
    exact isClosed_eq (continuousOn_iff_continuous_restrict.mp (hf _ hs)) (continuousOn_iff_continuous_restrict.mp (hg _ hs))
  have hall : ⋃ n, T n=univ := by
    apply eq_univ_of_forall
    intro y
    obtain ⟨ρ,hρ,hr⟩ := Metric.mem_nhds_iff.mp (he y.val y.property)
    obtain ⟨n,hn⟩ := exists_nat_one_div_lt hρ
    exact mem_iUnion.mpr ⟨n,fun _ hs ↦ hr ((ball_subset_ball (le_trans (min_le_right _ _) hn.le)) hs)⟩
  obtain ⟨n,hi⟩ := nonempty_interior_of_iUnion_of_closed hT hall
  let U := ((↑) : W → Y) '' interior (T n)
  have hUW : U ⊆ W := by rintro _ ⟨x,_,rfl⟩; exact x.property
  refine ⟨U,r n,hW.isOpenMap_subtype_val _ isOpen_interior,hi.image _,hUW,lt_min hδ (by positivity),min_le_left _ _,?_⟩
  rintro _ ⟨y,hy,rfl⟩
  exact interior_subset hy

end EuclideanMidpointRigidity

