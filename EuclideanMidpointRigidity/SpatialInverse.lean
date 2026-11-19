module

public import EuclideanMidpointRigidity.ImplicitPatches
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Tactic

/-! # Smooth spatial coordinates on an open neighborhood -/

public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

set_option backward.isDefEq.respectTransparency false in
theorem smooth_spatial_inverse {W : Set E} (hW : IsOpen W) {f : E → F} (hf : ContDiffOn ℝ ∞ f W)
    {p : E} (hp : p ∈ W) (hinv : (fderiv ℝ f p).IsInvertible) :
    ∃ (V : Set F) (r : F → E), IsOpen V ∧ f p ∈ V ∧ r (f p)=p ∧ ContDiffOn ℝ ∞ r V ∧
      ∀ q ∈ V, r q ∈ W ∧ f (r q)=q ∧ (fderiv ℝ f (r q)).IsInvertible := by
  let W' := W ∩ fderiv ℝ f ⁻¹' {T : E →L[ℝ] F | T.IsInvertible}
  have hW' : IsOpen W' := (hf.continuousOn_fderiv_of_isOpen hW (by simp)).isOpen_inter_preimage hW
    ContinuousLinearMap.isOpen_setOfPred_isInvertible
  let O := (univ : Set F) ×ˢ W'
  have hO : IsOpen O := isOpen_univ.prod hW'
  let G := fun v : F × E ↦ f v.2-v.1
  have hmaps : MapsTo (Prod.snd : F × E → E) O W := fun v hv ↦ hv.2.1
  have hg : ContDiffOn ℝ ∞ G O :=
    (hf.comp contDiffOn_snd hmaps).sub contDiffOn_fst
  have hreg (v : F × E) (hv : v ∈ O) : (fderiv ℝ G v ∘L .inr ℝ F E).IsInvertible := by
    have hcomp := ((hg.contDiffAt (hO.mem_nhds hv)).differentiableAt (by simp)).hasFDerivAt.comp
      v.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) v.1 v.2)
    have hd := ((hf.contDiffAt (hW.mem_nhds hv.2.1)).differentiableAt (by simp)).hasFDerivAt.sub_const v.1
    have he : fderiv ℝ G v ∘L .inr ℝ F E=fderiv ℝ f v.2 := hcomp.unique hd
    exact he ▸ hv.2.2
  have hbase : (f p,p) ∈ O := ⟨trivial,hp,hinv⟩
  obtain ⟨V,D,r,hV,_,hD,hr,hsol,hgraph⟩ := smooth_implicit_patch hO hg hreg hbase
  obtain ⟨hpV,hrp⟩ := hgraph (f p,p) hD
  have he : r (f p)=p := hrp rfl
  let U := V ∩ r ⁻¹' W'
  have hU : IsOpen U := hr.continuousOn.isOpen_inter_preimage hV hW'
  refine ⟨U,r,hU,⟨hpV,by change r (f p) ∈ W'; rw [he]; exact hbase.2⟩,he,hr.mono inter_subset_left,?_⟩
  intro q hq
  refine ⟨hq.2.1,?_,hq.2.2⟩
  have h := hsol q hq.1
  change f (r q)-q=f p-f p at h
  exact sub_eq_zero.mp (h.trans (sub_self _))

end EuclideanMidpointRigidity

