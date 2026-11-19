module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! # A global smooth representative of a local vector field -/

public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem local_smooth_representative {W : Set E} (hW : IsOpen W) {f : E → F} (hf : ContDiffOn ℝ ∞ f W)
    {p : E} (hp : p ∈ W) : ∃ g : E → F, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 p] f := by
  obtain ⟨b,hb,_,hs,_,hb₀⟩ := exists_contDiff_tsupport_subset (n := (⊤:ℕ∞)) (hW.mem_nhds hp)
  let k := fun x ↦ Real.smoothTransition (2*b x)
  have hk : ContDiff ℝ ∞ k := Real.smoothTransition.contDiff.comp (contDiff_const.mul hs)
  refine ⟨fun x ↦ k x • f x,?_,?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ W
    · exact hk.contDiffAt.smul (hf.contDiffAt (hW.mem_nhds hx))
    · have hnb : x ∉ tsupport b := fun h ↦ hx (hb h)
      apply (contDiffAt_const (c := (0:F))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnb] with y hy
      simp [k,show b y=0 from hy,Real.smoothTransition.zero]
  · have htwo : Continuous (fun x ↦ (2:ℝ)*b x) := continuous_const.mul hs.continuous
    have hnear : ∀ᶠ x in 𝓝 p, 1<2*b x :=
      htwo.continuousAt (Ioi_mem_nhds (show 1<2*b p by rw [hb₀]; norm_num))
    filter_upwards [hnear] with x hx
    simp [k,Real.smoothTransition.one_of_one_le hx.le]

end EuclideanMidpointRigidity

