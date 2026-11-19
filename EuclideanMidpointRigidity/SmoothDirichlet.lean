module

public import EuclideanMidpointRigidity.SpatialInverse
public import EuclideanMidpointRigidity.SmoothSuperposition

/-! # Smooth dependence for a path-valued Dirichlet equation -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
variable {I E F : Type} [TopologicalSpace I] [CompactSpace I]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
local notation "P" => C(I,E)
local notation "Q" => C(I,F)
set_option backward.isDefEq.respectTransparency false

def dirichletInput (G : Q →L[ℝ] P) (f : C(E,F)) (y : P) : P := y-G (f.comp y)

theorem contDiff_dirichletInput (G : Q →L[ℝ] P) (f : C(E,F)) (hf : ContDiff ℝ ∞ (f : E → F)) :
    ContDiff ℝ ∞ (dirichletInput G f) :=
  contDiff_id.sub (G.contDiff.comp (postcomp_contDiff f hf))

/-- The derivative in path space is the identity at a constant path where the force has zero derivative. -/
theorem hasFDerivAt_dirichletInput_rest (G : Q →L[ℝ] P) (f : C(E,F)) (hf : ContDiff ℝ ∞ (f : E → F))
    (p : E) (hDf : fderiv ℝ (f : E → F) p=0) :
    HasFDerivAt (dirichletInput G f) (ContinuousLinearMap.id ℝ P) (ContinuousMap.const I p) := by
  let u := ContinuousMap.const I p
  have hd := postcomp_hasFDerivAt (hf.of_le (by simp) : ContDiff ℝ 1 (f : E → F)) u
  have hz : HasFDerivAt (𝕜 := ℝ) (fun y : P ↦ f.comp y) 0 u := by
    apply hd.congr_fderiv
    ext v i
    change fderiv ℝ (f : E → F) p (v i)=0
    rw [hDf,zero_apply]
  have h := (hasFDerivAt_id u).fun_sub (G.hasFDerivAt.comp u hz)
  rw [ContinuousLinearMap.comp_zero,sub_zero] at h
  exact h

variable [CompleteSpace E]

/-- For each nearby input path the Green equation has a smoothly varying solution
in the prescribed open neighborhood of the constant path. -/
theorem smooth_green_response (G : Q →L[ℝ] P) (f : C(E,F)) (hf : ContDiff ℝ ∞ (f : E → F))
    {p : E} (hfp : f p=0) (hDf : fderiv ℝ (f : E → F) p=0)
    {U : Set P} (hU : IsOpen U) (hpU : ContinuousMap.const I p ∈ U) :
    ∃ (V : Set P) (s : P → P), IsOpen V ∧ ContinuousMap.const I p ∈ V ∧
      s (ContinuousMap.const I p)=ContinuousMap.const I p ∧ ContDiffOn ℝ ∞ s V ∧
      ∀ a ∈ V, s a ∈ U ∧ s a=a+G (f.comp (s a)) ∧ (fderiv ℝ (dirichletInput G f) (s a)).IsInvertible := by
  let u := ContinuousMap.const I p
  have hf₀ : f.comp u=0 := by ext i; exact hfp
  have hR : dirichletInput G f u=u := by rw [dirichletInput,hf₀,map_zero,sub_zero]
  have hi : (fderiv ℝ (dirichletInput G f) u).IsInvertible := by
    rw [(hasFDerivAt_dirichletInput_rest G f hf p hDf).fderiv]
    exact ⟨ContinuousLinearEquiv.refl ℝ P,rfl⟩
  obtain ⟨V,s,hV,hV₀,hs₀,hs,hq⟩ := smooth_spatial_inverse hU (contDiff_dirichletInput G f hf).contDiffOn hpU hi
  rw [hR] at hV₀ hs₀
  refine ⟨V,s,hV,hV₀,hs₀,hs,?_⟩
  intro a ha
  obtain ⟨h₁,h₂,h₃⟩ := hq a ha
  change s a-G (f.comp (s a))=a at h₂
  exact ⟨h₁,sub_eq_iff_eq_add.mp h₂,h₃⟩

end EuclideanMidpointRigidity

