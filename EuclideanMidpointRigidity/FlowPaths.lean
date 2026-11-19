module

public import EuclideanMidpointRigidity.PathPrimitive
public import EuclideanMidpointRigidity.SmoothSuperposition
public import EuclideanMidpointRigidity.ImplicitPatches
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-! # Smooth dependence of a local integral curve on its initial data -/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace EuclideanMidpointRigidity
open PathIntegral

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
local notation "P" => C(Time,E)
set_option backward.isDefEq.respectTransparency false

def flowResidual (f : C(E,E)) (q : (E × ℝ) × P) : P :=
  q.2 - ContinuousMap.const Time q.1.1 - q.1.2 • integration (f.comp q.2)

theorem contDiff_flowResidual (f : C(E,E)) (hf : ContDiff ℝ ∞ (f : E → E)) :
    ContDiff ℝ ∞ (flowResidual f) := by
  have hi : ContDiff ℝ ∞ (fun q : (E × ℝ) × P ↦ q.1.1) := contDiff_fst.comp contDiff_fst
  have ht : ContDiff ℝ ∞ (fun q : (E × ℝ) × P ↦ q.1.2) := contDiff_snd.comp contDiff_fst
  let constPath : E →L[ℝ] P := ContinuousLinearMap.const ℝ Time
  have hc : ContDiff ℝ ∞ (ContinuousMap.const Time : E → P) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) («E» := E) (F := P) constPath
  have hA : ContDiff ℝ ∞ (fun q : (E × ℝ) × P ↦ integration (f.comp q.2)) :=
    (integration (E := E)).contDiff.comp ((postcomp_contDiff f hf).comp contDiff_snd)
  exact (contDiff_snd.sub (hc.comp hi)).sub (ht.smul hA)

/-- The solution on a fixed unit interval is smooth as a path-valued
function of the initial point and the signed length of the time interval. -/
theorem smooth_flow_paths (f : C(E,E)) (hf : ContDiff ℝ ∞ (f : E → E)) (p : E) :
    ∃ (V : Set (E × ℝ)) (s : E × ℝ → P), IsOpen V ∧ (p,0) ∈ V ∧ ContDiffOn ℝ ∞ s V ∧
      (∀ q ∈ V, s q=ContinuousMap.const Time q.1+q.2 • integration (f.comp (s q))) ∧
      ∀ q ∈ V, (fderiv ℝ (flowResidual f) (q,s q) ∘L .inr ℝ (E × ℝ) P).IsInvertible := by
  let u : (E × ℝ) × P := ((p,0),ContinuousMap.const Time p)
  let R := flowResidual f
  let L := fun v : (E × ℝ) × P ↦ fderiv ℝ R v ∘L .inr ℝ (E × ℝ) P
  have hr := contDiff_flowResidual f hf
  have hL : Continuous L := (hr.continuous_fderiv (by decide)).clm_comp continuous_const
  let O := L ⁻¹' {T : P →L[ℝ] P | T.IsInvertible}
  have hO : IsOpen O := ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage hL
  have hu : u ∈ O := by
    have hcomp := ((hr.differentiable (by decide) u).hasFDerivAt).comp u.2
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) u.1 u.2)
    have hid : HasFDerivAt (fun Z : P ↦ flowResidual f (u.1,Z)) (ContinuousLinearMap.id ℝ P) u.2 := by
      simpa [flowResidual,u] using (hasFDerivAt_id u.2).sub_const (ContinuousMap.const Time p)
    have he : L u=ContinuousLinearMap.id ℝ P := hcomp.unique hid
    change (L u).IsInvertible
    rw [he]
    exact ⟨ContinuousLinearEquiv.refl ℝ P,rfl⟩
  obtain ⟨V,D,s,hV,hD,huD,hs,hsol,hgraph⟩ := smooth_implicit_patch hO hr.contDiffOn
    (fun v hv ↦ (show (L v).IsInvertible from hv)) hu
  have hpV := (hgraph u huD).1
  have hsu : s (p,0)=ContinuousMap.const Time p := (hgraph u huD).2 rfl
  have hR₀ : R u=0 := by simp [R,u,flowResidual]
  let V' := V ∩ (fun q ↦ (q,s q)) ⁻¹' O
  have hV' : IsOpen V' := (continuousOn_id.prodMk hs.continuousOn).isOpen_inter_preimage hV hO
  refine ⟨V',s,hV',⟨hpV,by change ((p,0),s (p,0)) ∈ O; rwa [hsu]⟩,hs.mono inter_subset_left,?_,fun q hq ↦ hq.2⟩
  intro q hq
  have he := (hsol q hq.1).trans hR₀
  change s q-ContinuousMap.const Time q.1-q.2 • integration (f.comp (s q))=0 at he
  exact sub_eq_iff_eq_add'.mp (sub_eq_zero.mp he)

end EuclideanMidpointRigidity

