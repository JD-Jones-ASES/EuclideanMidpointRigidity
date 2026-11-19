module

public import EuclideanMidpointRigidity.FlowScaling

/-! # A local smooth flow with its time derivative -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
open PathIntegral

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
local notation "P" => C(Time,E)
set_option backward.isDefEq.respectTransparency false

/-- Taking the endpoint of the path at signed time τ gives a jointly
smooth local flow. Its ordinary time derivative is the vector field
at that endpoint, including at time zero. -/
theorem smooth_autonomous_flow (f : C(E,E)) (hf : ContDiff ℝ ∞ (f : E → E)) (p : E) :
    ∃ (V : Set (E × ℝ)) (Φ : E × ℝ → E), IsOpen V ∧ (p,0) ∈ V ∧ ContDiffOn ℝ ∞ Φ V ∧
      (∀ y, (y,0) ∈ V → Φ (y,0)=y) ∧
      ∀ q ∈ V, HasDerivAt (fun r ↦ Φ (q.1,r)) (f (Φ q)) q.2 := by
  obtain ⟨V,s,hV,hp,hs,hsol,_⟩ := smooth_flow_paths f hf p
  let one : Time := ⟨1,by simp⟩
  let L : P →L[ℝ] E := ContinuousMap.evalCLM ℝ one
  let Φ := fun q ↦ L (s q)
  have hph : ContDiffOn ℝ ∞ Φ V := L.contDiff.comp_contDiffOn hs
  have hs₀ (y : E) (hy : (y,0) ∈ V) : s (y,0)=ContinuousMap.const Time y := by simpa using hsol (y,0) hy
  have h₀ (y : E) (hy : (y,0) ∈ V) : Φ (y,0)=y := by change s (y,0) one=y; rw [hs₀ y hy]; rfl
  refine ⟨V,Φ,hV,hp,hph,h₀,?_⟩
  rintro ⟨y,τ⟩ hq
  let g := fun r ↦ Φ (y,r)
  have hline : ContDiff ℝ ∞ (fun r : ℝ ↦ (y,r)) := contDiff_const.prodMk contDiff_id
  have hsc : ContDiffAt ℝ ∞ (fun r ↦ s (y,r)) τ :=
    (hs.contDiffAt (hV.mem_nhds hq)).comp τ hline.contDiffAt
  have hgc : ContDiffAt ℝ ∞ g τ := L.contDiff.contDiffAt.comp τ hsc
  change HasDerivAt g (f (g τ)) τ
  by_cases ht : τ=0
  · subst τ
    let A := fun r ↦ L (integration (f.comp (s (y,r))))
    have hA : ContDiffAt ℝ ∞ A 0 := L.contDiff.contDiffAt.comp 0 ((integration (E := E)).contDiff.contDiffAt.comp 0
      ((postcomp_contDiff f hf).contDiffAt.comp 0 hsc))
    have he : g =ᶠ[𝓝 0] fun r ↦ y+r • A r := by
      filter_upwards [hline.continuous.continuousAt (hV.mem_nhds hq)] with r hr
      exact congrArg (fun a : P ↦ a one) (hsol (y,r) hr)
    have hpA : A 0=f y := by
      change primitive (f.comp (s (y,0))) 1=f y
      rw [hs₀ y hq]
      simp [primitive,extend]
    have h := (((hasDerivAt_id (0:ℝ)).smul (hA.differentiableAt (by decide)).hasDerivAt).const_add y)
    have hg₀ : g 0=y := h₀ y hq
    rw [hg₀]
    apply HasDerivAt.congr_of_eventuallyEq _ he
    simpa [hpA,Function.id_def] using h
  · have h₁ : ContDiff ℝ 1 (f : E → E) := hf.of_le (by simp)
    have hg := (hgc.differentiableAt (by simp)).hasDerivAt
    have hlin : HasDerivAt (fun r : ℝ ↦ r*τ) τ 1 := by simpa using (hasDerivAt_id (1:ℝ)).mul_const τ
    have hd : HasDerivAt g (deriv g τ) (1*τ) := by simpa using hg
    have hleft := hd.scomp 1 hlin
    have hj : (1:ℝ) ∈ Icc (0:ℝ) 1 := by simp
    have hnear : ∀ᶠ r in 𝓝 (1:ℝ), (y,r*τ) ∈ V := by
      have hc : Continuous (fun r : ℝ ↦ (y,r*τ)) := continuous_const.prodMk (continuous_id.mul continuous_const)
      apply hc.continuousAt (hV.mem_nhds _)
      simpa using hq
    have heq : (fun r ↦ g (r*τ)) =ᶠ[𝓝[Icc (0:ℝ) 1] 1] flowCurve f y τ (s (y,τ)) := by
      filter_upwards [self_mem_nhdsWithin,hnear.filter_mono nhdsWithin_le_nhds] with r hr hv
      exact flowCurve_scale f h₁ hr (hsol (y,τ) hq) (hsol (y,r*τ) hv)
    have hcurve := flowCurve_derivative (hsol (y,τ) hq) hj
    have hat : flowCurve f y τ (s (y,τ)) 1=g τ := flowCurve_at (hsol _ hq) one
    rw [hat] at hcurve
    have hright := hcurve.hasDerivWithinAt.congr_of_eventuallyEq_of_mem heq hj
    have huniq := uniqueDiffOn_Icc_zero_one 1 hj
    have hv := (hleft.hasDerivWithinAt.derivWithin huniq).symm.trans (hright.derivWithin huniq)
    have hd' : deriv g τ=f (g τ) := by
      simpa only [smul_smul,inv_mul_cancel₀ ht,one_smul] using congrArg (fun v : E ↦ τ⁻¹ • v) hv
    rwa [hd'] at hg

end EuclideanMidpointRigidity

