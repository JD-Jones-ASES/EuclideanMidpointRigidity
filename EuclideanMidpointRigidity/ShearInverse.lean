module

public import EuclideanMidpointRigidity.ShearPaths

/-! # The differential of the inverse at every scale, including zero -/

@[expose] public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
local notation "I" => ContinuousLinearMap.id ℝ E

theorem eq_at_zero_of_punctured {F : Type} [TopologicalSpace F] [T2Space F] {f g : ℝ → F}
    (hf : ContinuousAt f 0) (hg : ContinuousAt g 0) (he : ∀ᶠ t in 𝓝 (0:ℝ), t≠0 → f t=g t) : f 0=g 0 := by
  have H : f =ᶠ[𝓝[≠] (0:ℝ)] g := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht hn
    exact ht hn
  exact tendsto_nhds_unique_of_eventuallyEq (hf.tendsto.mono_left nhdsWithin_le_nhds) (hg.tendsto.mono_left nhdsWithin_le_nhds) H

structure ShearInverse (e : E → E) (W : Set E) (p : E) where
  domain : Set (ℝ × E)
  isOpen : IsOpen domain
  origin : (0,0) ∈ domain
  inverse : ℝ × E → E
  smooth : ContDiffOn ℝ ∞ inverse domain
  maps : MapsTo inverse domain W
  center : ∀ r, (r,0) ∈ domain → inverse (r,0)=p
  physical : ∀ q ∈ domain, q.1 • inverse q+e (inverse q)=q.1 • p+e p+q.1^2 • q.2
  spatial : ∀ q ∈ domain, HasFDerivAt (fun z ↦ inverse (q.1,z)) (q.1 • I-fderiv ℝ e (inverse q)) q.2

theorem exists_shear_inverse {W : Set E} {e : E → E} (hW : IsOpen W) (he : ContDiffOn ℝ ∞ e W)
    (hA : ∀ x ∈ W, ∀ z, fderiv ℝ e x (fderiv ℝ e x z)=0) {p : E} (hp : p ∈ W) :
    Nonempty (ShearInverse e W p) := by
  obtain ⟨U,g,hU,h₀,hg,hm,hc,hphysical⟩ := smooth_shear_paths hW he hA hp
  let J := fun q ↦ (fderiv ℝ g q).comp (ContinuousLinearMap.inr ℝ ℝ E)
  let A := fderiv ℝ e
  have hJ : ContinuousOn J U := (hg.continuousOn_fderiv_of_isOpen hU (by simp)).clm_comp continuousOn_const
  have hJ' (q : ℝ × E) (hq : q ∈ U) : HasFDerivAt (fun z ↦ g (q.1,z)) (J q) q.2 :=
    ((hg.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt.comp q.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2)
  have hzero (q : ℝ × E) (hq : q ∈ U) (hn : q.1≠0) : J q=q.1 • I-A (g q) := by
    let f := fun z ↦ g (q.1,z)
    have gj := hJ' q hq
    have ej := ((he.contDiffAt (hW.mem_nhds (hm hq))).differentiableAt (by simp)).hasFDerivAt.comp q.2 gj
    have H := (gj.const_smul q.1).add ej
    have L : HasFDerivAt (fun z ↦ q.1 • p+e p+q.1^2 • z) (q.1^2 • I) q.2 := by
      simpa only [zero_add,Pi.smul_apply,id_eq] using (hasFDerivAt_const (q.1 • p+e p) q.2).fun_add ((hasFDerivAt_id q.2).const_smul (q.1^2))
    have hh : (fun z ↦ q.1 • f z+e (f z)) =ᶠ[𝓝 q.2] (fun z ↦ q.1 • p+e p+q.1^2 • z) :=
      (show ∀ᶠ z in 𝓝 q.2, (q.1,z) ∈ U from (continuous_const.prodMk continuous_id).continuousAt (hU.mem_nhds hq)).mono (fun z hz ↦ hphysical (q.1,z) hz)
    have eqn := H.unique (L.congr_of_eventuallyEq hh)
    ext v : 1
    have hv := DFunLike.congr_fun eqn v
    change q.1 • J q v+A (g q) (J q v)=q.1^2 • v at hv
    have hav := congrArg (A (g q)) hv
    simp only [map_add,map_smul,show A (g q) (A (g q) (J q v))=0 from hA _ (hm hq) _,add_zero] at hav
    have hb := congrArg (fun u : E ↦ q.1 • u) hv
    simp only [smul_add,hav,smul_smul,← sq] at hb
    change J q v=q.1 • v-A (g q) v
    apply (smul_right_injective E (pow_ne_zero 2 hn))
    change q.1^2 • J q v=q.1^2 • (q.1 • v-A (g q) v)
    rw [smul_sub,smul_smul,mul_comm (q.1^2) q.1]
    exact eq_sub_of_add_eq hb
  refine ⟨⟨U,hU,h₀,g,hg,hm,hc,hphysical,?_⟩⟩
  intro q hq
  convert hJ' q hq using 1
  symm
  by_cases hn : q.1=0
  · rcases q with ⟨r,z⟩
    change r=0 at hn
    subst r
    let i := fun r : ℝ ↦ (r,z)
    have hi : Continuous i := continuous_id.prodMk continuous_const
    have hJ₀ : ContinuousAt (J ∘ i) 0 := ContinuousAt.comp (f := i) (x := (0:ℝ)) (hJ.continuousAt (hU.mem_nhds hq)) hi.continuousAt
    have hA₀ : ContinuousAt (fun r : ℝ ↦ r • I-A (g (r,z))) 0 :=
      (continuousAt_id.smul continuousAt_const).sub (((he.continuousOn_fderiv_of_isOpen hW (by simp)).comp hg.continuousOn hm).continuousAt
        (hU.mem_nhds hq) |>.comp (f := i) (x := (0:ℝ)) hi.continuousAt)
    exact eq_at_zero_of_punctured hJ₀ hA₀ ((show ∀ᶠ r in 𝓝 (0:ℝ), (r,z) ∈ U from hi.continuousAt (hU.mem_nhds hq)).mono fun r hr hn ↦ hzero (r,z) hr hn)
  · exact hzero q hq hn

end EuclideanMidpointRigidity

