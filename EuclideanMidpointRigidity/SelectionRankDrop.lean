module

public import EuclideanMidpointRigidity.RankDropCoordinates
public import Mathlib.Analysis.InnerProductSpace.Dual

/-! # A local rank drop when a value-preserving motion changes a selector -/

public section
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity
variable {E Z : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]

/-- A motion starts at each point and carries its selected value unchanged.
A nonzero derivative in the velocity direction removes one independent direction
from the selector, by restricting its starting points to one scalar level. -/
theorem selection_rank_drop {W : Set E} (hW : IsOpen W) {f : E → Z} (hf : ContDiffOn ℝ ∞ f W)
    {O : Set (E × ℝ)} (hO : IsOpen O) {X : E × ℝ → E} (hX : ContDiffOn ℝ ∞ X O)
    {p v : E} (hp : p ∈ W) (hpO : (p,0) ∈ O) (hinit : ∀ᶠ y in 𝓝 p, X (y,0)=y)
    (hvel : HasDerivAt (fun t ↦ X (p,t)) v 0) (hne : fderiv ℝ f p v≠0)
    {k : ℕ} (hrank : ∀ y ∈ W, derivativeRank f y≤k)
    {R : E → Z → Prop} (hmove : ∀ q ∈ O, R (X q) (f q.1)) :
    ∃ (U : Set E) (g : E → Z), IsOpen U ∧ p ∈ U ∧ U ⊆ W ∧ ContDiffOn ℝ ∞ g U ∧
      ∀ y ∈ U, R y (g y) ∧ derivativeRank g y<k := by
  let w := fderiv ℝ f p v
  let L : Z →L[ℝ] ℝ := innerSL ℝ w
  have hw : L (fderiv ℝ f p v)≠0 := by
    change ⟪w,w⟫_ℝ≠0
    exact inner_self_ne_zero.mpr hne
  let c := L (f p)
  let D := W ∩ (fun y ↦ L (fderiv ℝ f y v)) ⁻¹' ({0} : Set ℝ)ᶜ
  have hD : IsOpen D := (L.continuous.comp_continuousOn ((hf.continuousOn_fderiv_of_isOpen hW (by simp)).clm_apply continuousOn_const)).isOpen_inter_preimage hW isClosed_singleton.isOpen_compl
  let B := O ∩ (Prod.fst : E × ℝ → E) ⁻¹' D
  have hB : IsOpen B := hO.inter (hD.preimage continuous_fst)
  have hpB : (p,(0:ℝ)) ∈ B := ⟨hpO,hp,hw⟩
  let M := fun q : E × ℝ ↦ (X q,L (f q.1))
  have hBmap : MapsTo (Prod.fst : E × ℝ → E) B W := fun _ h ↦ h.2.1
  have hM : ContDiffOn ℝ ∞ M B := (hX.mono inter_subset_left).prodMk (L.contDiff.comp_contDiffOn (hf.comp contDiffOn_fst hBmap))
  have hi := transverse_scalar_coordinates L ((hX.contDiffAt (hO.mem_nhds hpO)).differentiableAt (by simp))
    ((hf.contDiffAt (hW.mem_nhds hp)).differentiableAt (by simp)) hinit hvel hw
  obtain ⟨V,r,hV,hmV,_,hr,hsol⟩ := smooth_spatial_inverse hB hM hpB hi
  let I := fun y : E ↦ (y,c)
  have hI : ContDiff ℝ ∞ I := contDiff_id.prodMk contDiff_const
  let U := W ∩ I ⁻¹' V
  have hU : IsOpen U := hW.inter (hV.preimage hI.continuous)
  have hm0 : M (p,0)=I p := Prod.ext hinit.self_of_nhds rfl
  have hpU : p ∈ U := ⟨hp,by change I p ∈ V; rwa [← hm0]⟩
  let q := r ∘ I
  let y := fun x ↦ (q x).1
  have hq : ContDiffOn ℝ ∞ q U := hr.comp hI.contDiffOn (fun _ h ↦ h.2)
  have hy : ContDiffOn ℝ ∞ y U := hq.fst
  have hyD (x : E) (hx : x ∈ U) : y x ∈ D := (hsol (I x) hx.2).1.2
  let g := f ∘ y
  have hg : ContDiffOn ℝ ∞ g U := hf.comp hy (fun x hx ↦ (hyD x hx).1)
  have he (x : E) (hx : x ∈ U) : M (q x)=I x := (hsol _ hx.2).2.1
  have hlevel (x : E) (hx : x ∈ U) : L (g x)=c := congrArg Prod.snd (he x hx)
  refine ⟨U,g,hU,hpU,inter_subset_left,hg,?_⟩
  intro x hx
  have hXeq : X (q x)=x := congrArg Prod.fst (he x hx)
  have hrel := hmove (q x) (hsol _ hx.2).1.1
  rw [hXeq] at hrel
  refine ⟨hrel,?_⟩
  have hyw := (hyD x hx).1
  have hDf := (hf.contDiffAt (hW.mem_nhds hyw)).differentiableAt (by simp)
  have hDy := (hy.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hDg : fderiv ℝ g x=(fderiv ℝ f (y x)).comp (fderiv ℝ y x) := (hDf.hasFDerivAt.comp x hDy.hasFDerivAt).fderiv
  have hrange : (fderiv ℝ g x).toLinearMap.range ≤ (fderiv ℝ f (y x)).toLinearMap.range := by
    rintro z ⟨u,rfl⟩
    exact ⟨fderiv ℝ y x u,by rw [hDg]; rfl⟩
  have hconst : L ∘ g =ᶠ[𝓝 x] (fun _ ↦ c) := (show ∀ᶠ x' in 𝓝 x, x' ∈ U from hU.mem_nhds hx).mono (fun z hz ↦ hlevel z hz)
  have hder := ((L.hasFDerivAt.comp x ((hg.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt).unique
    ((hasFDerivAt_const c x).congr_of_eventuallyEq hconst))
  exact (strict_rank_on_slice (hyD x hx).2 hrange (fun u ↦ congrArg (fun D : E →L[ℝ] ℝ ↦ D u) hder)).trans_le (hrank _ hyw)

end EuclideanMidpointRigidity

