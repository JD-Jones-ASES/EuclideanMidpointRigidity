module

public import EuclideanMidpointRigidity.SpatialInverse
public import EuclideanMidpointRigidity.TransverseCoordinates
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Coordinates for reducing the rank of a family of selected directions -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
variable {E Z : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

def selectionBlock (v : E) (L : E →L[ℝ] ℝ) : (E × ℝ) →L[ℝ] (E × ℝ) :=
  ((ContinuousLinearMap.fst ℝ E ℝ)+(ContinuousLinearMap.snd ℝ E ℝ).smulRight v).prod (L.comp (.fst ℝ E ℝ))

theorem selectionBlock_invertible {v : E} {L : E →L[ℝ] ℝ} (h : L v≠0) : (selectionBlock v L).IsInvertible := by
  let B := selectionBlock v L
  have hs : Function.Surjective B := by
    rintro ⟨u,t⟩
    let k := (L u-t)/(L v)
    refine ⟨(u-k • v,k),Prod.ext ?_ ?_⟩
    · change u-k • v+k • v=u; abel
    · change L (u-k • v)=t
      rw [map_sub,map_smul,smul_eq_mul]
      dsimp only [k]
      field_simp
      ring
  let e := (LinearEquiv.ofBijective B.toLinearMap ⟨LinearMap.injective_iff_surjective.mpr hs,hs⟩).toContinuousLinearEquiv
  exact ⟨e,ContinuousLinearMap.ext (fun _ ↦ rfl)⟩

theorem derivative_initial_motion {p v : E} {X : E × ℝ → E} (hX : DifferentiableAt ℝ X (p,0))
    (hinit : ∀ᶠ y in 𝓝 p, X (y,0)=y) (hvel : HasDerivAt (fun t ↦ X (p,t)) v 0) (z : E × ℝ) :
    fderiv ℝ X (p,0) z=z.1+z.2 • v := by
  let B := fderiv ℝ X (p,0)
  have hl := hX.hasFDerivAt.comp p (hasFDerivAt_prodMk_left (𝕜 := ℝ) p (0:ℝ))
  have hi : HasFDerivAt (fun y ↦ X (y,0)) (ContinuousLinearMap.id ℝ E) p := (hasFDerivAt_id p).congr_of_eventuallyEq hinit
  have hf (x : E) : B (x,0)=x := congrArg (fun L : E →L[ℝ] E ↦ L x) (hl.unique hi)
  have hr : B (0,1)=v := (hX.hasFDerivAt.comp_hasDerivAt (0:ℝ) ((hasDerivAt_const (0:ℝ) p).prodMk (hasDerivAt_id (0:ℝ)))).unique hvel
  change B z=_
  have hs : z=(z.1,0)+z.2 • ((0,1) : E × ℝ) := by ext <;> simp
  calc
    B z=B ((z.1,0)+z.2 • ((0,1) : E × ℝ)) := congrArg B hs
    _ = _ := by rw [map_add,map_smul,hf,hr]

theorem transverse_scalar_coordinates {p v : E} {X : E × ℝ → E} {f : E → Z} (L : Z →L[ℝ] ℝ)
    (hX : DifferentiableAt ℝ X (p,0)) (hf : DifferentiableAt ℝ f p)
    (hinit : ∀ᶠ y in 𝓝 p, X (y,0)=y) (hvel : HasDerivAt (fun t ↦ X (p,t)) v 0)
    (hv : L (fderiv ℝ f p v)≠0) : (fderiv ℝ (fun q : E × ℝ ↦ (X q,L (f q.1))) (p,0)).IsInvertible := by
  let M := L.comp (fderiv ℝ f p)
  have h := hX.hasFDerivAt.prodMk ((L.hasFDerivAt.comp p hf.hasFDerivAt).comp (p,(0:ℝ)) hasFDerivAt_fst)
  have he : fderiv ℝ (fun q : E × ℝ ↦ (X q,L (f q.1))) (p,0)=selectionBlock v M := by
    change HasFDerivAt (fun q : E × ℝ ↦ (X q,L (f q.1))) _ _ at h
    rw [h.fderiv]
    apply ContinuousLinearMap.ext
    intro z
    exact Prod.ext (derivative_initial_motion hX hinit hvel z) rfl
  rw [he]
  exact selectionBlock_invertible hv

def derivativeRank (f : E → Z) (p : E) := Module.finrank ℝ (fderiv ℝ f p).toLinearMap.range

theorem strict_rank_on_slice {L : Z →L[ℝ] ℝ} {A B : E →L[ℝ] Z} {v : E} (hv : L (A v)≠0)
    (hab : B.toLinearMap.range ≤ A.toLinearMap.range) (hz : ∀ w, L (B w)=0) :
    Module.finrank ℝ B.toLinearMap.range<Module.finrank ℝ A.toLinearMap.range := by
  apply Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hab ?_)
  intro he
  obtain ⟨w,hw⟩ := (show A v ∈ B.toLinearMap.range from he ▸ ⟨v,rfl⟩)
  exact hv (hw ▸ hz w)

end EuclideanMidpointRigidity

