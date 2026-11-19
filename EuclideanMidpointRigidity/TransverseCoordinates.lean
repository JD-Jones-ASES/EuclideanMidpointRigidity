module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Tactic

/-! # Spatial coordinates from a transverse slice and a time parameter -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def transverseLinear (v : E) : E →L[ℝ] E × ℝ :=
  (ContinuousLinearMap.id ℝ E-(innerSL ℝ v).smulRight v).prod (innerSL ℝ v)

def transverseCoordinates (p v y : E) : E × ℝ := (p,0)+transverseLinear v (y-p)

@[simp] theorem transverseCoordinates_center (p v : E) : transverseCoordinates p v p=(p,0) := by
  simp [transverseCoordinates]

theorem transverseLinear_axis {v : E} (hv : ‖v‖=1) : transverseLinear v v=(0,1) := by
  ext <;> simp [transverseLinear,hv]

theorem hasFDerivAt_transverseCoordinates (p v y : E) :
    HasFDerivAt (transverseCoordinates p v) (transverseLinear v) y := by
  have h := ((transverseLinear v).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const p)).const_add (p,0)
  change HasFDerivAt (fun x ↦ (p,0)+transverseLinear v (x-p)) (transverseLinear v) y
  simpa only [Function.comp_def,id_eq,ContinuousLinearMap.comp_id] using h

theorem contDiff_transverseCoordinates (p v : E) : ContDiff ℝ ∞ (transverseCoordinates p v) :=
  contDiff_const.add ((transverseLinear v).contDiff.comp (contDiff_id.sub contDiff_const))

theorem fderiv_time_direction {Z : E × ℝ → F} {q : E × ℝ} (hZ : DifferentiableAt ℝ Z q)
    {b : F} (ht : HasDerivAt (fun t ↦ Z (q.1,t)) b q.2) : fderiv ℝ Z q (0,1)=b := by
  have hline : HasDerivAt (fun t : ℝ ↦ (q.1,t)) (0,1) q.2 := (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
  exact (hZ.hasFDerivAt.comp_hasDerivAt q.2 hline).unique ht

theorem transverse_axial_derivative {p v y : E} (hv : ‖v‖=1) {Z : E × ℝ → F}
    (hZ : DifferentiableAt ℝ Z (transverseCoordinates p v y)) {b : F}
    (ht : HasDerivAt (fun t ↦ Z ((transverseCoordinates p v y).1,t)) b (transverseCoordinates p v y).2) :
    fderiv ℝ (Z ∘ transverseCoordinates p v) y v=b := by
  rw [(hZ.hasFDerivAt.comp y (hasFDerivAt_transverseCoordinates p v y)).fderiv,
    ContinuousLinearMap.comp_apply,transverseLinear_axis hv]
  exact fderiv_time_direction hZ ht

/-- At the initial point the parameter-to-position map has derivative the identity:
the transverse part is fixed at time zero and the missing direction is supplied by velocity. -/
theorem transverse_initial_derivative {p v : E} {Z : E × ℝ → E} (hZ : DifferentiableAt ℝ Z (p,0))
    (hinit : ∀ᶠ y in 𝓝 p, Z (y,0)=y) (ht : HasDerivAt (fun t ↦ Z (p,t)) v 0) :
    fderiv ℝ (Z ∘ transverseCoordinates p v) p=ContinuousLinearMap.id ℝ E := by
  let L := fderiv ℝ Z (p,0)
  have hcomp := hZ.hasFDerivAt.comp p (hasFDerivAt_prodMk_left (𝕜 := ℝ) p (0:ℝ))
  have hid : HasFDerivAt (fun y ↦ Z (y,0)) (ContinuousLinearMap.id ℝ E) p :=
    (hasFDerivAt_id p).congr_of_eventuallyEq hinit
  have hl : L ∘L .inl ℝ E ℝ=ContinuousLinearMap.id ℝ E := hcomp.unique hid
  have hleft (w : E) : L (w,0)=w := congrArg (fun A : E →L[ℝ] E ↦ A w) hl
  have htime : L (0,1)=v := fderiv_time_direction hZ ht
  have hz : HasFDerivAt Z L (transverseCoordinates p v p) := by simpa only [transverseCoordinates_center] using hZ.hasFDerivAt
  rw [(hz.comp p (hasFDerivAt_transverseCoordinates p v p)).fderiv]
  ext w
  change L (transverseLinear v w)=w
  let t := ⟪v,w⟫_ℝ
  have hsplit : transverseLinear v w=(w-t • v,0)+t • ((0,1) : E × ℝ) := by
    ext <;> simp [transverseLinear,t]
  rw [hsplit,map_add,map_smul,hleft,htime,sub_add_cancel]

end EuclideanMidpointRigidity

