module

public import EuclideanMidpointRigidity.KillingTraceRigidity

/-! # A fixed stationary idempotent has spatially constant multiplication -/

public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.FixedAxis
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d
local notation "Op" => E →L[ℝ] E

theorem constant_slice {W : Set E} {C : E → T} {u : E} (hW : IsOpen W) (hC : ContDiffOn ℝ ∞ C W)
    (hQ : QuarticOn W C) (he : ∀ x ∈ W, K (C x) u u=u)
    (hU : ∀ x ∈ W, fderiv ℝ C x u=0) (hF : ∀ x ∈ W, Nonempty (SliceFrame (C x) u))
    {p : E} (hp : p ∈ W) (v w : E) : K (fderiv ℝ C p v) u w=0 := by
  let B := fun x ↦ sliceMap u (C x)
  have dB (x : E) (hx : x ∈ W) : HasFDerivAt B ((sliceMap u).comp (fderiv ℝ C x)) x :=
    (sliceMap u).hasFDerivAt.comp x ((hC.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have hJ (x : E) (hx : x ∈ W) (l : E) : K (fderiv ℝ C x l) u u=0 := by
    let L := (ContinuousLinearMap.apply ℝ E u).comp (sliceMap u)
    have h : HasFDerivAt (L ∘ C) (L.comp (fderiv ℝ C x)) x :=
      L.hasFDerivAt.comp x ((hC.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    have hh : L ∘ C =ᶠ[𝓝 x] (fun _ ↦ u) := (show ∀ᶠ y in 𝓝 x, y ∈ W from hW.mem_nhds hx).mono fun y hy ↦ he y hy
    exact DFunLike.congr_fun (h.unique ((hasFDerivAt_const u x).congr_of_eventuallyEq hh)) l
  have hk (x : E) (hx : x ∈ W) (l : E) : squareValue (fderiv ℝ B x l) l=0 := by
    rw [(dB x hx).fderiv]
    exact (diagonal_identities (hF x hx).some (hQ hx) (he x hx) (hJ x hx) (hU x hx) l).1
  have htr (x : E) (hx : x ∈ W) (l : E) : operatorTrace (weightDerivative (B x) (fderiv ℝ B x l))=0 := by
    rw [(dB x hx).fderiv]
    exact trace_rate_zero (hF x hx).some (hQ hx) (he x hx) (hJ x hx) (hU x hx) l
  have hz := killing_trace_rigidity hW (fun x hx ↦ (dB x hx).differentiableAt.differentiableWithinAt)
    (fun x _ a b ↦ K_selfAdjoint (C x) u a b) hk htr hp
  rw [(dB p hp).fderiv] at hz
  exact DFunLike.congr_fun (DFunLike.congr_fun hz v) w

end EuclideanMidpointRigidity.FixedAxis

