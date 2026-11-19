module

public import EuclideanMidpointRigidity.ObservationBound
public import EuclideanMidpointRigidity.FirstTiltSeparation
public import EuclideanMidpointRigidity.FiniteObservations

/-! # A spatially fixed maximizing direction stays idempotent on an open ball -/

public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity.HorizontalPatch
open Endpoint
variable {d : ℕ} {S : LiftedSection d} (H : HorizontalPatch S)
local notation "E" => Space d
local notation "Op" => E →L[ℝ] E
set_option backward.isDefEq.respectTransparency false

include H in
theorem persistent_idempotent {p : E} (hp : p ∈ S.domain) {r : ℝ} (hr : 0<r) (hsub : ball p r ⊆ S.domain)
    (hin : ∀ x ∈ ball p r, fderiv ℝ S.field x (S.idempotent p)=0) :
    ∀ᶠ x in 𝓝 p, K (S.field x) (S.idempotent p) (S.idempotent p)=S.idempotent p := by
  classical
  let u := S.idempotent p
  let W := ball p r
  have h₀ : p ∈ W := mem_ball_self hr
  let F := (S.idempotent_frame hp (H.maximizes p hp)).some
  let I := Unit ⊕ Fin F.n
  obtain ⟨D⟩ := H.charts p hp
  let R := fun v : E ↦ Horizontal.spatialSlice (fderiv ℝ S.field (p+v)) u
  let q := fun v : E ↦ K (S.field (p+v)) u u-K (S.field p) u u
  have hsmall : ∀ᶠ h in 𝓝 (0:ℝ), h*‖u‖<r := (continuous_id.mul continuous_const).continuousAt
    (Iio_mem_nhds (by simpa using hr : 0*‖u‖<r))
  have realized := S.eventually_realized_chords hp H.maximizes D
  change ∀ᶠ h in 𝓝[>] (0:ℝ), chordEnds p u h ∈ D.domain ∧ _ at realized
  have test (m : I × I) : ∃ (A : E → Op →L[ℝ] E), ContinuousAt A 0 ∧
      (∃ L : ℝ, 0≤L ∧ ∀ᶠ v in 𝓝 (0:E), ‖A v (R v)‖≤L*‖q v‖) ∧
      ∀ M : Op, A 0 M=0 → ⟪F.basis m.2,M (F.basis m.1)⟫_ℝ=0 := by
    let b := F.eigenvalue m.1
    let c := F.eigenvalue m.2
    let k := 1-2*b
    let η := 1-2*c
    have hbad : ∃ᶠ h in 𝓝[>] (0:ℝ), ¬VanishingResponse η h (centeredCoordinate k h) := by
      simpa only [Filter.Frequently,not_not] using firstTilt_detects η k
    obtain ⟨h,hfail,⟨hd,J,N⟩,hsize⟩ := (hbad.and_eventually (realized.and (mem_nhdsWithin_of_mem_nhds hsmall))).exists
    let j := (centeredProfile k h).ends h (F.basis m.1)
    let A := D.observation u h J.positive j
    have ins (t : UnitInterval) : axialPosition p u h t ∈ W ∧ axialPosition p (-u) h t ∈ W := by
      have hb := abs_le.mpr (chordParameter_bounds J.positive.le t.property)
      have hh := (mul_le_mul_of_nonneg_right hb (norm_nonneg u)).trans_lt hsize
      simpa only [W,axialPosition,mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,norm_neg,and_self] using hh
    refine ⟨A,D.observation_continuous J N j,D.observation_bound J N hd isOpen_ball (convex_ball _ _)
      (S.smooth.mono hsub) h₀ (fun t ↦ (ins t).1) (fun t ↦ (ins t).2) hin j (centered_ends ..),?_⟩
    intro M hm
    by_contra hn
    have h₁ := (S.idempotent_slice p _).symm.trans (F.eigen m.1)
    have h₂ := (S.idempotent_slice p _).symm.trans (F.eigen m.2)
    have hsol := D.observation_kernel J N S.isOpen S.smooth h₁ h₂ M hm
    apply hfail
    apply (hsol.smul (⟪F.basis m.2,M (F.basis m.1)⟫_ℝ)⁻¹).congr
    intro s _
    change _⁻¹*(_*centeredCoordinate k h s)=_
    rw [← mul_assoc,inv_mul_cancel₀ hn,one_mul]
  choose A hA hb hk using test
  have injective (M : Op) (hm : ∀ i, A i 0 M=0) : M=0 := by
    have he (i : I) : M (F.basis i)=0 := by
      rw [← F.basis.sum_repr' (M (F.basis i))]
      exact Finset.sum_eq_zero fun j _ ↦ by rw [hk (i,j) M (hm (i,j)),zero_smul]
    exact ContinuousLinearMap.coe_injective (F.basis.toBasis.ext he)
  obtain ⟨K₀,_,hK⟩ := finite_observation_bound A _ R q (fun i ↦ (hA i).tendsto) injective hb
  have hnear : ∀ᶠ v in 𝓝 (0:E), p+v ∈ S.domain := (continuous_const.add continuous_id).continuousAt
    (S.isOpen.mem_nhds (by simpa using hp : p+0 ∈ S.domain))
  have hd {v : E} (hv : p+v ∈ S.domain) : HasFDerivAt q (R v) v := by
    let L := (ContinuousLinearMap.apply ℝ E u).comp (FixedAxis.sliceMap u)
    have hc := ((S.smooth.contDiffAt (S.isOpen.mem_nhds hv)).differentiableAt (by simp)).hasFDerivAt
    have hshift := (hasFDerivAt_id (𝕜 := ℝ) v).const_add p
    exact (((L.hasFDerivAt.comp (p+v) hc).comp v hshift).sub_const (K (S.field p) u u))
  have hz := local_zero_of_derivative_bound (p := (0:E)) (f := q) (by simp [q]) K₀
    (hnear.and hK |>.mono fun v hv ↦ ⟨(hd hv.1).differentiableAt,(hd hv.1).fderiv.symm ▸ hv.2⟩)
  have ht : Tendsto (fun x : E ↦ x-p) (𝓝 p) (𝓝 (0:E)) := by
    have h : ContinuousAt (fun x : E ↦ x-p) p := continuousAt_id.sub continuousAt_const
    simpa only [sub_self] using h.tendsto
  filter_upwards [ht hz] with x hx
  have he : K (S.field x) u u=K (S.field p) u u := sub_eq_zero.mp (by simpa [q] using hx)
  exact he.trans (S.idempotent_square hp)

end EuclideanMidpointRigidity.HorizontalPatch

