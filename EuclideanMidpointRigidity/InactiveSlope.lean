module

public import EuclideanMidpointRigidity.WeakShearLimit
public import EuclideanMidpointRigidity.FixedAxisSlice
public import EuclideanMidpointRigidity.NormalizedAxisFrame
public import EuclideanMidpointRigidity.CoupledKilling

/-! # The derivative of the maximizing direction takes values in the kernel of the cubic derivative -/

public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.HorizontalPatch
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d
set_option backward.isDefEq.respectTransparency false

private theorem fixed_idempotent {S : LiftedSection d} (H : HorizontalPatch S) {p : Space d}
    (R : ShearInverse S.axis S.domain p) {r : ℝ} (hr : 0<r) (hB : ∀ z ∈ ball (0:E) r, (0,z) ∈ R.domain)
    {z : E} (hz : z ∈ ball (0:E) r) : S.idempotent (R.inverse (0,z))=S.idempotent p := by
  have ha : ContDiffOn ℝ ∞ S.a S.domain := contDiffOn_sectionValue S.smooth S.smoothAxis
  have hd (y : E) (hy : y ∈ ball (0:E) r) : HasFDerivAt (𝕜 := ℝ) (fun v ↦ S.a (R.inverse (0,v))) 0 y := by
    have h := ((ha.contDiffAt (S.isOpen.mem_nhds (R.maps (hB y hy)))).differentiableAt (by simp)).hasFDerivAt.comp y (R.spatial (0,y) (hB y hy))
    rw [S.stationary_value (R.maps (hB y hy)) H.maximizes,ContinuousLinearMap.zero_comp] at h
    exact h
  have h := isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball _ _).isPreconnected
    (fun y hy ↦ (hd y hy).differentiableAt.differentiableWithinAt) (fun {y} hy ↦ (hd y hy).fderiv) hz (mem_ball_self hr)
  rw [R.center 0 R.origin] at h
  simp only [LiftedSection.idempotent,h,H.fixed_limit_axis R hr hB hz]

theorem inactive_slope {S : LiftedSection d} (H : HorizontalPatch S) {p : E} (hp : p ∈ S.domain) (v : E) :
    fderiv ℝ S.field p (fderiv ℝ S.axis p v)=0 := by
  obtain ⟨R⟩ := exists_shear_inverse S.isOpen S.smoothAxis (fun q h ↦ H.square_zero h) hp
  let i := fun z : E ↦ ((0:ℝ),z)
  have hi : ContDiff ℝ ∞ i := contDiff_const.prodMk contDiff_id
  obtain ⟨r,hr,hB⟩ := Metric.mem_nhds_iff.mp (hi.continuous.continuousAt (R.isOpen.mem_nhds R.origin) : i ⁻¹' R.domain ∈ 𝓝 0)
  let W := ball (0:E) r
  let f := fun z : E ↦ R.inverse (0,z)
  let F := S.field ∘ f
  let u := S.idempotent p
  have hmem (z : E) (hz : z ∈ W) : f z ∈ S.domain := R.maps (hB hz)
  have hid (z : E) (hz : z ∈ W) : S.idempotent (f z)=u := H.fixed_idempotent R hr (fun _ hy ↦ hB hy) hz
  have hF : ContDiffOn ℝ ∞ F W := S.smooth.comp (R.smooth.comp hi.contDiffOn hB) hmem
  have hQ : QuarticOn W F := fun z hz w ↦ (H.limit_equations R (hB hz) w).1
  have hdiff (z : E) (hz : z ∈ W) (w : E) :
      fderiv ℝ F z w= -fderiv ℝ S.field (f z) (fderiv ℝ S.axis (f z) w) := by
    have hh := ((S.smooth.contDiffAt (S.isOpen.mem_nhds (hmem z hz))).differentiableAt (by simp)).hasFDerivAt.comp z (R.spatial (0,z) (hB hz))
    rw [show fderiv ℝ F z=_ from hh.fderiv]
    change fderiv ℝ S.field (f z) ((0:ℝ) • w-fderiv ℝ S.axis (f z) w)=_
    rw [zero_smul,zero_sub,map_neg]
  have hframe (z : E) (hz : z ∈ W) : Nonempty (FixedAxis.SliceFrame (F z) u) := by
    rw [← hid z hz]
    exact S.idempotent_frame (hmem z hz) (H.maximizes _ (hmem z hz))
  have he (z : E) (hz : z ∈ W) : K (F z) u u=u := by
    rw [← hid z hz]; exact S.idempotent_square (hmem z hz)
  have hU (z : E) (hz : z ∈ W) : fderiv ℝ F z u=0 := by
    rw [hdiff z hz,← hid z hz,LiftedSection.idempotent,map_smul,S.straight_axis (hmem z hz) H.maximizes,smul_zero,map_zero,neg_zero]
  have hk (z : E) (hz : z ∈ W) (l : E) (hl : K (F z) u l=0) : fderiv ℝ F z l=0 := by
    rw [← hid z hz,LiftedSection.idempotent,K_smul_left] at hl
    have ha : 0<S.a (f z) := S.positive (f z) (hmem z hz)
    have hl' : K (S.field (f z)) (S.axis (f z)) l=(0:ℝ) • l := by
      rw [zero_smul]; exact (smul_eq_zero.mp hl).resolve_left (inv_ne_zero ha.ne')
    rw [hdiff z hz,H.annihilates_eigen (hmem z hz) hl' (by apply mul_ne_zero <;> nlinarith),map_zero,neg_zero]
  have hK (z : E) (hz : z ∈ W) : ∀ w, directionProfile w (fderiv ℝ F z w)=0 :=
    FixedAxis.killing_of_slice_kernel (hframe z hz).some (hQ hz) (hU z hz)
      (FixedAxis.constant_slice isOpen_ball hF hQ he hU hframe hz) (hk z hz)
  have h₀ : (0:E) ∈ W := mem_ball_self hr
  have hJ := killing_cubic_rigidity isOpen_ball (hF.of_le (by simp)) hQ hK h₀
  have h := hdiff 0 h₀ v
  rw [hJ,zero_apply,show f 0=p from R.center 0 R.origin] at h
  exact neg_eq_zero.mp h.symm

end EuclideanMidpointRigidity.HorizontalPatch

