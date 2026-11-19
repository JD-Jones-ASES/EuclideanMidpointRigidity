module

public import EuclideanMidpointRigidity.HorizontalSelector
public import EuclideanMidpointRigidity.ClearedMidpoint
public import EuclideanMidpointRigidity.InverseGerms

/-! # Continuation of the midpoint equations in square-zero shear coordinates -/

@[expose] public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.HorizontalPatch
variable {d : ℕ} {S : LiftedSection d} (H : HorizontalPatch S)
local notation "E" => Space d
local notation "I" => ContinuousLinearMap.id ℝ E

def position (S : LiftedSection d) (t : ℝ) (y : E) := y+t • S.axis y

include H

theorem cancel_shear {y : E} (hy : y ∈ S.domain) (t : ℝ) (v : E) :
    (I+t • fderiv ℝ S.axis y) ((I-t • fderiv ℝ S.axis y) v)=v := by
  simp only [add_apply,sub_apply,smul_apply,
    ContinuousLinearMap.id_apply,map_sub,map_smul,H.square_zero hy,smul_zero,sub_zero,add_zero,sub_add_cancel,add_sub_cancel_right]

def shearChart : LineChart E (Cubic d) where
  domain := S.domain
  isOpen := S.isOpen
  position := position S
  jacobian := JacobianPencil.jacobian S.axis
  hasJacobian := fun _ hy ↦ JacobianPencil.hasFDerivAt_chart S.isOpen S.smoothAxis hy
  determinant := fun _ _ ↦ 1
  detFamily := AnalyticLineFamily.const _ 1
  adjugate := fun y t ↦ I-t • fderiv ℝ S.axis y
  adjFamily := (AnalyticLineFamily.const _ I).sub ((AnalyticLineFamily.time _).smul
    (AnalyticLineFamily.spatial (S.smoothAxis.fderiv_of_isOpen S.isOpen (by simp))))
  adjIdentity := fun y hy t v ↦ (H.cancel_shear hy t v).trans (one_smul ℝ v).symm
  field := fun y _ ↦ S.field y
  fieldFamily := AnalyticLineFamily.spatial S.smooth

theorem invariant_strip {p : E} (hp : p ∈ S.domain) :
    ∃ (U : Set E) (r : ℝ), IsOpen U ∧ p ∈ U ∧ 0<r ∧ ∀ y ∈ U, ∀ t ∈ ball (0:ℝ) r,
      position S t y ∈ S.domain ∧ S.field (position S t y)=S.field y := by
  obtain ⟨U,r,hU,hpU,hr,hline⟩ := S.local_straight_rulings hp H.maximizes
  refine ⟨U,r,hU,hpU,hr,?_⟩
  intro y hy t ht
  let f := fun s ↦ position S s y
  have hg (s : ℝ) (hs : s ∈ ball (0:ℝ) r) := hline y hy s hs
  have hd (s : ℝ) (hs : s ∈ ball (0:ℝ) r) : HasDerivAt (S.field ∘ f) 0 s := by
    have h : HasDerivAt f (S.axis y) s := by
      simpa only [f,position,one_smul,zero_add,id_eq] using (hasDerivAt_const s y).fun_add ((hasDerivAt_id s).smul_const (S.axis y))
    have hmem : f s ∈ S.domain := (hg s hs).1
    have hdir : S.axis (f s)=S.axis y := (hg s hs).2.1
    have hz := S.stationary_field_along_axis H.maximizes H.charts hmem
    rw [hdir] at hz
    exact hz ▸ ((S.smooth.contDiffAt (S.isOpen.mem_nhds hmem)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s h
  refine ⟨(hg t ht).1,?_⟩
  have he := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball _ _).isPreconnected
    (fun s hs ↦ (hd s hs).differentiableAt.differentiableWithinAt) (fun {s} hs ↦ (hd s hs).deriv) ht (mem_ball_self hr)
  simpa only [Function.comp_apply,f,position,zero_smul,add_zero] using he

theorem extend_shear {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {f : (E → Cubic d) → E → Z}
    (F : Represented H.shearChart f) (hz : ∀ q ∈ S.domain, f S.field q=0) {p : E} (hp : p ∈ S.domain)
    {t : ℝ} {V : Set E} {G : E → Cubic d} (hV : IsOpen V) (hG : ContDiffOn ℝ ∞ G V)
    (hv : position S t p ∈ V) (hg : S.field =ᶠ[𝓝 p] G ∘ position S t) :
    f G (position S t p)=0 := by
  obtain ⟨U,r,hU,hpU,hr,hstrip⟩ := H.invariant_strip hp
  let N := F.some
  have hnear : N.numerator p =ᶠ[𝓝 (0:ℝ)] (fun _ ↦ 0) := by
    filter_upwards [ball_mem_nhds (0:ℝ) hr] with s hs
    have he : S.field =ᶠ[𝓝 p] S.field ∘ position S s :=
      (show ∀ᶠ y in 𝓝 p, y ∈ U from hU.mem_nhds hpU).mono fun y hy ↦ (hstrip y hy s hs).2.symm
    have h := N.correct S.isOpen S.smooth hp (hstrip p hpU s hs).1 he
    change N.numerator p s=(1:ℝ)^N.weight • f S.field (position S s p) at h
    rwa [hz _ (hstrip p hpU s hs).1,smul_zero] at h
  have h := N.family.extend_zero hp hnear t
  rw [N.correct hV hG hp hv hg] at h
  simpa only [shearChart,one_pow,one_smul] using h

end EuclideanMidpointRigidity.HorizontalPatch

