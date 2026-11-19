module

public import EuclideanMidpointRigidity.RulingStrip
public import EuclideanMidpointRigidity.JacobianPencil
public import EuclideanMidpointRigidity.ClearedTaylor

/-! # Continuing physical differential identities along a ruling strip -/

@[expose] public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.LiftedSection
variable {d : ℕ}
local notation "E" => Space d

def lineChart (S : LiftedSection d) : LineChart E (Cubic d) where
  domain := S.domain
  isOpen := S.isOpen
  position := fun t y ↦ y+t • S.axialDirection y
  jacobian := JacobianPencil.jacobian S.axialDirection
  hasJacobian := fun _ hy ↦ JacobianPencil.hasFDerivAt_chart S.isOpen S.smooth_axialDirection hy
  determinant := JacobianPencil.determinant S.axialDirection
  detFamily := JacobianPencil.determinantFamily S.isOpen S.smooth_axialDirection
  adjugate := JacobianPencil.adjugate S.axialDirection
  adjFamily := JacobianPencil.adjugateFamily S.isOpen S.smooth_axialDirection
  adjIdentity := fun y _ ↦ JacobianPencil.adjugate_identity S.axialDirection y
  field := S.continuedField
  fieldFamily := S.continuedFamily

theorem smooth_position (S : LiftedSection d) (t : ℝ) : ContDiffOn ℝ ∞ (S.lineChart.position t) S.domain :=
  contDiffOn_id.add ((contDiffOn_const (c := t)).smul S.smooth_axialDirection)

theorem RulingStrip.extend_expression {S : LiftedSection d} {U : Set E} {r : ℝ} (R : RulingStrip S U r)
    {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {f : (E → Cubic d) → E → Z}
    (F : Represented S.lineChart f) (hz : ∀ q ∈ S.domain, f S.field q=0)
    {Ω : Set E} {G : E → Cubic d} {y : E} {t : ℝ} (hΩ : IsOpen Ω) (hG : ContDiffOn ℝ ∞ G Ω)
    (hy : y ∈ U) (hx : S.lineChart.position t y ∈ Ω) (hd : S.lineChart.determinant y t≠0)
    (he : (fun z ↦ S.continuedField z t) =ᶠ[𝓝 y] (G ∘ S.lineChart.position t)) :
    f G (S.lineChart.position t y)=0 := by
  let N := F.some
  have hzero : N.numerator y =ᶠ[𝓝 (0:ℝ)] (fun _ ↦ 0) := by
    filter_upwards [ball_mem_nhds (0:ℝ) R.positive] with s hs
    have hn : (fun z ↦ S.lineChart.field z s) =ᶠ[𝓝 y] (S.field ∘ S.lineChart.position s) :=
      (show ∀ᶠ z in 𝓝 y, z ∈ U from R.isOpen.mem_nhds hy).mono (fun z h ↦ R.agrees z h s hs)
    have hdom : S.lineChart.position s y ∈ S.domain := R.maps y hy s hs
    rw [N.correct S.isOpen S.smooth (R.inside hy) hdom hn,hz _ hdom,smul_zero]
  have hh := N.family.extend_zero (R.inside hy) hzero t
  rw [N.correct hΩ hG (R.inside hy) hx he] at hh
  exact (smul_eq_zero.mp hh).resolve_left (pow_ne_zero _ hd)

end EuclideanMidpointRigidity.LiftedSection

