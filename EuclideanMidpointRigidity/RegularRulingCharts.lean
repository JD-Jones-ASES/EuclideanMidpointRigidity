module

public import EuclideanMidpointRigidity.RulingChart
public import EuclideanMidpointRigidity.ClearedMidpoint
public import EuclideanMidpointRigidity.InverseGerms
public import EuclideanMidpointRigidity.ConstantAmplitude

/-! # The midpoint equations and constant maximum on regular inverse charts -/

public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.LiftedSection
variable {d : ℕ}
local notation "E" => Space d

theorem RulingStrip.regular_amplitude {S : LiftedSection d} {U : Set E} {r : ℝ} (R : RulingStrip S U r)
    {p : E} (hp : p ∈ U) {t : ℝ} (hd : S.lineChart.determinant p t≠0) :
    (fun y ↦ amplitude (S.continuedField y t)) =ᶠ[𝓝 p] (fun _ ↦ amplitude (S.continuedField p t)) := by
  let A := S.lineChart
  let Φ := A.position t
  let W := U ∩ (fun y ↦ A.determinant y t) ⁻¹' ({0} : Set ℝ)ᶜ
  have hW : IsOpen W := ((A.detFamily.smooth_space t).continuousOn.mono R.inside).isOpen_inter_preimage R.isOpen isClosed_singleton.isOpen_compl
  have hpW : p ∈ W := ⟨hp,hd⟩
  have hΦ : ContDiffOn ℝ ∞ Φ W := (S.smooth_position t).mono (inter_subset_left.trans R.inside)
  have hInv : (fderiv ℝ Φ p).IsInvertible := by
    rw [(A.hasJacobian p (R.inside hp) t).fderiv]
    exact JacobianPencil.regular hd
  obtain ⟨V,ψ,hV,hpV,hψp,hψ,hinv⟩ := smooth_inverse_germs hW hΦ hpW hInv
  let G := fun x ↦ S.continuedField (ψ x) t
  have hG : ContDiffOn ℝ ∞ G V := (S.continuedFamily.smooth_space t).comp hψ (fun x hx ↦ R.inside (hinv x hx).1.1)
  have hgerm (x : E) (hx : x ∈ V) : (fun y ↦ S.continuedField y t) =ᶠ[𝓝 (ψ x)] G ∘ Φ := by
    filter_upwards [(hinv x hx).2.2] with y hy
    change ψ (Φ y)=y at hy
    change S.continuedField y t=S.continuedField (ψ (Φ y)) t
    rw [hy]
  have hPhysical {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {f : (E → Cubic d) → E → Z}
      (F : Represented A f) (hz : ∀ q ∈ S.domain, f S.field q=0) : ∀ x ∈ V, f G x=0 := by
    intro x hx
    obtain ⟨hw,he,_⟩ := hinv x hx
    have hmem : Φ (ψ x) ∈ V := he.symm ▸ hx
    have H := R.extend_expression F hz hV hG hw.1 hmem hw.2 (hgerm x hx)
    change f G (Φ (ψ x))=0 at H
    rwa [he] at H
  have hEq : MidpointJetEquations V G := ⟨fun p hp z ↦ hPhysical (Represented.quartic A z) (fun q hq ↦ S.equations.quartic hq z) p hp,
    fun p hp z ↦ hPhysical (Represented.sixth A z) (fun q hq ↦ S.equations.sixth hq z) p hp⟩
  obtain ⟨δ,hδ,hB⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hpV)
  obtain ⟨c,hc⟩ := (hEq.mono hB).amplitude_constant isOpen_ball (convex_ball _ _).isPreconnected (hG.mono hB)
  have hg := hgerm (Φ p) hpV
  rw [hψp] at hg
  have hnear : ∀ᶠ y in 𝓝 p, Φ y ∈ ball (Φ p) δ := (A.hasJacobian p (R.inside hp) t).continuousAt (ball_mem_nhds _ hδ)
  have he := hg.eq_of_nhds
  filter_upwards [hg,hnear] with y hy hb
  rw [hy,he]
  exact (hc _ hb).trans (hc _ (mem_ball_self hδ)).symm

end EuclideanMidpointRigidity.LiftedSection

