module

public import EuclideanMidpointRigidity.ShearCharts
public import EuclideanMidpointRigidity.ShearInverse

/-! # The physical midpoint field at a finite nonzero inverse scale -/

public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.HorizontalPatch
variable {d : ℕ} {S : LiftedSection d} (H : HorizontalPatch S)
local notation "E" => Space d
include H

theorem physical_chart {y : E} (hy : y ∈ S.domain) (t : ℝ) :
    ∃ (V : Set E) (G : E → Cubic d), IsOpen V ∧ position S t y ∈ V ∧ ContDiffOn ℝ ∞ G V ∧
      MidpointJetEquations V G ∧ S.field =ᶠ[𝓝 y] G ∘ position S t := by
  let Φ := position S t
  have hΦ : ContDiffOn ℝ ∞ Φ S.domain := contDiffOn_id.add ((contDiffOn_const (c := t)).smul S.smoothAxis)
  let J := H.shearChart.jacobian y t
  have hs : Function.Surjective J := fun v ↦ ⟨H.shearChart.adjugate y t v,H.cancel_shear hy t v⟩
  let L := (LinearEquiv.ofBijective J.toLinearMap ⟨LinearMap.injective_iff_surjective.mpr hs,hs⟩).toContinuousLinearEquiv
  have hi : (fderiv ℝ Φ y).IsInvertible := by
    change (fderiv ℝ (H.shearChart.position t) y).IsInvertible
    rw [(H.shearChart.hasJacobian y hy t).fderiv]
    exact ⟨L,ContinuousLinearMap.ext (fun _ ↦ rfl)⟩
  obtain ⟨V,g,hV,hpV,hgp,hg,hInv⟩ := smooth_inverse_germs S.isOpen hΦ hy hi
  let G := S.field ∘ g
  have hG : ContDiffOn ℝ ∞ G V := S.smooth.comp hg (fun q hq ↦ (hInv q hq).1)
  have hgerm (q : E) (hq : q ∈ V) : S.field =ᶠ[𝓝 (g q)] G ∘ Φ :=
    ((hInv q hq).2.2).mono fun z hz ↦ congrArg S.field hz.symm
  have hres {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {f : (E → Cubic d) → E → Z}
      (F : Represented H.shearChart f) (hz : ∀ q ∈ S.domain, f S.field q=0) (q : E) (hq : q ∈ V) : f G q=0 := by
    obtain ⟨hb,hi,_⟩ := hInv q hq
    have hV' : Φ (g q) ∈ V := by rwa [hi]
    have h := H.extend_shear F hz hb hV hG hV' (hgerm q hq)
    change f G (Φ (g q))=0 at h
    rwa [hi] at h
  refine ⟨V,G,hV,hpV,hG,⟨fun q hq v ↦ hres (Represented.quartic _ v) (fun x hx ↦ S.equations.quartic hx v) q hq,
    fun q hq v ↦ hres (Represented.sixth _ v) (fun x hx ↦ S.equations.sixth hx v) q hq⟩,?_⟩
  simpa only [hgp] using hgerm (Φ y) hpV

theorem rescaled_chart {p : E} (R : ShearInverse S.axis S.domain p) {q : ℝ × E} (hq : q ∈ R.domain) (hn : q.1≠0) :
    ∃ (V : Set E) (G : E → Cubic d), IsOpen V ∧ position S q.1⁻¹ p+q.1 • q.2 ∈ V ∧ ContDiffOn ℝ ∞ G V ∧
      MidpointJetEquations V G ∧ (fun z ↦ S.field (R.inverse (q.1,z))) =ᶠ[𝓝 q.2] (fun z ↦ G (position S q.1⁻¹ p+q.1 • z)) := by
  let b := position S q.1⁻¹ p
  have hpos (z : E) (hz : (q.1,z) ∈ R.domain) : position S q.1⁻¹ (R.inverse (q.1,z))=b+q.1 • z := by
    have h := congrArg (fun v : E ↦ q.1⁻¹ • v) (R.physical (q.1,z) hz)
    simp only [smul_add,smul_smul,inv_mul_cancel₀ hn,one_smul,sq,← mul_assoc] at h
    simpa only [one_mul,b,position] using h
  obtain ⟨V,G,hV,hpV,hG,hQ,he⟩ := H.physical_chart (R.maps hq) q.1⁻¹
  refine ⟨V,G,hV,(hpos q.2 hq) ▸ hpV,hG,hQ,?_⟩
  have hi : ContinuousAt (fun z : E ↦ (q.1,z)) q.2 := continuousAt_const.prodMk continuousAt_id
  have hs := (R.smooth.contDiffAt (R.isOpen.mem_nhds hq)).continuousAt
  have hi' := ContinuousAt.comp (f := fun z : E ↦ (q.1,z)) (x := q.2) hs hi
  have hv : ∀ᶠ z in 𝓝 q.2, (q.1,z) ∈ R.domain := hi (R.isOpen.mem_nhds hq)
  filter_upwards [hi'.tendsto.eventually he,hv] with z H' hz
  exact H'.trans (congrArg G (hpos z hz))

end EuclideanMidpointRigidity.HorizontalPatch

