module

public import EuclideanMidpointRigidity.RegularRulingCharts
public import EuclideanMidpointRigidity.RegularLineBounds

/-! # Constancy of the full cubic tensor along selected maximizing rulings -/

public section
noncomputable section
open Set Filter Metric Polynomial
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.LiftedSection
variable {d : ℕ}
local notation "E" => Space d

theorem RulingStrip.constant_line {S : LiftedSection d} {U : Set E} {r : ℝ} (R : RulingStrip S U r)
    (hm : ∀ q ∈ S.domain, S.Maximizes q) (hc : ∀ q ∈ S.domain, Nonempty (OrientedEndpointChart S.field q))
    {p : E} (hp : p ∈ U) : ∀ s t, S.continuedField p s=S.continuedField p t := by
  obtain ⟨P,hP,hdet⟩ := JacobianPencil.determinant_polynomial S.axialDirection p
  have hn : P≠0 := by intro h; simp [h] at hP
  apply S.continued_constant_of_regular_maximum (R.inside hp) hm hc hn
  intro x hx
  have hd : S.lineChart.determinant p x≠0 := by
    change JacobianPencil.determinant S.axialDirection p x≠0
    rw [← hdet x]
    exact hx
  let u := S.axialDirection p
  have hd₀ : Tendsto (fun h : ℝ ↦ p+h • u) (𝓝 0) (𝓝 p) := by
    change Tendsto (displacementLine p u) (𝓝 0) (𝓝 p)
    simpa only [displacementLine_zero] using (hasDerivAt_displacementLine p u).continuousAt.tendsto
  have h₀ : ∀ᶠ h in 𝓝 (0:ℝ), amplitude (S.continuedField p (h+x))=amplitude (S.continuedField p x) := by
    filter_upwards [R.translate hm hp,hd₀.eventually (R.regular_amplitude hp hd)] with h ht he
    rw [← ht.2 x]
    exact he
  have hs : Tendsto (fun s : ℝ ↦ s-x) (𝓝 x) (𝓝 0) := by
    have hs' : Continuous (fun s : ℝ ↦ s-x) := continuous_id.sub continuous_const
    simpa only [sub_self] using hs'.continuousAt.tendsto (x := x)
  exact (hs.eventually h₀).mono (fun s h ↦ by simpa only [sub_add_cancel] using h)

theorem RulingStrip.stationary_axis {S : LiftedSection d} {U : Set E} {r : ℝ} (R : RulingStrip S U r)
    (hm : ∀ q ∈ S.domain, S.Maximizes q) (hc : ∀ q ∈ S.domain, Nonempty (OrientedEndpointChart S.field q))
    {p : E} (hp : p ∈ U) : fderiv ℝ S.field p (S.axis p)=0 := by
  have hh := R.constant_line hm hc hp
  have hg := S.continuedField_germ (R.inside hp) hm hc
  have he : S.field ∘ displacementLine p (S.axialDirection p) =ᶠ[𝓝 (0:ℝ)] (fun _ ↦ S.continuedField p 0) :=
    hg.mono fun t ht ↦ ht.symm.trans (hh t 0)
  have hd := differentiableAlongLine ((S.smooth.contDiffAt (S.isOpen.mem_nhds (R.inside hp))).differentiableAt (by simp)) (S.axialDirection p)
  have hz := hd.unique ((hasDerivAt_const 0 (S.continuedField p 0)).congr_of_eventuallyEq he)
  change fderiv ℝ S.field p ((S.a p)⁻¹ • S.axis p)=0 at hz
  rw [map_smul] at hz
  exact (smul_eq_zero.mp hz).resolve_left (inv_ne_zero (S.positive _ (R.inside hp)).ne')

theorem stationary_field_along_axis (S : LiftedSection d) (hm : ∀ q ∈ S.domain, S.Maximizes q)
    (hc : ∀ q ∈ S.domain, Nonempty (OrientedEndpointChart S.field q)) {p : E} (hp : p ∈ S.domain) :
    fderiv ℝ S.field p (S.axis p)=0 := by
  let D := fun q ↦ fderiv ℝ S.field q (S.axis q)
  have hd : ContinuousOn D S.domain := (S.smooth.continuousOn_fderiv_of_isOpen S.isOpen (by simp)).clm_apply S.smoothAxis.continuousOn
  by_contra hn
  let V := S.domain ∩ D ⁻¹' ({0} : Set (Cubic d))ᶜ
  have hV : IsOpen V := hd.isOpen_inter_preimage S.isOpen isClosed_singleton.isOpen_compl
  obtain ⟨U,r,⟨q,hq⟩,hUV,R⟩ := S.exists_ruling_strip hV ⟨p,hp,hn⟩ inter_subset_left hm hc
  exact (hUV hq).2 (R.stationary_axis hm hc hq)

end EuclideanMidpointRigidity.LiftedSection

