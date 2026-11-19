module

public import EuclideanMidpointRigidity.ContinuedRulings
public import EuclideanMidpointRigidity.UniformLineGerm

/-! # A common strip of agreement and translation along a continued ruling -/

@[expose] public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.LiftedSection
variable {d : ℕ}
local notation "E" => Space d

structure RulingStrip (S : LiftedSection d) (U : Set E) (r : ℝ) : Prop where
  isOpen : IsOpen U
  inside : U ⊆ S.domain
  positive : 0<r
  maps : ∀ y ∈ U, ∀ s ∈ ball (0:ℝ) r, y+s • S.axialDirection y ∈ S.domain
  agrees : ∀ y ∈ U, ∀ s ∈ ball (0:ℝ) r, S.continuedField y s=S.field (y+s • S.axialDirection y)

theorem exists_ruling_strip (S : LiftedSection d) {U : Set E} (hU : IsOpen U) (hn : U.Nonempty) (hUS : U ⊆ S.domain)
    (hm : ∀ q ∈ S.domain, S.Maximizes q) (hc : ∀ q ∈ S.domain, Nonempty (OrientedEndpointChart S.field q)) :
    ∃ V r, V.Nonempty ∧ V ⊆ U ∧ RulingStrip S V r := by
  obtain ⟨p,hp⟩ := hn
  let L := fun q : E × ℝ ↦ q.1+q.2 • S.axialDirection q.1
  have hdir : ContinuousAt S.axialDirection p := (S.smooth_axialDirection.contDiffAt (S.isOpen.mem_nhds (hUS hp))).continuousAt
  have hu : ContinuousAt (fun q : E × ℝ ↦ S.axialDirection q.1) (p,0) := by
    change ContinuousAt (S.axialDirection ∘ (Prod.fst : E × ℝ → E)) (p,(0:ℝ))
    exact ContinuousAt.comp (g := S.axialDirection) (f := Prod.fst) (x := (p,(0:ℝ))) hdir continuousAt_fst
  have hL : ContinuousAt L (p,0) := continuousAt_fst.add (continuousAt_snd.smul hu)
  have hb : L ⁻¹' S.domain ∈ 𝓝 (p,(0:ℝ)) := hL (S.isOpen.mem_nhds (by simpa only [L,zero_smul,add_zero] using hUS hp))
  obtain ⟨M,hM,N,hN,hMN⟩ := mem_nhds_prod_iff.mp hb
  obtain ⟨W,hWM,hW,hpW⟩ := _root_.mem_nhds_iff.mp (inter_mem hM (hU.mem_nhds hp))
  obtain ⟨δ,hδ,hδN⟩ := Metric.mem_nhds_iff.mp hN
  have hWU : W ⊆ U := fun _ hw ↦ (hWM hw).2
  have maps (s : ℝ) (hs : s ∈ ball (0:ℝ) δ) (y : E) (hy : y ∈ W) :
      y+s • S.axialDirection y ∈ S.domain := hMN (show (y,s) ∈ M ×ˢ N from ⟨(hWM hy).1,hδN hs⟩)
  have hf (s : ℝ) : ContinuousOn (fun y ↦ S.continuedField y s) W := (S.continuedFamily.smooth_space s).continuousOn.mono (hWU.trans hUS)
  have hg (s : ℝ) (hs : s ∈ ball (0:ℝ) δ) : ContinuousOn (fun y ↦ S.field (y+s • S.axialDirection y)) W :=
    S.smooth.continuousOn.comp (continuousOn_id.add ((continuousOn_const (c := s)).smul (S.smooth_axialDirection.continuousOn.mono (hWU.trans hUS)))) (maps s hs)
  obtain ⟨V,r,hV,hnV,hVW,hr,hrδ,he⟩ := uniform_line_germ_subpatch hW ⟨p,hpW⟩ hδ _ _
    (fun s _ ↦ hf s) hg (fun y hy ↦ S.continuedField_germ (hUS (hWU hy)) hm hc)
  exact ⟨V,r,hnV,hVW.trans hWU,⟨hV,(hVW.trans hWU).trans hUS,hr,
    fun y hy s hs ↦ maps s (ball_subset_ball hrδ hs) y (hVW hy),he⟩⟩

theorem RulingStrip.translate {S : LiftedSection d} {U : Set (Space d)} {r : ℝ} (R : RulingStrip S U r)
    (hm : ∀ q ∈ S.domain, S.Maximizes q) {p : Space d} (hp : p ∈ U) :
    ∀ᶠ h in 𝓝 (0:ℝ), p+h • S.axialDirection p ∈ U ∧ ∀ t : ℝ,
      S.continuedField (p+h • S.axialDirection p) t=S.continuedField p (h+t) := by
  let u := S.axialDirection p
  obtain ⟨W,hW,h₀,hdata⟩ := S.local_normalized_line (R.inside hp) hm
  have hline : Continuous (fun h : ℝ ↦ p+h • u) := continuous_const.add (continuous_id.smul continuous_const)
  have near : ∀ᶠ h in 𝓝 (0:ℝ), p+h • u ∈ U := hline.continuousAt (R.isOpen.mem_nhds (by simpa using hp : p+(0:ℝ) • u ∈ U))
  filter_upwards [hW.mem_nhds h₀,ball_mem_nhds (0:ℝ) R.positive,near] with h hw hsmall hU
  refine ⟨hU,?_⟩
  let q := p+h • u
  have hu : S.axialDirection q=u := (hdata h hw).2.1
  have hs : ∀ᶠ s in 𝓝 (0:ℝ), h+s ∈ ball (0:ℝ) r :=
    (continuous_const.add continuous_id).continuousAt (isOpen_ball.mem_nhds (by simpa using hsmall : h+0 ∈ ball (0:ℝ) r))
  have he : S.continuedField q=ᶠ[𝓝 (0:ℝ)] (fun s ↦ S.continuedField p (h+s)) := by
    filter_upwards [hs,ball_mem_nhds (0:ℝ) R.positive] with s h₁ h₂
    rw [R.agrees q hU s h₂,R.agrees p hp (h+s) h₁,hu,add_smul]
    simp only [q,u,add_assoc]
  have e := (S.continuedFamily.analytic_time (R.inside hU)).analyticOnNhd.eq_of_eventuallyEq
    ((S.continuedFamily.analytic_time (R.inside hp)).comp (contDiff_const.add contDiff_id)).analyticOnNhd he
  exact fun t ↦ congrFun e t

end EuclideanMidpointRigidity.LiftedSection

