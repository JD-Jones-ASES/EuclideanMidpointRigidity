module

public import EuclideanMidpointRigidity.ExtremalCharacteristics
public import EuclideanMidpointRigidity.TransverseCoordinates
public import EuclideanMidpointRigidity.SpatialInverse

/-! # Straight neighboring characteristics from an arbitrary smooth maximizing graph -/

public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d
local notation "P" => AxisPhase d

private theorem forward_lines {Ω : Set E} {C : E → T} {e : E → E} {a : ℝ}
    (hΩ : IsOpen Ω) (hC : ContDiffOn ℝ ∞ C Ω) (hQ : QuarticOn Ω C) (he : ContDiffOn ℝ ∞ e Ω)
    (ha : a≠0) (hamp : ∀ q ∈ Ω, amplitude (C q)=|a|) (hu : ∀ q ∈ Ω, ‖e q‖=1)
    (hk : ∀ q ∈ Ω, K (C q) (e q) (e q)=a • e q) {p : E} (hp : p ∈ Ω) :
    ∃ (U : Set E) (r : ℝ), IsOpen U ∧ p ∈ U ∧ U ⊆ Ω ∧ 0<r ∧ ∀ y ∈ U, ∀ t ∈ Ico 0 r,
      y+t • e y ∈ Ω ∧ K (C (y+t • e y)) (e y) (e y)=a • e y := by
  let I := fun y : E ↦ ((y,e y),a)
  have hi : ContDiffOn ℝ ∞ I Ω := (contDiffOn_id.prodMk he).prodMk contDiffOn_const
  obtain ⟨B,F,hB,hpB,hF,hFB,h₀,hd⟩ := smooth_local_flow (isOpen_criticalPhaseDomain hΩ) (smooth_criticalPhaseVector hΩ hC)
    (show I p ∈ criticalPhaseDomain Ω from ⟨hp,ha⟩)
  let g := fun q : E × ℝ ↦ (I q.1,q.2)
  have hcI : ContinuousAt I p := hi.continuousOn.continuousAt (hΩ.mem_nhds hp)
  have hg : ContinuousAt g (p,0) := by
    change ContinuousAt (fun q : E × ℝ ↦ (I q.1,q.2)) (p,(0:ℝ))
    exact (ContinuousAt.comp (g := I) (f := Prod.fst) (x := (p,(0:ℝ))) hcI continuousAt_fst).prodMk continuousAt_snd
  obtain ⟨M,hM,N,hN,hmn⟩ := mem_nhds_prod_iff.mp (hg (hB.mem_nhds hpB))
  obtain ⟨U,hUM,hU,hpU⟩ := _root_.mem_nhds_iff.mp (inter_mem hM (hΩ.mem_nhds hp))
  obtain ⟨r,hr,hrN⟩ := Metric.mem_nhds_iff.mp hN
  refine ⟨U,r,hU,hpU,fun q h ↦ (hUM h).2,hr,?_⟩
  intro y hy t ht
  let γ := fun s ↦ F (I y,s)
  have hb (s : ℝ) (hs : s ∈ Icc 0 t) : (I y,s) ∈ B := by
    apply hmn (a := (y,s))
    exact ⟨(hUM hy).1,hrN (by simpa only [mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg hs.1] using hs.2.trans_lt ht.2)⟩
  exact extremal_phase_straight hΩ hC hQ ha hamp (hu y (hUM hy).2) (hk y (hUM hy).2) ht.1
    (γ := γ) (h₀ _ (hb 0 ⟨le_rfl,ht.1⟩)) (fun s hs ↦ hFB (hb s hs)) (fun s hs ↦ hd _ (hb s hs))

theorem maximizing_lines_on_strip {Ω : Set E} {C : E → T} {e : E → E} {a : ℝ}
    (hΩ : IsOpen Ω) (hC : ContDiffOn ℝ ∞ C Ω) (hQ : QuarticOn Ω C) (he : ContDiffOn ℝ ∞ e Ω)
    (ha : 0<a) (hamp : ∀ q ∈ Ω, amplitude (C q)=a) (hu : ∀ q ∈ Ω, ‖e q‖=1)
    (hk : ∀ q ∈ Ω, K (C q) (e q) (e q)=a • e q) {p : E} (hp : p ∈ Ω) :
    ∃ (U : Set E) (r : ℝ), IsOpen U ∧ p ∈ U ∧ U ⊆ Ω ∧ 0<r ∧ ∀ y ∈ U, ∀ t ∈ ball (0:ℝ) r,
      y+t • e y ∈ Ω ∧ K (C (y+t • e y)) (e y) (e y)=a • e y := by
  obtain ⟨U,r,hU,hpU,hUΩ,hr,h₁⟩ := forward_lines hΩ hC hQ he ha.ne' (fun q h ↦ (hamp q h).trans (abs_of_pos ha).symm) hu hk hp
  have hk' (q : E) (hq : q ∈ Ω) : K (C q) (-e q) (-e q)=(-a) • (-e q) := by simp [hk q hq]
  obtain ⟨V,s,hV,hpV,_,hs,h₂⟩ := forward_lines hΩ hC hQ (e := fun q ↦ -e q) he.neg (neg_ne_zero.mpr ha.ne')
    (fun q h ↦ by rw [abs_neg,abs_of_pos ha]; exact hamp q h) (fun q h ↦ by rw [norm_neg]; exact hu q h) hk' hp
  refine ⟨U ∩ V,min r s,hU.inter hV,⟨hpU,hpV⟩,fun _ h ↦ hUΩ h.1,lt_min hr hs,?_⟩
  intro y hy t ht
  have ht' : |t|<min r s := by simpa only [mem_ball,Real.dist_eq,sub_zero] using ht
  by_cases hn : 0≤t
  · exact h₁ y hy.1 t ⟨hn,(le_abs_self _).trans_lt (ht'.trans_le (min_le_left _ _))⟩
  · have hh := h₂ y hy.2 (-t) ⟨by linarith, (neg_le_abs _).trans_lt (ht'.trans_le (min_le_right _ _))⟩
    simpa only [neg_smul,smul_neg,neg_neg,K_neg_left,K_neg_right] using hh

end EuclideanMidpointRigidity

