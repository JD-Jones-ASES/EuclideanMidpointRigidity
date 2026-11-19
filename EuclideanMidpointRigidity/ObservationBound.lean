module

public import EuclideanMidpointRigidity.ObservedChord

/-! # Bounding a reflected tilt by the defect of the fixed axial product -/

public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.OrientedEndpointChart
variable {d : ℕ} {Ω W : Set (Space d)} {C : Space d → Cubic d} {p u : Space d} {h : ℝ}
  {B : Space d →L[ℝ] Space d} (D : OrientedEndpointChart C p)
local notation "E" => Space d
local notation "P" => PhaseCurve d
set_option backward.isDefEq.respectTransparency false

theorem observation_bound (J : RealizedChord Ω C 1 p u h B D.plus) (N : RealizedChord Ω C (-1) p (-u) h B D.minus)
    (hd : chordEnds p u h ∈ D.domain)
    (hW : IsOpen W) (hc : Convex ℝ W) (hC : ContDiffOn ℝ ∞ C W) (hp : p ∈ W)
    (hi : ∀ t : UnitInterval, axialPosition p u h t ∈ W) (hn : ∀ t : UnitInterval, axialPosition p (-u) h t ∈ W)
    (hz : ∀ x ∈ W, fderiv ℝ C x u=0) (j : E × E) (hj : j.swap= -j) :
    ∃ L : ℝ, 0≤L ∧ ∀ᶠ v in 𝓝 (0:E),
      ‖D.observation u h J.positive j v (Horizontal.spatialSlice (fderiv ℝ C (p+v)) u)‖≤
      L*‖K (C (p+v)) u u-K (C p) u u‖ := by
  let q := chordEnds p u h
  let q' := chordEnds p (-u) h
  let mid := midpointEvaluation (d := d)
  have hneg (x : E) (hx : x ∈ W) : fderiv ℝ C x (-u)=0 := by simp [hz _ hx]
  obtain ⟨a,ha,hA⟩ := J.trial_comparison hW hc hC hp hi hz j
  obtain ⟨b,hb,hB⟩ := N.trial_comparison hW hc hC hp hn hneg j
  have hnear : ∀ᶠ v in 𝓝 (0:E), q+(v,v) ∈ D.domain :=
    (continuous_const.add (continuous_id.prodMk continuous_id)).continuousAt (D.isOpen.mem_nhds (by change q+(0 : E × E) ∈ D.domain; rwa [add_zero] : q+(0,0) ∈ D.domain))
  refine ⟨‖mid‖*(a+b),mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (add_nonneg ha hb),?_⟩
  filter_upwards [hA,hB,hnear,D.observation_difference J N hW hc hC hp hi hn hz j] with v eq₁ eq₂ hq hdiff
  let X := D.plus.shiftResponse q v j
  let Z := D.minus.shiftResponse q' v j
  let Y := D.plus.variation (q+(v,v)) j
  let V := D.minus.variation (q'+(v,v)) j
  let R := Horizontal.spatialSlice (fderiv ℝ C (p+v)) u
  let Q := K (C (p+v)) u u-K (C p) u u
  have hj' : j.2= -j.1 := congrArg Prod.fst hj
  have hv := D.variation_law hq j
  rw [hj,hj',add_neg_cancel] at hv
  have he : (q+(v,v)).swap=q'+(v,v) := by change q.swap+(v,v)=_; rw [chordEnds_swap]
  rw [he] at hv
  change mid Y+mid (fderiv ℝ D.minus.phase (q'+(v,v)) (-j))=0 at hv
  rw [map_neg,map_neg,← sub_eq_add_neg,sub_eq_zero] at hv
  change mid Y=mid V at hv
  have hmid : mid (Z-X)=mid ((Z-V)-(X-Y)) := by
    simp only [map_sub,hv]; abel
  have hb' : ‖Z-V‖≤b*‖Q‖ := by simpa only [K_neg_left,K_neg_right,neg_neg] using eq₂
  have ha' : ‖X-Y‖≤a*‖Q‖ := eq₁
  change (2:ℝ) • D.observation u h J.positive j v R=mid (Z-X) at hdiff
  have hh := congrArg norm (hdiff.trans hmid)
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
  have hbound := mid.le_opNorm ((Z-V)-(X-Y))
  have hs := (norm_sub_le _ _).trans (add_le_add hb' ha')
  have hfinal := hbound.trans (mul_le_mul_of_nonneg_left hs (ContinuousLinearMap.opNorm_nonneg mid))
  change ‖D.observation u h J.positive j v R‖≤‖mid‖*(a+b)*‖Q‖
  linarith only [hh,hfinal,norm_nonneg (D.observation u h J.positive j v R)]

end EuclideanMidpointRigidity.OrientedEndpointChart

