module

public import EuclideanMidpointRigidity.CriticalPhase
public import EuclideanMidpointRigidity.MaximumEnvelope
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! # Straight critical paths through any maximum or minimum of constant absolute value -/

public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d

theorem active_profile_stationary {Ω : Set E} {C : E → T} {a : ℝ} (hΩ : IsOpen Ω) (hC : ContDiffOn ℝ ∞ C Ω)
    (ha : ∀ q ∈ Ω, amplitude (C q)=a) {p z : E} (hp : p ∈ Ω) (hu : ‖z‖=1) (hz : directionProfile z (C p)=a) (l : E) :
    directionProfile z (fderiv ℝ C p l)=0 := by
  have hb : z ∈ closedBall 0 1 := by simp [mem_closedBall,dist_zero_right,hu]
  have hm : IsLocalMax (directionProfile z ∘ C) p := by
    filter_upwards [hΩ.mem_nhds hp] with q hq
    change directionProfile z (C q)≤directionProfile z (C p)
    rw [hz,← ha q hq]
    exact directionProfile_le_amplitude hb _
  have hd := ((hC.contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have he := hm.hasFDerivAt_eq_zero ((directionProfile z).hasFDerivAt.comp p hd)
  exact congrArg (fun L : E →L[ℝ] ℝ ↦ L l) he

theorem extremal_liftStep_zero {Ω : Set E} {C : E → T} {a : ℝ} (hΩ : IsOpen Ω) (hC : ContDiffOn ℝ ∞ C Ω)
    (hQ : QuarticOn Ω C) (ha : a≠0) (hamp : ∀ q ∈ Ω, amplitude (C q)=|a|) {p z : E}
    (hp : p ∈ Ω) (hu : ‖z‖=1) (hz : K (C p) z z=a • z) : liftStep a (fderiv ℝ C p) z=0 := by
  let J := fderiv ℝ C p
  let u := K (J z) z z
  have heval : directionProfile z (C p)=a := by rw [directionProfile_apply,hz,real_inner_smul_left,real_inner_self_eq_norm_sq,hu]; ring
  have hneg (c : T) : directionProfile (-z) c= -directionProfile z c := by simp [directionProfile_apply,K]
  have hj : directionProfile z (J u)=0 := by
    by_cases hpos : 0≤a
    · exact active_profile_stationary hΩ hC hamp hp hu (heval.trans (abs_of_nonneg hpos).symm) u
    · have he : directionProfile (-z) (C p)=|a| := by rw [hneg,heval,abs_of_neg (lt_of_not_ge hpos)]
      have H := active_profile_stationary hΩ hC hamp hp (by simpa only [norm_neg] using hu : ‖-z‖=1) he u
      rw [hneg,neg_eq_zero] at H
      exact H
  rw [directionProfile_apply] at hj
  have h := critical_axis_source ha hz (hQ hp)
  change 7*⟪K (J u) z z,z⟫_ℝ=13*⟪u,u⟫_ℝ at h
  rw [hj,real_inner_self_eq_norm_sq] at h
  have hzero : ‖u‖=0 := by nlinarith
  change (2*a)⁻¹ • u=0
  rw [norm_eq_zero.mp hzero,smul_zero]

theorem extremal_phase_straight {Ω : Set E} {C : E → T} {a : ℝ} (hΩ : IsOpen Ω) (hC : ContDiffOn ℝ ∞ C Ω)
    (hQ : QuarticOn Ω C) (ha : a≠0) (hamp : ∀ q ∈ Ω, amplitude (C q)=|a|) {p z : E}
    (hu : ‖z‖=1) (hz : K (C p) z z=a • z) {γ : ℝ → AxisPhase d} {t : ℝ} (ht : 0≤t)
    (hinit : γ 0=((p,z),a)) (hdom : MapsTo γ (Icc 0 t) (criticalPhaseDomain Ω))
    (hd : ∀ s ∈ Icc 0 t, HasDerivAt γ (criticalPhaseVector C (γ s)) s) :
    p+t • z ∈ Ω ∧ K (C (p+t • z)) z z=a • z := by
  have hi := critical_phase_invariants hΩ hC hQ hdom hd (by simpa only [hinit] using ha)
    (by simpa only [hinit] using hu) (by simpa only [hinit] using hz)
  simp only [hinit] at hi
  let e := fun s ↦ (γ s).1.2
  let x := fun s ↦ (γ s).1.1
  have de (s : ℝ) (hs : s ∈ Icc 0 t) : HasDerivAt e 0 s := by
    have h := hasDerivAt_second_projection (hasDerivAt_first_projection (hd s hs))
    change HasDerivAt e (liftStep (γ s).2 (fderiv ℝ C (x s)) (e s)) s at h
    rw [(hi s hs).1,extremal_liftStep_zero hΩ hC hQ ha hamp (hdom hs).1 (hi s hs).2.1 (hi s hs).2.2] at h
    exact h
  have ee : ∀ s ∈ Icc 0 t, e s=z := by
    have H := constant_of_has_deriv_right_zero (HasDerivAt.continuousOn de) (fun s hs ↦ (de s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    simpa only [e,hinit] using H
  have dx (s : ℝ) (hs : s ∈ Icc 0 t) : HasDerivAt (fun r ↦ x r-r • z) 0 s := by
    have h := (hasDerivAt_first_projection (hasDerivAt_first_projection (hd s hs)))
    change HasDerivAt x (e s) s at h
    rw [ee s hs] at h
    have h' := h.sub ((hasDerivAt_id s).smul_const z)
    change HasDerivAt (x-(fun r : ℝ ↦ r • z)) 0 s
    simpa only [id_eq,one_smul,sub_self] using h'
  have hh := constant_of_has_deriv_right_zero (HasDerivAt.continuousOn dx) (fun s hs ↦ (dx s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
  have ht' : t ∈ Icc 0 t := ⟨ht,le_rfl⟩
  have hdif : x t-t • z=p := by simpa only [x,hinit,zero_smul,sub_zero] using hh t ht'
  have heq : x t=p+t • z := sub_eq_iff_eq_add.mp hdif
  have hm : x t ∈ Ω := (hdom ht').1
  have hk : K (C (x t)) (e t) (e t)=a • e t := (hi t ht').2.2
  rw [heq] at hm
  exact ⟨hm,by simpa only [heq,ee t ht'] using hk⟩

end EuclideanMidpointRigidity

