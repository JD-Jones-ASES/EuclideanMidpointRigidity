module

public import EuclideanMidpointRigidity.CriticalSection
public import EuclideanMidpointRigidity.CubicNorm
public import EuclideanMidpointRigidity.Envelope
public import Mathlib.Topology.Maps.Proper.Basic

/-! # The maximum of a cubic and its stationary supporting directions -/

@[expose] public section
noncomputable section
open Set Filter Metric
open scoped ContDiff InnerProductSpace Topology
namespace EuclideanMidpointRigidity

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

/-- Evaluation on three equal vectors, as a functional on cubic tensors. -/
def directionProfile (z : E) : Coeff →L[ℝ] ℝ :=
  (innerSL ℝ z).comp (((ContinuousLinearMap.apply ℝ E z).comp
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] E) z)).comp (cubicSubspace d).subtypeL)

theorem directionProfile_apply (z : E) (c : Coeff) :
    directionProfile z c = ⟪K c z z,z⟫_ℝ := by
  change ⟪z,K c z z⟫_ℝ = _
  exact real_inner_comm _ _

set_option backward.isDefEq.respectTransparency false in
theorem continuous_directionProfile :
    Continuous (fun p : Coeff × E ↦ directionProfile p.2 p.1) := by
  let inc : Coeff →L[ℝ] (E →L[ℝ] E →L[ℝ] E) := (cubicSubspace d).subtypeL
  have h : Continuous (fun p : Coeff × E ↦ inc p.1) := inc.continuous.comp continuous_fst
  simp only [directionProfile_apply]
  exact ((h.clm_apply continuous_snd).clm_apply continuous_snd).inner continuous_snd

/-- The unit ball includes the zero-dimensional space and attains the same
positive maximum as the unit sphere by cubic homogeneity. -/
def amplitude (c : Coeff) : ℝ :=
  sSup ((fun z : E ↦ directionProfile z c) '' closedBall 0 1)

theorem continuous_amplitude : Continuous (amplitude (d := d)) :=
  (isCompact_closedBall (0:E) 1).continuous_sSup continuous_directionProfile

theorem exists_maximizing_direction (c : Coeff) :
    ∃ z ∈ closedBall (0:E) 1, amplitude c=directionProfile z c ∧
      ∀ w ∈ closedBall (0:E) 1, directionProfile w c ≤ directionProfile z c := by
  apply (isCompact_closedBall (0:E) 1).exists_sSup_image_eq_and_ge
    ⟨0,mem_closedBall_self zero_le_one⟩
  exact (continuous_directionProfile.comp (Continuous.prodMk_right c)).continuousOn

theorem directionProfile_le_amplitude {z : E} (hz : z ∈ closedBall (0:E) 1) (c : Coeff) :
    directionProfile z c ≤ amplitude c := by
  obtain ⟨w,_,hw,hm⟩ := exists_maximizing_direction c
  rw [hw]
  exact hm z hz

theorem amplitude_nonneg (c : Coeff) : 0 ≤ amplitude c := by
  simpa [directionProfile_apply,K] using directionProfile_le_amplitude
    (z := (0:E)) (mem_closedBall_self zero_le_one) c

theorem amplitude_eq_zero_iff (c : Coeff) : amplitude c=0 ↔ c=0 := by
  constructor
  · intro ha
    have hub (z : E) (hz : ‖z‖=1) : ⟪K c z z,z⟫_ℝ ≤ 0 := by
      rw [← ha,← directionProfile_apply]
      exact directionProfile_le_amplitude (by simp [mem_closedBall,dist_zero_right,hz]) c
    have hz (z : E) : K c z z=0 := by
      apply norm_le_zero_iff.mp
      simpa using cubic_diagonal_norm_bound c 0 le_rfl hub z
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    have h := hz (u+v)
    simp only [K_add_left,K_add_right,hz u,hz v,K_symm c v u,zero_add,add_zero] at h
    change K c u v=0
    simpa using (show (2:ℝ) • K c u v=0 by simpa [two_smul] using h)
  · rintro rfl
    obtain ⟨z,_,he,_⟩ := exists_maximizing_direction (0:Coeff)
    simpa [directionProfile_apply,K] using he

theorem exists_unit_max_of_pos {c : Coeff} (ha : 0 < amplitude c) :
    ∃ e : E, ‖e‖=1 ∧ directionProfile e c=amplitude c := by
  obtain ⟨w,hw,he,_⟩ := exists_maximizing_direction c
  have hw₁ : ‖w‖ ≤ 1 := by simpa [mem_closedBall,dist_zero_right] using hw
  have hw₀ : w≠0 := by
    rintro rfl
    simp [directionProfile_apply,K] at he
    linarith
  let e := ‖w‖⁻¹ • w
  have hpos := norm_pos_iff.mpr hw₀
  have hen : ‖e‖=1 := by simp [e,norm_smul,hpos.ne']
  have hre : ‖w‖ • e=w := by simp [e,smul_smul,hpos.ne']
  have hsc : directionProfile w c=‖w‖^3 * directionProfile e c := by
    conv_lhs => rw [← hre,directionProfile_apply,K_smul_left,K_smul_right,real_inner_smul_left,
      real_inner_smul_left,real_inner_smul_right]
    rw [directionProfile_apply]
    ring
  have hle := directionProfile_le_amplitude (z := e) (by simp [mem_closedBall,dist_zero_right,hen]) c
  have hge : 1 ≤ ‖w‖^3 := by
    apply le_of_mul_le_mul_right (a := amplitude c) _ ha
    calc
      1*amplitude c = ‖w‖^3*directionProfile e c := by rw [one_mul,← hsc,← he]
      _ ≤ ‖w‖^3*amplitude c := mul_le_mul_of_nonneg_left hle (by positivity)
  have hone : ‖w‖=1 := by
    by_contra hn
    exact (not_lt_of_ge hge) (pow_lt_one₀ hpos.le (lt_of_le_of_ne hw₁ hn) (by decide))
  exact ⟨w,hone,he.symm⟩

theorem amplitude_eq_of_unit_max {c : Coeff} {z : E} (hz : ‖z‖=1) {a : ℝ} (ha : 0 ≤ a)
    (hm : ∀ w : E, ‖w‖=1 → ⟪K c w w,w⟫_ℝ ≤ a) (he : ⟪K c z z,z⟫_ℝ=a) :
    amplitude c=a := by
  obtain ⟨w,hw,hw',_⟩ := exists_maximizing_direction c
  have hw₁ : ‖w‖ ≤ 1 := by simpa [mem_closedBall,dist_zero_right] using hw
  have hnorm := cubic_diagonal_norm_bound c a ha hm w
  apply le_antisymm
  · rw [hw',directionProfile_apply]
    calc
      _ ≤ ‖K c w w‖ * ‖w‖ := real_inner_le_norm _ _
      _ ≤ (a * ‖w‖^2) * ‖w‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
      _ ≤ a := by
        have hpow : ‖w‖^3 ≤ 1 := pow_le_one₀ (norm_nonneg w) hw₁
        nlinarith only [mul_le_mul_of_nonneg_left hpow ha]
  · rw [← he,← directionProfile_apply]
    exact directionProfile_le_amplitude (by simp [mem_closedBall,dist_zero_right,hz]) c

/-- A maximizing direction whose fixed-vector profile has zero derivative
in every spatial direction. -/
def StationaryMaximum (C : E → Coeff) (p : E) : Prop :=
  ∃ z ∈ closedBall (0:E) 1, directionProfile z (C p)=amplitude (C p) ∧
    ∀ l : E, directionProfile z (fderiv ℝ C p l)=0

theorem stationaryMaximum_of_amplitude_zero {C : E → Coeff} {p : E} (ha : amplitude (C p)=0) :
    StationaryMaximum C p := by
  refine ⟨0,mem_closedBall_self zero_le_one,?_,?_⟩ <;> simp [ha,directionProfile_apply,K]

private theorem closed_exists_direction {X B I : Type*} [TopologicalSpace X] [TopologicalSpace B]
    [CompactSpace B] (f g : X × B → ℝ) (w : I → X × B → ℝ)
    (hf : Continuous f) (hg : Continuous g) (hw : ∀ l, Continuous (w l)) :
    IsClosed {x : X | ∃ z : B, f (x,z)=g (x,z) ∧ ∀ l, w l (x,z)=0} := by
  let active := {q : X × B | f q=g q}
  let still := ⋂ l : I, {q : X × B | w l q=0}
  have h₀ : IsClosed active := isClosed_eq hf hg
  have h₁ : IsClosed still := isClosed_iInter fun l ↦ isClosed_eq (hw l) continuous_const
  have heq : {x : X | ∃ z : B, f (x,z)=g (x,z) ∧ ∀ l, w l (x,z)=0} =
      Prod.fst '' (active ∩ still) := by
    ext x
    constructor
    · rintro ⟨z,hz,hs⟩
      exact ⟨(x,z),⟨hz,mem_iInter.mpr hs⟩,rfl⟩
    · rintro ⟨⟨x,z⟩,⟨hz,hs⟩,rfl⟩
      exact ⟨z,hz,mem_iInter.mp hs⟩
  rw [heq]
  exact isClosedMap_fst_of_compactSpace _ (h₀.inter h₁)

private theorem continuous_applied_profile {X : Type*} [TopologicalSpace X]
    {F : X → Coeff} {Z : X → E} (hf : Continuous F) (hz : Continuous Z) :
    Continuous (fun x ↦ directionProfile (Z x) (F x)) := by
  let u : Coeff × E → ℝ := fun p ↦ directionProfile p.2 p.1
  let v : X → Coeff × E := fun x ↦ (F x,Z x)
  have hu : Continuous u := continuous_directionProfile (d := d)
  have hv : Continuous v := hf.prodMk hz
  exact Continuous.comp (g := u) (f := v) hu hv

theorem isClosed_stationaryMaximum {Ω : Set E} {C : E → Coeff} (hΩ : IsOpen Ω)
    (hC : ContDiffOn ℝ ∞ C Ω) : IsClosed {p : Ω | StationaryMaximum C p} := by
  let B := closedBall (0:E) 1
  let _ : CompactSpace B := isCompact_iff_compactSpace.mp (isCompact_closedBall (0:E) 1)
  let f := fun q : Ω × B ↦ C (q.1 : E)
  let j := fun q : Ω × B ↦ fderiv ℝ C (q.1 : E)
  let z := fun q : Ω × B ↦ (q.2 : E)
  have hf : Continuous f := hC.continuousOn.domRestrict.comp continuous_fst
  have hz : Continuous z := continuous_subtype_val.comp continuous_snd
  have hj₀ : ContinuousOn (fderiv ℝ C) Ω := fun p hp ↦
    ((hC.contDiffAt (hΩ.mem_nhds hp)).fderiv_right (m := 0) (by simp)).continuousAt.continuousWithinAt
  have hj : Continuous j := hj₀.domRestrict.comp continuous_fst
  have hw (l : E) : Continuous (fun q : Ω × B ↦ directionProfile (z q) (j q l)) := by
    apply continuous_applied_profile (d := d) _ hz
    exact hj.clm_apply (continuous_const (y := l))
  have h := closed_exists_direction (fun q ↦ directionProfile (z q) (f q))
    (fun q ↦ amplitude (f q)) (fun l q ↦ directionProfile (z q) (j q l))
    (continuous_applied_profile (d := d) hf hz) ((continuous_amplitude (d := d)).comp hf) hw
  convert h using 1
  apply Set.ext
  intro p
  constructor
  · rintro ⟨v,hv,hm,hs⟩
    exact ⟨⟨v,hv⟩,hm,hs⟩
  · rintro ⟨v,hm,hs⟩
    exact ⟨v,v.property,hm,hs⟩

theorem amplitude_constant_of_dense_stationaryMaximum {Ω : Set E} {C : E → Coeff}
    (hΩ : IsOpen Ω) (hc : IsPreconnected Ω) (hC : ContDiffOn ℝ ∞ C Ω)
    (hd : Dense {p : Ω | StationaryMaximum C p}) :
    ∃ a : ℝ, ∀ p ∈ Ω, amplitude (C p)=a := by
  have hall := (isClosed_stationaryMaximum hΩ hC).closure_eq.symm.trans hd.closure_eq
  apply constant_of_stationary_supports hΩ hc (continuous_amplitude.comp_continuousOn hC.continuousOn)
  intro p hp
  obtain ⟨z,hz,he,hs⟩ : StationaryMaximum C p := by
    change (⟨p,hp⟩ : Ω) ∈ {q : Ω | StationaryMaximum C q}
    rw [hall]
    trivial
  refine ⟨fun q ↦ directionProfile z (C q),?_,he,fun q _ ↦ directionProfile_le_amplitude hz (C q)⟩
  have h := (directionProfile z).hasFDerivAt.comp p
    ((hC.contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have heq : (directionProfile z).comp (fderiv ℝ C p)=0 := ContinuousLinearMap.ext hs
  rwa [heq] at h

end EuclideanMidpointRigidity

