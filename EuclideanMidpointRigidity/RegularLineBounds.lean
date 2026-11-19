module

public import EuclideanMidpointRigidity.ContinuedEquation
public import EuclideanMidpointRigidity.MaximumEnvelope
public import Mathlib.Algebra.Polynomial.Roots

/-! # Bounding a continued tensor from its maximum on regular line charts -/

public section
noncomputable section
open Set Filter Polynomial Metric
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity
open Endpoint

theorem bounded_of_locally_constant_off_roots {f : ℝ → ℝ} (hf : Continuous f) {P : ℝ[X]} (hP : P≠0)
    (h : ∀ x, ¬P.IsRoot x → f =ᶠ[𝓝 x] (fun _ ↦ f x)) : ∃ K, ∀ t, f t≤K := by
  have hc {W : Set ℝ} (hW : IsOpen W) (hw : IsPreconnected W) (hr : ∀ x ∈ W, ¬P.IsRoot x) :
      ∃ a, ∀ x ∈ W, f x=a := by
    have hd (x : ℝ) (hx : x ∈ W) : HasDerivAt f 0 x :=
      (hasDerivAt_const x (f x)).congr_of_eventuallyEq (h x (hr x hx))
    exact hW.exists_is_const_of_deriv_eq_zero hw (fun x hx ↦ (hd x hx).differentiableAt.differentiableWithinAt)
      (fun {x} hx ↦ (hd x hx).deriv)
  obtain ⟨a,ha⟩ := eventually_atBot.mp (eventually_atBot_not_isRoot hP)
  obtain ⟨b,hb⟩ := eventually_atTop.mp (eventually_atTop_not_isRoot hP)
  obtain ⟨u,hu⟩ := hc (W := Iio a) isOpen_Iio isPreconnected_Iio (fun x hx ↦ ha x hx.le)
  obtain ⟨v,hv⟩ := hc (W := Ioi b) isOpen_Ioi isPreconnected_Ioi (fun x hx ↦ hb x hx.le)
  obtain ⟨w,hw⟩ := ((isCompact_Icc (a := a) (b := b)).image hf).bddAbove
  refine ⟨max (max u v) w,fun t ↦ ?_⟩
  by_cases h₁ : t<a
  · rw [hu t h₁]; exact (le_max_left _ _).trans (le_max_left _ _)
  by_cases h₂ : b<t
  · rw [hv t h₂]; exact (le_max_right _ _).trans (le_max_left _ _)
  exact (hw (mem_image_of_mem f ⟨le_of_not_gt h₁,le_of_not_gt h₂⟩)).trans (le_max_right _ _)

theorem LiftedSection.continued_constant_of_regular_maximum {d : ℕ} (S : LiftedSection d) {p : Space d} (hp : p ∈ S.domain)
    (hm : ∀ q ∈ S.domain, S.Maximizes q) (hc : ∀ q ∈ S.domain, Nonempty (OrientedEndpointChart S.field q))
    {P : ℝ[X]} (hP : P≠0) (h : ∀ x, ¬P.IsRoot x → (fun t ↦ amplitude (S.continuedField p t)) =ᶠ[𝓝 x] (fun _ ↦ amplitude (S.continuedField p x))) :
    ∀ s t, S.continuedField p s=S.continuedField p t := by
  obtain ⟨K,hK⟩ := bounded_of_locally_constant_off_roots (continuous_amplitude.comp (S.continuedFamily.analytic_time hp).continuous) hP h
  have hbound (z : Space d) (hz : z ∈ closedBall 0 1) (t : ℝ) : |directionProfile z (S.continuedField p t)|≤K := by
    have hn : -z ∈ closedBall 0 1 := by simpa only [mem_closedBall,dist_zero_right,norm_neg] using hz
    have hl := (directionProfile_le_amplitude hn (S.continuedField p t)).trans (hK t)
    have hr := (directionProfile_le_amplitude hz (S.continuedField p t)).trans (hK t)
    have he (c : Cubic d) : directionProfile (-z) c= -directionProfile z c := by simp [directionProfile_apply,EuclideanMidpointRigidity.K]
    rw [he] at hl
    exact abs_le.mpr ⟨by linarith,hr⟩
  intro s t
  apply sub_eq_zero.mp
  apply (amplitude_eq_zero_iff _).mp
  obtain ⟨z,hz,he,_⟩ := exists_maximizing_direction (S.continuedField p s-S.continuedField p t)
  rw [he,map_sub,S.bounded_observation_constant hp hm hc (directionProfile z) (hbound z hz) s t,sub_self]

end EuclideanMidpointRigidity

