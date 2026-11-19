module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Tactic

/-! # Continuous envelopes with stationary lower supports -/

public section

open Set Filter Metric
open scoped Topology

namespace EuclideanMidpointRigidity

/-- A continuous function on a segment cannot decrease if each point before
the right endpoint has a differentiable lower support of zero slope. -/
theorem left_le_right_of_stationary_support {F : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hF : ContinuousOn F (Icc a b))
    (htouch : ∀ x ∈ Ico a b, ∃ g : ℝ → ℝ, HasDerivAt g 0 x ∧ g x = F x ∧
      ∀ y ∈ Icc a b, g y ≤ F y) : F a ≤ F b := by
  have h := image_le_of_liminf_slope_right_le_deriv_boundary
    (f := fun x ↦ -F x) (B := fun _ ↦ -F a) (B' := fun _ ↦ (0 : ℝ))
    hF.neg (le_refl _) continuousOn_const
    (fun x _ ↦ (hasDerivAt_const x _).hasDerivWithinAt) ?_
    (x := b) ⟨hab, le_refl b⟩
  · exact neg_le_neg_iff.mp h
  intro x hx r hr
  obtain ⟨g, hg, hgf, hle⟩ := htouch x hx
  have hn : HasDerivWithinAt (fun x ↦ -g x) 0 (Ioi x) x := by
    convert! hg.neg.hasDerivWithinAt (s := Ioi x) using 1
    simp
  apply Filter.Eventually.frequently
  filter_upwards [hn.limsup_slope_le' (lt_irrefl x) hr,
    self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hx.2)] with y hsl hxy hyb
  apply lt_of_le_of_lt _ hsl
  rw [slope_def_field, slope_def_field]
  exact div_le_div_of_nonneg_right (by rw [hgf]; linarith [hle y ⟨hx.1.trans hxy.le, hyb.le⟩])
    (sub_nonneg.mpr hxy.le)

/-- A spatial envelope is constant if at each point some smooth lower profile
touches it there and has zero derivative. Profiles can differ from point to point. -/
theorem constant_of_stationary_supports {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : V → ℝ} {Ω : Set V} (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hF : ContinuousOn F Ω)
    (htouch : ∀ x ∈ Ω, ∃ g : V → ℝ, HasFDerivAt g (0 : V →L[ℝ] ℝ) x ∧ g x = F x ∧
      ∀ y ∈ Ω, g y ≤ F y) : ∃ a : ℝ, ∀ x ∈ Ω, F x = a := by
  have along {S : Set V} (hS : Convex ℝ S) (hsub : S ⊆ Ω) {p q : V}
      (hp : p ∈ S) (hq : q ∈ S) : F p ≤ F q := by
    let z := fun t : ℝ ↦ p + t • (q-p)
    have hz (t : ℝ) : HasDerivAt z (q-p) t := by
      simpa [z] using ((hasDerivAt_id t).smul_const (q-p)).const_add p
    have hmem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : z t ∈ Ω := by
      apply hsub
      rw [show z t = (1-t) • p + t • q by dsimp [z]; module]
      exact hS hp hq (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
    have hcont : ContinuousOn (F ∘ z) (Icc 0 1) :=
      hF.comp (fun t _ ↦ (hz t).continuousAt.continuousWithinAt) (fun _ ht ↦ hmem ht)
    have h := left_le_right_of_stationary_support zero_le_one hcont ?_
    · simpa [z] using h
    intro t ht
    obtain ⟨g, hg, heq, hle⟩ := htouch (z t) (hmem ⟨ht.1, ht.2.le⟩)
    refine ⟨g ∘ z, ?_, heq, fun s hs ↦ hle _ (hmem hs)⟩
    simpa using hg.comp_hasDerivAt t (hz t)
  have hder (x : V) (hx : x ∈ Ω) : HasFDerivAt F (0 : V →L[ℝ] ℝ) x := by
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ x hx
    apply (hasFDerivAt_const (F x) x).congr_of_eventuallyEq
    filter_upwards [ball_mem_nhds x hr] with y hy
    exact le_antisymm (along (convex_ball x r) hball hy (mem_ball_self hr))
      (along (convex_ball x r) hball (mem_ball_self hr) hy)
  exact hΩ.exists_is_const_of_fderiv_eq_zero hconn
    (fun x hx ↦ (hder x hx).differentiableAt.differentiableWithinAt)
    (fun x hx ↦ (hder x hx).fderiv)

end EuclideanMidpointRigidity
