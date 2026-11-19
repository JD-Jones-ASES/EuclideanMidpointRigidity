module

public import EuclideanMidpointRigidity.WeightedRulings
public import EuclideanMidpointRigidity.LocalFlow

/-! # The maximizing line and its constant axial slice -/

@[expose] public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d
local notation "Op" => E →L[ℝ] E

private theorem constant_on_time_ball {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {δ : ℝ} (hδ : 0<δ) (hd : ∀ t ∈ ball (0:ℝ) δ, HasDerivAt f 0 t)
    {t : ℝ} (ht : t ∈ ball (0:ℝ) δ) : f t=f 0 :=
  isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0:ℝ) δ).isPreconnected
    (fun s hs ↦ (hd s hs).differentiableAt.differentiableWithinAt) (fun s hs ↦ (hd s hs).deriv) ht (mem_ball_self hδ)

namespace LiftedSection
variable (S : LiftedSection d)

set_option backward.isDefEq.respectTransparency false in
theorem contDiffOn_axisSlice : ContDiffOn ℝ ∞ S.axisSlice S.domain := by
  let inc : Cubic d →L[ℝ] (E →L[ℝ] Op) := (cubicSubspace d).subtypeL
  have ha : ContDiffOn ℝ ∞ S.a S.domain := contDiffOn_sectionValue S.smooth S.smoothAxis
  have hc : ContDiffOn ℝ ∞ S.cubic S.domain := (ha.inv (fun x hx ↦ (S.positive x hx).ne')).smul S.smooth
  have hh := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) («E» := Cubic d) (F := E →L[ℝ] Op) inc
  have hinc : ContDiffOn ℝ ∞ (inc ∘ S.cubic) S.domain := ContDiff.comp_contDiffOn
    («E» := E) (F := Cubic d) (G := E →L[ℝ] Op) hh hc
  exact hinc.clm_apply S.smoothAxis

theorem axial_slice_derivative_zero {p : E} (hp : p ∈ S.domain) (hm : ∀ q ∈ S.domain, S.Maximizes q) :
    fderiv ℝ S.axisSlice p (S.axis p)=0 := by
  have d₁ := differentiableAlongLine ((S.contDiffOn_axisSlice.contDiffAt (S.isOpen.mem_nhds hp)).differentiableAt (by simp)) (S.axis p)
  exact (d₁.unique (S.hasDerivAt_axisSlice hp hm)).trans (S.weighted_ruling hp hm).2.2

/-- Uniformly over nearby initial points and signed times, the axis stays fixed on
its affine line. Its critical value and the full normalized axial slice stay fixed as well. -/
theorem local_straight_rulings {p : E} (hp : p ∈ S.domain) (hm : ∀ q ∈ S.domain, S.Maximizes q) :
    ∃ (U : Set E) (δ : ℝ), IsOpen U ∧ p ∈ U ∧ 0<δ ∧ ∀ y ∈ U, ∀ t ∈ ball (0:ℝ) δ,
      let z := displacementLine y (S.axis y) t
      z ∈ S.domain ∧ S.axis z=S.axis y ∧ S.axisSlice z=S.axisSlice y ∧ S.a z=S.a y := by
  obtain ⟨V,Φ,hV,hpV,_,hmap,h₀,hd⟩ := smooth_local_flow S.isOpen S.smoothAxis hp
  obtain ⟨M,hM,N,hN,hMN⟩ := mem_nhds_prod_iff.mp (hV.mem_nhds hpV)
  obtain ⟨U,hUM,hU,hpU⟩ := _root_.mem_nhds_iff.mp hM
  obtain ⟨δ,hδ,hδN⟩ := Metric.mem_nhds_iff.mp hN
  refine ⟨U,δ,hU,hpU,hδ,?_⟩
  intro y hy
  let x := fun t : ℝ ↦ Φ (y,t)
  have hq (t : ℝ) (ht : t ∈ ball (0:ℝ) δ) : (y,t) ∈ V := hMN ⟨hUM hy,hδN ht⟩
  have hx (t : ℝ) (ht : t ∈ ball (0:ℝ) δ) : x t ∈ S.domain := hmap (hq t ht)
  have dx (t : ℝ) (ht : t ∈ ball (0:ℝ) δ) : HasDerivAt x (S.axis (x t)) t := hd _ (hq t ht)
  have hx₀ : x 0=y := h₀ y (hq 0 (mem_ball_self hδ))
  have de (t : ℝ) (ht : t ∈ ball (0:ℝ) δ) : HasDerivAt (S.axis ∘ x) 0 t := by
    have h := ((S.smoothAxis.contDiffAt (S.isOpen.mem_nhds (hx t ht))).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (dx t ht)
    rwa [S.straight_axis (hx t ht) hm] at h
  have he (t : ℝ) (ht : t ∈ ball (0:ℝ) δ) : S.axis (x t)=S.axis y := by
    simpa only [Function.comp_apply,hx₀] using constant_on_time_ball hδ de ht
  have dline (t : ℝ) (ht : t ∈ ball (0:ℝ) δ) : HasDerivAt (fun s ↦ x s-s • S.axis y) 0 t := by
    have h := (dx t ht).fun_sub ((hasDerivAt_id t).smul_const (S.axis y))
    simpa only [he t ht,one_smul,sub_self,id_eq] using h
  have dB (t : ℝ) (ht : t ∈ ball (0:ℝ) δ) : HasDerivAt (S.axisSlice ∘ x) 0 t := by
    have h := ((S.contDiffOn_axisSlice.contDiffAt (S.isOpen.mem_nhds (hx t ht))).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (dx t ht)
    rwa [S.axial_slice_derivative_zero (hx t ht) hm] at h
  have ha : ContDiffOn ℝ ∞ S.a S.domain := contDiffOn_sectionValue S.smooth S.smoothAxis
  have da (t : ℝ) (ht : t ∈ ball (0:ℝ) δ) : HasDerivAt (S.a ∘ x) 0 t := by
    have h := ((ha.contDiffAt (S.isOpen.mem_nhds (hx t ht))).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (dx t ht)
    rwa [S.stationary_value (hx t ht) hm,zero_apply] at h
  intro t ht
  have h := constant_on_time_ball hδ dline ht
  simp only [hx₀,zero_smul,sub_zero] at h
  have hr : x t=displacementLine y (S.axis y) t := sub_eq_iff_eq_add.mp h
  dsimp only
  rw [← hr]
  exact ⟨hx t ht,he t ht,by simpa only [Function.comp_apply,hx₀] using constant_on_time_ball hδ dB ht,
    by simpa only [Function.comp_apply,hx₀] using constant_on_time_ball hδ da ht⟩

end LiftedSection
end EuclideanMidpointRigidity

