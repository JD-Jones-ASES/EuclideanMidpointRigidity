module

public import EuclideanMidpointRigidity.GeometricObstruction
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Spatial differentiation of the quartic equation -/

@[expose] public section
noncomputable section
open Set Filter
open scoped InnerProductSpace Topology
namespace EuclideanMidpointRigidity

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

private theorem K_zero_left' (c : Coeff) (h : E) : K c 0 h = 0 := by simp [K]
private theorem K_zero_right' (c : Coeff) (h : E) : K c h 0 = 0 := by simp [K]

theorem hasDerivAt_obstruction {c : ℝ → Coeff} {j : ℝ → E →L[ℝ] Coeff}
    {c' : Coeff} {j' : E →L[ℝ] Coeff} {t : ℝ}
    (hc : HasDerivAt c c' t) (hj : HasDerivAt j j' t) (h : E) :
    HasDerivAt (fun s ↦ obstruction (c s) (j s) h)
      (obstruction (c t) j' h + obstruction c' (j t) h) t := by
  have hh := hasDerivAt_const t h
  have hjh : HasDerivAt (fun s ↦ j s h) (j' h) t := by simpa using hj.clm_apply hh
  have hq : HasDerivAt (fun s ↦ K (c s) h h) (K c' h h) t := by
    simpa only [K_zero_left', K_zero_right', add_zero] using hasDerivAt_K hc hh hh
  have hu : HasDerivAt (fun s ↦ K (j s h) h h) (K (j' h) h h) t := by
    simpa only [K_zero_left', K_zero_right', add_zero] using hasDerivAt_K hjh hh hh
  have h₁ := (hasDerivAt_K hc hh hu).const_smul (2:ℝ)
  have h₂ := (hasDerivAt_K (hj.clm_apply hq) hh hh).const_smul (5:ℝ)
  have h₃ := (hasDerivAt_K hjh hh hq).const_smul (4:ℝ)
  have hv := (h₁.add h₂).sub h₃
  simp only [obstruction, ← Nat.cast_smul_eq_nsmul ℝ]
  convert! hv using 1
  simp only [K_zero_left', K_zero_right', K_add_coeff, add_zero]
  push_cast
  module

/-- Differentiating at an interior point yields the genuine second spatial
jet in the prolongation. The direction of differentiation is independent of
the quartic test vector. -/
theorem prolongation_of_quartic {Ω : Set E} {C : E → Coeff}
    (hΩ : IsOpen Ω) (smooth : ContDiffOn ℝ 2 C Ω) (hm : QuarticOn Ω C)
    {p : E} (hp : p ∈ Ω) (l h : E) :
    obstruction (C p) ((fderiv ℝ (fderiv ℝ C) p) l) h +
      obstruction ((fderiv ℝ C p) l) (fderiv ℝ C p) h = 0 := by
  let line := fun s : ℝ ↦ p+s • l
  have hline : HasDerivAt line l 0 := by
    simpa [line] using ((hasDerivAt_id (0:ℝ)).smul_const l).const_add p
  have h₀ : line 0 = p := by simp [line]
  have hC := smooth.contDiffAt (hΩ.mem_nhds hp)
  have hJ : ContDiffAt ℝ 1 (fderiv ℝ C) p := hC.fderiv_right (by norm_num)
  have hc := (hC.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq
    0 hline h₀.symm
  have hj := (hJ.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq
    0 hline h₀.symm
  have hd := hasDerivAt_obstruction hc hj h
  have hnear : ∀ᶠ s in 𝓝 (0:ℝ), line s ∈ Ω :=
    hline.continuousAt (h₀ ▸ hΩ.mem_nhds hp)
  have hz : HasDerivAt (fun s ↦ obstruction (C (line s)) (fderiv ℝ C (line s)) h) 0 0 :=
    (hasDerivAt_const 0 (0:E)).congr_of_eventuallyEq
      (hnear.mono fun s hs ↦ hm hs h)
  simpa only [Function.comp_apply, h₀] using hd.unique hz

theorem axial_second_derivative_of_quartic {Ω : Set E} {C : E → Coeff}
    (hΩ : IsOpen Ω) (smooth : ContDiffOn ℝ 2 C Ω) (hm : QuarticOn Ω C)
    {p : E} (hp : p ∈ Ω) {a : ℝ} (ha : a ≠ 0) {e : E} (he : K (C p) e e = a • e) :
    let j := fderiv ℝ C p
    let u := K (j e) e e
    7*a*⟪K ((fderiv ℝ (fderiv ℝ C) p) e e) e e,e⟫_ℝ = -17*⟪u,u⟫_ℝ :=
  critical_axis_second_derivative ha he (hm hp)
    (prolongation_of_quartic hΩ smooth hm hp e e)

theorem prolongation_of_localMidpointInvariance {Ω : Set E} {C : E → Coeff}
    (hΩ : IsOpen Ω) (smooth : ContDiffOn ℝ 2 C Ω) (hm : LocalMidpointInvariance Ω C)
    {p : E} (hp : p ∈ Ω) (l h : E) :
    obstruction (C p) ((fderiv ℝ (fderiv ℝ C) p) l) h +
      obstruction ((fderiv ℝ C p) l) (fderiv ℝ C p) h = 0 :=
  prolongation_of_quartic hΩ smooth (QuarticOn.of_midpoint hΩ smooth hm) hp l h

theorem axial_second_derivative_of_localMidpointInvariance {Ω : Set E} {C : E → Coeff}
    (hΩ : IsOpen Ω) (smooth : ContDiffOn ℝ 2 C Ω) (hm : LocalMidpointInvariance Ω C)
    {p : E} (hp : p ∈ Ω) {a : ℝ} (ha : a ≠ 0) {e : E} (he : K (C p) e e = a • e) :
    let j := fderiv ℝ C p
    let u := K (j e) e e
    7*a*⟪K ((fderiv ℝ (fderiv ℝ C) p) e e) e e,e⟫_ℝ = -17*⟪u,u⟫_ℝ :=
  axial_second_derivative_of_quartic hΩ smooth (QuarticOn.of_midpoint hΩ smooth hm) hp ha he

end EuclideanMidpointRigidity
