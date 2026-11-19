module

public import EuclideanMidpointRigidity.CriticalSection

/-! # Differentiating a persistent axial eigenvalue -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

theorem obstruction_smul_coeff (s : ℝ) (c : Coeff) (J : E →L[ℝ] Coeff) (w : E) :
    obstruction (s • c) J w=s • obstruction c J w := by
  simp only [obstruction,K_smul_coeff,map_smul,K_smul_right]
  module

theorem eigen_section_derivative {Ω : Set E} {C : E → Coeff} {e f : E → E} (hΩ : IsOpen Ω)
    (hC : ContDiffOn ℝ ∞ C Ω) (he : ContDiffOn ℝ ∞ e Ω) {p : E} (hp : p ∈ Ω)
    (hf : DifferentiableAt ℝ f p) {b : ℝ}
    (heig : ∀ᶠ q in 𝓝 p, K (C q) (e q) (f q)=(b*sectionValue C e q) • f q) (l : E) :
    K (fderiv ℝ C p l) (e p) (f p)+K (C p) (fderiv ℝ e p l) (f p)+
      K (C p) (e p) (fderiv ℝ f p l)=
      (b*sectionValue C e p) • fderiv ℝ f p l+(b*fderiv ℝ (sectionValue C e) p l) • f p := by
  let line := fun t : ℝ ↦ p+t • l
  have h₀ : line 0=p := by simp [line]
  have hd : HasDerivAt line l 0 := by
    simpa [line] using ((hasDerivAt_id (0:ℝ)).smul_const l).const_add p
  have dC := ((hC.contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
    0 hd h₀.symm
  have de := ((he.contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
    0 hd h₀.symm
  have df := hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hd h₀.symm
  have dA := (((contDiffOn_sectionValue hC he).contDiffAt (hΩ.mem_nhds hp)).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hd h₀.symm
  have dl := hasDerivAt_K dC de df
  have dr := (dA.const_mul b).smul df
  have hn : ∀ᶠ t in 𝓝 (0:ℝ), K (C (line t)) (e (line t)) (f (line t))=
      (b*sectionValue C e (line t)) • f (line t) :=
    hd.continuousAt (h₀ ▸ heig)
  simpa only [Function.comp_apply,h₀] using dl.unique (dr.congr_of_eventuallyEq hn)

/-- Pairing with the eigenvector cancels its derivative even at a multiple eigenvalue. -/
theorem eigen_section_tangent {Ω : Set E} {C : E → Coeff} {e f : E → E} (hΩ : IsOpen Ω)
    (hC : ContDiffOn ℝ ∞ C Ω) (he : ContDiffOn ℝ ∞ e Ω) (hm : QuarticOn Ω C)
    (hunit : ∀ q ∈ Ω, ‖e q‖=1) {p : E} (hp : p ∈ Ω)
    (hc : K (C p) (e p) (e p)=sectionValue C e p • e p) (ha : sectionValue C e p≠0)
    (hf : DifferentiableAt ℝ f p) {b : ℝ}
    (heig : ∀ᶠ q in 𝓝 p, K (C q) (e q) (f q)=(b*sectionValue C e q) • f q) :
    ⟪K (fderiv ℝ C p (e p)) (e p) (f p),f p⟫_ℝ =
      -⟪K (C p) (fderiv ℝ e p (e p)) (f p),f p⟫_ℝ := by
  have hv := eigen_section_derivative hΩ hC he hp hf heig (e p)
  rw [critical_section_value_along_axis hΩ hC he hm hunit hp ha hc] at hv
  have h := congrArg (fun w : E ↦ ⟪w,f p⟫_ℝ) hv
  simp only [mul_zero,zero_smul,add_zero,inner_add_left,
    real_inner_smul_left,K_selfAdjoint (C p) (e p) (fderiv ℝ f p (e p)) (f p),
    heig.self_of_nhds,real_inner_smul_right] at h
  linarith only [h]

end EuclideanMidpointRigidity
