module

public import EuclideanMidpointRigidity.AxialCoefficientLaw
public import EuclideanMidpointRigidity.TiltedOddJet
public import EuclideanMidpointRigidity.ResponseLinearity

/-! # The differential equations forced by reflected scalar midpoint responses -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.Endpoint

def tiltRate (κ : ℝ) := 21*κ^2+42*κ+1

theorem tiltRate_pos {κ : ℝ} (hκ : 0≤κ) : 0<tiltRate κ := by unfold tiltRate; positivity

theorem oddTilt_rate_conditions {W : Set ℝ} {f : ℝ → ℝ} {η κ p : ℝ} (hW : IsOpen W)
    (hf : ContDiffOn ℝ ∞ f W) (hp : p ∈ W)
    (hv : ∀ᶠ h in 𝓝[>] (0:ℝ), VanishingResponse η h (oddTilt κ f p)) :
    (η-2*κ-2)*iteratedDeriv 1 f p=0 ∧
    (η=2*κ+2 → iteratedDeriv 3 f p=tiltRate κ*iteratedDeriv 1 f p) := by
  obtain ⟨h₄,h₆⟩ := vanishing_response_coefficients (oddTilt_coefficients hW hf hp κ) hv
  rw [fourth_eq] at h₄
  rw [sixth_eq] at h₆
  refine ⟨by linarith only [h₄],?_⟩
  rintro rfl
  unfold tiltRate
  linarith only [h₆]

theorem oddTilt_differential_equation {W : Set ℝ} {f : ℝ → ℝ} {η κ : ℝ} (hW : IsOpen W)
    (hf : ContDiffOn ℝ ∞ f W)
    (hv : ∀ p ∈ W, ∀ᶠ h in 𝓝[>] (0:ℝ), VanishingResponse η h (oddTilt κ f p)) :
    ∀ p ∈ W, iteratedDeriv 3 f p=tiltRate κ*iteratedDeriv 1 f p := by
  have hr (p : ℝ) (hp : p ∈ W) := oddTilt_rate_conditions hW hf hp (hv p hp)
  by_cases hη : η=2*κ+2
  · exact fun p hp ↦ (hr p hp).2 hη
  have hn : η-2*κ-2≠0 := fun hz ↦ hη (by linarith)
  have hd (q : ℝ) (hq : q ∈ W) : deriv f q=0 := by
    simpa only [iteratedDeriv_one] using (mul_eq_zero.mp (hr q hq).1).resolve_left hn
  intro p hp
  have he : deriv f =ᶠ[𝓝 p] (fun _ ↦ (0:ℝ)) := (show ∀ᶠ q in 𝓝 p, q ∈ W from hW.mem_nhds hp).mono (fun q hq ↦ hd q hq)
  change iteratedDeriv (2+1) f p=_
  rw [iteratedDeriv_succ',he.iteratedDeriv_eq 2,iteratedDeriv_one,hd p hp,mul_zero]
  simp

end EuclideanMidpointRigidity.Endpoint

