module

public import EuclideanMidpointRigidity.LineTiltLaws
public import EuclideanMidpointRigidity.AxialRates

/-! # Scalar sources obtained by tilting individual pairs of endpoints -/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace EuclideanMidpointRigidity
open Endpoint
namespace ThirdTiltLaws

def singleSource (α h : ℝ) (Q P : ℝ → ℝ) (x s : ℝ) :=
  -tiltAmplitude α h s*(Q (x-s)+Q (x+s))+2*tiltSlope α s*(P (x-s)-P (x+s))

def SingleLaw (W : Set ℝ) (η α : ℝ) (Q P : ℝ → ℝ) : Prop :=
  ∀ x ∈ W, ∀ᶠ h in 𝓝[>] (0:ℝ), VanishingResponse η h (singleSource α h Q P x)

theorem translation {W : Set ℝ} {k n : ℝ} {A : ℝ → TiltData} (H : ThirdTiltLaws W k n A) (x : ℝ) (hx : x ∈ W) :
    ∀ᶠ h in 𝓝[>] (0:ℝ), VanishingResponse k h (oddTilt 0 (fun t ↦ (A t).q) x) := by
  filter_upwards [H x hx] with h hh
  apply ((hh false false false).smul (-1)).congr
  intro s _
  simp [TiltData.test,TiltData.profile,TiltData.eval,TiltData.reflect,signedProfile,constantProfile,oddTilt]
  <;> ring

theorem singles {W : Set ℝ} {k n : ℝ} {A : ℝ → TiltData} (H : ThirdTiltLaws W k n A) :
    SingleLaw W k k (fun t ↦ (A t).q) (fun t ↦ (A t).p₁) ∧
    SingleLaw W k n (fun t ↦ (A t).q) (fun t ↦ (A t).p₃) := by
  constructor <;> intro x hx <;> filter_upwards [H x hx] with h hh
  · apply (hh true false false).congr
    intro s _
    simp [TiltData.test,TiltData.profile,TiltData.eval,TiltData.reflect,signedProfile,constantProfile,singleSource]
    <;> ring
  · apply (hh false false true).congr
    intro s _
    simp [TiltData.test,TiltData.profile,TiltData.eval,TiltData.reflect,signedProfile,constantProfile,singleSource]
    <;> ring

theorem mixed_source (k n h s : ℝ) (U V : TiltData) {p z : ℝ}
    (hu : U.q=0) (hv : V.q=0) (h₁ : U.p₁=p) (h₂ : V.p₁=p) (h₃ : U.p₃=z) (h₄ : V.p₃=z) (hr : U.r₂=V.r₂) :
    TiltData.test k n h true false true U V s=
      (-4*k*p)*Real.exp (k*s)*tiltAmplitude n h s+(-4*n*z)*Real.exp (n*s)*tiltAmplitude k h s := by
  simp [TiltData.test,TiltData.profile,TiltData.eval,TiltData.reflect,signedProfile,constantProfile,
    hu,hv,h₁,h₂,h₃,h₄,hr,tiltSlope]
  <;> ring

theorem triple_source (k n h s r : ℝ) (U V : TiltData)
    (hq : U.q=0 ∧ V.q=0)
    (hp : U.p₁=0 ∧ V.p₁=0 ∧ U.p₂=0 ∧ V.p₂=0 ∧ U.p₃=0 ∧ V.p₃=0)
    (hr : U.r₁=r ∧ V.r₁=r ∧ U.r₂=r ∧ V.r₂=r ∧ U.r₃=0 ∧ V.r₃=0) :
    TiltData.test k n h true true true U V s=
      (-8*k*n*r)*Real.exp ((k+n)*s)*tiltAmplitude k h s := by
  rcases hq with ⟨hq₁,hq₂⟩
  rcases hp with ⟨hp₁,hp₂,hp₃,hp₄,hp₅,hp₆⟩
  rcases hr with ⟨hr₁,hr₂,hr₃,hr₄,hr₅,hr₆⟩
  simp [TiltData.test,TiltData.profile,TiltData.eval,TiltData.reflect,signedProfile,constantProfile,
    hq₁,hq₂,hp₁,hp₂,hp₃,hp₄,hp₅,hp₆,hr₁,hr₂,hr₃,hr₄,hr₅,hr₆,tiltSlope,add_mul,Real.exp_add]
  <;> ring

end ThirdTiltLaws
end EuclideanMidpointRigidity

