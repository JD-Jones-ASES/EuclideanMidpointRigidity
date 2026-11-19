module

public import EuclideanMidpointRigidity.TripleResponses
public import EuclideanMidpointRigidity.ReflectedResponses
public import EuclideanMidpointRigidity.DirichletBoundary

/-! # Symmetric endpoint tilts and translations of the center -/

@[expose] public section
noncomputable section
open Set Filter Metric
open scoped Topology
namespace EuclideanMidpointRigidity
open Endpoint

def Endpoint.tiltAmplitude (k h s : ℝ) := Real.exp (k*s)-Real.cosh (k*h)
def Endpoint.tiltSlope (k s : ℝ) := k*Real.exp (k*s)

def Endpoint.signedProfile (k h : ℝ) (tilted reverse : Bool) : ChordProfile k :=
  if tilted then
    let sign : ℝ := if reverse then -1 else 1
    { value := fun s ↦ sign*tiltAmplitude k h s
      slope := fun s ↦ sign*tiltSlope k s
      first := fun s ↦ by
        convert (((exp_line_diff k s).sub_const (Real.cosh (k*h))).const_mul sign) using 1 <;> first | rfl | dsimp [tiltSlope]; ring
      second := fun s ↦ by
        convert (((exp_line_diff k s).const_mul k).const_mul sign) using 1 <;> first | rfl | dsimp [tiltSlope]; ring }
  else constantProfile k

theorem Endpoint.signedProfile_swap {d : ℕ} (k h : ℝ) (t : Bool) (v : Space d) :
    (signedProfile k h t true).ends h v=((signedProfile k h t false).ends h v).swap := by
  cases t
  · rfl
  · have he : Real.exp (k*(-h))+Real.exp (k*h)=2*Real.cosh (k*h) := by
      rw [Real.cosh_eq,mul_neg]; ring
    apply Prod.ext <;> dsimp [signedProfile,ChordProfile.ends,tiltAmplitude] <;> congr 1 <;> linarith only [he]

def TiltData.test (k n h : ℝ) (i j l : Bool) (A B : TiltData) (s : ℝ) :=
  A.reflect.profile (signedProfile k h i true) (signedProfile k h j true) (signedProfile n h l true) s-
    B.profile (signedProfile k h i false) (signedProfile k h j false) (signedProfile n h l false) s

def TiltData.combine (a b : ℝ) (X Y : TiltData) : TiltData :=
  ⟨a*X.q+b*Y.q,a*X.p₁+b*Y.p₁,a*X.p₂+b*Y.p₂,a*X.p₃+b*Y.p₃,
    a*X.r₁+b*Y.r₁,a*X.r₂+b*Y.r₂,a*X.r₃+b*Y.r₃⟩

theorem TiltData.test_combine (k n h : ℝ) (i j l : Bool) (a b : ℝ) (X Y U V : TiltData) (s : ℝ) :
    test k n h i j l (combine a b X Y) (combine a b U V) s=
      a*test k n h i j l X U s+b*test k n h i j l Y V s := by
  dsimp only [test,profile,eval,reflect,combine]; ring

def ThirdTiltLaws (W : Set ℝ) (k n : ℝ) (A : ℝ → TiltData) : Prop :=
  ∀ x ∈ W, ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ i j l : Bool, VanishingResponse k h
    (fun s ↦ TiltData.test k n h i j l (A (x-s)) (A (x+s)) s)

namespace ThirdTiltLaws

theorem shift {W V : Set ℝ} {k n t : ℝ} {A : ℝ → TiltData} (H : ThirdTiltLaws W k n A)
    (hV : ∀ x ∈ V, x+t ∈ W) : ThirdTiltLaws V k n (fun x ↦ A (x+t)) := by
  intro x hx
  filter_upwards [H _ (hV x hx)] with h hh
  intro i j l
  convert hh i j l using 2
  rename_i s
  rw [show x-s+t=x+t-s by ring,show x+s+t=x+t+s by ring]

theorem mono {W V : Set ℝ} {k n : ℝ} {A : ℝ → TiltData} (H : ThirdTiltLaws W k n A) (hV : V ⊆ W) :
    ThirdTiltLaws V k n A := fun x hx ↦ H x (hV hx)

theorem combine {W : Set ℝ} {k n : ℝ} {X Y : ℝ → TiltData} (H : ThirdTiltLaws W k n X)
    (J : ThirdTiltLaws W k n Y) (a b : ℝ) : ThirdTiltLaws W k n (fun x ↦ TiltData.combine a b (X x) (Y x)) := by
  intro x hx
  filter_upwards [H x hx,J x hx] with h hh hj
  intro i j l
  apply (((hh i j l).smul a).add ((hj i j l).smul b)).congr
  intro s _
  exact (TiltData.test_combine ..).symm

theorem small_segments {W : Set ℝ} (hW : IsOpen W) {x : ℝ} (hx : x ∈ W) :
    ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ s ∈ Icc (-h) h, x-s ∈ W ∧ x+s ∈ W := by
  obtain ⟨δ,hδ,hb⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hx)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)] with h hh
  intro s hs
  have he := (abs_le.mpr hs).trans_lt hh
  constructor <;> apply hb <;> simpa [Real.dist_eq] using he

end ThirdTiltLaws
end EuclideanMidpointRigidity

