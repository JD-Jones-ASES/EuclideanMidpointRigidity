module

public import EuclideanMidpointRigidity.AxialChords
public import EuclideanMidpointRigidity.OrientedEndpoints
public import EuclideanMidpointRigidity.GeodesicForceJets
public import EuclideanMidpointRigidity.PhaseDirichlet
public import EuclideanMidpointRigidity.TiltProfiles

/-! # First endpoint variations on a realized axial chord -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity
open Endpoint
variable {d : ℕ}
local notation "E" => Space d
local notation "H" => E × E
local notation "P" => PhaseCurve d
local notation "Op" => E →L[ℝ] E

def chordEnds (p u : E) (h : ℝ) : H := (p+(-h) • u,p+h • u)

structure RealizedChord (Ω : Set E) (C : E → Cubic d) (σ : ℝ) (p u : E) (h : ℝ) (B : Op) {r : ℝ}
    (F : SmoothEndpointFamily C σ p r) : Prop extends AxialChord Ω C σ p u h B where
  mem : chordEnds p u h ∈ F.domain
  path_eq : ∀ t : UnitInterval, F.phase (chordEnds p u h) t=(axialPosition p u h t,axialVelocity u h t)

namespace RealizedChord
variable {Ω : Set (Space d)} {C : Space d → Cubic d} {σ r : ℝ} {p u : Space d} {h : ℝ} {B : Space d →L[ℝ] Space d}
  {F : SmoothEndpointFamily C σ p r} (J : RealizedChord Ω C σ p u h B F)
include J

theorem force_on_chord (hΩ : IsOpen Ω) (hC : ContDiffOn ℝ ∞ C Ω) (Y : P) (t : UnitInterval) :
    F.linearForce (chordEnds p u h) Y t=(-(2*chordSpeed h t)) • B (Y t).2 := by
  let z := p+chordParameter h t • u
  have hs := chordParameter_bounds J.positive.le t.property
  have hc : ContDiffAt ℝ ∞ C z := hC.contDiffAt (hΩ.mem_nhds (J.inside _ hs))
  change fderiv ℝ (F.force : H → E) (F.phase (chordEnds p u h) t) (Y t)=_
  rw [(F.forceGerm _ J.mem t).fderiv_eq,J.path_eq t,fderiv_geodesicForce_apply σ _ _ hc]
  have h₀ : K (fderiv ℝ C z (Y t).1) u u=0 := J.stationary _ hs _
  have hB : σ • K (C z) u (Y t).2=B (Y t).2 := J.slice _ hs _
  change -σ • (K (fderiv ℝ C z (Y t).1) (chordSpeed h t • u) (chordSpeed h t • u)+
    (2:ℝ) • K (C z) (chordSpeed h t • u) (Y t).2)=_
  simp only [K_smul_left,K_smul_right,h₀,smul_zero,zero_add,← hB]
  module

theorem translation (hΩ : IsOpen Ω) (hC : ContDiffOn ℝ ∞ C Ω) (l : E) :
    F.variation (chordEnds p u h) (l,l)=ContinuousMap.const UnitInterval (l,(0:E)) := by
  let y : P := ContinuousMap.const UnitInterval (l,0)
  apply Eq.symm
  apply F.variation_unique J.mem
  have hz : F.linearForce (chordEnds p u h) y=0 := by
    ext t : 1
    rw [J.force_on_chord hΩ hC]; simp [y]
  change y=affinePhaseMap (l,l)+greenOperator (F.linearForce _ y)
  rw [hz,map_zero,add_zero,affinePhaseMap_apply,affinePhase_diagonal]

theorem profile (hΩ : IsOpen Ω) (hC : ContDiffOn ℝ ∞ C Ω) (w : E) {b : ℝ} (heig : B w=b • w)
    (T : ChordProfile (1-2*b)) (t : UnitInterval) :
    F.variation (chordEnds p u h) (T.value (-h) • w,T.value h • w) t =
      (T.value (chordParameter h t) • w,(chordSpeed h t*T.slope (chordParameter h t)) • w) := by
  let x := fun s ↦ T.value (chordParameter h s) • w
  let v := fun s ↦ (chordSpeed h s*T.slope (chordParameter h s)) • w
  let a := fun s ↦ (((1-2*b)-1)*(chordSpeed h s)^2*T.slope (chordParameter h s)) • w
  have dx (s : ℝ) (hs : s ∈ UnitInterval) : HasDerivAt x (v s) s :=
    ((T.time_derivatives J.positive.le hs).1).smul_const w
  have dv (s : ℝ) (hs : s ∈ UnitInterval) : HasDerivAt v (a s) s :=
    ((T.time_derivatives J.positive.le hs).2).smul_const w
  let Y : P := ⟨fun s ↦ (x s,v s),
    (continuousOn_iff_continuous_domRestrict.mp (HasDerivAt.continuousOn dx)).prodMk
      (continuousOn_iff_continuous_domRestrict.mp (HasDerivAt.continuousOn dv))⟩
  let A := F.linearForce (chordEnds p u h) Y
  have ha (s : ℝ) (hs : s ∈ UnitInterval) : pathExtend A s=a s := by
    rw [pathExtend_mem A s hs]
    change F.linearForce (chordEnds p u h) Y ⟨s,hs⟩=a s
    rw [J.force_on_chord hΩ hC]
    change (-(2*chordSpeed h s)) • B ((chordSpeed h s*T.slope (chordParameter h s)) • w)=a s
    rw [map_smul,heig]
    dsimp only [a]
    module
  have hY := green_phase_of_derivatives (a := A) (y := Y) (x := x) (v := v) (fun _ ↦ rfl)
    dx (fun s hs ↦ ha s hs ▸ dv s hs) (show x 0=T.value (-h) • w by simp [x]) (show x 1=T.value h • w by simp [x])
  have hy := F.variation_unique J.mem (T.value (-h) • w,T.value h • w) hY
  exact congrArg (fun y : P ↦ y t) hy.symm

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 110000 in
set_option maxHeartbeats 1000000 in
theorem second_force_on_chord (hΩ : IsOpen Ω) (hC : ContDiffOn ℝ ∞ C Ω) (l w : E) {b : ℝ}
    (heig : B w=b • w) (T : ChordProfile (1-2*b)) (t : UnitInterval) :
    let q := chordEnds p u h
    let s := chordParameter h t
    let v := chordSpeed h t
    let z := p+s • u
    F.secondForce q (F.variation q (l,l)) (F.variation q (T.value (-h) • w,T.value h • w)) t=
      -σ • ((v^2*T.value s) • secondProduct C z w l u u+
        (2*v^2*T.slope s) • firstProduct C z l u w) := by
  dsimp only
  rw [F.secondForce_apply,J.translation hΩ hC,J.profile hΩ hC w heig T]
  have hs := chordParameter_bounds J.positive.le t.property
  have hg := F.forceGerm _ J.mem t
  rw [(hg.fderiv (𝕜 := ℝ)).fderiv_eq,J.path_eq t,fderiv_geodesicForce_second hΩ hC σ _ _ _ (J.inside _ hs)]
  let z := p+chordParameter h t • u
  have hz₁ : ∀ m n, K (fderiv ℝ C z m) n 0=0 := by simp [K]
  have hz₂ : ∀ n, K (C z) n 0=0 := by simp [K]
  change secondForceJet C σ (z,chordSpeed h t • u)
    (T.value (chordParameter h t) • w,(chordSpeed h t*T.slope (chordParameter h t)) • w) (l,0)=_
  simp only [secondForceJet,secondProduct,firstProduct,Prod.fst,Prod.snd,K_smul_left,K_smul_right,
    map_smul,smul_apply,K_smul_coeff,hz₁,hz₂,smul_zero,add_zero]
  module

end RealizedChord
end EuclideanMidpointRigidity

