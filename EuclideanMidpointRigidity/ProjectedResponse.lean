module

public import EuclideanMidpointRigidity.RealizedChords
public import EuclideanMidpointRigidity.AxialResponse

/-! # The projected mixed Jacobi equation on a maximizing line -/

@[expose] public section
noncomputable section
open Set
open scoped ContDiff InnerProductSpace
namespace EuclideanMidpointRigidity
open Endpoint
variable {d : ℕ}
local notation "E" => Space d
local notation "H" => E × E
local notation "P" => PhaseCurve d

def translationSource (C : E → Cubic d) (p u l w o : E) (s : ℝ) :=
  ⟪o,secondProduct C (p+s • u) w l u u⟫_ℝ
def tiltSource (C : E → Cubic d) (p u l w o : E) (s : ℝ) :=
  ⟪o,firstProduct C (p+s • u) l u w⟫_ℝ

namespace RealizedChord
variable {Ω : Set (Space d)} {C : Space d → Cubic d} {σ r : ℝ} {p u : Space d} {h : ℝ} {B : Space d →L[ℝ] Space d}
  {F : SmoothEndpointFamily C σ p r} (J : RealizedChord Ω C σ p u h B F)
include J

theorem symmetric_slice (o v : E) : ⟪o,B v⟫_ℝ=⟪B o,v⟫_ℝ := by
  have ht : 0 ∈ Icc (-h) h := ⟨neg_nonpos.mpr J.positive.le,J.positive.le⟩
  rw [← J.slice 0 ht v,← J.slice 0 ht o,real_inner_smul_right,real_inner_smul_left,K_selfAdjoint]

theorem projected_response (hΩ : IsOpen Ω) (hC : ContDiffOn ℝ ∞ C Ω) (l w o : E) {b c : ℝ}
    (hw : B w=b • w) (ho : B o=c • o) (T : ChordProfile (1-2*b)) :
    let q := chordEnds p u h
    let f := fun s ↦ -σ*(T.value s*translationSource C p u l w o s + 2*T.slope s*tiltSource C p u l w o s)
    ∃ X V, ScalarDirichlet (1-2*c) h f X V ∧
      X (Real.log (Real.cosh h))=⟪o,midpointEvaluation (F.mixedVariation q (l,l) (T.value (-h) • w,T.value h • w))⟫_ℝ := by
  let q := chordEnds p u h
  let j : H := (T.value (-h) • w,T.value h • w)
  let Y := F.mixedVariation q (l,l) j
  let N := F.secondForce q (F.variation q (l,l)) (F.variation q j)
  let A := N+F.linearForce q Y
  let x := bvpPosition (0:E) 0 A
  let v := bvpVelocity (0:E) 0 A
  let f := fun s ↦ -σ*(T.value s*translationSource C p u l w o s+2*T.slope s*tiltSource C p u l w o s)
  have hy : Y=affinePhase 0 0+greenOperator A := by
    have hz : affinePhase (0:E) 0=0 := by ext t : 1; simp [affinePhase]
    rw [hz,zero_add]
    exact F.mixed_variation_equation J.mem (l,l) j
  have hpath (t : UnitInterval) : (x t,v t)=Y t := green_phase_eq hy t
  have hf (t : UnitInterval) :
      ⟪o,A t⟫_ℝ=(chordSpeed h t)^2*f (chordParameter h t)-2*c*chordSpeed h t*⟪o,v t⟫_ℝ := by
    let s := chordParameter h t
    let k := chordSpeed h t
    have hN : N t= -σ • ((k^2*T.value s) • secondProduct C (p+s • u) w l u u+
      (2*k^2*T.slope s) • firstProduct C (p+s • u) l u w) := J.second_force_on_chord hΩ hC l w hw T t
    have hL : F.linearForce q Y t=(-(2*k)) • B (v t) := by
      rw [J.force_on_chord hΩ hC,← hpath]
    change ⟪o,N t+F.linearForce q Y t⟫_ℝ=k^2*f s-2*c*k*⟪o,v t⟫_ℝ
    rw [hN,hL]
    simp only [f,translationSource,tiltSource,inner_add_right,real_inner_smul_right,J.symmetric_slice o (v t),ho,real_inner_smul_left]
    ring
  let «π» : E →L[ℝ] ℝ := innerSL ℝ o
  have dx (t : ℝ) (_ : t ∈ UnitInterval) : HasDerivAt (π ∘ x) (π (v t)) t := π.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_bvpPosition _ _ _ t)
  have dv (t : ℝ) (ht : t ∈ UnitInterval) : HasDerivAt (π ∘ v)
      ((chordSpeed h t)^2*f (chordParameter h t)-2*c*chordSpeed h t*π (v t)) t := by
    have hv := π.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_bvpVelocity (0:E) 0 A t)
    rw [pathExtend_mem _ t ht] at hv
    exact hf ⟨t,ht⟩ ▸ hv
  obtain ⟨X,V,hsol,he⟩ := scalar_response_in_line_coordinate J.positive (v := π ∘ v) dx dv
    (show (π ∘ x) 0=0 by simp [x]) (show (π ∘ x) 1=0 by simp [x])
  refine ⟨X,V,hsol,he.trans ?_⟩
  exact congrArg (fun z : E × E ↦ π z.1) (hpath middleParameter)

end RealizedChord
end EuclideanMidpointRigidity

