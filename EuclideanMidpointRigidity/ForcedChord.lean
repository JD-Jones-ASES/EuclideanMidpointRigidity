module

public import EuclideanMidpointRigidity.ProjectedResponse
public import EuclideanMidpointRigidity.TranslatedSourceJets

/-! # A forced variation in the physical coordinate of an axial chord -/

public section
noncomputable section
open Set
open scoped ContDiff InnerProductSpace
namespace EuclideanMidpointRigidity.RealizedChord
open Endpoint
variable {d : ℕ} {Ω : Set (Space d)} {C : Space d → Cubic d} {σ r : ℝ} {p u : Space d} {h : ℝ}
  {B : Space d →L[ℝ] Space d} {F : SmoothEndpointFamily C σ p r}
local notation "E" => Space d
local notation "H" => E × E
local notation "P" => PhaseCurve d
local notation "Q" => AccelerationCurve d
variable (J : RealizedChord Ω C σ p u h B F)
include J

theorem forced_projection (hΩ : IsOpen Ω) (hC : ContDiffOn ℝ ∞ C Ω) {o : E} {c : ℝ} (ho : B o=c • o)
    (Y : P) (N : Q) (hy : Y=greenOperator (N+F.linearForce (chordEnds p u h) Y))
    (f : ℝ → ℝ) (hf : ∀ t : UnitInterval, ⟪o,N t⟫_ℝ=(chordSpeed h t)^2*f (chordParameter h t)) :
    ∃ X V, ScalarDirichlet (1-2*c) h f X V ∧ X (Real.log (Real.cosh h))=⟪o,midpointEvaluation Y⟫_ℝ := by
  let A := N+F.linearForce (chordEnds p u h) Y
  let x := bvpPosition (0:E) 0 A
  let v := bvpVelocity (0:E) 0 A
  have he : Y=affinePhase 0 0+greenOperator A := by
    have hz : affinePhase (0:E) 0=0 := by ext t : 1; simp [affinePhase]
    rw [hz,zero_add]; exact hy
  have hp (t : UnitInterval) : (x t,v t)=Y t := green_phase_eq he t
  let L : E →L[ℝ] ℝ := innerSL ℝ o
  have hA (t : UnitInterval) : L (A t)=(chordSpeed h t)^2*f (chordParameter h t)-2*c*chordSpeed h t*L (v t) := by
    change ⟪o,N t+F.linearForce _ Y t⟫_ℝ=_
    rw [inner_add_right,hf,J.force_on_chord hΩ hC,← hp t,real_inner_smul_right,J.symmetric_slice o (v t),ho,real_inner_smul_left]
    change _=_-2*c*chordSpeed h t*⟪o,v t⟫_ℝ
    ring
  have dx (t : ℝ) (_ : t ∈ UnitInterval) : HasDerivAt (L ∘ x) (L (v t)) t :=
    L.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_bvpPosition _ _ _ t)
  have dv (t : ℝ) (ht : t ∈ UnitInterval) : HasDerivAt (L ∘ v)
      ((chordSpeed h t)^2*f (chordParameter h t)-2*c*chordSpeed h t*L (v t)) t := by
    have hv := L.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_bvpVelocity (0:E) 0 A t)
    rw [pathExtend_mem A t ht] at hv
    exact hA ⟨t,ht⟩ ▸ hv
  obtain ⟨X,V,hsol,hval⟩ := scalar_response_in_line_coordinate J.positive (v := L ∘ v) dx dv
    (show (L ∘ x) 0=0 by simp [x]) (show (L ∘ x) 1=0 by simp [x])
  exact ⟨X,V,hsol,hval.trans (congrArg (fun z : E × E ↦ L z.1) (hp middleParameter))⟩

theorem translated_third (hΩ : IsOpen Ω) (hC : ContDiffOn ℝ ∞ C Ω) (b : E)
    (hflat : ∀ s ∈ Icc (-h) h, FlatAxialForce (directional C b) (p+s • u) u)
    (j₁ j₂ j₃ : H) :
    let q := chordEnds p u h
    let xs := [j₁,j₂,j₃]
    let Y := directions (F.translatedVariation b) xs q
    let N := directions (F.translatedSource b) xs q
    Y=greenOperator (N+F.linearForce q Y) ∧ ∀ t : UnitInterval,
      N t= -σ • tripleForce (directional C b) (axialPosition p u h t) (axialVelocity u h t)
        (F.variation q j₁ t) (F.variation q j₂ t) (F.variation q j₃ t) := by
  let q := chordEnds p u h
  let D := directional C b
  have hD : ContDiffOn ℝ ∞ D Ω := directions.smooth hΩ hC [b]
  have ht (t : UnitInterval) := chordParameter_bounds J.positive.le t.property
  have hx (t : UnitInterval) : (F.phase q t).1 ∈ Ω := by rw [J.path_eq t]; exact J.inside _ (ht t)
  have hz (t : UnitInterval) (ys : List H) (hy : ys.length<3) : directions (phaseCore D) ys (F.phase q t)=0 := by
    rw [J.path_eq t]
    exact (hflat _ (ht t)).flat hΩ hD (J.inside _ (ht t)) (chordSpeed h t) ys hy
  have hs (ys : List H) (hy : ys.length<3) : directions (F.translatedSource b) ys q=0 := by
    ext t : 1
    rw [F.source_word hΩ hC b J.mem t (hx t) ys (fun zs he ↦ hz t zs (he.trans hy)),hz t _ (by simpa using hy),smul_zero]
    rfl
  refine ⟨F.translated_word b J.mem _ (F.translated_flat b J.mem 3 hs),?_⟩
  intro t
  rw [F.source_word hΩ hC b J.mem t (hx t) [j₁,j₂,j₃] (hz t)]
  change -σ • directions (phaseCore D) [F.variation q j₁ t,F.variation q j₂ t,F.variation q j₃ t] (F.phase q t)=_
  rw [J.path_eq t]
  exact congrArg (fun z : E ↦ -σ • z) (triple_force_formula (x := axialPosition p u h t) hΩ hD (J.inside _ (ht t)) _ _ _ _)

end EuclideanMidpointRigidity.RealizedChord

