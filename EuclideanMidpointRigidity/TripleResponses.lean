module

public import EuclideanMidpointRigidity.ForcedChord
public import EuclideanMidpointRigidity.SmallRealizedChords
public import EuclideanMidpointRigidity.TiltData
public import EuclideanMidpointRigidity.TranslatedMidpoints

/-! # The actual reflected third endpoint response of a translated field -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff InnerProductSpace Topology
namespace EuclideanMidpointRigidity
open Endpoint
variable {d : ℕ}
local notation "E" => Space d
local notation "H" => E × E
local notation "T" => Cubic d

def Endpoint.ChordProfile.ends {κ : ℝ} (P : ChordProfile κ) (h : ℝ) (v : E) : H := (P.value (-h) • v,P.value h • v)

def TiltData.profile {α β γ : ℝ} (D : TiltData) (P : ChordProfile α) (Q : ChordProfile β) (R : ChordProfile γ) (s : ℝ) :=
  D.eval (P.value s) (Q.value s) (R.value s) (P.slope s) (Q.slope s) (R.slope s)

theorem FlatAxialForce.neg {D : E → T} {x u : E} (hf : FlatAxialForce D x u) : FlatAxialForce D x (-u) :=
  ⟨hf.value,fun v w ↦ by rw [K_neg_left,hf.first,neg_zero],fun v w ↦ by rw [K_neg_left,K_neg_right,hf.second,neg_zero,neg_zero]⟩

theorem RealizedChord.projected_third {Ω : Set E} {C : E → T} {σ r : ℝ} {p u : E} {h : ℝ}
    {B : E →L[ℝ] E} {F : SmoothEndpointFamily C σ p r} (J : RealizedChord Ω C σ p u h B F)
    (hΩ : IsOpen Ω) (hC : ContDiffOn ℝ ∞ C Ω) (b : E)
    (hf : ∀ s ∈ Icc (-h) h, FlatAxialForce (directional C b) (p+s • u) u)
    {i j l o : E} {α β γ c : ℝ} (hi : B i=α • i) (hj : B j=β • j) (hl : B l=γ • l) (ho : B o=c • o)
    (P : ChordProfile (1-2*α)) (Q : ChordProfile (1-2*β)) (R : ChordProfile (1-2*γ)) :
    let A := fun s ↦ TiltData.atPoint (directional C b) (p+s • u) u i j l o
    let Y := directions (F.translatedVariation b) [P.ends h i,Q.ends h j,R.ends h l] (chordEnds p u h)
    ∃ X V, ScalarDirichlet (1-2*c) h (fun s ↦ -σ*(A s).profile P Q R s) X V ∧
      X (Real.log (Real.cosh h))=⟪o,midpointEvaluation Y⟫_ℝ := by
  obtain ⟨he,hs⟩ := J.translated_third hΩ hC b hf (P.ends h i) (Q.ends h j) (R.ends h l)
  apply J.forced_projection hΩ hC ho _ _ he _
  intro t
  rw [hs,real_inner_smul_right]
  simp only [ChordProfile.ends]
  rw [J.profile hΩ hC i hi P t,J.profile hΩ hC j hj Q t,J.profile hΩ hC l hl R t]
  have hD : ContDiffOn ℝ ∞ (directional C b) Ω := directions.smooth hΩ hC [b]
  have hx : axialPosition p u h t ∈ Ω := J.inside _ (chordParameter_bounds J.positive.le t.property)
  simp only [axialVelocity]
  rw [TiltData.inner_triple hΩ hD hx]
  dsimp only [TiltData.profile,axialPosition]
  ring

theorem OrientedEndpointChart.reflected_third {Ω : Set E} {C : E → T} {p u : E} {h : ℝ}
    {B : E →L[ℝ] E} (D : OrientedEndpointChart C p) (hΩ : IsOpen Ω) (hC : ContDiffOn ℝ ∞ C Ω)
    (hd : chordEnds p u h ∈ D.domain) (J : RealizedChord Ω C 1 p u h B D.plus)
    (N : RealizedChord Ω C (-1) p (-u) h B D.minus) (b : E)
    (hf : ∀ s ∈ Icc (-h) h, FlatAxialForce (directional C b) (p+s • u) u)
    {i j l o : E} {α β γ c : ℝ} (hi : B i=α • i) (hj : B j=β • j) (hl : B l=γ • l) (ho : B o=c • o)
    (P P' : ChordProfile (1-2*α)) (Q Q' : ChordProfile (1-2*β)) (R R' : ChordProfile (1-2*γ))
    (hp : P'.ends h i=(P.ends h i).swap) (hq : Q'.ends h j=(Q.ends h j).swap) (hr : R'.ends h l=(R.ends h l).swap) :
    let A := fun s ↦ TiltData.atPoint (directional C b) (p+s • u) u i j l o
    VanishingResponse (1-2*c) h (fun s ↦ ((A (-s)).reflect).profile P' Q' R' s-(A s).profile P Q R s) := by
  have hn (s : ℝ) (hs : s ∈ Icc (-h) h) : FlatAxialForce (directional C b) (p+s • (-u)) (-u) := by
    rw [smul_neg,← neg_smul]
    exact (hf (-s) ⟨by linarith [hs.2],by linarith [hs.1]⟩).neg
  obtain ⟨x,v,hx,ex⟩ := J.projected_third hΩ hC b hf hi hj hl ho P Q R
  obtain ⟨y,w,hy,ey⟩ := N.projected_third hΩ hC b hn hi hj hl ho P' Q' R'
  refine ⟨fun s ↦ x s+y s,fun s ↦ v s+w s,?_,?_⟩
  · convert hx.add hy using 1
    funext s
    dsimp only
    rw [TiltData.atPoint_neg,smul_neg,← neg_smul]
    ring
  · change x _+y _=0
    rw [ex,ey,hp,hq,hr,← chordEnds_swap,← inner_add_right]
    have law := D.translated_law hd b [P.ends h i,Q.ends h j,R.ends h l]
    rw [show (List.map Prod.swap [P.ends h i,Q.ends h j,R.ends h l])=[(P.ends h i).swap,(Q.ends h j).swap,(R.ends h l).swap] from rfl] at law
    rw [law,inner_zero_right]

end EuclideanMidpointRigidity

