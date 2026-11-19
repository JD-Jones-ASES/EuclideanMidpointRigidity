module

public import EuclideanMidpointRigidity.ChordParameter
public import EuclideanMidpointRigidity.SmoothComplementarity
public import EuclideanMidpointRigidity.StraightRulings

/-! # Actual short geodesics on a straight maximizing chord -/

@[expose] public section
noncomputable section
open Set Metric
open scoped ContDiff
namespace EuclideanMidpointRigidity
open Endpoint
variable {d : ℕ}
local notation "E" => Space d
local notation "H" => E × E
local notation "Op" => E →L[ℝ] E

structure AxialChord (Ω : Set E) (C : E → Cubic d) (σ : ℝ) (p u : E) (h : ℝ) (B : Op) : Prop where
  positive : 0<h
  inside : ∀ s ∈ Icc (-h) h, p+s • u ∈ Ω
  direction : B u=u
  slice : ∀ s ∈ Icc (-h) h, ∀ v, σ • K (C (p+s • u)) u v=B v
  stationary : ∀ s ∈ Icc (-h) h, ∀ l, K (fderiv ℝ C (p+s • u) l) u u=0

def axialPosition (p u : E) (h t : ℝ) := p+chordParameter h t • u
def axialVelocity (u : E) (h t : ℝ) := chordSpeed h t • u

namespace AxialChord
variable {Ω : Set (Space d)} {C : Space d → Cubic d} {σ : ℝ} {p u : Space d} {h : ℝ}
  {B : Space d →L[ℝ] Space d} (J : AxialChord Ω C σ p u h B)
include J

theorem geodesic : IsGeodesicSegment C σ (axialPosition p u h) (axialVelocity u h) := by
  constructor
  · intro t ht
    exact ((hasDerivAt_chordParameter J.positive.le ht).smul_const u).const_add p
  · intro t ht
    have he := (J.slice _ (chordParameter_bounds J.positive.le ht) u).trans J.direction
    have hd := (hasDerivAt_chordSpeed J.positive.le ht).smul_const u
    change HasDerivAt (fun s ↦ chordSpeed h s • u) (-σ • K (C (p+chordParameter h t • u)) (chordSpeed h t • u) (chordSpeed h t • u)) t
    convert hd using 1
    simp only [K_smul_left,K_smul_right,smul_smul]
    change _=(-(chordSpeed h t)^2) • u
    conv_rhs => rw [← he]
    module

theorem short {r : ℝ} (hx : h*‖u‖<r) (hv : (Real.exp (2*h)-1)*‖u‖<r) :
    IsShortGeodesic C σ p r (p+(-h) • u) (p+h • u) (axialPosition p u h) (axialVelocity u h) := by
  refine ⟨J.geodesic,by simp [axialPosition],by simp [axialPosition],?_⟩
  intro t ht
  obtain ⟨h₁,h₂⟩ := chordParameter_bounds J.positive.le ht
  obtain ⟨h₃,h₄⟩ := chordSpeed_bounds J.positive.le ht
  constructor
  · simpa only [axialPosition,add_sub_cancel_left,norm_smul,Real.norm_eq_abs] using
      (mul_le_mul_of_nonneg_right (abs_le.mpr ⟨h₁,h₂⟩) (norm_nonneg u)).trans_lt hx
  · simpa only [axialVelocity,norm_smul,Real.norm_eq_abs,abs_of_nonneg h₃] using
      (mul_le_mul_of_nonneg_right h₄ (norm_nonneg u)).trans_lt hv

end AxialChord

namespace LiftedSection
variable (S : LiftedSection d)

/-- Positive and negative geodesics use opposite axial vectors, with the same normalized slice. -/
theorem small_axial_chords {p : E} (hp : p ∈ S.domain) (hm : ∀ q ∈ S.domain, S.Maximizes q) :
    ∃ R>0, ∀ h ∈ Ioo (0:ℝ) R, ∀ σ : ℝ, σ=1 ∨ σ= -1 →
      AxialChord S.domain S.field σ p ((σ*(S.a p)⁻¹) • S.axis p) h (S.axisSlice p) := by
  obtain ⟨U,δ,_,hpU,hδ,hr⟩ := S.local_straight_rulings hp hm
  have ha : 0<S.a p := S.positive p hp
  refine ⟨δ*S.a p,mul_pos hδ ha,?_⟩
  intro h hh σ hσ
  let c := σ*(S.a p)⁻¹
  have hc : |c|=(S.a p)⁻¹ := by
    rcases hσ with h₁|h₁ <;> rw [show c=σ*(S.a p)⁻¹ from rfl,h₁] <;> simp [abs_of_pos ha]
  have hline (s : ℝ) (hs : s ∈ Icc (-h) h) :=
    hr p hpU (s*c) (show s*c ∈ ball (0:ℝ) δ by
      rw [mem_ball,Real.dist_0_eq_abs,abs_mul,hc,← div_eq_mul_inv]
      exact (div_lt_iff₀ ha).mpr ((abs_le.mpr hs).trans_lt hh.2))
  let y := fun s : ℝ ↦ p+s • (c • S.axis p)
  have hyd (s : ℝ) : displacementLine p (S.axis p) (s*c)=y s := by simp only [displacementLine,y,smul_smul]
  have hrule (s : ℝ) (hs : s ∈ Icc (-h) h) : y s ∈ S.domain ∧ S.axis (y s)=S.axis p ∧
      S.axisSlice (y s)=S.axisSlice p ∧ S.a (y s)=S.a p := by simpa only [hyd] using hline s hs
  refine ⟨hh.1,fun s hs ↦ (hrule s hs).1,?_,?_,?_⟩
  · rw [map_smul]
    exact congrArg (fun z : E ↦ (σ*(S.a p)⁻¹) • z) (by simpa only [one_smul] using S.normalized_axis hp :
      K (S.cubic p) (S.axis p) (S.axis p)=S.axis p)
  · intro s hs v
    obtain ⟨_,he,hB,ha'⟩ := hrule s hs
    have hsquare : σ*c=(S.a p)⁻¹ := by rcases hσ with h₁|h₁ <;> simp [c,h₁]
    change σ • K (S.field (y s)) (c • S.axis p) v=S.axisSlice p v
    rw [K_smul_left,smul_smul,hsquare,← hB]
    change _=K (S.cubic (y s)) (S.axis (y s)) v
    rw [cubic,K_smul_coeff,he,ha']
  · intro s hs l
    obtain ⟨hy,he,_,_⟩ := hrule s hs
    change K (fderiv ℝ S.field (y s) l) (c • S.axis p) (c • S.axis p)=0
    rw [K_smul_left,K_smul_right,← he,(S.weighted_ruling hy hm).1 l,smul_zero,smul_zero]

end LiftedSection
end EuclideanMidpointRigidity

