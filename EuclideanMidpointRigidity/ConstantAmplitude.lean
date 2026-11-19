module

public import EuclideanMidpointRigidity.CharacteristicSection

/-! # Constancy of the spherical maximum on a connected open set -/

public section
noncomputable section
open Set
open scoped ContDiff
namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

theorem exists_maximizing_section_on_subpatch {W : Set E} {C : E → Coeff}
    (hW : IsOpen W) (hn : W.Nonempty) (hC : ContDiffOn ℝ ∞ C W) (hQ : MidpointJetEquations W C)
    (ha : ∀ x ∈ W, 0<amplitude (C x)) : ∃ x ∈ W, HasMaximizingSection C x := by
  obtain ⟨U,e,hU,hnU,hUW,he,hm⟩ := smooth_maximizing_direction_on_subpatch hW hn hC ha
  obtain ⟨p,hp,hgap⟩ := spherical_critical_value_gap hU hnU (hC.mono hUW)
  obtain ⟨H⟩ := maximizing_characteristics_at hU (hC.mono hUW) (hQ.mono hUW).quartic he
    (fun x hx ↦ ha x (hUW hx)) hm hp hgap
  obtain ⟨x,hx,hs⟩ := H.exists_section (hC.mono hUW) (hQ.mono hUW)
  exact ⟨x,hUW hx,hs⟩

/-- The fourth- and sixth-order midpoint equations force the maximum of
the cubic on the closed unit ball to be spatially constant. -/
theorem MidpointJetEquations.amplitude_constant {Ω : Set E} {C : E → Coeff}
    (hQ : MidpointJetEquations Ω C) (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) (hC : ContDiffOn ℝ ∞ C Ω) :
    ∃ a : ℝ, ∀ p ∈ Ω, amplitude (C p)=a := by
  apply amplitude_constant_of_dense_sections hΩ hconn hC
  apply dense_iff_inter_open.mpr
  intro U hU hnU
  let W := ((↑) : Ω → E) '' U
  have hW : IsOpen W := hΩ.isOpenMap_subtype_val _ hU
  have hWΩ : W ⊆ Ω := by rintro _ ⟨x,_,rfl⟩; exact x.property
  by_cases hz : ∃ x ∈ W, C x=0
  · obtain ⟨x,⟨u,hu,rfl⟩,he⟩ := hz
    exact ⟨u,hu,Or.inl he⟩
  · have ha (x : E) (hx : x ∈ W) : 0<amplitude (C x) := by
      refine lt_of_le_of_ne (amplitude_nonneg _) (fun h ↦ hz ⟨x,hx,?_⟩)
      exact (amplitude_eq_zero_iff _).mp h.symm
    obtain ⟨x,⟨u,hu,rfl⟩,hs⟩ := exists_maximizing_section_on_subpatch hW (hnU.image _)
      (hC.mono hWΩ) (hQ.mono hWΩ) ha
    exact ⟨u,hu,Or.inr hs⟩

theorem midpoint_amplitude_constant {Ω : Set E} {C : E → Coeff} (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hC : ContDiffOn ℝ ∞ C Ω) (hmid : LocalMidpointInvariance Ω C) :
    ∃ a : ℝ, ∀ p ∈ Ω, amplitude (C p)=a :=
  (MidpointJetEquations.of_midpoint hΩ hC hmid).amplitude_constant hΩ hconn hC

end EuclideanMidpointRigidity

