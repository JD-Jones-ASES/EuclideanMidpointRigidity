module

public import EuclideanMidpointRigidity.SectionAmplitude
public import EuclideanMidpointRigidity.MaximumEnvelope

/-! # From maximizing sections to the global maximum envelope -/

@[expose] public section
noncomputable section
open Set Filter Metric
open scoped ContDiff InnerProductSpace Topology
namespace EuclideanMidpointRigidity

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

namespace LiftedSection
variable (S : LiftedSection d)

theorem stationaryMaximum {p : E} (hp : p ∈ S.domain) (hm : ∀ᶠ q in 𝓝 p, S.Maximizes q) :
    StationaryMaximum S.field p := by
  have he := S.unit p hp
  have ha := amplitude_eq_of_unit_max he (S.positive p hp).le hm.self_of_nhds rfl
  refine ⟨S.axis p,by simp [mem_closedBall,dist_zero_right,he],?_,?_⟩
  · rw [ha,directionProfile_apply]
    rfl
  · intro l
    have h := sectionValue_gradient S.isOpen S.smooth S.smoothAxis S.unit hp (S.critical p hp) l
    change ⟪gradient S.a p,l⟫_ℝ = _ at h
    rw [S.gradient_zero hp hm,inner_zero_left] at h
    simpa only [directionProfile_apply] using h.symm

end LiftedSection

/-- A local maximizing section for the specified cubic field. -/
def HasMaximizingSection (C : E → Coeff) (p : E) : Prop :=
  ∃ S : LiftedSection d, S.field=C ∧ p ∈ S.domain ∧ ∀ q ∈ S.domain, S.Maximizes q

theorem HasMaximizingSection.stationary {C : E → Coeff} {p : E} (h : HasMaximizingSection C p) :
    StationaryMaximum C p := by
  obtain ⟨S,rfl,hp,hm⟩ := h
  exact S.stationaryMaximum hp ((show ∀ᶠ q in 𝓝 p, q ∈ S.domain from S.isOpen.mem_nhds hp).mono hm)

/-- Density is needed only at nonzero coefficients. The closed unit ball
provides a stationary support at every zero coefficient. -/
theorem amplitude_constant_of_dense_sections {Ω : Set E} {C : E → Coeff}
    (hΩ : IsOpen Ω) (hc : IsPreconnected Ω) (hC : ContDiffOn ℝ ∞ C Ω)
    (hd : Dense {p : Ω | C p=0 ∨ HasMaximizingSection C p}) :
    ∃ a : ℝ, ∀ p ∈ Ω, amplitude (C p)=a := by
  apply amplitude_constant_of_dense_stationaryMaximum hΩ hc hC (hd.mono ?_)
  intro p hp
  rcases hp with h|h
  · exact stationaryMaximum_of_amplitude_zero ((amplitude_eq_zero_iff _).mpr h)
  · exact h.stationary

end EuclideanMidpointRigidity

