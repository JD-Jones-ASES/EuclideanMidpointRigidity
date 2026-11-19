module

public import EuclideanMidpointRigidity.RealizedChords

/-! # Realization of both oriented maximizing chords for all sufficiently small separations -/

public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d

theorem chordEnds_swap (p u : E) (h : ℝ) : (chordEnds p u h).swap=chordEnds p (-u) h := by
  apply Prod.ext <;> simp [chordEnds,smul_neg,neg_smul]

theorem LiftedSection.eventually_realized_chords (S : LiftedSection d) {p : E} (hp : p ∈ S.domain)
    (hm : ∀ q ∈ S.domain, S.Maximizes q) (D : OrientedEndpointChart S.field p) :
    let u := (S.a p)⁻¹ • S.axis p
    ∀ᶠ h in 𝓝[>] (0:ℝ), chordEnds p u h ∈ D.domain ∧
      RealizedChord S.domain S.field 1 p u h (S.axisSlice p) D.plus ∧
      RealizedChord S.domain S.field (-1) p (-u) h (S.axisSlice p) D.minus := by
  let u := (S.a p)⁻¹ • S.axis p
  obtain ⟨R,hR,hs⟩ := S.small_axial_chords hp hm
  let ρ := min D.plusRadius D.minusRadius
  have hρ : 0<ρ := lt_min D.positivePlus D.positiveMinus
  have h₁ : Continuous (fun h : ℝ ↦ h*‖u‖) := continuous_id.mul continuous_const
  have h₂ : Continuous (fun h : ℝ ↦ (Real.exp (2*h)-1)*‖u‖) := by fun_prop
  have h₃ : Continuous (fun h : ℝ ↦ chordEnds p u h) := by unfold chordEnds; fun_prop
  have hnear₁ : ∀ᶠ h in 𝓝 (0:ℝ), h*‖u‖<ρ := h₁.continuousAt (Iio_mem_nhds (by simpa using hρ : 0*‖u‖<ρ))
  have hnear₂ : ∀ᶠ h in 𝓝 (0:ℝ), (Real.exp (2*h)-1)*‖u‖<ρ :=
    h₂.continuousAt (Iio_mem_nhds (by simpa using hρ : (Real.exp (2*0)-1)*‖u‖<ρ))
  have hD : ∀ᶠ h in 𝓝 (0:ℝ), chordEnds p u h ∈ D.domain :=
    h₃.continuousAt (D.isOpen.mem_nhds (by simpa [chordEnds] using D.center))
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hR),
    mem_nhdsWithin_of_mem_nhds hnear₁,mem_nhdsWithin_of_mem_nhds hnear₂,mem_nhdsWithin_of_mem_nhds hD] with h hh hsmall hpos hvel hd
  have hc := hs h ⟨hh,hsmall⟩
  have hplus : AxialChord S.domain S.field 1 p u h (S.axisSlice p) := by simpa only [one_mul,u] using hc 1 (Or.inl rfl)
  have hminus : AxialChord S.domain S.field (-1) p (-u) h (S.axisSlice p) := by simpa [u,neg_smul] using hc (-1) (Or.inr rfl)
  have hP := hplus.short (hpos.trans_le (min_le_left _ _)) (hvel.trans_le (min_le_left _ _))
  have hM := hminus.short (by simpa only [norm_neg] using hpos.trans_le (min_le_right _ _))
    (by simpa only [norm_neg] using hvel.trans_le (min_le_right _ _))
  refine ⟨hd,⟨hplus,D.plusDomain _ hd,D.plusUnique _ hd _ _ hP⟩,⟨hminus,?_,?_⟩⟩
  · rw [← chordEnds_swap]; exact D.minusDomain _ hd
  · have hq : IsShortGeodesic S.field (-1) p D.minusRadius (chordEnds p u h).2 (chordEnds p u h).1
        (axialPosition p (-u) h) (axialVelocity (-u) h) := by simpa only [chordEnds,smul_neg,neg_smul,neg_neg] using hM
    rw [← chordEnds_swap]
    exact D.minusUnique _ hd _ _ hq

end EuclideanMidpointRigidity

