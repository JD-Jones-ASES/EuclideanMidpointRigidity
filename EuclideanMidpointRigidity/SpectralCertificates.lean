module

public import EuclideanMidpointRigidity.SpectralIntervals

/-! # Spectral certificates for all nonnegative gradient ratios -/

@[expose] public section
namespace EuclideanMidpointRigidity.Spectral
open IntervalPolynomial

/-- The intervals cover the entire range of `s = r/(1+r)`. At a common
endpoint either adjacent certificate proves the required signs. -/
theorem certificate_cover {r : ℝ} (hr : 0 ≤ r) :
    ∃ w : MixedCertificate, w.verify = true ∧
      w.ratio.lo*(1+r) ≤ r ∧ r ≤ w.ratio.hi*(1+r) := by
  by_cases h₁ : r ≤ ((1/4:ℚ):ℝ)*(1+r)
  · exact ⟨case1,case1_verified,by simpa [case1] using hr,h₁⟩
  by_cases h₂ : r ≤ ((23/50:ℚ):ℝ)*(1+r)
  · exact ⟨case2,case2_verified,(le_of_not_ge h₁),h₂⟩
  by_cases h₃ : r ≤ ((14/25:ℚ):ℝ)*(1+r)
  · exact ⟨case3,case3_verified,(le_of_not_ge h₂),h₃⟩
  by_cases h₄ : r ≤ ((31/50:ℚ):ℝ)*(1+r)
  · exact ⟨case4,case4_verified,(le_of_not_ge h₃),h₄⟩
  by_cases h₅ : r ≤ ((17/25:ℚ):ℝ)*(1+r)
  · exact ⟨case5,case5_verified,(le_of_not_ge h₄),h₅⟩
  by_cases h₆ : r ≤ ((18/25:ℚ):ℝ)*(1+r)
  · exact ⟨case6,case6_verified,(le_of_not_ge h₅),h₆⟩
  by_cases h₇ : r ≤ ((77/100:ℚ):ℝ)*(1+r)
  · exact ⟨case7,case7_verified,(le_of_not_ge h₆),h₇⟩
  by_cases h₈ : r ≤ ((81/100:ℚ):ℝ)*(1+r)
  · exact ⟨case8,case8_verified,(le_of_not_ge h₇),h₈⟩
  exact ⟨case9,case9_verified,(le_of_not_ge h₈),by simp [case9]⟩

/-- A weighted row rules out every assignment in the regular spectral chart.
The index type can have any finite cardinality, including zero. -/
theorem mixed_spectral_exclusion {r : ℝ} (hr : 0 ≤ r) :
    ∃ w : MixedCertificate, w.verify = true ∧
      ∀ {ι : Type} [Fintype ι] (x L H : ι → ℝ) (h σ : ℝ),
      (∀ i, -1 ≤ x i ∧ x i ≤ 1/2) → 0 ≤ h → 0 ≤ σ →
      ¬ (∑ i, w.combined.atChannel (x i) (L i) (H i)) + eval w.combined.internal r * h ≤
        eval w.combined.rhs r + (w.weights.getLastD 0 : ℝ)*σ := by
  obtain ⟨w,hw,hl,hu⟩ := certificate_cover hr
  refine ⟨w,hw,?_⟩
  intro ι inst x L H h σ hx hh hσ
  exact MixedCertificate.excludes hw hx hr hh hσ hl hu

end EuclideanMidpointRigidity.Spectral
