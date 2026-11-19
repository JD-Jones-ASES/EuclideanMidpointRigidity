module

public import EuclideanMidpointRigidity.SixthCoefficients
public import EuclideanMidpointRigidity.JetCalculus

/-! # The coefficient functions solve their signed differential equations -/

@[expose] public section
namespace EuclideanMidpointRigidity.Jet

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def pathTerm (σ : ℚ) (n : ℕ) : TimePolynomial := (signedPaths σ)[n]?.getD []

theorem dirichlet_equations {σ : ℚ} (hσ : σ = 1 ∨ σ = -1)
    {n : ℕ} (hn : n ∈ [2,3,4,5,6]) (f : Tree → V) :
    let p := pathTerm σ n
    value p f (-1) = 0 ∧ value p f 1 = 0 ∧
    ∀ t : ℝ, HasDerivAt (value p f) (value (differentiate p) f t) t ∧
      HasDerivAt (value (differentiate p) f) (value (forcing σ (signedPaths σ) n) f t) t := by
  have hb : boundaryEquations σ = true := hσ.elim
    (fun h ↦ h ▸ positive_boundary_equations) (fun h ↦ h ▸ negative_boundary_equations)
  unfold boundaryEquations at hb
  have hall := List.all_eq_true.mp hb n hn
  simp only [Bool.and_eq_true] at hall
  obtain ⟨⟨hode,hl⟩,hr⟩ := hall
  have hl' := same_sound hl f 0
  have hr' := same_sound hr f 0
  simp only [value_atTime, Rat.cast_neg, Rat.cast_one] at hl' hr'
  refine ⟨hl',hr',fun t ↦ ⟨hasDerivAt_value _ _ _,?_⟩⟩
  rw [← same_sound hode f t]
  exact hasDerivAt_value _ _ _

/-- The degree-six midpoint of the two coefficient paths is the complete
twenty-seven-term expression. -/
theorem summed_sixth_midpoint (f : Tree → V) :
    value (pathTerm 1 6) f 0 + value (pathTerm (-1) 6) f 0 =
      value affineSixth f 0 + value higherSixth f 0 := by
  have h := sixth_value f
  simpa only [midpointCoefficient, pathTerm, value_collect, value_append, value_atTime,
    Rat.cast_zero] using h

end EuclideanMidpointRigidity.Jet
