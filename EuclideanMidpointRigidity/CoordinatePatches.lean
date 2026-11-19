module

public import EuclideanMidpointRigidity.LimitingCoordinates
public import EuclideanMidpointRigidity.ScaledPolynomialSystem

/-! # Simultaneous coordinate equations on an open parameter patch -/

@[expose] public section
noncomputable section
open Set Filter Polynomial
open scoped Topology
namespace EuclideanMidpointRigidity.SmoothPolynomial

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {W : Set E} {n : ℕ}
local notation "A" => SmoothCoefficient W

/-- Every convergent sequence of regularized solutions satisfies the same
finite family of limiting coordinate equations on one open subpatch. -/
theorem regularized_coordinate_patch (g : Fin n → MvPolynomial (Fin n) A) (k : ℕ)
    (hg : ∀ i, (g i).totalDegree≤k) (hW : IsOpen W) (hn : W.Nonempty) :
    ∃ (V : Set E) (q : Fin n → Polynomial A), IsOpen V ∧ V.Nonempty ∧ V ⊆ W ∧
      (∀ x ∈ V, ∀ i, fiber (q i) x≠0) ∧
      ∀ x ∈ V, ∀ (t : ℕ → ℝ) (z : ℕ → Fin n → ℝ) (w : Fin n → ℝ),
        Tendsto t atTop (𝓝 0) → (∀ j, t j≠0) → (∀ i, Tendsto (fun j ↦ z j i) atTop (𝓝 (w i))) →
        (∀ j i, t j*(z j i)^(k+1)=(g i).eval₂ (evaluateCoefficient x) (z j)) →
        ∀ i, (fiber (q i) x).eval (w i)=0 := by
  classical
  choose H hmon hrel using regularized_coordinate_relation k g hg
  let Q := fun (i : Fin n) (q : Polynomial A) (x : E) ↦ fiber q x≠0 ∧
    ∀ (t z : ℕ → ℝ) (w : ℝ), Tendsto t atTop (𝓝 0) → Tendsto z atTop (𝓝 w) →
      (∀ j, t j≠0) →
      (∀ j, (H i).eval₂ (Polynomial.eval₂RingHom (evaluateCoefficient x) (t j)) (t j*z j)=0) →
      (fiber q x).eval w=0
  have aux (S : Finset (Fin n)) : ∃ (V : Set E) (q : Fin n → Polynomial A),
      IsOpen V ∧ V.Nonempty ∧ V ⊆ W ∧ ∀ i ∈ S, ∀ x ∈ V, Q i (q i) x := by
    induction S using Finset.induction_on with
    | empty => exact ⟨W,0,hW,hn,Subset.rfl,by simp⟩
    | @insert i S hi ih =>
      obtain ⟨U,q,hU,hnU,hUW,hq⟩ := ih
      obtain ⟨V,q',hV,hnV,hVU,hne,hl⟩ := limiting_coordinate_polynomial (hmon i) hU hnU hUW
      refine ⟨V,Function.update q i q',hV,hnV,hVU.trans hUW,?_⟩
      intro a ha x hx
      rcases Finset.mem_insert.mp ha with rfl | h
      · rw [Function.update_self]
        exact ⟨hne _ hx,hl _ hx⟩
      · have hai : a≠i := by rintro rfl; exact hi h
        rw [Function.update_of_ne hai]
        exact hq a h x (hVU hx)
  obtain ⟨V,q,hV,hnV,hVW,hq⟩ := aux Finset.univ
  refine ⟨V,q,hV,hnV,hVW,fun x hx i ↦ (hq i (Finset.mem_univ i) x hx).1,?_⟩
  intro x hx t z w ht ht₀ hz he i
  apply (hq i (Finset.mem_univ i) x hx).2 t (fun j ↦ z j i) (w i) ht (hz i) ht₀
  exact fun j ↦ hrel i (evaluateCoefficient x) (t j) (z j) (he j)

end EuclideanMidpointRigidity.SmoothPolynomial

