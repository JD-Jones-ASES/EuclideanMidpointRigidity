module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Tactic

/-! # Smooth solutions of parameter-dependent linear equations on open patches -/

public section
noncomputable section
open Set
open scoped ContDiff
namespace EuclideanMidpointRigidity

private theorem sum_row_sub {n : ℕ} (c a b : Fin n → ℝ) (r : ℝ) :
    ∑ j, c j*(a j-r*b j) = (∑ j, c j*a j)-r*∑ j, c j*b j := by
  simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- On a smaller nonempty open set a pointwise-solvable smooth linear
system has a smooth solution. The number of unknowns is finite; the
collection of scalar equations may be infinite. -/
theorem smooth_linear_solution_on_subpatch {X I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (m : ℕ) (A : Fin m → I → X → ℝ) (b : I → X → ℝ) {W : Set X}
    (hW : IsOpen W) (hn : W.Nonempty) (hA : ∀ j i, ContDiffOn ℝ ∞ (A j i) W)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) W)
    (hs : ∀ x ∈ W, ∃ v : Fin m → ℝ, ∀ i, ∑ j, v j*A j i x=b i x) :
    ∃ (V : Set X) (v : Fin m → X → ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ W ∧
      (∀ j, ContDiffOn ℝ ∞ (v j) V) ∧ ∀ x ∈ V, ∀ i, ∑ j, v j x*A j i x=b i x := by
  classical
  induction m generalizing b W with
  | zero =>
    refine ⟨W,fun _ _ ↦ 0,hW,hn,Subset.rfl,fun _ ↦ contDiffOn_const,?_⟩
    intro x hx i
    obtain ⟨v,hv⟩ := hs x hx
    simpa using hv i
  | succ m ih =>
    by_cases h : ∀ x ∈ W, ∀ j i, A j i x=0
    · refine ⟨W,fun _ _ ↦ 0,hW,hn,Subset.rfl,fun _ ↦ contDiffOn_const,?_⟩
      intro x hx i
      obtain ⟨v,hv⟩ := hs x hx
      simpa [h x hx] using hv i
    push Not at h
    obtain ⟨p,hp,j₀,i₀,hpiv⟩ := h
    let U := W ∩ (A j₀ i₀) ⁻¹' ({0}ᶜ : Set ℝ)
    have hU : IsOpen U := (hA j₀ i₀).continuousOn.isOpen_inter_preimage hW isClosed_singleton.isOpen_compl
    have hUW : U ⊆ W := inter_subset_left
    have hne (x : X) (hx : x ∈ U) : A j₀ i₀ x≠0 := hx.2
    let r := fun i x ↦ A j₀ i x/A j₀ i₀ x
    have hr (i : I) : ContDiffOn ℝ ∞ (r i) U :=
      ((hA j₀ i).mono hUW).div ((hA j₀ i₀).mono hUW) hne
    let E := fun (j : Fin m) i x ↦ A (j₀.succAbove j) i x-r i x*A (j₀.succAbove j) i₀ x
    let f := fun i x ↦ b i x-r i x*b i₀ x
    have hE (j : Fin m) (i : I) : ContDiffOn ℝ ∞ (E j i) U :=
      ((hA _ i).mono hUW).sub ((hr i).mul ((hA _ i₀).mono hUW))
    have hf (i : I) : ContDiffOn ℝ ∞ (f i) U := ((hb i).mono hUW).sub ((hr i).mul ((hb i₀).mono hUW))
    have hsolve (x : X) (hx : x ∈ U) : ∃ v : Fin m → ℝ, ∀ i, ∑ j, v j*E j i x=f i x := by
      obtain ⟨v,hv⟩ := hs x (hUW hx)
      refine ⟨fun j ↦ v (j₀.succAbove j),?_⟩
      intro i
      have eq₁ := hv i
      have eq₀ := hv i₀
      rw [Fin.sum_univ_succAbove _ j₀] at eq₁ eq₀
      have hcancel : r i x*A j₀ i₀ x=A j₀ i x := div_mul_cancel₀ _ (hne x hx)
      dsimp only [E,f]
      rw [sum_row_sub]
      linear_combination eq₁ - r i x*eq₀ + v j₀*hcancel
    obtain ⟨V,v,hV,hVn,hVU,hv,hsol⟩ := ih E f hU ⟨p,hp,hpiv⟩ hE hf hsolve
    let t := fun x ↦ ∑ j, v j x*A (j₀.succAbove j) i₀ x
    let y := fun x ↦ (b i₀ x-t x)/A j₀ i₀ x
    let c : Fin (m+1) → X → ℝ := j₀.insertNth y v
    have hVW := hVU.trans hUW
    have ht : ContDiffOn ℝ ∞ t V := ContDiffOn.sum fun j _ ↦ (hv j).mul ((hA _ _).mono hVW)
    have hy : ContDiffOn ℝ ∞ y V := (((hb i₀).mono hVW).sub ht).div
      ((hA j₀ i₀).mono hVW) (fun x hx ↦ hne x (hVU hx))
    refine ⟨V,c,hV,hVn,hVW,?_,?_⟩
    · exact j₀.succAboveCases (by simpa [c] using hy) (fun j ↦ by simpa [c] using hv j)
    · intro x hx i
      have eq := hsol x hx i
      dsimp only [E,f] at eq
      rw [sum_row_sub] at eq
      change (∑ j, v j x*A (j₀.succAbove j) i x)-r i x*t x=b i x-r i x*b i₀ x at eq
      rw [Fin.sum_univ_succAbove _ j₀]
      simp only [c,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
      have hcancel : y x*A j₀ i x=r i x*(b i₀ x-t x) := by dsimp only [y,r]; ring
      rw [hcancel]
      linarith only [eq]

end EuclideanMidpointRigidity

