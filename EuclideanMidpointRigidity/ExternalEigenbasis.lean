module

public import EuclideanMidpointRigidity.Basic
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! # Extending prescribed orthonormal eigenvectors of a symmetric operator -/

@[expose] public section
noncomputable section
open Set Submodule
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity

theorem extend_orthonormal_eigenvectors {d : ℕ} {ι : Type*} [Fintype ι]
    (T : Space d →ₗ[ℝ] Space d) (hT : T.IsSymmetric) (f : ι → Space d) (a : ι → ℝ)
    (hf : Orthonormal ℝ f) (he : ∀ i, T (f i)=a i • f i) :
    ∃ (n : ℕ) (B : OrthonormalBasis (ι ⊕ Fin n) ℝ (Space d)) (s : Fin n → ℝ),
      (∀ i, B (.inl i)=f i) ∧ ∀ i, T (B (.inr i))=s i • B (.inr i) := by
  classical
  let P := span ℝ (range f)
  have hP : ∀ z ∈ P, T z ∈ P := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i,rfl⟩ := hx
      rw [he]
      exact P.smul_mem _ (subset_span (mem_range_self i))
    | zero => simp
    | add x y _ _ hx hy => simpa using P.add_mem hx hy
    | smul r x _ hx => simpa using P.smul_mem r hx
  have hi : ∀ z ∈ Pᗮ, T z ∈ Pᗮ := by
    intro z hz
    apply (P.mem_orthogonal _).2
    intro w hw
    rw [← hT w z]
    exact P.inner_right_of_mem_orthogonal (hP w hw) hz
  let n := Module.finrank ℝ Pᗮ
  let H := hT.restrict_invariant hi
  let V : OrthonormalBasis (Fin n) ℝ Pᗮ := H.eigenvectorBasis rfl
  let s : Fin n → ℝ := H.eigenvalues rfl
  let F : ι ⊕ Fin n → Space d := Sum.elim f (fun i ↦ (V i : Space d))
  have horth (i : ι) (j : Fin n) : ⟪f i,(V j : Space d)⟫_ℝ=0 :=
    P.inner_right_of_mem_orthogonal (subset_span (mem_range_self i)) (V j).property
  have hon : Orthonormal ℝ F := by
    apply orthonormal_iff_ite.mpr
    intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j => simpa [F] using orthonormal_iff_ite.mp hf i j
      | inr j => simpa [F] using horth i j
    | inr i =>
      cases j with
      | inl j => simpa [F] using (inner_eq_zero_symm.mp (horth j i))
      | inr j =>
        have h := orthonormal_iff_ite.mp V.orthonormal i j
        simpa [F,Submodule.coe_inner] using h
  let Q := span ℝ (range F)
  have hpq : P≤Q := Submodule.span_le.mpr (by
    rintro _ ⟨i,rfl⟩
    exact subset_span (mem_range_self (f := F) (Sum.inl i)))
  have hq : Pᗮ≤Q := by
    intro w hw
    let z : Pᗮ := ⟨w,hw⟩
    have h := congrArg (fun w : Pᗮ ↦ (w : Space d)) (V.sum_repr z)
    change (∑ i, V.repr z i • V i : Pᗮ).val=w at h
    rw [Submodule.coe_sum] at h
    rw [← h]
    exact Q.sum_mem fun i _ ↦ Q.smul_mem _ (subset_span (mem_range_self (f := F) (Sum.inr i)))
  have htop : ⊤≤Q := by rw [← P.isCompl_orthogonal.sup_eq_top]; exact sup_le hpq hq
  let B := OrthonormalBasis.mk hon htop
  have hB : ⇑B=F := OrthonormalBasis.coe_mk _ _
  refine ⟨n,B,s,fun i ↦ congrFun hB (.inl i),?_⟩
  intro i
  rw [congrFun hB (.inr i)]
  exact congrArg (fun w : Pᗮ ↦ (w : Space d)) (H.apply_eigenvectorBasis (n := n) rfl i)

end EuclideanMidpointRigidity
