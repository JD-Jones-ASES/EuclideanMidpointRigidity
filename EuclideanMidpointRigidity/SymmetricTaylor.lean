module

public import EuclideanMidpointRigidity.SpatialTaylorBound
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic

/-! # Symmetric spatial Taylor coefficients

Permutation averaging preserves diagonal evaluation. It therefore gives the
same spatial Taylor polynomial and allows unordered spatial slots in the
Dirichlet recursion.
-/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

abbrev SpatialForm (U V : Type*) [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ℕ) :=
  ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ U) V

def symmetricPart {n : ℕ} (B : SpatialForm U V n) : SpatialForm U V n :=
  (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ •
    ∑ σ : Equiv.Perm (Fin n), B.domDomCongr σ

theorem symmetricPart_apply {n : ℕ} (B : SpatialForm U V n) (v : Fin n → U) :
    symmetricPart B v = (Fintype.card (Equiv.Perm (Fin n)):ℝ)⁻¹ •
      ∑ σ : Equiv.Perm (Fin n), B (v ∘ σ) := by
  classical
  simp [symmetricPart, ContinuousMultilinearMap.domDomCongr_apply, Function.comp_def]

theorem symmetricPart_perm {n : ℕ} (B : SpatialForm U V n) (v : Fin n → U)
    (τ : Equiv.Perm (Fin n)) : symmetricPart B (v ∘ τ) = symmetricPart B v := by
  classical
  rw [symmetricPart_apply, symmetricPart_apply]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ : Equiv.Perm (Fin n) ↦ B (v ∘ σ))

theorem symmetricPart_diagonal {n : ℕ} (B : SpatialForm U V n) (v : U) :
    symmetricPart B (fun _ ↦ v) = B (fun _ ↦ v) := by
  rw [symmetricPart_apply]
  have hn : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [Function.comp_def, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hn]

def listForm (B : ∀ k, SpatialForm U V k) (vs : List U) : V :=
  symmetricPart (B vs.length) vs.get

private theorem perm_get_equiv {α : Type*} {xs ys : List α} (h : xs.Perm ys) :
    ∃ σ : Fin xs.length ≃ Fin ys.length, ∀ i, xs.get i = ys.get (σ i) := by
  induction h with
  | nil => exact ⟨Equiv.refl _, fun i ↦ Fin.elim0 i⟩
  | @cons x l l' _ ih =>
    obtain ⟨σ,hσ⟩ := ih
    let e := (finSuccEquiv l.length).trans (σ.optionCongr.trans (finSuccEquiv l'.length).symm)
    refine ⟨e,?_⟩
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [e]
    · simpa [e] using hσ j
  | swap a b l =>
    let σ : Equiv.Perm (Fin (l.length+2)) := Equiv.swap 0 1
    refine ⟨σ,?_⟩
    intro i
    refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ ?_) j) i
    · simp [σ]
    · simp [σ]
    · have h0 : k.succ.succ ≠ 0 := Fin.succ_ne_zero _
      have h1 : k.succ.succ ≠ 1 := by
        change k.succ.succ ≠ (0 : Fin (l.length+1)).succ
        exact fun h ↦ Fin.succ_ne_zero k (Fin.succ_inj.mp h)
      simp [σ, Equiv.swap_apply_of_ne_of_ne h0 h1]
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨σ,hσ⟩ := ih₁
    obtain ⟨τ,hτ⟩ := ih₂
    exact ⟨σ.trans τ, fun i ↦ (hσ i).trans (hτ (σ i))⟩

private theorem form_congr (B : ∀ k, SpatialForm U V k) {n m : ℕ} (hlen : n=m)
    (u : Fin n → U) (v : Fin m → U) (σ : Fin n ≃ Fin m) (hσ : ∀ i, u i = v (σ i)) :
    symmetricPart (B n) u = symmetricPart (B m) v := by
  subst m
  exact (congrArg (symmetricPart (B n)) (funext hσ)).trans
    (symmetricPart_perm _ _ σ)

theorem listForm_perm (B : ∀ k, SpatialForm U V k) {xs ys : List U} (h : xs.Perm ys) :
    listForm B xs = listForm B ys := by
  obtain ⟨σ,hσ⟩ := perm_get_equiv h
  exact form_congr B h.length_eq xs.get ys.get σ hσ

end EuclideanMidpointRigidity
