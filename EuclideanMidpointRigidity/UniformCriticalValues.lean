module

public import EuclideanMidpointRigidity.SmoothPolynomialFamily
public import EuclideanMidpointRigidity.CriticalRelationColumns
public import EuclideanMidpointRigidity.CertificateSelection
public import Mathlib.Data.Finsupp.Encodable

/-! # A uniform equation for critical values on a spatial subpatch -/

@[expose] public section
noncomputable section
open Set
open scoped ContDiff
namespace EuclideanMidpointRigidity.SmoothPolynomial

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [BaireSpace X]
variable {W : Set X} {n : ℕ}
local notation "R" => MvPolynomial (Fin n) (SmoothCoefficient W)

omit [BaireSpace X] in
private theorem specialize_column (f : R) (x : X) {N : ℕ} {S : Finset (Fin n →₀ ℕ)}
    (j : CriticalColumn n N S) :
    specialize (criticalColumn f j) x=criticalColumn (specialize f x) j := by
  rcases j with j|⟨i,a⟩ <;> simp [criticalColumn]

/-- All critical values, including saddle values, satisfy one monic equation
with smooth coefficients on some nonempty open part of any given open domain. -/
theorem critical_values_on_subpatch (f : R) (hW : IsOpen W) (hn : W.Nonempty) :
    ∃ (V : Set X) (N : ℕ) (c : Fin N → X → ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ W ∧
      (∀ j, ContDiffOn ℝ ∞ (c j) V) ∧ ∀ x ∈ V, ∀ z : Fin n → ℝ,
        (∀ i, MvPolynomial.eval z (MvPolynomial.pderiv i (specialize f x))=0) →
        (MvPolynomial.eval z (specialize f x))^N=∑ j, c j x*(MvPolynomial.eval z (specialize f x))^(j:ℕ) := by
  classical
  let τ := ℕ × Finset (Fin n →₀ ℕ)
  let J := fun k : τ ↦ CriticalColumn n k.1 k.2
  let m := fun k ↦ Fintype.card (J k)
  let e := fun k ↦ Fintype.equivFin (J k)
  let A := fun (k : τ) (j : Fin (m k)) (s : Fin n →₀ ℕ) (x : X) ↦
    (specialize (criticalColumn f ((e k).symm j)) x).coeff s
  let b := fun (k : τ) (s : Fin n →₀ ℕ) (x : X) ↦ (specialize (f^k.1) x).coeff s
  have hA (k : τ) (j : Fin (m k)) (s : Fin n →₀ ℕ) : ContDiffOn ℝ ∞ (A k j s) W :=
    smooth_coeff (criticalColumn f ((e k).symm j)) s
  have hb (k : τ) (s : Fin n →₀ ℕ) : ContDiffOn ℝ ∞ (b k s) W := smooth_coeff (f^k.1) s
  have hs (x : X) (_ : x ∈ W) :
      ∃ k, ∃ v : Fin (m k) → ℝ, ∀ s, ∑ j, v j*A k j s x=b k s x := by
    obtain ⟨N,S,v,hv⟩ := exists_critical_column_relation (specialize f x)
    let k : τ := (N,S)
    refine ⟨k,fun j ↦ v ((e k).symm j),?_⟩
    intro s
    have h := congrArg (fun g : MvPolynomial (Fin n) ℝ ↦ g.coeff s) hv
    simp only [MvPolynomial.coeff_sum,MvPolynomial.coeff_smul,smul_eq_mul] at h
    change (∑ j, v ((e k).symm j)*(specialize (criticalColumn f ((e k).symm j)) x).coeff s)=
      (specialize (f^N) x).coeff s
    simp only [specialize_column,specialize_pow]
    exact ((e k).symm.sum_comp (fun j ↦ v j*(criticalColumn (specialize f x) j).coeff s)).trans h
  obtain ⟨k,V,v,hV,hVn,hVW,hv,hrel⟩ := smooth_certificate_on_subpatch m A b hW hn hA hb hs
  let c := fun (j : J k) ↦ v (e k j)
  refine ⟨V,k.1,fun j ↦ c (.inl j),hV,hVn,hVW,fun j ↦ hv _,?_⟩
  intro x hx z hz
  let g := specialize f x
  have hcert : (∑ j : J k, c j x • criticalColumn g j)=g^k.1 := by
    apply MvPolynomial.ext
    intro s
    simp only [MvPolynomial.coeff_sum,MvPolynomial.coeff_smul,smul_eq_mul]
    have h := hrel x hx s
    dsimp only [A,b] at h
    simp only [specialize_column,specialize_pow] at h
    rw [← h]
    simpa only [Equiv.symm_apply_apply,c] using
      (e k).sum_comp (fun j ↦ v j x*(criticalColumn g ((e k).symm j)).coeff s)
  have h := congrArg (MvPolynomial.eval z) hcert
  change ∀ i, MvPolynomial.eval z (MvPolynomial.pderiv i g)=0 at hz
  rw [map_sum,Fintype.sum_sum_type,Fintype.sum_prod_type,map_pow] at h
  simp only [criticalColumn,MvPolynomial.smul_eq_C_mul,map_mul,MvPolynomial.eval_C,map_pow,hz,
    mul_zero,Finset.sum_const_zero,add_zero] at h
  exact h.symm

end EuclideanMidpointRigidity.SmoothPolynomial

