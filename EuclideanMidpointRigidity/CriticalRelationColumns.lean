module

public import EuclideanMidpointRigidity.CriticalValuePolynomial
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Finite linear systems representing critical-value relations -/

@[expose] public section
noncomputable section
open Set
namespace EuclideanMidpointRigidity

/-- The lower powers and finite monomial multiples of the partial derivatives. -/
abbrev CriticalColumn (n N : ℕ) (S : Finset (Fin n →₀ ℕ)) := Fin N ⊕ (Fin n × S)

def criticalColumn {k : Type*} [CommRing k] {n N : ℕ} {S : Finset (Fin n →₀ ℕ)}
    (f : MvPolynomial (Fin n) k) : CriticalColumn n N S → MvPolynomial (Fin n) k
  | .inl i => f^(i:ℕ)
  | .inr (j,a) => MvPolynomial.monomial a.val 1 * MvPolynomial.pderiv j f

private theorem coefficients_on_support {k : Type*} [CommRing k] {n : ℕ} (p : MvPolynomial (Fin n) k)
    (S : Finset (Fin n →₀ ℕ)) (hs : p.support ⊆ S) :
    ∑ α : S, (p.coeff α.val) • MvPolynomial.monomial α.val 1=p := by
  classical
  simp only [MvPolynomial.smul_monomial,smul_eq_mul,mul_one]
  calc
    _ = ∑ α ∈ S, MvPolynomial.monomial α (p.coeff α) :=
      Finset.sum_coe_sort S (fun α ↦ MvPolynomial.monomial α (p.coeff α))
    _ = ∑ α ∈ p.support, MvPolynomial.monomial α (p.coeff α) := by
      apply (Finset.sum_subset hs ?_).symm
      intro x _ hx
      simp [MvPolynomial.notMem_support_iff.mp hx]
    _ = _ := MvPolynomial.support_sum_monomial_coeff p

private theorem monic_value_expansion {k : Type*} [Field k] {n : ℕ} {m : Polynomial k}
    (hm : m.Monic) (f : MvPolynomial (Fin n) k) :
    Polynomial.aeval f m = (∑ j : Fin m.natDegree, m.coeff j • f^(j:ℕ))+f^m.natDegree := by
  have h := congrArg (Polynomial.aeval f) m.as_sum_range_C_mul_X_pow
  rw [map_sum,Finset.sum_range_succ] at h
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ m.coeff j • f^j) m.natDegree]
  simpa only [map_mul,map_pow,Polynomial.aeval_C,Polynomial.aeval_X,hm.coeff_natDegree,map_one,
    one_mul,MvPolynomial.smul_eq_C_mul,MvPolynomial.algebraMap_eq] using h

/-- The degree and supporting monomials range over a countable index set
even though the coefficients in the relation may be arbitrary real numbers. -/
theorem exists_critical_column_relation {k : Type} [Field k] [CharZero k] {n : ℕ}
    (f : MvPolynomial (Fin n) k) :
    ∃ (N : ℕ) (S : Finset (Fin n →₀ ℕ)) (v : CriticalColumn n N S → k),
      ∑ j, v j • criticalColumn f j=f^N := by
  classical
  obtain ⟨m,hm,hI⟩ := exists_monic_critical_relation f
  let grad := fun i : Fin n ↦ MvPolynomial.pderiv i f
  obtain ⟨b,he⟩ := (Submodule.mem_span_range_iff_exists_fun (R := MvPolynomial (Fin n) k) (v := grad)).mp hI
  let S := Finset.univ.biUnion fun i ↦ (b i).support
  have hS (i : Fin n) : (b i).support ⊆ S :=
    Finset.subset_biUnion_of_mem (fun j : Fin n ↦ (b j).support) (Finset.mem_univ i)
  let v : CriticalColumn n m.natDegree S → k := Sum.elim (fun j ↦ -m.coeff j) (fun s ↦ (b s.1).coeff s.2.val)
  refine ⟨m.natDegree,S,v,?_⟩
  have hgrad (i : Fin n) :
      (∑ α : S, (b i).coeff α.val • (MvPolynomial.monomial α.val 1 * grad i)) = b i*grad i := by
    calc
      _ = (∑ α : S, (b i).coeff α.val • MvPolynomial.monomial α.val 1)*grad i := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun α _ ↦ (smul_mul_assoc _ _ _).symm
      _ = _ := by rw [coefficients_on_support (b i) S (hS i)]
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [v,Sum.elim_inl,Sum.elim_inr,criticalColumn,neg_smul,Finset.sum_neg_distrib]
  change -(∑ j : Fin m.natDegree, m.coeff j • f^(j:ℕ))+
    (∑ i : Fin n, ∑ α : S, (b i).coeff α.val • (MvPolynomial.monomial α.val 1*grad i))=f^m.natDegree
  simp_rw [hgrad]
  change ∑ i, b i*grad i=Polynomial.aeval f m at he
  rw [he,monic_value_expansion hm]
  abel

end EuclideanMidpointRigidity

