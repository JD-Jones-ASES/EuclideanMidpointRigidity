module

public import EuclideanMidpointRigidity.FieldDifferential
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.FiniteType

/-! # A polynomial relation for all critical values -/

@[expose] public section
noncomputable section
open Algebra KaehlerDifferential
namespace EuclideanMidpointRigidity

variable {k : Type} [Field k] [CharZero k] {n : ℕ}
local notation "R" => MvPolynomial (Fin n) k

/-- The ideal of formal partial derivatives of a polynomial. -/
def gradientIdeal (f : R) : Ideal R := Ideal.span (Set.range fun i ↦ MvPolynomial.pderiv i f)

omit [CharZero k] in
private theorem differential_at_critical (L : Type) [Field L] [Algebra k L] [Algebra R L]
    [IsScalarTower k R L] (f : R) (h : ∀ i, algebraMap R L (MvPolynomial.pderiv i f)=0) :
    D k L (algebraMap R L f)=0 := by
  let B := mvPolynomialBasis k (Fin n)
  have hs := congrArg (KaehlerDifferential.map k k R L) (B.sum_repr (D k R f))
  rw [map_D] at hs
  rw [← hs,map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_smul,← IsScalarTower.algebraMap_smul L]
  simp only [B,mvPolynomialBasis_repr_apply,h,zero_smul]

private theorem relation_at_prime (f : R) (P : Ideal R) [P.IsPrime] (hP : gradientIdeal f ≤ P) :
    ∃ m : Polynomial k, m.Monic ∧ Polynomial.aeval f m ∈ P := by
  let A := R ⧸ P
  let L := FractionRing A
  let _ : Algebra.EssFiniteType A L := Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors A)
  let _ : Algebra.EssFiniteType k L := Algebra.EssFiniteType.comp k A L
  have hzero (i : Fin n) : algebraMap R L (MvPolynomial.pderiv i f)=0 := by
    rw [IsScalarTower.algebraMap_apply R A L]
    have hq : algebraMap R A (MvPolynomial.pderiv i f)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (hP (Ideal.subset_span (Set.mem_range_self i)))
    rw [hq,map_zero]
  have halg := algebraic_of_differential_zero k L (differential_at_critical L f hzero)
  obtain ⟨m,hm,hval⟩ := halg.isIntegral
  refine ⟨m,hm,Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  apply (IsFractionRing.injective A L)
  change algebraMap A L (algebraMap R A (Polynomial.aeval f m))=algebraMap A L 0
  rw [← IsScalarTower.algebraMap_apply,map_zero,← Polynomial.aeval_algebraMap_apply]
  exact hval

/-- A monic polynomial in the value of the original polynomial lies in the
gradient ideal. This also covers positive-dimensional critical loci. -/
theorem exists_monic_critical_relation (f : R) :
    ∃ m : Polynomial k, m.Monic ∧ Polynomial.aeval f m ∈ gradientIdeal f := by
  classical
  let I := gradientIdeal f
  let _ : Fintype I.minimalPrimes := (Ideal.finite_minimalPrimes_of_isNoetherianRing R I).fintype
  have hloc (P : I.minimalPrimes) :
      ∃ m : Polynomial k, m.Monic ∧ Polynomial.aeval f m ∈ P.val := by
    let _ : P.val.IsPrime := P.property.1.1
    exact relation_at_prime f P.val P.property.1.2
  choose m hm hv using hloc
  let s := ∏ P, m P
  have hs : s.Monic := Polynomial.monic_prod_of_monic _ _ fun i _ ↦ hm i
  have hrad : Polynomial.aeval f s ∈ I.radical := by
    rw [← Ideal.sInf_minimalPrimes,Ideal.mem_sInf]
    intro P hP
    let i : I.minimalPrimes := ⟨P,hP⟩
    apply P.mem_of_dvd _ (hv i)
    apply map_dvd (Polynomial.aeval f)
    exact Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  obtain ⟨r,hr⟩ := hrad
  exact ⟨s^r,hs.pow r,by simpa only [map_pow] using hr⟩

end EuclideanMidpointRigidity

