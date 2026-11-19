module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic

/-! # Finite polynomial algebras from diagonal leading powers -/

@[expose] public section
noncomputable section
open Set MvPolynomial
namespace EuclideanMidpointRigidity

variable {R : Type} [CommRing R] {n : ℕ}
local notation "P" => MvPolynomial (Fin n) R

def powerReductionIdeal (m : ℕ) (g : Fin n → P) : Ideal P :=
  Ideal.span (Set.range fun i ↦ (MvPolynomial.X i)^m-g i)

/-- Reducing a power of any one variable strictly decreases total degree.
The residue classes of the monomials in the exponent box span the quotient. -/
theorem finite_power_reduction (m : ℕ) (g : Fin n → P) (hg : ∀ i, (g i).totalDegree<m) :
    Module.Finite R (P ⧸ powerReductionIdeal m g) := by
  classical
  let I := powerReductionIdeal m g
  let Q := P ⧸ I
  let f : P →ₐ[R] Q := Ideal.Quotient.mkₐ R I
  let mon := fun a : Fin n →₀ ℕ ↦ MvPolynomial.monomial a (1:R)
  let exp := fun u : Fin n → Fin m ↦ Finsupp.equivFunOnFinite.symm (fun i ↦ (u i : ℕ))
  let V : Submodule R Q := Submodule.span R (Set.range fun u ↦ f (mon (exp u)))
  have power (i : Fin n) : f (MvPolynomial.X i)^m=f (g i) := by
    apply sub_eq_zero.mp
    rw [← map_pow,← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
  let deg := fun a : Fin n →₀ ℕ ↦ ∑ i, a i
  have addDeg (a b : Fin n →₀ ℕ) : deg (a+b)=deg a+deg b := by simp [deg,Finset.sum_add_distrib]
  have small (i : Fin n) {a : Fin n →₀ ℕ} (ha : a ∈ (g i).support) : deg a<m := by
    have h := MvPolynomial.le_totalDegree ha
    rw [Finsupp.sum_fintype _ _ (by simp)] at h
    exact h.trans_lt (hg i)
  have inside (a : Fin n →₀ ℕ) : f (mon a) ∈ V := by
    induction a using (measure deg).wf.induction with
    | h a ih =>
      by_cases hbox : ∀ i, a i<m
      · apply Submodule.subset_span
        refine ⟨fun i ↦ ⟨a i,hbox i⟩,?_⟩
        exact congrArg (fun b ↦ f (mon b)) (Finsupp.ext fun _ ↦ rfl)
      push Not at hbox
      obtain ⟨i,hi⟩ := hbox
      let β := a-Finsupp.single i m
      have hle : Finsupp.single i m ≤ a := by
        intro j
        by_cases hji : i=j
        · subst j; simpa using hi
        · simp [hji]
      have heq : β+Finsupp.single i m=a := tsub_add_cancel_of_le hle
      have hdeg : deg β+m=deg a := by
        rw [← heq,addDeg]
        simp [deg]
      have split : mon a=mon β*(MvPolynomial.X i)^m := by
        rw [← heq]
        simp [mon,MvPolynomial.X_pow_eq_monomial,MvPolynomial.monomial_mul_monomial]
      rw [split,map_mul,map_pow,power,← map_mul]
      have hsum : mon β*g i=∑ b ∈ (g i).support, (g i).coeff b • mon (β+b) := by
        conv_lhs => rhs; rw [(g i).as_sum]
        simp only [Finset.mul_sum,mon,MvPolynomial.monomial_mul_monomial,one_mul,
          MvPolynomial.smul_monomial,smul_eq_mul,mul_one]
      rw [hsum,map_sum]
      apply Submodule.sum_mem
      intro b hb
      rw [map_smul]
      apply Submodule.smul_mem
      apply ih
      change deg (β+b)<deg a
      rw [addDeg,← hdeg]
      exact Nat.add_lt_add_left (small i hb) _
  have htop : V=⊤ := by
    apply top_unique
    intro x _
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
    change f p ∈ V
    have he := congrArg f p.as_sum
    rw [he,map_sum]
    apply Submodule.sum_mem
    intro b _
    have h : MvPolynomial.monomial b (p.coeff b)=p.coeff b • mon b := by
      simp [mon,MvPolynomial.smul_monomial]
    rw [h,map_smul]
    exact V.smul_mem _ (inside b)
  apply Module.Finite.of_fg_top
  rw [← htop]
  exact Submodule.fg_span (Set.finite_range _)

theorem monic_relation_of_power_reductions (m : ℕ) (g : Fin n → P) (hg : ∀ i, (g i).totalDegree<m)
    (i : Fin n) : ∃ h : Polynomial R, h.Monic ∧ Polynomial.aeval (MvPolynomial.X i) h ∈ powerReductionIdeal m g := by
  let I := powerReductionIdeal m g
  let Q := P ⧸ I
  let _ : Module.Finite R Q := finite_power_reduction m g hg
  obtain ⟨h,hm,hz⟩ := IsIntegral.of_finite (R := R) (algebraMap P Q (MvPolynomial.X i))
  refine ⟨h,hm,Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  change algebraMap P Q (Polynomial.aeval (MvPolynomial.X i) h)=0
  rwa [← Polynomial.aeval_algebraMap_apply]

/-- The same monic equation applies after every real specialization of the
coefficients and to every solution of the specialized system. -/
theorem specialized_power_relation (m : ℕ) (g : Fin n → P) (hg : ∀ i, (g i).totalDegree<m)
    (i : Fin n) : ∃ h : Polynomial R, h.Monic ∧ ∀ (φ : R →+* ℝ) (z : Fin n → ℝ),
      (∀ j, z j^m=(g j).eval₂ φ z) → h.eval₂ φ (z i)=0 := by
  obtain ⟨h,hm,hI⟩ := monic_relation_of_power_reductions m g hg i
  refine ⟨h,hm,?_⟩
  intro φ z hz
  let F := MvPolynomial.eval₂Hom φ z
  have hk : powerReductionIdeal m g ≤ RingHom.ker F := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    apply RingHom.mem_ker.mpr
    rw [map_sub,map_pow]
    apply sub_eq_zero.mpr
    simpa only [F,MvPolynomial.eval₂Hom_X',MvPolynomial.coe_eval₂Hom] using (hz j)
  have he := RingHom.mem_ker.mp (hk hI)
  rw [Polynomial.aeval_def,Polynomial.hom_eval₂] at he
  have hcomp : F.comp (algebraMap R P)=φ := by
    ext a
    exact MvPolynomial.eval₂Hom_C φ z a
  simpa only [hcomp,F,MvPolynomial.eval₂Hom_X'] using he

end EuclideanMidpointRigidity

