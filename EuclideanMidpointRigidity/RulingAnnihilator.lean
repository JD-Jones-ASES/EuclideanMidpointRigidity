module

public import EuclideanMidpointRigidity.LineOperatorCalculus
public import EuclideanMidpointRigidity.LineSpectrum
public import Mathlib.Algebra.Polynomial.Splits

/-! # The common monic differential operator and its real roots -/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped ContDiff
namespace EuclideanMidpointRigidity
open Endpoint

def Endpoint.tiltPolynomial (κ : ℝ) : ℝ[X] := X^2*(X^2-1)*(X^2-C (tiltRate κ))

theorem RulingResponseLaws.solves_tilt {W : Set ℝ} {η κ : ℝ} {Q P : ℝ → ℝ} (H : RulingResponseLaws W η κ Q P)
    (hW : IsOpen W) : SolvesOn hW (tiltPolynomial κ) P := by
  let F := LineSpace.restrict P H.smoothP
  have ep : tiltPolynomial κ=X^6-C (tiltRate κ+1)*X^4+C (tiltRate κ)*X^2 := by
    simp only [tiltPolynomial,map_add,map_one]
    ring
  refine ⟨H.smoothP,LineSpace.ext_on (fun x hx ↦ ?_)⟩
  change ((LineSpace.operator hW (tiltPolynomial κ)) F).val x=0
  rw [ep,map_add,map_sub]
  simp only [LinearMap.add_apply,LinearMap.sub_apply,Submodule.coe_add,Submodule.coe_sub,Pi.add_apply,Pi.sub_apply,
    LineSpace.operator_X_pow hW F _ hx,LineSpace.operator_monomial hW F _ _ hx,F,
    LineSpace.iteratedDeriv_restrict hW H.smoothP hx,smul_eq_mul]
  linarith only [H.tilt_equation hW hx]

namespace LiftedSection
variable {d : ℕ} (S : LiftedSection d)

def entryDerivativePolynomial (p : Space d) : ℝ[X] :=
  X^2*(X^2-1)*((S.rateOperator p).toLinearMap.charpoly.comp (X^2))

theorem entryDerivativePolynomial_mul_X (p : Space d) :
    S.entryDerivativePolynomial p*X=S.rulingPolynomial p := by
  dsimp only [entryDerivativePolynomial,rulingPolynomial]; ring

theorem rulingPolynomial_monic (p : Space d) : (S.rulingPolynomial p).Monic := by
  have h : (X^2-1 : ℝ[X]).Monic := by simpa using monic_X_pow_sub_C (R := ℝ) (1:ℝ) (by decide : 2≠0)
  exact ((monic_X_pow 3).mul h).mul ((S.rateOperator p).toLinearMap.charpoly_monic.comp (monic_X_pow 2) (by simp))

theorem rulingPolynomial_degree (p : Space d) : (S.rulingPolynomial p).natDegree=2*d+5 := by
  have ht : (X^2-1 : ℝ[X]).natDegree=2 := by simpa using natDegree_X_pow_sub_C (R := ℝ) (n := 2) (1:ℝ)
  have hn : (X^2-1 : ℝ[X])≠0 := fun hz ↦ by simp [hz] at ht
  have hpoly := (S.rateOperator p).toLinearMap.charpoly_monic.ne_zero
  have hcomp : ((S.rateOperator p).toLinearMap.charpoly.comp (X^2)).Monic :=
    (S.rateOperator p).toLinearMap.charpoly_monic.comp (monic_X_pow 2) (by simp)
  rw [rulingPolynomial,natDegree_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) hn) hcomp.ne_zero,
    natDegree_mul (pow_ne_zero _ X_ne_zero) hn,ht,natDegree_X_pow,natDegree_comp,natDegree_X_pow,
    LinearMap.charpoly_natDegree]
  simp [Space]
  <;> omega

namespace RulingFrame
variable {S : LiftedSection d} {p : Space d} {ι : Type*} [Fintype ι] [DecidableEq ι] (F : RulingFrame S p ι)

theorem derivative_factors (hp : p ∈ S.domain) :
    S.entryDerivativePolynomial p=X^2*(X^2-1)*∏ i, (X^2-C (F.exponentSquare i)) := by
  simp only [entryDerivativePolynomial,F.charpoly_rates hp,Polynomial.prod_comp,sub_comp,X_comp,C_comp]

theorem tilt_dvd (hp : p ∈ S.domain) {i : ι} (hi : i≠F.axial) :
    tiltPolynomial (1-2*F.value i) ∣ S.entryDerivativePolynomial p := by
  rw [tiltPolynomial,F.derivative_factors hp]
  apply mul_dvd_mul_left
  have h := Finset.dvd_prod_of_mem (fun j ↦ (X^2-C (F.exponentSquare j) : ℝ[X])) (Finset.mem_univ i)
  simpa only [exponentSquare,ite_eq_right hi] using h

private theorem splits_quadratic {a : ℝ} (ha : 0≤a) : (X^2-C a : ℝ[X]).Splits := by
  let r := Real.sqrt a
  have he : C a=(C r)^2 := by rw [← map_pow,Real.sq_sqrt ha]
  rw [he,show X^2-(C r)^2=(X-C r)*(X-C (-r)) by rw [map_neg]; ring]
  exact (Splits.X_sub_C _).mul (Splits.X_sub_C _)

include F in
theorem rulingPolynomial_splits (hp : p ∈ S.domain) : (S.rulingPolynomial p).Splits := by
  rw [← S.entryDerivativePolynomial_mul_X,F.derivative_factors hp]
  have h₁ : (X^2-1 : ℝ[X]).Splits := by simpa using splits_quadratic (by norm_num : (0:ℝ)≤1)
  exact ((((Splits.X (R := ℝ)).pow 2).mul h₁).mul (Splits.prod (fun i _ ↦ splits_quadratic (F.exponentSquare_pos i).le))).mul Splits.X

end RulingFrame
end LiftedSection
end EuclideanMidpointRigidity

