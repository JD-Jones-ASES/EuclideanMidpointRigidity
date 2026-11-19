module

public import EuclideanMidpointRigidity.FinitePowerReduction

/-! # Monic coordinate equations for a polynomial perturbation -/

@[expose] public section
noncomputable section
open Set
namespace EuclideanMidpointRigidity

variable {R : Type} [CommRing R] {n : ℕ}
local notation "P" => MvPolynomial (Fin n) R

/-- The polynomial obtained from a degree-bounded right side by the change
of variables w = t z and multiplication by the common power of t. -/
def scaledRightSide (k : ℕ) (g : P) : MvPolynomial (Fin n) (Polynomial R) :=
  ∑ a ∈ g.support, MvPolynomial.monomial a
    (Polynomial.C (g.coeff a)*Polynomial.X^(k-∑ i, a i))

theorem scaledRightSide_degree {k : ℕ} {g : P} (hg : g.totalDegree ≤ k) :
    (scaledRightSide k g).totalDegree ≤ k := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro a ha
  exact (MvPolynomial.totalDegree_monomial_le _ _).trans ((MvPolynomial.le_totalDegree ha).trans hg)

theorem eval_scaledRightSide {k : ℕ} {g : P} (hg : g.totalDegree ≤ k) (φ : R →+* ℝ)
    (t : ℝ) (z : Fin n → ℝ) :
    (scaledRightSide k g).eval₂ (Polynomial.eval₂RingHom φ t) (fun i ↦ t*z i) =
      t^k*g.eval₂ φ z := by
  classical
  rw [MvPolynomial.eval₂_eq' φ z g,Finset.mul_sum]
  change MvPolynomial.eval₂Hom _ _ (∑ a ∈ g.support, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hdeg := (MvPolynomial.le_totalDegree ha).trans hg
  rw [Finsupp.sum_fintype _ _ (by simp)] at hdeg
  rw [MvPolynomial.eval₂Hom_monomial,Finsupp.prod_pow]
  simp only [map_mul,map_pow,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,Polynomial.eval₂_X,
    mul_pow,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  have ht : t^(k-∑ i, a i)*t^(∑ i, a i)=t^k := by rw [← pow_add,Nat.sub_add_cancel hdeg]
  linear_combination (φ (g.coeff a)*(∏ i, z i ^ a i))*ht

/-- A monic equation for the scaled coordinate t zᵢ, uniformly in the real
parameter and in all other coefficients, when t zⱼᵐ is a lower-degree polynomial. -/
theorem regularized_coordinate_relation (k : ℕ) (g : Fin n → P) (hg : ∀ i, (g i).totalDegree ≤ k)
    (i : Fin n) : ∃ h : Polynomial (Polynomial R), h.Monic ∧ ∀ (φ : R →+* ℝ) (t : ℝ) (z : Fin n → ℝ),
      (∀ j, t*z j^(k+1)=(g j).eval₂ φ z) → h.eval₂ (Polynomial.eval₂RingHom φ t) (t*z i)=0 := by
  obtain ⟨h,hm,he⟩ := specialized_power_relation (k+1) (fun j ↦ scaledRightSide k (g j))
    (fun j ↦ Nat.lt_succ_of_le (scaledRightSide_degree (hg j))) i
  refine ⟨h,hm,?_⟩
  intro φ t z hz
  apply he (Polynomial.eval₂RingHom φ t) (fun j ↦ t*z j)
  intro j
  rw [eval_scaledRightSide (hg j),← hz j,mul_pow,pow_succ t]
  ring

end EuclideanMidpointRigidity

