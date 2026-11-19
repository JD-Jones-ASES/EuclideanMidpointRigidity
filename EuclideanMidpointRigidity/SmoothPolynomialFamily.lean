module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Tactic

/-! # Polynomial families with smooth spatial coefficients -/

@[expose] public section
noncomputable section
open Set
open scoped ContDiff
namespace EuclideanMidpointRigidity

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def smoothCoefficients (W : Set X) : Subring (X → ℝ) where
  carrier := {f | ContDiffOn ℝ ∞ f W}
  add_mem' := fun hf hg ↦ ContDiffOn.add hf hg
  zero_mem' := contDiffOn_const
  neg_mem' := fun hf ↦ ContDiffOn.neg hf
  mul_mem' := fun hf hg ↦ ContDiffOn.mul hf hg
  one_mem' := contDiffOn_const

abbrev SmoothCoefficient (W : Set X) : Type _ := smoothCoefficients W

namespace SmoothPolynomial
variable {W : Set X} {n : ℕ}
local notation "A" => SmoothCoefficient W
local notation "R" => MvPolynomial (Fin n) A

def evaluateCoefficient (x : X) : A →+* ℝ :=
  (Pi.evalRingHom (fun _ : X ↦ ℝ) x).comp (smoothCoefficients W).subtype

def specialize (f : R) (x : X) : MvPolynomial (Fin n) ℝ := MvPolynomial.map (evaluateCoefficient x) f

@[simp] theorem specialize_coeff (f : R) (x : X) (j : Fin n →₀ ℕ) :
    (specialize f x).coeff j = (f.coeff j).val x := MvPolynomial.coeff_map _ _ _

theorem smooth_coeff (f : R) (j : Fin n →₀ ℕ) :
    ContDiffOn ℝ ∞ (fun x ↦ (specialize f x).coeff j) W := by
  simp only [specialize_coeff]
  exact (f.coeff j).property

@[simp] theorem specialize_pow (f : R) (x : X) (k : ℕ) :
    specialize (f^k) x=(specialize f x)^k := map_pow _ _ _

@[simp] theorem specialize_mul (f g : R) (x : X) :
    specialize (f*g) x=specialize f x*specialize g x := map_mul _ _ _

@[simp] theorem specialize_monomial (a : Fin n →₀ ℕ) (s : A) (x : X) :
    specialize (MvPolynomial.monomial a s) x = MvPolynomial.monomial a (s.val x) := by
  simp [specialize,evaluateCoefficient]

@[simp] theorem specialize_pderiv (f : R) (i : Fin n) (x : X) :
    specialize (MvPolynomial.pderiv i f) x=MvPolynomial.pderiv i (specialize f x) := by
  exact MvPolynomial.pderiv_map.symm

end SmoothPolynomial
end EuclideanMidpointRigidity

