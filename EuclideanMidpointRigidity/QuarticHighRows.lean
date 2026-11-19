module

public import EuclideanMidpointRigidity.QuarticPolarization

/-! # The single-index sums for the higher quartic coefficients -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity.Quartic
variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

theorem cubicEntry_swap₁ (c : Coeff) (i j k : E) : cubicEntry c i j k=cubicEntry c j i k := by
  simp only [cubicEntry,K_symm c i j]

theorem cubicEntry_swap₂ (c : Coeff) (i j k : E) : cubicEntry c i j k=cubicEntry c i k j := by
  simp only [cubicEntry,K_selfAdjoint c i j k]
  exact real_inner_comm _ _

theorem jetEntry_swap₁ (J : E →L[ℝ] Coeff) (l i j k : E) : jetEntry J l i j k=jetEntry J l j i k :=
  cubicEntry_swap₁ _ _ _ _

theorem jetEntry_swap₂ (J : E →L[ℝ] Coeff) (l i j k : E) : jetEntry J l i j k=jetEntry J l i k j :=
  cubicEntry_swap₂ _ _ _ _

def row31 {V : Type*} (F : V → V → V → V → ℝ) (a b : V) :=
  F a a a b+F a a b a+F a b a a+F b a a a

theorem row31_zero {c : Coeff} {J : E →L[ℝ] Coeff} (hE : ∀ z, obstruction c J z=0) (o a b : E) :
    row31 (term c J o) a b=0 := by
  have h := row211_zero hE o a a b
  dsimp only [row211,row31] at h ⊢
  linear_combination h/3

inductive Pattern | twoTwo | twoOneOne | threeOne

def Pattern.eval {V : Type*} (p : Pattern) (F : V → V → V → V → ℝ) (a b c : V) : ℝ :=
  match p with
  | .twoTwo => row22 F a b
  | .twoOneOne => row211 F a b c
  | .threeOne => row31 F a b

def termAt (c : Coeff) (J : E →L[ℝ] Coeff) (p : Pattern) (r o a b w : E) : ℝ :=
  p.eval (contraction (cubicEntry c) (jetEntry J) r o) a b w

theorem sum_termAt_eq_zero {ι : Type*} [Fintype ι] (B : OrthonormalBasis ι ℝ E)
    {c : Coeff} {J : E →L[ℝ] Coeff} (hE : ∀ z, obstruction c J z=0) (p : Pattern) (o a b w : E) :
    ∑ i, termAt c J p (B i) o a b w=0 := by
  have hh : p.eval (term c J o) a b w=0 := by
    cases p with
    | twoTwo => exact row22_zero hE o a b
    | twoOneOne => exact row211_zero hE o a b w
    | threeOne => exact row31_zero hE o a b
  cases p <;> simp only [termAt,Pattern.eval,row22,row211,row31,Finset.sum_add_distrib,term_eq_sum B] at hh ⊢ <;> exact hh

end EuclideanMidpointRigidity.Quartic
