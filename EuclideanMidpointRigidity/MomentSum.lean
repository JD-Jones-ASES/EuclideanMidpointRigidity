module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic

/-! # Sums of internal and external terms in the critical equations -/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity

structure Moment (ι : Type*) where
  internal : ℝ
  external : ι → ℝ

namespace Moment
variable {ι : Type*}

def constant (x : ℝ) : Moment ι := ⟨x,fun _ ↦ 0⟩
def add (x y : Moment ι) : Moment ι := ⟨x.internal+y.internal,fun i ↦ x.external i+y.external i⟩
def scale (a : ℝ) (x : Moment ι) : Moment ι := ⟨a*x.internal,fun i ↦ a*x.external i⟩
def total [Fintype ι] (x : Moment ι) := x.internal+∑ i, x.external i

@[simp] theorem total_constant [Fintype ι] (x : ℝ) : (constant x : Moment ι).total=x := by simp [total,constant]
@[simp] theorem total_add [Fintype ι] (x y : Moment ι) : (x.add y).total=x.total+y.total := by
  simp only [add,total,Finset.sum_add_distrib]; ring
@[simp] theorem total_scale [Fintype ι] (a : ℝ) (x : Moment ι) : (x.scale a).total=a*x.total := by
  simp only [scale,total,← Finset.mul_sum]; ring

theorem eq_of_coordinates {x y : Moment ι} (hi : x.internal=y.internal) (he : ∀ i, x.external i=y.external i) :
    x=y := by cases x; cases y; congr 1; exact funext he

end Moment
end EuclideanMidpointRigidity
