module

public import EuclideanMidpointRigidity.PureChannelGeometry

/-! # Cancellation of the two higher quartic rows in either pure case -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity.PureResonance
open Quartic
variable {d : ℕ}
local notation "E" => Space d
local notation "C" => Cubic d

def normalWeight : PureResonance → ℝ | .negative => 8 | .positive => -19/2
def slopeWeight : PureResonance → ℝ | .negative => 20 | .positive => 156/5
def offset : PureResonance → ℝ | .negative => 19/26 | .positive => 8

def high (i : PureResonance) (c : C) (J : E →L[ℝ] C) (e f w : E) :=
  i.normalWeight*termAt c J .threeOne w e f e e+termAt c J .twoTwo w f e f f

def raw (i : PureResonance) (v : PureChannel) := match i with
  | .negative => v.q*(85*v.x-30*v.y-32*v.z)
  | .positive => v.q*(-90*v.x+40*v.y+38*v.z)

theorem cost_eq (i : PureResonance) (v : PureChannel) (s : ℝ) :
    v.cost i s=i.raw v+i.slopeWeight*(v.q*v.y/(1-2*s)) := by
  cases i <;> dsimp only [PureChannel.cost,raw,slopeWeight] <;> ring

structure Leading (i : PureResonance) (c : C) (J : E →L[ℝ] C) (e f : E) : Prop where
  eee : cubicEntry c e e e=1
  eef : cubicEntry c e e f=0
  eff : cubicEntry c e f f=i.b
  fff : cubicEntry c f f f=0
  normal : jetEntry J e e e e=0
  gradient : jetEntry J f e e e=1
  axialJet : jetEntry J e e e f=i.axial

theorem sum_high {ι : Type*} [Fintype ι] (B : OrthonormalBasis ι ℝ E) (i : PureResonance)
    {c : C} {J : E →L[ℝ] C} (hE : ∀ v, obstruction c J v=0) (e f : E) :
    ∑ j, i.high c J e f (B j)=0 := by
  simp only [high,Finset.sum_add_distrib,← Finset.mul_sum,sum_termAt_eq_zero B hE,mul_zero,add_zero]

theorem core_high {i : PureResonance} {c : C} {J : E →L[ℝ] C} {e f : E} (h : i.Leading c J e f) :
    i.high c J e f e+i.high c J e f f=i.offset-i.slopeWeight*jetEntry J f e f f := by
  obtain ⟨a,b,c,d,g,l,k⟩ := h
  cases i <;> dsimp only [high,normalWeight,offset,slopeWeight,termAt,Pattern.eval,row31,row22,contraction]
  all_goals
    simp only [cubicEntry_swap₁,cubicEntry_swap₂,jetEntry_swap₁,jetEntry_swap₂] at *
    simp only [a,b,c,d,g,l,k,PureResonance.b,axial]
    ring

theorem outside_high (i : PureResonance) {c : C} {J : E →L[ℝ] C} {e f w : E}
    (h₀ : cubicEntry c e e w=0) (h₁ : cubicEntry c e f w=0) :
    i.high c J e f w=i.raw ⟨jetEntry J w e e f,jetEntry J f e e w,jetEntry J e e f w,cubicEntry c f f w⟩ := by
  cases i <;> dsimp only [high,normalWeight,raw,termAt,Pattern.eval,row31,row22,contraction]
  all_goals
    simp only [cubicEntry_swap₁,cubicEntry_swap₂,jetEntry_swap₁,jetEntry_swap₂] at *
    simp only [h₀,h₁]
    ring

theorem offset_pos (i : PureResonance) : 0 < i.offset-i.slopeWeight*i.b := by
  cases i <;> norm_num [offset,slopeWeight,b]

end EuclideanMidpointRigidity.PureResonance

