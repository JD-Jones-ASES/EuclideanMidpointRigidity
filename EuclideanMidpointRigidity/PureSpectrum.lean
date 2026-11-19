module

public import EuclideanMidpointRigidity.EigenpairRows

/-! # The two pure resonances and their higher-quartic contributions -/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity

inductive PureResonance | negative | positive

namespace PureResonance

def b : PureResonance → ℝ | .negative => -1/2 | .positive => 1/5
def axial : PureResonance → ℝ | .negative => 7/13 | .positive => 0
def γ (r : PureResonance) : ℝ := r.axial/2

end PureResonance

structure PureChannel where
  x : ℝ
  y : ℝ
  z : ℝ
  q : ℝ

namespace PureChannel

structure Equations (v : PureChannel) (r : PureResonance) (s : ℝ) : Prop where
  normal : (10*s-3*r.b)*v.x+(10*r.b-3*s)*v.y+(7-2*r.b-2*s)*v.z+(5-4*r.axial)*v.q=0
  forward : (r.b+5*s-2)*v.x+(2*r.b-4*s+3)*v.z+r.axial*v.q=0
  reverse : (5*r.b+s-2)*v.y+(-4*r.b+2*s+3)*v.z+r.axial*v.q=0
  transport : (1-2*r.b)*(v.z+r.γ*v.q)=(s-r.b)*v.x

def cost (v : PureChannel) (r : PureResonance) (s : ℝ) :=
  match r with
  | .negative => v.q*(85*v.x+20*v.y/(1-2*s)-30*v.y-32*v.z)
  | .positive => v.q*(-90*v.x+(156/5)*v.y/(1-2*s)+40*v.y+38*v.z)

theorem negative_zero {v : PureChannel} {s : ℝ} (hs : s≤1/2) (h : v.Equations .negative s) : v.q=0 := by
  obtain ⟨a,b,c,d⟩ := h
  dsimp only [PureResonance.b,PureResonance.axial,PureResonance.γ] at a b c d
  have hz : (4/13*(s-1)*(170*s^2+16*s+93))*v.q=0 := by
    linear_combination (s-2)*(2*s-9)*(2*s-1)*a+(4*s^3+64*s^2-77*s-19)*b+
      2*(s-2)*(2*s-1)*(3*s+5)*c+(2*s-1)*(30*s^2+18*s-41)*d
  have hp : 0<170*s^2+16*s+93 := by nlinarith only [sq_nonneg (s+4/85)]
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num) (by linarith)) hp.ne')

theorem positive_alternatives {v : PureChannel} {s : ℝ} (hs : s≤1/2) (h : v.Equations .positive s) :
    (v.q=0 ∧ v.x=0 ∧ v.y=0 ∧ v.z=0) ∨
    (7/25<s ∧ s<1/2 ∧ 25*s^2-45*s+11=0 ∧
      v.q= -2*(1385*s-316)/225*v.x ∧
      -90*v.x+(156/5)*v.y/(1-2*s)+40*v.y+38*v.z= -2*(14005*s-3608)/63*v.x) := by
  obtain ⟨a,b,c,d⟩ := h
  dsimp only [PureResonance.b,PureResonance.axial,PureResonance.γ] at a b c d
  have hz : v.z=(5*s-1)/3*v.x := by linear_combination (5/3)*d
  rw [hz] at b c a
  have hp : (25*s^2-45*s+11)*v.x=0 := by linear_combination -(15/4)*b
  have hn : 1-s≠0 := by linarith
  have hy : v.y= -5*(34*s-11)/9*v.x := by
    apply mul_left_cancel₀ hn
    linear_combination -c-(28/45)*hp
  rw [hy] at a
  have hq : v.q= -2*(1385*s-316)/225*v.x := by linear_combination a/5-(32/75)*hp
  by_cases hzero : v.x=0
  · left
    exact ⟨by rw [hq,hzero,mul_zero],hzero,by rw [hy,hzero,mul_zero],by rw [hz,hzero,mul_zero]⟩
  have he := (mul_eq_zero.mp hp).resolve_right hzero
  have hl : 7/25<s := by
    by_contra! hn
    have hh : 25*s-38≤0 := by linarith
    nlinarith only [he,mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hn) hh]
  have hr : s<1/2 := by
    refine lt_of_le_of_ne hs ?_
    intro hh
    rw [hh] at he
    norm_num at he
  have gap : 1-2*s≠0 := by linarith
  right
  refine ⟨hl,hr,he,hq,?_⟩
  apply mul_left_cancel₀ gap
  simp only [mul_add]
  rw [show (1-2*s)*((156/5)*v.y/(1-2*s))=(156/5)*v.y by field_simp]
  rw [hy,hz]
  linear_combination (416/21)*hp

theorem cost_nonnegative {v : PureChannel} {s : ℝ} {r : PureResonance} (hs : s≤1/2) (h : v.Equations r s) :
    0≤v.cost r s := by
  cases r with
  | negative => simp [cost,negative_zero hs h]
  | positive =>
    rcases positive_alternatives hs h with ⟨q,_,_,_⟩|⟨hl,_,_,q,hc⟩
    · simp [cost,q]
    · dsimp only [cost]
      rw [q,hc]
      have a : 0<1385*s-316 := by linarith
      have b : 0<14005*s-3608 := by linarith
      calc
        0 ≤ (4/(225*63):ℝ)*(1385*s-316)*(14005*s-3608)*v.x^2 := by positivity
        _ = _ := by ring

theorem diagonal_zero {r : PureResonance} {v : PureChannel} (h : v.Equations r r.b) : v.q=0 := by
  cases r with
  | negative => exact negative_zero (by norm_num [PureResonance.b]) h
  | positive =>
    rcases positive_alternatives (by norm_num [PureResonance.b]) h with ⟨q,_,_,_⟩|⟨hl,_,_,_⟩
    · exact q
    · norm_num [PureResonance.b] at hl

theorem half_zero {r : PureResonance} {v : PureChannel} (h : v.Equations r (1/2)) : v.q=0 := by
  cases r with
  | negative => exact negative_zero le_rfl h
  | positive =>
    rcases positive_alternatives le_rfl h with ⟨q,_,_,_⟩|⟨_,hh,_⟩
    · exact q
    · exact (lt_irrefl _ hh).elim

end PureChannel
end EuclideanMidpointRigidity

