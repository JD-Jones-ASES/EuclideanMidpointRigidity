module

public import EuclideanMidpointRigidity.EigenpairRows

/-! # Solving the quartic equations inside the two resonant directions -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity

/-- The coordinates in the two distinguished directions after normalizing
the cubic value at the maximum to one. The first subscript of `r` is the
output direction and the second is the spatial derivative direction. -/
structure ResonantPlane where
  u : ℝ
  v : ℝ
  t111 : ℝ
  t112 : ℝ
  t122 : ℝ
  t222 : ℝ
  r11 : ℝ
  r12 : ℝ
  r21 : ℝ
  r22 : ℝ
  z11 : ℝ
  z12 : ℝ
  z22 : ℝ

namespace ResonantPlane
variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

def ofJet (c : Coeff) (J : E →L[ℝ] Coeff) (e x y : E) (u v : ℝ) : ResonantPlane :=
  ⟨u,v,⟪x,K c x x⟫_ℝ,⟪y,K c x x⟫_ℝ,⟪x,K c y y⟫_ℝ,⟪y,K c y y⟫_ℝ,
    ⟪K (J x) e e,x⟫_ℝ,⟪K (J y) e e,x⟫_ℝ,⟪K (J x) e e,y⟫_ℝ,⟪K (J y) e e,y⟫_ℝ,
    ⟪K (J e) e x,x⟫_ℝ,⟪K (J e) e x,y⟫_ℝ,⟪K (J e) e y,y⟫_ℝ⟩

structure LowRows (p : ResonantPlane) : Prop where
  first11 : -10*p.r11+8*p.z11+(14/13)*p.u*p.t111=0
  normal11 : -14*p.r11+18*p.z11+(74/13)*p.u*p.t111+10*p.v*p.t112=0
  first22 : (-8/5)*p.r22+(26/5)*p.z22+(14/13)*p.u*p.t122=0
  normal22 : (28/5)*p.r22+(62/5)*p.z22+(74/13)*p.u*p.t122+10*p.v*p.t222=0
  first21 : (-43/5)*p.r21+(54/5)*p.z12+(14/13)*p.u*p.t112=0
  first12 : -3*p.r12+(12/5)*p.z12+(14/13)*p.u*p.t112=0
  normal12 : (-56/5)*p.r21+7*p.r12+(76/5)*p.z12+(74/13)*p.u*p.t112+10*p.v*p.t122=0
  tangent11 : p.z11=-(7/26)*p.u*p.t111
  tangent22 : p.z22=-(7/26)*p.u*p.t122

theorem lowRows_of_jet {c : Coeff} {J : E →L[ℝ] Coeff} {e x y : E} {u v : ℝ}
    (hc : K c e e=(1:ℝ) • e) (hE : ∀ w, obstruction c J w=0)
    (hx : K c e x=(-1/2:ℝ) • x) (hy : K c e y=(1/5:ℝ) • y)
    (hU : K (J e) e e=(7/13*u) • x) (hg : ∀ l, ⟪K (J l) e e,e⟫_ℝ=⟪u • x+v • y,l⟫_ℝ)
    (htx : ⟪K (J e) e x,x⟫_ℝ=-(7/26)*u*⟪x,K c x x⟫_ℝ)
    (hty : ⟪K (J e) e y,y⟫_ℝ=-(7/26)*u*⟪x,K c y y⟫_ℝ) :
    (ofJet c J e x y u v).LowRows := by
  have v₁ := eigenpair_vector_row hc hE hx hx
  have n₁ := eigenpair_normal_row hc hE hg hx hx
  have v₂ := eigenpair_vector_row hc hE hy hy
  have n₂ := eigenpair_normal_row hc hE hg hy hy
  have v₂₁ := eigenpair_vector_row hc hE hx hy
  have v₁₂ := eigenpair_vector_row hc hE hy hx
  have n₁₂ := eigenpair_normal_row hc hE hg hx hy
  have hα : ⟪x,K c x y⟫_ℝ=⟪y,K c x x⟫_ℝ := by rw [← K_selfAdjoint,real_inner_comm]
  have hβ : ⟪y,K c x y⟫_ℝ=⟪x,K c y y⟫_ℝ := by rw [K_symm c x y,← K_selfAdjoint,real_inner_comm]
  have hZ : ⟪K (J e) e y,x⟫_ℝ=⟪K (J e) e x,y⟫_ℝ := by rw [K_selfAdjoint,real_inner_comm]
  dsimp only at v₁ n₁ v₂ n₂ v₂₁ v₁₂ n₁₂
  simp only [hU,inner_add_left,real_inner_smul_left,K_symm c y x,hα,hβ,hZ] at v₁ n₁ v₂ n₂ v₂₁ v₁₂ n₁₂
  constructor <;> dsimp only [ofJet] <;> linarith only [v₁,n₁,v₂,n₂,v₂₁,v₁₂,n₁₂,htx,hty]

structure Solution (p : ResonantPlane) : Prop where
  t111 : p.u*p.t111=-(650/153)*p.v*p.t112
  t222 : p.v*p.t222=-(159/1300)*p.u*p.t122
  r11 : p.r11=(70/153)*p.v*p.t112
  r12 : p.r12=-(5/7059)*(634*p.u*p.t112+1677*p.v*p.t122)
  r21 : p.r21=-(5/4706)*(1076*p.u*p.t112+1755*p.v*p.t122)
  r22 : p.r22=-(21/104)*p.u*p.t122
  z11 : p.z11=(175/153)*p.v*p.t112
  z12 : p.z12=-(5/28236)*(5704*p.u*p.t112+8385*p.v*p.t122)
  z22 : p.z22=-(7/26)*p.u*p.t122

theorem LowRows.solve {p : ResonantPlane} (h : p.LowRows) : p.Solution := by
  obtain ⟨a,b,c,d,e,f,g,i,j⟩ := h
  constructor <;> linarith only [a,b,c,d,e,f,g,i,j]

def scalarSixth (p : ResonantPlane) : ℝ :=
  let s := 7/13*p.u
  217*s^2*p.r11 + 231*s*(p.u*p.r11+p.v*p.r21) - 918*s*(p.u*p.z11+p.v*p.z12) -
    340*s^2*(p.u*p.t111+p.v*p.t112)

theorem mixed_cubic_relation {p : ResonantPlane} (h : p.LowRows) (hu : 0<p.u) (hv : 0<p.v)
    (hs : p.scalarSixth=0) : 86354*p.u*p.t112+219375*p.v*p.t122=0 := by
  have q := h.solve
  rw [scalarSixth,q.r11,q.r21,q.z11,q.z12,q.t111] at hs
  have hmul : (70/30589*p.u*p.v)*(86354*p.u*p.t112+219375*p.v*p.t122)=0 := by
    linear_combination hs
  exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt (by positivity))

end ResonantPlane
end EuclideanMidpointRigidity
