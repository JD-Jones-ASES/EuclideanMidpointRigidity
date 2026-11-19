module

public import EuclideanMidpointRigidity.EigenpairRows

/-! # Equations of one external spectral direction in the mixed case -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity

/-- The cubic components, first jets, and frame derivatives in one external
direction. Quantities with one or two positive-fifth slots carry one or two
powers of the gradient ratio as appropriate. -/
structure MixedChannel where
  q : ℝ
  l : ℝ
  h : ℝ
  r1w : ℝ
  rw1 : ℝ
  z1w : ℝ
  r2w : ℝ
  rw2 : ℝ
  z2w : ℝ
  rot1 : ℝ
  rot2 : ℝ

namespace MixedChannel
variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

def ofJet (c : Coeff) (J : E →L[ℝ] Coeff) (e x y w : E) (t o p : ℝ) : MixedChannel :=
  ⟨⟪w,K c x x⟫_ℝ,t*⟪w,K c x y⟫_ℝ,t^2*⟪w,K c y y⟫_ℝ,
    ⟪K (J w) e e,x⟫_ℝ,⟪K (J x) e e,w⟫_ℝ,⟪K (J e) e x,w⟫_ℝ,
    t*⟪K (J w) e e,y⟫_ℝ,t*⟪K (J y) e e,w⟫_ℝ,t*⟪K (J e) e y,w⟫_ℝ,o,p⟩

structure LowRows (v : MixedChannel) (s : ℝ) : Prop where
  normal1 : (20*s+3)*v.r1w+(-6*s-10)*v.rw1+(16-4*s)*v.z1w+74/13*v.q+10*v.l=0
  first1w : (10*s-5)*v.r1w+(4-8*s)*v.z1w+14/13*v.q=0
  firstw1 : (2*s-9)*v.rw1+(4*s+10)*v.z1w+14/13*v.q=0
  normal2 : (20*s-6/5)*v.r2w+(4-6*s)*v.rw2+(66/5-4*s)*v.z2w+74/13*v.l+10*v.h=0
  first2w : (10*s-18/5)*v.r2w+(34/5-8*s)*v.z2w+14/13*v.l=0
  firstw2 : (2*s-2)*v.rw2+(4*s+22/5)*v.z2w+14/13*v.l=0

structure Equations (v : MixedChannel) (s : ℝ) : Prop extends v.LowRows s where
  rotate1 : (-1/2-s)*v.rot1=v.z1w+7/26*v.q
  rotate2 : (1/5-s)*v.rot2=v.z2w+7/26*v.l
  transport : v.rot1+v.rot2+v.r1w/2+5*v.r2w/3=0

theorem lowRows_of_jet {c : Coeff} {J : E →L[ℝ] Coeff} {e x y w : E} {t s : ℝ}
    (hc : K c e e=(1:ℝ) • e) (hE : ∀ z, obstruction c J z=0)
    (hx : K c e x=(-1/2:ℝ) • x) (hy : K c e y=(1/5:ℝ) • y) (hw : K c e w=s • w)
    (hU : K (J e) e e=(7/13:ℝ) • x)
    (hg : ∀ l, ⟪K (J l) e e,e⟫_ℝ=⟪x+t • y,l⟫_ℝ) (o p : ℝ) :
    (ofJet c J e x y w t o p).LowRows s := by
  have h₁ := eigenpair_normal_row hc hE hg hx hw
  have h₂ := eigenpair_vector_row hc hE hw hx
  have h₃ := eigenpair_vector_row hc hE hx hw
  have h₄ := eigenpair_normal_row hc hE hg hy hw
  have h₅ := eigenpair_vector_row hc hE hw hy
  have h₆ := eigenpair_vector_row hc hE hy hw
  have htri (f g : E) : ⟪f,K c g w⟫_ℝ=⟪w,K c f g⟫_ℝ := by
    rw [← K_selfAdjoint,K_symm c g f,real_inner_comm]
  have hZ (f : E) : ⟪K (J e) e w,f⟫_ℝ=⟪K (J e) e f,w⟫_ℝ := by
    rw [K_selfAdjoint,real_inner_comm]
  dsimp only at h₁ h₂ h₃ h₄ h₅ h₆
  simp only [hU,K_symm c w x,K_symm c w y,htri,K_add_left,K_smul_left,
    inner_add_right,real_inner_smul_right,K_symm c y x,hZ] at h₁ h₂ h₃ h₄ h₅ h₆
  constructor <;> dsimp only [ofJet]
  · linear_combination h₁
  · linear_combination h₂
  · linear_combination h₃
  · linear_combination t*h₄
  · linear_combination t*h₅
  · linear_combination t*h₆

/-- A null spherical-Hessian direction contributes zero in every raw channel slot. -/
theorem zero_at_half {v : MixedChannel} (he : v.Equations (1/2)) (h₁ : v.rw1=0) (h₂ : v.rw2=0) :
    v.q=0 ∧ v.l=0 ∧ v.h=0 ∧ v.r1w=0 ∧ v.z1w=0 ∧ v.r2w=0 ∧ v.z2w=0 ∧
      v.rot1=0 ∧ v.rot2=0 := by
  obtain ⟨⟨a,b,c,d,e,f⟩,g,i,j⟩ := he
  constructor <;> repeat' apply And.intro
  all_goals linarith only [a,b,c,d,e,f,g,i,j,h₁,h₂]

end MixedChannel
end EuclideanMidpointRigidity
