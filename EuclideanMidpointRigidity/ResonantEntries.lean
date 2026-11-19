module

public import EuclideanMidpointRigidity.MixedEigenbasis
public import EuclideanMidpointRigidity.QuarticHighRows

/-! # Tensor entries used by the higher quartic equations -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity.Quartic
variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

structure CoreEntries where
  t : ℝ
  d1 : ℝ
  m : ℝ
  n : ℝ
  d2 : ℝ
  r11 : ℝ
  r12 : ℝ
  r21 : ℝ
  r22 : ℝ
  z11 : ℝ
  z12 : ℝ
  z22 : ℝ
  j1xx : ℝ
  j1xy : ℝ
  j1yy : ℝ
  j2xx : ℝ
  j2xy : ℝ
  j2yy : ℝ
  s111 : ℝ
  s112 : ℝ
  s122 : ℝ
  s222 : ℝ

def CoreEntries.ofJet (c : Coeff) (J : E →L[ℝ] Coeff) (e x y : E) (t : ℝ) : CoreEntries :=
  ⟨t,cubicEntry c x x x,cubicEntry c x x y,cubicEntry c x y y,cubicEntry c y y y,
    jetEntry J x e e x,jetEntry J y e e x,jetEntry J x e e y,jetEntry J y e e y,
    jetEntry J e e x x,jetEntry J e e x y,jetEntry J e e y y,
    jetEntry J x e x x,jetEntry J x e x y,jetEntry J x e y y,
    jetEntry J y e x x,jetEntry J y e x y,jetEntry J y e y y,
    jetEntry J e x x x,jetEntry J e x x y,jetEntry J e x y y,jetEntry J e y y y⟩

/-- The external components before inserting powers of the gradient ratio. -/
structure OutsideEntries where
  q : ℝ
  l : ℝ
  h : ℝ
  r1w : ℝ
  rw1 : ℝ
  z1w : ℝ
  r2w : ℝ
  rw2 : ℝ
  z2w : ℝ

def OutsideEntries.ofJet (c : Coeff) (J : E →L[ℝ] Coeff) (e x y w : E) : OutsideEntries :=
  ⟨cubicEntry c x x w,cubicEntry c x y w,cubicEntry c y y w,
    jetEntry J w e e x,jetEntry J x e e w,jetEntry J e e x w,
    jetEntry J w e e y,jetEntry J y e e w,jetEntry J e e y w⟩

structure CoreLeading (c : Coeff) (J : E →L[ℝ] Coeff) (e x y : E) (t : ℝ) : Prop where
  eee : cubicEntry c e e e=1
  eex : cubicEntry c e e x=0
  eey : cubicEntry c e e y=0
  exx : cubicEntry c e x x= -1/2
  exy : cubicEntry c e x y=0
  eyy : cubicEntry c e y y=1/5
  je : jetEntry J e e e e=0
  jx : jetEntry J x e e e=1
  jy : jetEntry J y e e e=t
  ux : jetEntry J e e e x=7/13
  uy : jetEntry J e e e y=0

structure OutsideLeading (c : Coeff) (J : E →L[ℝ] Coeff) (e x y w : E) : Prop where
  ee : cubicEntry c e e w=0
  ex : cubicEntry c e x w=0
  ey : cubicEntry c e y w=0
  jw : jetEntry J w e e e=0
  uw : jetEntry J e e e w=0

private theorem leading_values {c : Coeff} {J : E →L[ℝ] Coeff} {e x y : E} {t : ℝ}
    (hc : K c e e=(1:ℝ) • e) (hx : K c e x=(-1/2:ℝ) • x) (hy : K c e y=(1/5:ℝ) • y)
    (hU : K (J e) e e=(7/13:ℝ) • x) (hg : ∀ w, ⟪K (J w) e e,e⟫_ℝ=⟪x+t • y,w⟫_ℝ)
    (h₀ : ‖e‖=1) (h₁ : ‖x‖=1) (h₂ : ‖y‖=1) (hex : ⟪e,x⟫_ℝ=0) (hey : ⟪e,y⟫_ℝ=0)
    (hxy : ⟪x,y⟫_ℝ=0) : CoreLeading c J e x y t := by
  have hxe := inner_eq_zero_symm.mp hex
  have hyx := inner_eq_zero_symm.mp hxy
  constructor <;> simp only [jetEntry,cubicEntry,hc,hx,hy,hU,hg,inner_add_left,real_inner_smul_left,
    one_smul,real_inner_self_eq_norm_sq,h₀,h₁,h₂,hex,hey,hxy,hxe,hyx] <;> ring

theorem core_leading (S : LiftedSection d) {p : E} (hm : S.IsMixed p) :
    CoreLeading (S.cubic p) (S.jet p) (S.axis p) (S.x p) (S.y p) (S.ratio p) := by
  obtain ⟨hx,hy,hxy,hex,hey,_,_,_⟩ := S.plane_data hm
  obtain ⟨hU,hg⟩ := S.normalized_jet_data hm
  exact leading_values (S.normalized_axis hm.1) (S.normalized_eigenvector hm.1 (S.eigenvectors hm.1).1)
    (S.normalized_eigenvector hm.1 (S.eigenvectors hm.1).2) hU hg (S.unit p hm.1) hx hy hex hey hxy

theorem outside_leading (S : LiftedSection d) {p : E} (hm : S.IsMixed p) {w : E}
    (he : ⟪S.axis p,w⟫_ℝ=0) (hx : ⟪S.x p,w⟫_ℝ=0) (hy : ⟪S.y p,w⟫_ℝ=0) :
    OutsideLeading (S.cubic p) (S.jet p) (S.axis p) (S.x p) (S.y p) w := by
  obtain ⟨hU,hg⟩ := S.normalized_jet_data hm
  have h₁ := S.normalized_eigenvector hm.1 (S.eigenvectors hm.1).1
  have h₂ := S.normalized_eigenvector hm.1 (S.eigenvectors hm.1).2
  constructor <;> simp only [jetEntry,cubicEntry,S.normalized_axis hm.1,h₁,h₂,hU,hg,one_smul,
    inner_add_left,real_inner_smul_left,he,hx,hy] <;> ring

end EuclideanMidpointRigidity.Quartic
