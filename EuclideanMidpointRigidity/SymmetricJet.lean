module

public import EuclideanMidpointRigidity.KillingCubics
public import EuclideanMidpointRigidity.QuarticHighRows

/-! # Complete polarization of the derivative of a symmetric cubic -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity.Quartic
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d

def symJet (J : E →L[ℝ] T) (w x y z : E) :=
  jetEntry J w x y z+jetEntry J x w y z+jetEntry J y w x z+jetEntry J z w x y

private theorem rotate (J : E →L[ℝ] T) (w x y z : E) : symJet J w x y z=symJet J x y z w := by
  simp only [symJet,jetEntry_swap₁,jetEntry_swap₂]; ring

private theorem add_first (J : E →L[ℝ] T) (a b x y z : E) :
    symJet J (a+b) x y z=symJet J a x y z+symJet J b x y z := by
  simp only [symJet,jetEntry,cubicEntry,map_add,K_add_coeff,K_add_left,inner_add_left]; ring

private theorem smul_first (J : E →L[ℝ] T) (r : ℝ) (a x y z : E) :
    symJet J (r • a) x y z=r*symJet J a x y z := by
  simp only [symJet,jetEntry,cubicEntry,map_smul,K_smul_coeff,K_smul_left,real_inner_smul_left]; ring

private theorem add_second (J : E →L[ℝ] T) (w a b y z : E) :
    symJet J w (a+b) y z=symJet J w a y z+symJet J w b y z := by
  rw [rotate,add_first,← rotate J w a y z,← rotate J w b y z]

private theorem add_third (J : E →L[ℝ] T) (w x a b z : E) :
    symJet J w x (a+b) z=symJet J w x a z+symJet J w x b z := by
  rw [rotate,add_second,← rotate J w x a z,← rotate J w x b z]

private theorem add_last (J : E →L[ℝ] T) (w x y a b : E) :
    symJet J w x y (a+b)=symJet J w x y a+symJet J w x y b := by
  rw [rotate,add_third,← rotate J w x y a,← rotate J w x y b]

private theorem swap_middle (J : E →L[ℝ] T) (w x y z : E) :
    symJet J w x y z=symJet J w y x z := by simp only [symJet,jetEntry_swap₁,jetEntry_swap₂]; ring

private theorem swap_last (J : E →L[ℝ] T) (w x y z : E) :
    symJet J w x y z=symJet J w x z y := by simp only [symJet,jetEntry_swap₁,jetEntry_swap₂]; ring

theorem symJet_of_killing {J : E →L[ℝ] T} (h : ∀ v, directionProfile v (J v)=0) (w x y z : E) :
    symJet J w x y z=0 := by
  have diag (v : E) : symJet J w v v v=0 := by
    have hh := polarize_killing_jet h v w
    have hslot : ⟪w,K (J v) v v⟫_ℝ=jetEntry J v w v v := by
      exact (real_inner_comm _ _).trans ((jetEntry_swap₂ J v v v w).trans (jetEntry_swap₁ J v v w v))
    rw [directionProfile_apply,hslot] at hh
    dsimp only [symJet,jetEntry,cubicEntry] at hh ⊢
    linarith only [hh]
  have e := diag (x+y+z)
  have exy := diag (x+y)
  have exz := diag (x+z)
  have eyz := diag (y+z)
  simp only [add_second,add_third,add_last,swap_middle,swap_last] at e exy exz eyz ⊢
  linarith only [e,exy,exz,eyz,diag x,diag y,diag z]

theorem killing_of_symJet_basis {ι : Type*} (B : Module.Basis ι ℝ E) {J : E →L[ℝ] T}
    (h : ∀ i j k l, symJet J (B i) (B j) (B k) (B l)=0) (v : E) :
    directionProfile v (J v)=0 := by
  have extend (x y z : E) (hh : ∀ i, symJet J (B i) x y z=0) (w : E) : symJet J w x y z=0 := by
    let L : E →ₗ[ℝ] ℝ := ⟨⟨fun q ↦ symJet J q x y z,fun a b ↦ add_first _ _ _ _ _ _⟩,fun r a ↦ smul_first _ _ _ _ _ _⟩
    have hL : L=0 := B.ext hh
    exact DFunLike.congr_fun hL w
  have mixed (w x y z : E) : symJet J w x y z=0 := by
    apply extend
    intro i
    rw [rotate]
    apply extend
    intro j
    rw [rotate]
    apply extend
    intro k
    rw [rotate]
    exact extend _ _ _ (fun l ↦ h l i j k) _
  have hz := mixed v v v v
  rw [directionProfile_apply]
  dsimp only [symJet,jetEntry,cubicEntry] at hz
  linarith only [hz]

end EuclideanMidpointRigidity.Quartic

