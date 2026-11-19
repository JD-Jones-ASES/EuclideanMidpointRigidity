module

public import EuclideanMidpointRigidity.FlatForceJets

/-! # The three spatial, mixed, and velocity terms in the projected third endpoint variation -/

@[expose] public section
noncomputable section
open Set
open scoped ContDiff InnerProductSpace
namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d

structure TiltData where
  q : ℝ
  p₁ : ℝ
  p₂ : ℝ
  p₃ : ℝ
  r₁ : ℝ
  r₂ : ℝ
  r₃ : ℝ

namespace TiltData

def atPoint (D : E → T) (x u i j l o : E) : TiltData where
  q := ⟪o,K (directions D [i,j,l] x) u u⟫_ℝ
  p₁ := ⟪o,K (directions D [j,l] x) u i⟫_ℝ
  p₂ := ⟪o,K (directions D [i,l] x) u j⟫_ℝ
  p₃ := ⟪o,K (directions D [i,j] x) u l⟫_ℝ
  r₁ := ⟪o,K (directions D [i] x) j l⟫_ℝ
  r₂ := ⟪o,K (directions D [j] x) i l⟫_ℝ
  r₃ := ⟪o,K (directions D [l] x) i j⟫_ℝ

def eval (D : TiltData) (a b c x y z : ℝ) :=
  D.q*a*b*c+2*(D.p₁*x*b*c+D.p₂*a*y*c+D.p₃*a*b*z)+2*(D.r₁*a*y*z+D.r₂*x*b*z+D.r₃*x*y*c)

def reflect (D : TiltData) : TiltData := {D with p₁ := -D.p₁, p₂ := -D.p₂, p₃ := -D.p₃}

theorem atPoint_neg (D : E → T) (x u i j l o : E) : atPoint D x (-u) i j l o=(atPoint D x u i j l o).reflect := by
  simp [atPoint,reflect,K_neg_left,K_neg_right,inner_neg_right]

private theorem head (D : E → T) (xs : List E) (x v : E) (s : ℝ) :
    directions D ((s • v)::xs) x=s • directions D (v::xs) x := map_smul _ _ _

private theorem scale2 {W : Set E} {D : E → T} (hW : IsOpen W) (hD : ContDiffOn ℝ ∞ D W)
    {p : E} (hp : p ∈ W) (v w : E) (a b : ℝ) (xs : List E) :
    directions D ((a • v)::(b • w)::xs) p=(a*b) • directions D (v::w::xs) p := by
  rw [head,directions.perm hW hD (List.Perm.swap (b • w) v xs) hp,head,
    directions.perm hW hD (List.Perm.swap v w xs) hp,smul_smul]

private theorem scale3 {W : Set E} {D : E → T} (hW : IsOpen W) (hD : ContDiffOn ℝ ∞ D W)
    {p : E} (hp : p ∈ W) (i j l : E) (a b c : ℝ) :
    directions D [a • i,b • j,c • l] p=(a*b*c) • directions D [i,j,l] p := by
  rw [scale2 hW hD hp]
  have hperm (w : E) : [i,j,w].Perm [w,i,j] := List.perm_middle (l₁ := [i,j]) (l₂ := [])
  rw [directions.perm hW hD (hperm _) hp,head,directions.perm hW hD (hperm l).symm hp,smul_smul]

theorem inner_triple {W : Set E} {D : E → T} (hW : IsOpen W) (hD : ContDiffOn ℝ ∞ D W) {p : E}
    (hp : p ∈ W) (u i j l o : E) (k a b c x y z : ℝ) :
    ⟪o,tripleForce D p (k • u) (a • i,(k*x) • i) (b • j,(k*y) • j) (c • l,(k*z) • l)⟫_ℝ=
      k^2*(atPoint D p u i j l o).eval a b c x y z := by
  simp only [tripleForce,Prod.fst,Prod.snd,scale3 hW hD hp,scale2 hW hD hp,head,K_smul_coeff,K_smul_left,K_smul_right,
    inner_add_right,real_inner_smul_right,atPoint,eval]
  ring

end TiltData
end EuclideanMidpointRigidity

