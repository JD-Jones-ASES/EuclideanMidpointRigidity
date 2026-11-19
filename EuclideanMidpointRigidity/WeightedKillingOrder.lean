module

public import EuclideanMidpointRigidity.SymmetricJet
public import EuclideanMidpointRigidity.DirectionalDerivatives

/-! # Fourth derivatives in the image of a weighted Killing equation -/

public section
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity
open Quartic
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d
set_option backward.isDefEq.respectTransparency false

theorem weighted_killing_order {W : Set E} {C : E → T} (hW : IsOpen W) (hC : ContDiffOn ℝ ∞ C W)
    (B : E →L[ℝ] E) (hk : ∀ p ∈ W, ∀ z, directionProfile z (fderiv ℝ C p (B z))=0)
    {p : E} (hp : p ∈ W) (v : E) : directions C [B v,B v,B v,B v] p=0 := by
  have jet (xs : List E) (z : E) : directionProfile z (fderiv ℝ (directions C xs) p (B z))=0 := by
    let g := directions C [B z]
    have he : directionProfile z ∘ g =ᶠ[𝓝 p] (fun _ ↦ 0) :=
      (show ∀ᶠ q in 𝓝 p, q ∈ W from hW.mem_nhds hp).mono fun q hq ↦ hk q hq z
    have hh := (directions.congr_germ he xs).eq_of_nhds
    rw [directions.zero,directions.linear_map hW (directions.smooth hW hC [B z]) (directionProfile z) xs hp] at hh
    have perm : (B z::xs).Perm (xs++[B z]) := (List.perm_append_singleton _ _).symm
    have eq := directions.perm hW hC perm hp
    rw [directions.append] at eq
    exact (congrArg (directionProfile z) eq).trans hh
  have sym (xs : List E) (a b c e : E) :=
    symJet_of_killing (J := (fderiv ℝ (directions C xs) p).comp B) (jet xs) a b c e
  apply (amplitude_eq_zero_iff _).mp
  obtain ⟨z,_,hz,_⟩ := exists_maximizing_direction (directions C [B v,B v,B v,B v] p)
  rw [hz]
  let w := B v
  let q := B z
  have h₁ := sym [w,w,w] v z z z
  have h₂ := sym [q,w,w] v v z z
  have h₃ := sym [q,q,w] v v v z
  have h₄ := sym [q,q,q] v v v v
  have s₁ : directions C (w::q::[w,w]) p=directions C (q::w::[w,w]) p :=
    directions.perm hW hC (List.Perm.swap q w _) hp
  have s₂ : directions C [w,q,q,w] p=directions C [q,q,w,w] p :=
    directions.perm hW hC ((List.Perm.swap q w _).trans ((List.Perm.swap q w _).cons q)) hp
  have s₃ : directions C [w,q,q,q] p=directions C [q,q,q,w] p :=
    directions.perm hW hC (List.perm_append_singleton w [q,q,q]).symm hp
  have val (xs : List E) (a b c e : E) :
      jetEntry ((fderiv ℝ (directions C xs) p).comp B) a b c e=cubicEntry (directions C (B a::xs) p) b c e := rfl
  simp only [symJet,val] at h₁ h₂ h₃ h₄
  rw [directionProfile_apply]
  change cubicEntry (directions C [w,w,w,w] p) z z z=0
  simp only [show B v=w from rfl,show B z=q from rfl,s₁,s₂,s₃,cubicEntry_swap₁,cubicEntry_swap₂] at h₁ h₂ h₃ h₄
  linarith only [h₁,h₂,h₃,h₄]

end EuclideanMidpointRigidity

