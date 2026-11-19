module

public import EuclideanMidpointRigidity.Basic
public import EuclideanMidpointRigidity.SymmetricTaylor
public import EuclideanMidpointRigidity.SixthRecursion
public import EuclideanMidpointRigidity.JetCalculus

/-! # Interpretation of Taylor trees by the spatial derivatives of a cubic -/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity.Jet

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d
abbrev Derivatives (d : ℕ) := ∀ k, SpatialForm (Space d) (Cubic d) k

def Tree.realize (D : Derivatives d) (z : E) : Tree → E
  | .direction => z
  | .k u v => K (listForm D []) (u.realize D z) (v.realize D z)
  | .j p u v => K (listForm D [p.realize D z]) (u.realize D z) (v.realize D z)
  | .hess p q u v => K (listForm D [p.realize D z,q.realize D z]) (u.realize D z) (v.realize D z)
  | .third p q r u v => K (listForm D [p.realize D z,q.realize D z,r.realize D z])
      (u.realize D z) (v.realize D z)
  | .fourth p q r s u v => K (listForm D [p.realize D z,q.realize D z,r.realize D z,s.realize D z])
      (u.realize D z) (v.realize D z)

private theorem insertTree_perm (x : Tree) (xs : List Tree) :
    (insertTree x xs).Perm (x::xs) := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [insertTree]
    split
    · rfl
    · exact (ih.cons y).trans (List.Perm.swap _ _ _)

private theorem sorted_perm (xs : List Tree) : (xs.foldr insertTree []).Perm xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact (insertTree_perm x _).trans (ih.cons x)

private theorem branch_realize {ps : List Tree} {u v w : Tree} (hw : branch ps u v = some w)
    (D : Derivatives d) (z : E) :
    w.realize D z = K (listForm D (ps.map (Tree.realize D z))) (u.realize D z) (v.realize D z) := by
  unfold branch at hw
  split at hw <;> simp_all <;> subst w <;> rfl

theorem product_realize {ps : List Tree} {u v w : Tree} (hw : product ps u v = some w)
    (D : Derivatives d) (z : E) :
    w.realize D z = K (listForm D (ps.map (Tree.realize D z))) (u.realize D z) (v.realize D z) := by
  have hs := listForm_perm D ((sorted_perm ps).map (Tree.realize D z))
  unfold product at hw
  split at hw
  · simpa only [hs] using branch_realize hw D z
  · rw [K_symm]
    simpa only [hs] using branch_realize hw D z

private theorem branch_exists (ps : List Tree) (u v : Tree) (hs : ps.length ≤ 4) :
    ∃ w, branch ps u v = some w := by
  rcases ps with _ | ⟨a,ps⟩
  · exact ⟨_,rfl⟩
  rcases ps with _ | ⟨b,ps⟩
  · exact ⟨_,rfl⟩
  rcases ps with _ | ⟨c,ps⟩
  · exact ⟨_,rfl⟩
  rcases ps with _ | ⟨d,ps⟩
  · exact ⟨_,rfl⟩
  rcases ps with _ | ⟨e,ps⟩
  · exact ⟨_,rfl⟩
  simp at hs
  omega

theorem product_exists (ps : List Tree) (u v : Tree) (hs : ps.length ≤ 4) :
    ∃ w, product ps u v = some w := by
  have hl := (sorted_perm ps).length_eq.trans_le hs
  unfold product
  split <;> exact branch_exists _ _ _ hl

/-- The tree values use the symmetrized spatial Taylor forms of the actual field. -/
def fieldDerivatives (C : E → Coeff) (p : E) : Derivatives d :=
  fun k ↦ iteratedFDeriv ℝ k C p

end EuclideanMidpointRigidity.Jet
