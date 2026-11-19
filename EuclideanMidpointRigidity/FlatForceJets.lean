module

public import EuclideanMidpointRigidity.PhaseProducts

/-! # The third force jet at a field variation vanishing through the axial slots -/

@[expose] public section
noncomputable section
open Set
open scoped ContDiff
namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d
local notation "H" => E × E
local notation "T" => Cubic d

def phaseCore (D : E → T) (q : H) := K (D q.1) q.2 q.2

structure FlatAxialForce (D : Space d → Cubic d) (x u : Space d) : Prop where
  value : D x=0
  first : ∀ v w, K (directions D [v] x) u w=0
  second : ∀ v w, K (directions D [v,w] x) u u=0

theorem FlatAxialForce.flat {W : Set E} {D : E → T} (hW : IsOpen W) (hD : ContDiffOn ℝ ∞ D W)
    {x u : E} (hx : x ∈ W) (H₀ : FlatAxialForce D x u) (k : ℝ) (xs : List H) (hn : xs.length<3) :
    directions (phaseCore D) xs (x,k • u)=0 := by
  rw [show directions (phaseCore D) xs (x,k • u)=PhaseProduct.sumValue (PhaseProduct.terms xs) D (x,k • u) from
    PhaseProduct.jet_formula hW hD xs (show (x,k • u) ∈ (Prod.fst ⁻¹' W : Set H) from hx)]
  have h₀ : directions D [] x=0 := H₀.value
  have hk (v w : E) : K (0:T) v w=0 := rfl
  have hr (v w : E) : K (directions D [v] x) w u=0 := (K_symm _ _ _).trans (H₀.first v w)
  rcases xs with _|⟨a,_|⟨b,_|⟨c,cs⟩⟩⟩
  · simp [PhaseProduct.terms,PhaseProduct.sumValue,PhaseProduct.value,h₀,hk]
  · simp [PhaseProduct.terms,PhaseProduct.sumValue,PhaseProduct.derivative,PhaseProduct.value,K_smul_left,K_smul_right,h₀,hk,H₀.first]
  · simp [PhaseProduct.terms,PhaseProduct.sumValue,PhaseProduct.derivative,PhaseProduct.value,K_smul_left,K_smul_right,h₀,hk,H₀.first,H₀.second,hr]
  · simp only [List.length_cons] at hn; omega

def tripleForce (D : E → T) (x v : E) (a b c : H) :=
  K (directions D [a.1,b.1,c.1] x) v v+
  (2:ℝ) • (K (directions D [b.1,c.1] x) v a.2+K (directions D [a.1,c.1] x) v b.2+
    K (directions D [a.1,b.1] x) v c.2)+
  (2:ℝ) • (K (directions D [a.1] x) b.2 c.2+K (directions D [b.1] x) a.2 c.2+
    K (directions D [c.1] x) a.2 b.2)

theorem triple_force_formula {W : Set E} {D : E → T} (hW : IsOpen W) (hD : ContDiffOn ℝ ∞ D W)
    {x : E} (hx : x ∈ W) (v : E) (a b c : H) : directions (phaseCore D) [a,b,c] (x,v)=tripleForce D x v a b c := by
  rw [show directions (phaseCore D) [a,b,c] (x,v)=_ from
    PhaseProduct.jet_formula hW hD [a,b,c] (show (x,v) ∈ (Prod.fst ⁻¹' W : Set H) from hx)]
  simp [PhaseProduct.terms,PhaseProduct.sumValue,PhaseProduct.derivative,PhaseProduct.value,tripleForce,K_symm]
  module

end EuclideanMidpointRigidity

