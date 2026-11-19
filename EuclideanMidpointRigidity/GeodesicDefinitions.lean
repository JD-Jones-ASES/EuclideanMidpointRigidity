module

public import EuclideanMidpointRigidity.Basic

@[expose] public section

open Set Metric

namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

/-- An affinely parametrized geodesic for the connection with coefficient `σ K`. -/
def IsGeodesicSegment (C : E → Coeff) (σ : ℝ) (γ v : ℝ → E) : Prop :=
  (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt γ (v t) t) ∧
  (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt v (-σ • K (C (γ t)) (v t) (v t)) t)

/-- Position and velocity stay in a small neighborhood of the zero-velocity phase. -/
def IsShortGeodesic (C : E → Coeff) (σ : ℝ) (p : E) (r : ℝ)
    (P Q : E) (γ v : ℝ → E) : Prop :=
  IsGeodesicSegment C σ γ v ∧ γ 0 = P ∧ γ 1 = Q ∧
    ∀ t ∈ Icc (0 : ℝ) 1, ‖γ t - p‖ < r ∧ ‖v t‖ < r

/-- The midpoint of the unique short geodesic for each pair of nearby endpoints. -/
def IsCanonicalLocalMidpoint (Ω : Set E) (C : E → Coeff) (σ : ℝ)
    (p : E) (r : ℝ) (W : Set (E × E)) (A : E → E → E) : Prop :=
  0 < r ∧ ball p r ⊆ Ω ∧ IsOpen W ∧ (p, p) ∈ W ∧
  ∀ P Q, (P, Q) ∈ W → ∃ γ v,
    IsShortGeodesic C σ p r P Q γ v ∧ A P Q = γ midpointTime ∧
    ∀ γ' v', IsShortGeodesic C σ p r P Q γ' v' →
      ∀ t ∈ Icc (0 : ℝ) 1, γ' t = γ t ∧ v' t = v t

/-- The canonical midpoints of the dual connections are complementary near the diagonal. -/
def LocalMidpointInvariance (Ω : Set E) (C : E → Coeff) : Prop :=
  ∀ p ∈ Ω, ∃ rPlus rMinus W APlus AMinus,
    IsCanonicalLocalMidpoint Ω C 1 p rPlus W APlus ∧
    IsCanonicalLocalMidpoint Ω C (-1) p rMinus W AMinus ∧
    ∀ P Q, (P, Q) ∈ W → APlus P Q + AMinus P Q = P + Q

def ArbitrarilyShortComplementaryPairs (C : E → Coeff) (p : E) : Prop :=
  ∀ r > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ P Q,
    P ∈ ball p δ → Q ∈ ball p δ → ∃ γPlus vPlus γMinus vMinus,
      IsShortGeodesic C 1 p r P Q γPlus vPlus ∧
      IsShortGeodesic C (-1) p r P Q γMinus vMinus ∧
      γPlus (1/2) + γMinus (1/2) = P + Q

end EuclideanMidpointRigidity
