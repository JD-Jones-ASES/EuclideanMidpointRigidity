module

public import EuclideanMidpointRigidity.AmplitudeSubstitution
public import EuclideanMidpointRigidity.SixthDirichlet
public import EuclideanMidpointRigidity.UniformPolynomial

/-! # Endpoint data and time derivatives of the sixth-order trajectories -/

@[expose] public section
noncomputable section
open Set
namespace EuclideanMidpointRigidity.Jet

variable {d : ℕ}
local notation "E" => Space d

def positionCoefficient (paths : List TimePolynomial) (f : Tree → E) (t : ℝ) (j : ℕ) : E :=
  value (paths[j]?.getD []) f t

def velocityCoefficient (paths : List TimePolynomial) (f : Tree → E) (t : ℝ) (j : ℕ) : E :=
  value (differentiate (paths[j]?.getD [])) f t

def displacement (σ : ℚ) (f : Tree → E) (ε t : ℝ) : E :=
  amplitudeSum 6 ε (positionCoefficient (signedPaths σ) f t)

def velocity (σ : ℚ) (f : Tree → E) (ε t : ℝ) : E :=
  amplitudeSum 6 ε (velocityCoefficient (signedPaths σ) f t)

def acceleration (σ : ℚ) (f : Tree → E) (ε t : ℝ) : E :=
  amplitudeSum 6 ε (fun j ↦ value (forcing σ (signedPaths σ) j) f t)

theorem pathTerm_one (σ : ℚ) : pathTerm σ 1 = [⟨.direction,1,1⟩] := rfl

theorem position_one (σ : ℚ) (f : Tree → E) (t : ℝ) :
    positionCoefficient (signedPaths σ) f t 1 = t • f .direction := by
  change value (pathTerm σ 1) f t = _
  rw [pathTerm_one]
  simp [value,Term.value]

theorem velocity_one (σ : ℚ) (f : Tree → E) (t : ℝ) :
    velocityCoefficient (signedPaths σ) f t 1 = f .direction := by
  change value (differentiate (pathTerm σ 1)) f t = _
  rw [pathTerm_one]
  simp [differentiate,value,Term.value]

private theorem hasDerivAt_weightedSum (ns : List ℕ) (ε t : ℝ) (X Y : ℕ → ℝ → E)
    (h : ∀ i ∈ ns, HasDerivAt (X i) (Y i t) t) :
    HasDerivAt (fun s ↦ (ns.map fun i ↦ ε^i • X i s).sum)
      ((ns.map fun i ↦ ε^i • Y i t).sum) t := by
  induction ns with
  | nil => exact hasDerivAt_const _ _
  | cons i ns ih =>
    exact ((h i (by simp)).const_smul (ε^i)).fun_add (ih (fun j hj ↦ h j (by simp [hj])))

theorem hasDerivAt_displacement (σ : ℚ) (f : Tree → E) (ε t : ℝ) :
    HasDerivAt (displacement σ f ε) (velocity σ f ε t) t := by
  exact hasDerivAt_weightedSum (positiveOrders 6) ε t
    (fun i s ↦ positionCoefficient (signedPaths σ) f s i)
    (fun i s ↦ velocityCoefficient (signedPaths σ) f s i) (fun _ _ ↦ hasDerivAt_value _ f t)

theorem hasDerivAt_velocity {σ : ℚ} (hσ : σ=1 ∨ σ= -1) (f : Tree → E) (ε t : ℝ) :
    HasDerivAt (velocity σ f ε) (acceleration σ f ε t) t := by
  refine hasDerivAt_weightedSum (positiveOrders 6) ε t
    (fun i s ↦ velocityCoefficient (signedPaths σ) f s i)
    (fun i s ↦ value (forcing σ (signedPaths σ) i) f s) ?_
  intro i hi
  change i ∈ ([1,2,3,4,5,6] : List ℕ) at hi
  rcases List.mem_cons.mp hi with rfl | hmem
  · change HasDerivAt (fun s ↦ velocityCoefficient (signedPaths σ) f s 1) (0:E) t
    simp only [velocity_one]
    exact hasDerivAt_const t (f .direction)
  · exact ((dirichlet_equations hσ hmem f).2.2 t).2

theorem displacement_endpoints {σ : ℚ} (hσ : σ=1 ∨ σ= -1) (f : Tree → E) (ε : ℝ) :
    displacement σ f ε (-1) = -(ε • f .direction) ∧ displacement σ f ε 1 = ε • f .direction := by
  have hend (t : ℝ) (ht : ∀ i ∈ ([2,3,4,5,6] : List ℕ), positionCoefficient (signedPaths σ) f t i=0) :
      displacement σ f ε t = ε • (t • f .direction) := by
    simp only [displacement, amplitudeSum, show positiveOrders 6=[1,2,3,4,5,6] from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, position_one, ht 2 (by decide),
      ht 3 (by decide), ht 4 (by decide), ht 5 (by decide), ht 6 (by decide), smul_zero,
      add_zero,pow_one]
  exact ⟨by simpa using hend (-1) (fun _ hi ↦ (dirichlet_equations hσ hi f).1),
    by simpa using hend 1 (fun _ hi ↦ (dirichlet_equations hσ hi f).2.1)⟩

theorem trajectory_size (σ : ℚ) (f : Tree → E) :
    ∃ B : ℝ, 1≤B ∧ ∀ ε t : ℝ, |ε|≤1 → t ∈ Icc (-1:ℝ) 1 →
      ‖displacement σ f ε t‖ ≤ B*|ε| ∧ ‖velocity σ f ε t‖ ≤ B*|ε| := by
  have hp (i : ℕ) (hi : i ∈ positiveOrders 6) : 1 ≤ i := by
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
    omega
  have bound (P : ℕ → TimePolynomial) := compact_power_sum_bound (positiveOrders 6) id
    (fun i ↦ value (P i) f) (isCompact_Icc (a := (-1:ℝ)) (b := 1)) 1 hp
    (fun i _ ↦ (continuous_iff_continuousAt.mpr fun t ↦ (hasDerivAt_value (P i) f t).continuousAt).continuousOn)
  obtain ⟨B₁,h₁,hX⟩ := bound (pathTerm σ)
  obtain ⟨B₂,h₂,hV⟩ := bound (fun i ↦ differentiate (pathTerm σ i))
  refine ⟨max 1 (max B₁ B₂), le_max_left _ _,?_⟩
  intro ε t hε ht
  have hx := hX ε t hε ht
  have hv := hV ε t hε ht
  simp only [pow_one,id_eq,pathTerm] at hx hv
  dsimp only [displacement,velocity,amplitudeSum,positionCoefficient,velocityCoefficient]
  exact ⟨hx.trans (mul_le_mul_of_nonneg_right
    ((le_max_left B₁ B₂).trans (le_max_right 1 _)) (abs_nonneg ε)),
    hv.trans (mul_le_mul_of_nonneg_right
    ((le_max_right B₁ B₂).trans (le_max_right 1 _)) (abs_nonneg ε))⟩

end EuclideanMidpointRigidity.Jet
