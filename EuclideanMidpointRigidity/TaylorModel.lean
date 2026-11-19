module

public import EuclideanMidpointRigidity.JetInterpretation

/-! # Relating the tree coefficients to the ordinary spatial Taylor polynomial -/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity.Jet

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

def taylorModel (D : Derivatives d) (n : ℕ) (v : E) : Coeff :=
  ((List.range (n+1)).map fun s ↦ (s.factorial:ℝ)⁻¹ • listForm D (List.replicate s v)).sum

theorem listForm_replicate (D : Derivatives d) (n : ℕ) (v : E) :
    listForm D (List.replicate n v) = D n (fun _ ↦ v) := by
  have hv : (List.replicate n v).get = fun _ ↦ v := by
    funext i
    simp
  rw [listForm, hv, symmetricPart_diagonal]
  exact congrArg (fun k ↦ D k (fun _ ↦ v)) (List.length_replicate (n := n) (a := v))

theorem sum_map_range {V : Type*} [AddCommMonoid V] (f : ℕ → V) (n : ℕ) :
    ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem taylorModel_field (C : E → Coeff) (p : E) (n : ℕ) (v : E) :
    taylorModel (fieldDerivatives C p) n v = spatialTaylor C n p v := by
  simp only [taylorModel, listForm_replicate, sum_map_range, fieldDerivatives, spatialTaylor]

end EuclideanMidpointRigidity.Jet
