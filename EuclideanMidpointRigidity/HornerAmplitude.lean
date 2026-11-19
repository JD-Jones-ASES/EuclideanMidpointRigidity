module

public import EuclideanMidpointRigidity.TaylorModel
public import EuclideanMidpointRigidity.AmplitudeSubstitution
public import EuclideanMidpointRigidity.UniformPolynomial

/-! # Uniqueness of the coefficients of a finite amplitude expansion -/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity.Jet

theorem amplitudeSum_eq_range {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (m : ℕ) (ε : ℝ) (X : ℕ → V) (h0 : X 0 = 0) :
    amplitudeSum m ε X = ∑ k ∈ Finset.range (m+1), ε^k • X k := by
  rw [Finset.sum_range_succ']
  simp only [amplitudeSum, positiveOrders, List.map_map, Function.comp_def, sum_map_range,
    h0,smul_zero,add_zero]

theorem amplitudeSum_add {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (m : ℕ) (t : ℝ) (X Y : ℕ → V) :
    amplitudeSum m t (fun i ↦ X i+Y i) = amplitudeSum m t X+amplitudeSum m t Y := by
  simp only [amplitudeSum,positiveOrders,List.map_map,Function.comp_def,sum_map_range,
    smul_add,Finset.sum_add_distrib]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem horner_range (X : ℕ → V) (n : ℕ) (t : ℝ) :
    horner ((List.range n).map X) t = ∑ i ∈ Finset.range n, t^i • X i := by
  induction n generalizing X with
  | zero => simp [horner]
  | succ n ih =>
    rw [List.range_succ_eq_map,List.map_cons,List.map_map,horner,ih,
      Finset.sum_range_succ' (fun i ↦ t^i • X i) n,Finset.smul_sum]
    simp only [Function.comp_def, pow_zero, one_smul, pow_succ', smul_smul]
    rw [add_comm]

theorem last_coefficient_zero (m : ℕ) (X : ℕ → V) (h0 : X 0=0) {δ M : ℝ} (hδ : 0<δ)
    (hb : ∀ t : ℝ, 0<t → t<δ → ‖amplitudeSum m t X‖ ≤ M*t^(m+1)) : X m=0 := by
  let cs := (List.range (m+1)).map X
  refine horner_coefficients_zero cs (M := M) hδ ?_ (X m)
    (List.mem_map.mpr ⟨m,List.mem_range.mpr (Nat.lt_succ_self m),rfl⟩)
  intro t ht htd
  simpa only [cs,List.length_map,List.length_range,horner_range,← amplitudeSum_eq_range _ t X h0]
    using hb t ht htd

end EuclideanMidpointRigidity.Jet
