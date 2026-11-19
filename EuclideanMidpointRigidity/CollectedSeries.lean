module

public import EuclideanMidpointRigidity.UniformPolynomial

/-! # Exact low coefficients and uniform bounds for the remaining terms -/

@[expose] public section
namespace EuclideanMidpointRigidity
open Set
variable {α V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def degreeCoefficient (terms : List α) (degree : α → ℕ) (f : α → V) (k : ℕ) : V :=
  ((terms.filter (fun a ↦ decide (degree a=k))).map f).sum

private theorem degreeCoefficient_cons (a : α) (terms : List α) (degree : α → ℕ)
    (f : α → V) (k : ℕ) :
    degreeCoefficient (a::terms) degree f k =
      (if degree a=k then f a else 0) + degreeCoefficient terms degree f k := by
  by_cases h : degree a=k <;> simp [degreeCoefficient,h]

theorem collect_amplitude_degrees (terms : List α) (degree : α → ℕ) (f : α → V)
    (cut : ℕ) (ε : ℝ) :
    (terms.map (fun a ↦ ε^(degree a) • f a)).sum =
      (∑ k ∈ Finset.range (cut+1), ε^k • degreeCoefficient terms degree f k) +
      (((terms.filter (fun a ↦ decide (cut<degree a))).map fun a ↦ ε^(degree a) • f a).sum) := by
  induction terms with
  | nil => simp [degreeCoefficient]
  | cons a terms ih =>
    have hsingle : (∑ k ∈ Finset.range (cut+1), ε^k • (if degree a=k then f a else 0)) =
        if degree a≤cut then ε^(degree a) • f a else 0 := by
      simp [smul_ite,Nat.lt_succ_iff]
    simp only [List.map_cons,List.sum_cons,degreeCoefficient_cons,smul_add,Finset.sum_add_distrib,
      hsingle,ih]
    by_cases h : cut<degree a
    · simp [h,(not_le.mpr h)]
      abel
    · simp [h,le_of_not_gt h,add_assoc]

theorem uniform_remainder_after_collection (terms : List α) (degree : α → ℕ)
    (f : α → ℝ → V) {S : Set ℝ} (hS : IsCompact S) (cut : ℕ)
    (hf : ∀ a ∈ terms, ContinuousOn (f a) S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (ε t : ℝ), |ε|≤1 → t ∈ S →
      ‖(terms.map (fun a ↦ ε^(degree a) • f a t)).sum -
        (∑ k ∈ Finset.range (cut+1), ε^k • degreeCoefficient terms degree (fun a ↦ f a t) k)‖
        ≤ M*|ε|^(cut+1) := by
  let high := terms.filter (fun a ↦ decide (cut<degree a))
  have hi {a : α} (ha : a ∈ high) : a ∈ terms ∧ cut<degree a := by
    simpa [high] using ha
  obtain ⟨M,hM,hb⟩ := compact_power_sum_bound high degree f hS (cut+1)
    (fun _ h ↦ (hi h).2) (fun _ h ↦ hf _ (hi h).1)
  refine ⟨M,hM,?_⟩
  intro ε t hε ht
  rw [collect_amplitude_degrees terms degree (fun a ↦ f a t) cut ε,add_sub_cancel_left]
  exact hb ε t hε ht

end EuclideanMidpointRigidity
