module

public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic

/-! # Uniform polynomial remainders and uniqueness of midpoint coefficients -/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace EuclideanMidpointRigidity

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A finite sum of continuous time profiles with amplitude powers at least
`k` is uniformly of order `k` on a compact time interval. -/
theorem compact_power_sum_bound {α : Type*} (terms : List α) (deg : α → ℕ)
    (f : α → ℝ → V) {S : Set ℝ} (hs : IsCompact S) (k : ℕ)
    (hk : ∀ a ∈ terms, k ≤ deg a) (hf : ∀ a ∈ terms, ContinuousOn (f a) S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (ε t : ℝ), |ε| ≤ 1 → t ∈ S →
      ‖(terms.map (fun a ↦ ε^(deg a) • f a t)).sum‖ ≤ M*|ε|^k := by
  induction terms with
  | nil => exact ⟨0,le_rfl,by simp⟩
  | cons a terms ih =>
    obtain ⟨B,hB⟩ := hs.exists_bound_of_continuousOn (hf a (by simp))
    obtain ⟨M,hM,hrest⟩ := ih (fun i hi ↦ hk i (by simp [hi])) (fun i hi ↦ hf i (by simp [hi]))
    refine ⟨max B 0+M,by positivity,?_⟩
    intro ε t hε ht
    have hpow := pow_le_pow_of_le_one (abs_nonneg ε) hε (hk a (by simp))
    have hterm : ‖ε^(deg a) • f a t‖ ≤ |ε|^k * max B 0 := by
      rw [norm_smul, Real.norm_eq_abs, abs_pow]
      exact mul_le_mul hpow ((hB t ht).trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
    simp only [List.map_cons, List.sum_cons]
    calc
      _ ≤ _ := norm_add_le _ _
      _ ≤ |ε|^k * max B 0 + M*|ε|^k := add_le_add hterm (hrest ε t hε ht)
      _ = _ := by ring

def horner : List V → ℝ → V
  | [], _ => 0
  | a :: p, t => a+t • horner p t

theorem continuous_horner (p : List V) : Continuous (horner p) := by
  induction p with
  | nil => exact continuous_const
  | cons a p ih => exact continuous_const.add (continuous_id.smul ih)

/-- If the norm of a vector polynomial of degree below `p.length` has
one further order of decay, every coefficient vanishes. A one-sided
neighborhood at zero is sufficient. -/
theorem horner_coefficients_zero (p : List V) {δ M : ℝ} (hδ : 0 < δ)
    (hb : ∀ t : ℝ, 0<t → t<δ → ‖horner p t‖ ≤ M*t^p.length) :
    ∀ a ∈ p, a=0 := by
  induction p with
  | nil => simp
  | cons a p ih =>
    have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0<t := self_mem_nhdsWithin
    have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t<δ :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)
    have hnorm : Tendsto (fun x : ℝ ↦ ‖horner (a::p) x‖) (𝓝[>] 0) (𝓝 ‖horner (a::p) 0‖) :=
      (continuous_horner (a::p)).norm.continuousAt.continuousWithinAt
    have hlim : Tendsto (fun t : ℝ ↦ M*t^(a::p).length) (𝓝[>] 0) (𝓝 (M*(0:ℝ)^(a::p).length)) :=
      (continuous_const.mul (continuous_id.pow _)).continuousAt.continuousWithinAt
    have hle := le_of_tendsto_of_tendsto hnorm hlim
      ((hpos.and hsmall).mono fun t ht ↦ hb t ht.1 ht.2)
    have ha : a=0 := by simpa [horner] using hle
    have htail (t : ℝ) (ht : 0<t) (htδ : t<δ) : ‖horner p t‖ ≤ M*t^p.length := by
      have h := hb t ht htδ
      simp only [horner, ha, zero_add, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
        List.length_cons, pow_succ] at h
      apply le_of_mul_le_mul_right (a := t) _ ht
      linarith only [h]
    intro b hb'
    rcases List.mem_cons.mp hb' with rfl | hm
    · exact ha
    · exact ih htail b hm

end EuclideanMidpointRigidity
