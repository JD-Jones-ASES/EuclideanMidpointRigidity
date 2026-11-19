module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Tactic

/-! # A uniform Taylor bound for the coefficient field on a Euclidean ball -/

@[expose] public section
noncomputable section
open Set Metric Filter
open scoped Topology ContDiff
namespace EuclideanMidpointRigidity

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The ordinary derivative along the spatial line evaluates the iterated
Fréchet derivative on repeated copies of its velocity. -/
theorem iteratedDeriv_spatial_line {Ω : Set U} {f : U → V} (hΩ : IsOpen Ω)
    (hf : ContDiffOn ℝ ∞ f Ω) (p v : U) (t : ℝ) (ht : p+t • v ∈ Ω) (k : ℕ) :
    iteratedDeriv k (fun s : ℝ ↦ f (p+s • v)) t =
      iteratedFDeriv ℝ k f (p+t • v) (fun _ ↦ v) := by
  let A := (fun y : U ↦ p+y) ⁻¹' Ω
  let L := ContinuousLinearMap.toSpanSingleton ℝ v
  have hA : IsOpen A := hΩ.preimage (continuous_const.add continuous_id)
  have hB : IsOpen (L ⁻¹' A) := hA.preimage L.continuous
  have hshift : ContDiffOn ℝ ∞ (fun y : U ↦ f (p+y)) A :=
    hf.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ hx ↦ hx)
  have hcomp := L.iteratedFDerivWithin_comp_right hshift hA.uniqueDiffOn hB.uniqueDiffOn
    (show L t ∈ A from ht) (i := k) (by simp)
  rw [iteratedFDerivWithin_of_isOpen k hB (show t ∈ L ⁻¹' A from ht),
    iteratedFDerivWithin_of_isOpen k hA (show L t ∈ A from ht),
    iteratedFDeriv_comp_add_left] at hcomp
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change (iteratedFDeriv ℝ k ((fun y : U ↦ f (p+y)) ∘ L) t) (fun _ ↦ (1:ℝ)) = _
  rw [hcomp]
  simp [L]

def spatialTaylor (f : U → V) (n : ℕ) (p v : U) : V :=
  ∑ k ∈ Finset.range (n+1), ((k.factorial:ℝ)⁻¹) •
    iteratedFDeriv ℝ k f p (fun _ ↦ v)

/-- The bound and radius are independent of the displacement. In the sixth
geodesic coefficient calculation `n = 4` gives an order-five field error. -/
theorem exists_spatialTaylor_bound {Ω : Set U} {f : U → V} (hΩ : IsOpen Ω)
    (hf : ContDiffOn ℝ ∞ f Ω) {p : U} (hp : p ∈ Ω) (n : ℕ) :
    ∃ ρ M : ℝ, 0 < ρ ∧ 0 ≤ M ∧ ∀ v : U, ‖v‖ < ρ →
      ‖f (p+v) - spatialTaylor f n p v‖ ≤ M*‖v‖^(n+1) := by
  let M := ‖iteratedFDeriv ℝ (n+1) f p‖+1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hcont := (hf.contDiffAt (hΩ.mem_nhds hp)).continuousAt_iteratedFDeriv
    (k := n+1) (by simp)
  have hb : ∀ᶠ x in 𝓝 p, ‖iteratedFDeriv ℝ (n+1) f x‖ < M :=
    hcont.norm (Iio_mem_nhds (show ‖iteratedFDeriv ℝ (n+1) f p‖ < M by dsimp [M]; linarith))
  obtain ⟨ρ,hρ,hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (hΩ.mem_nhds hp) hb)
  refine ⟨ρ,M/(n.factorial:ℝ),hρ,by positivity,?_⟩
  intro v hv
  let line := fun t : ℝ ↦ p+t • v
  let F := f ∘ line
  have hseg {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : line t ∈ ball p ρ := by
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [line, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg v) ht.2).trans_lt hv
  have hF {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : ContDiffAt ℝ ∞ F t :=
    (hf.contDiffAt (hΩ.mem_nhds (hball (hseg ht)).1)).comp t
      (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  have heval (k : ℕ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
      iteratedDerivWithin k F (Icc (0:ℝ) 1) t =
        iteratedFDeriv ℝ k f (line t) (fun _ ↦ v) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      ((hF ht).of_le (by simp)) ht]
    exact iteratedDeriv_spatial_line hΩ hf p v t (hball (hseg ht)).1 k
  have hder (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      ‖iteratedDerivWithin (n+1) F (Icc (0:ℝ) 1) t‖ ≤ M*‖v‖^(n+1) := by
    rw [heval _ ht]
    have h := (iteratedFDeriv ℝ (n+1) f (line t)).le_opNorm (fun _ ↦ v)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hball (hseg ht)).2.le (by positivity))
  have hT := taylor_mean_remainder_bound
    (fun t (ht : t ∈ Icc (0:ℝ) 1) ↦ ((hF ht).of_le (m := (n+1:ℕ)) (by simp)).contDiffWithinAt)
    (show (1:ℝ) ∈ Icc 0 1 by simp) hder
  rw [taylor_within_apply] at hT
  simp only [sub_zero, one_pow, mul_one, heval _ (show (0:ℝ) ∈ Icc 0 1 by simp),
    F, Function.comp_apply, line, zero_smul, one_smul, add_zero] at hT
  unfold spatialTaylor
  convert hT using 1
  ring

end EuclideanMidpointRigidity
