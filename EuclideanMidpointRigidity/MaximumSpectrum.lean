module

public import EuclideanMidpointRigidity.CubicNorm

/-! # Spectral bounds at a global maximizing axis -/

@[expose] public section
open Set Filter
open scoped InnerProductSpace Topology
namespace EuclideanMidpointRigidity

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

private theorem cycle_slots (c : Coeff) (e v : E) :
    ⟪K c v v,e⟫_ℝ = ⟪K c e v,v⟫_ℝ := by
  rw [K_selfAdjoint, K_symm c v e, real_inner_comm]

private theorem cubic_even_part (c : Coeff) (e v : E) (s t : ℝ) :
    let P := fun x : E ↦ ⟪K c x x,x⟫_ℝ
    P (s • e + t • v) + P (s • e + (-t) • v) =
      2*s^3*P e + 6*s*t^2*⟪K c e v,v⟫_ℝ := by
  dsimp only
  simp only [K_add_left, K_add_right, K_smul_left, K_smul_right,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    K_symm c v e, cycle_slots c e v]
  ring

/-- In a transverse unit direction the normalized Rayleigh quotient lies in
`[-1,1/2]` when the maximum is positive. The upper endpoint is included. -/
theorem maximizing_axis_spectral_bounds {c : Coeff} {a : ℝ} (ha : 0 ≤ a)
    (diag : ∀ u : E, ‖u‖=1 → ⟪K c u u,u⟫_ℝ ≤ a) {e v : E}
    (he : ‖e‖=1) (hv : ‖v‖=1) (hort : ⟪e,v⟫_ℝ=0) (hmax : ⟪K c e e,e⟫_ℝ=a) :
    -a ≤ ⟪K c e v,v⟫_ℝ ∧ ⟪K c e v,v⟫_ℝ ≤ a/2 := by
  let b := ⟪K c e v,v⟫_ℝ
  have hnorm (z : E) := cubic_diagonal_norm_bound c a ha diag z
  have hlow := real_inner_le_norm (-K c v v) e
  rw [inner_neg_left, norm_neg, he, mul_one, cycle_slots] at hlow
  have hnv : ‖K c v v‖ ≤ a := by simpa [hv] using hnorm v
  refine ⟨by linarith,?_⟩
  let y := fun t : ℝ ↦ (1-t^2) • e + (2*t) • v
  have hlen (t : ℝ) : ‖y t‖ = 1+t^2 := by
    have h := norm_add_sq_real ((1-t^2) • e) ((2*t) • v)
    simp only [real_inner_smul_left, real_inner_smul_right, hort, mul_zero, add_zero,
      norm_smul, Real.norm_eq_abs, he, hv, mul_one, sq_abs] at h
    change ‖(1-t^2) • e+(2*t) • v‖ = 1+t^2
    nlinarith [norm_nonneg (y t), sq_nonneg t, sq_nonneg (t^2)]
  have hside (t : ℝ) : ⟪K c (y t) (y t),y t⟫_ℝ ≤ a*(1+t^2)^3 := by
    calc
      _ ≤ ‖K c (y t) (y t)‖ * ‖y t‖ := real_inner_le_norm _ _
      _ ≤ (a * ‖y t‖^2) * ‖y t‖ := mul_le_mul_of_nonneg_right (hnorm _) (norm_nonneg _)
      _ = _ := by rw [hlen]; ring
  have heven (t : ℝ) : (1-t^2)^3*a + 12*(1-t^2)*t^2*b ≤ a*(1+t^2)^3 := by
    have h := cubic_even_part c e v (1-t^2) (2*t)
    dsimp only at h
    rw [hmax] at h
    have h₂ := hside (-t)
    simp only [y, neg_sq, mul_neg] at h₂
    have h₁ := hside t
    dsimp [y] at h₁
    dsimp [b]
    linarith only [h,h₁,h₂]
  have hdiv (t : ℝ) (ht : 0<t) : 12*(1-t^2)*b ≤ a*(6+2*t^4) := by
    apply le_of_mul_le_mul_right (a := t^2) _ (sq_pos_of_pos ht)
    linarith only [heven t]
  have h₁ : Tendsto (fun t : ℝ ↦ 12*(1-t^2)*b) (𝓝[>] 0) (𝓝 (12*(1-(0:ℝ)^2)*b)) :=
    (show ContinuousAt (fun t : ℝ ↦ 12*(1-t^2)*b) 0 by fun_prop).continuousWithinAt
  have h₂ : Tendsto (fun t : ℝ ↦ a*(6+2*t^4)) (𝓝[>] 0) (𝓝 (a*(6+2*(0:ℝ)^4))) :=
    (show ContinuousAt (fun t : ℝ ↦ a*(6+2*t^4)) 0 by fun_prop).continuousWithinAt
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have hb := le_of_tendsto_of_tendsto h₁ h₂ (hpos.mono fun t ht ↦ hdiv t ht)
  change b ≤ a/2
  linarith only [hb]

end EuclideanMidpointRigidity
