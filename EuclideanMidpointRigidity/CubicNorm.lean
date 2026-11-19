module

public import EuclideanMidpointRigidity.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-! # The sharp diagonal norm inequality for a real symmetric cubic -/

@[expose] public section
noncomputable section
open Set Metric
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

private theorem unitize {v : E} (hv : v ≠ 0) : ‖‖v‖⁻¹ • v‖ = 1 := by
  have hn := norm_pos_iff.mpr hv
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']

private theorem norm_le_of_unit_tests {v : E} {b : ℝ} (hb : 0 ≤ b)
    (hs : ∀ w : E, ‖w‖ = 1 → ⟪v,w⟫_ℝ ≤ b) : ‖v‖ ≤ b := by
  by_cases hz : v = 0
  · simpa [hz] using hb
  have h := hs _ (unitize hz)
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq] at h
  have hnorm : ‖v‖⁻¹ * ‖v‖^2 = ‖v‖ := by field_simp
  rwa [hnorm] at h

private theorem attaining_vector {x w : E} {m : ℝ} (hm : 0 ≤ m)
    (hw : ‖w‖ = 1) (hx : ‖x‖ ≤ m) (hpair : ⟪x,w⟫_ℝ = m) : x = m • w := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have h := norm_sub_sq_real x (m • w)
  rw [real_inner_smul_right, hpair, norm_smul, Real.norm_eq_abs, abs_of_nonneg hm, hw, mul_one] at h
  nlinarith [pow_le_pow_left₀ (norm_nonneg x) hx 2, norm_nonneg (x-m • w)]

private theorem unit_pair_to_quadratic {c : Coeff} {m : ℝ}
    (h : ∀ v w : E, ‖v‖ = 1 → ‖w‖ = 1 → ⟪K c v v,w⟫_ℝ ≤ m)
    {w : E} (hw : ‖w‖ = 1) (v : E) : ⟪K c v v,w⟫_ℝ ≤ m*‖v‖^2 := by
  by_cases hz : v = 0
  · simp [hz, K]
  have hu := h _ w (unitize hz) hw
  simp only [K_smul_left, K_smul_right, real_inner_smul_left] at hu
  have hn := norm_pos_iff.mpr hz
  field_simp [hn.ne'] at hu
  linarith only [hu]

private theorem unit_pair_to_triple {c : Coeff} {m : ℝ}
    (h : ∀ v w : E, ‖v‖ = 1 → ‖w‖ = 1 → ⟪K c v v,w⟫_ℝ ≤ m)
    {u v w : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) : ⟪K c u v,w⟫_ℝ ≤ m := by
  have h₁ := unit_pair_to_quadratic h hw (u+v)
  have h₂ := unit_pair_to_quadratic h (show ‖-w‖=1 by simpa using hw) (u-v)
  rw [norm_add_sq_real, hu, hv] at h₁
  rw [norm_sub_sq_real, hu, hv] at h₂
  simp only [sub_eq_add_neg, K_add_left, K_add_right, K_neg_left, K_neg_right,
    K_symm c v u, inner_add_left, inner_neg_right, inner_neg_left] at h₁ h₂
  linarith only [h₁,h₂]

/-- Maximizing the diagonal polynomial controls `K(v,v)` with constant one.
The zero-dimensional case is included. -/
theorem cubic_diagonal_norm_bound (c : Coeff) (a : ℝ) (ha : 0 ≤ a)
    (diag : ∀ u : E, ‖u‖ = 1 → ⟪K c u u,u⟫_ℝ ≤ a) (z : E) :
    ‖K c z z‖ ≤ a*‖z‖^2 := by
  by_cases hz : z = 0
  · simp [hz,K]
  let S : Set E := sphere (0:E) 1
  let f := fun p : E × E ↦ ⟪K c p.1 p.1,p.2⟫_ℝ
  let g := fun p : E × E ↦ ⟪p.1,p.2⟫_ℝ
  have hf : Continuous f := by
    exact (((c.val.continuous.comp continuous_fst).clm_apply continuous_fst).inner continuous_snd)
  have hg : Continuous g := continuous_fst.inner continuous_snd
  have memS (v : E) : v ∈ S ↔ ‖v‖ = 1 := by simp [S]
  have hS : IsCompact S := isCompact_sphere _ _
  have hne : S.Nonempty := ⟨_, (memS _).mpr (unitize hz)⟩
  obtain ⟨p,hp,hm⟩ := (hS.prod hS).exists_isMaxOn (hne.prod hne) hf.continuousOn
  let m := f p
  let T := (S ×ˢ S) ∩ {q | f q = m}
  have hT : IsCompact T := (hS.prod hS).inter_right (isClosed_eq hf continuous_const)
  obtain ⟨⟨v,w⟩,hwit,halign⟩ := hT.exists_isMaxOn ⟨p,hp,rfl⟩ hg.continuousOn
  have hv := (memS _).mp hwit.1.1
  have hw := (memS _).mp hwit.1.2
  have hpair : ⟪K c v v,w⟫_ℝ = m := hwit.2
  have hub (i j : E) (hi : ‖i‖=1) (hj : ‖j‖=1) : ⟪K c i i,j⟫_ℝ ≤ m :=
    hm (show (i,j) ∈ S ×ˢ S from ⟨(memS _).mpr hi, (memS _).mpr hj⟩)
  have hm₀ : 0 ≤ m := by
    have hn := hub v (-w) hv (by simpa using hw)
    rw [inner_neg_right, hpair] at hn
    linarith
  have hvv : K c v v = m • w := attaining_vector hm₀ hw
    (norm_le_of_unit_tests hm₀ (fun j hj ↦ hub v j hv hj)) hpair
  have hvw : K c v w = m • v := by
    apply attaining_vector hm₀ hv (norm_le_of_unit_tests hm₀ (fun j hj ↦ unit_pair_to_triple hub hv hw hj))
    rw [K_selfAdjoint, real_inner_comm (K c v v) w, hpair]
  have han : 0 ≤ ⟪v,w⟫_ℝ := by
    have hn : (-v,w) ∈ T := ⟨⟨(memS _).mpr (by simpa using hv),hwit.1.2⟩, by simpa [f] using hpair⟩
    have h := halign hn
    change ⟪-v,w⟫_ℝ ≤ ⟪v,w⟫_ℝ at h
    rw [inner_neg_left] at h
    linarith
  let R := ‖v+w‖
  have hR : R^2 = 2 + 2*⟪v,w⟫_ℝ := by rw [norm_add_sq_real, hv, hw]; ring
  have hR₀ : 0 < R := by nlinarith [show 0 ≤ R from norm_nonneg _]
  let u := R⁻¹ • (v+w)
  have hunit : ‖u‖ = 1 := unitize (norm_pos_iff.mp hR₀)
  have hprod : K c v u = m • u := by
    simp only [u, K_smul_right, K_add_right, hvv, hvw]
    module
  have hnew : (u,v) ∈ T := by
    refine ⟨⟨(memS u).mpr hunit,(memS v).mpr hv⟩, ?_⟩
    change ⟪K c u u,v⟫_ℝ = m
    rw [K_selfAdjoint, K_symm c u v, hprod, real_inner_smul_right, real_inner_self_eq_norm_sq, hunit]
    ring
  have hmono := halign hnew
  change ⟪R⁻¹ • (v+w),v⟫_ℝ ≤ ⟪v,w⟫_ℝ at hmono
  rw [real_inner_smul_left, inner_add_left, real_inner_self_eq_norm_sq, hv,
    real_inner_comm v w, ← div_eq_inv_mul] at hmono
  have hlt := (div_le_iff₀ hR₀).mp hmono
  have hRle : R ≤ 2*⟪v,w⟫_ℝ := by
    apply le_of_mul_le_mul_right (a := R) _ hR₀
    nlinarith only [hR,hlt]
  have hupper := real_inner_le_norm v w
  rw [hv,hw,one_mul] at hupper
  have heq : ⟪v,w⟫_ℝ = 1 := by
    have hp := pow_le_pow_left₀ hR₀.le hRle 2
    by_contra hne'
    have hlt' := lt_of_le_of_ne hupper hne'
    nlinarith [mul_neg_of_pos_of_neg (show 0 < 2*⟪v,w⟫_ℝ+1 by linarith) (sub_neg.mpr hlt')]
  have hvw' : v = w := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    nlinarith [norm_sub_sq_real v w, show 0 ≤ ‖v-w‖ from norm_nonneg _]
  have hma : m ≤ a := by simpa [← hvw', ← hpair] using diag v hv
  apply norm_le_of_unit_tests (mul_nonneg ha (sq_nonneg _))
  intro i hi
  exact (unit_pair_to_quadratic hub hi z).trans (mul_le_mul_of_nonneg_right hma (sq_nonneg _))

/-- A maximizing unit vector of value `a` is a critical axis of the
raised product. Equality in the sharp norm bound gives the vector equation. -/
theorem maximizing_axis_product {c : Coeff} {a : ℝ} (ha : 0 ≤ a)
    (diag : ∀ u : E, ‖u‖ = 1 → ⟪K c u u,u⟫_ℝ ≤ a)
    {e : E} (he : ‖e‖=1) (hmax : ⟪K c e e,e⟫_ℝ = a) : K c e e = a • e := by
  apply attaining_vector ha he _ hmax
  simpa [he] using cubic_diagonal_norm_bound c a ha diag e

end EuclideanMidpointRigidity
