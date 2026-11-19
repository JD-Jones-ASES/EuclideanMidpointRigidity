module

public import EuclideanMidpointRigidity.CriticalValueGap
public import EuclideanMidpointRigidity.CubicPolynomial
public import EuclideanMidpointRigidity.PolynomialPartial
public import EuclideanMidpointRigidity.MaximumEnvelope

/-! # A gap below the top spherical critical value on an open subpatch -/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology ContDiff InnerProductSpace
namespace EuclideanMidpointRigidity
open SmoothPolynomial

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

private theorem multiplier_line_stationary {c : Coeff} {e : E} {a : ℝ}
    (hu : ‖e‖=1) (hc : K c e e=a • e) (v : E) (r : ℝ) :
    HasDerivAt (fun t : ℝ ↦ ⟪K c (e+t • v) (e+t • v),e+t • v⟫_ℝ-
      (3*a/2+t*r)*(‖e+t • v‖^2-1)) 0 0 := by
  let w := fun t : ℝ ↦ e+t • v
  have hw : HasDerivAt w v 0 := by simpa [w] using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add e
  have w₀ : w 0=e := by simp [w]
  have hK := hasDerivAt_K (hasDerivAt_const 0 c) hw hw
  have hC := hK.inner ℝ hw
  have hN := (hw.inner ℝ hw).sub_const 1
  have hmult : HasDerivAt (fun t : ℝ ↦ 3*a/2+t*r) r 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const r).const_add (3*a/2)
  have h := hC.fun_sub (hmult.fun_mul hN)
  have hzero : K (0:Coeff) e e=0 := by simp [K]
  simp only [w₀,zero_mul,mul_zero,add_zero,zero_add,hzero,
    real_inner_self_eq_norm_sq,hu,one_pow,sub_self] at h
  have h₁ : ⟪K c e v,e⟫_ℝ=a*⟪v,e⟫_ℝ := by rw [K_selfAdjoint,hc,real_inner_smul_right]
  have h₂ : ⟪K c v e,e⟫_ℝ=a*⟪v,e⟫_ℝ := by rw [K_symm,h₁]
  convert h using 1
  simp only [K] at h₁ h₂
  simp only [K,inner_add_left]
  change 0 = _
  rw [h₁,h₂]
  change 0= ⟪K c e e,v⟫_ℝ + _ - _
  rw [hc,real_inner_smul_left,real_inner_comm v e]
  ring

theorem spherical_critical_specialization {W : Set E} {C : E → Coeff} (hC : ContDiffOn ℝ ∞ C W)
    (p : E) {e : E} {a : ℝ} (hu : ‖e‖=1) (hc : K (C p) e e=a • e) :
    let z : Fin (d+1) → ℝ := Fin.cons (3*a/2) (fun i ↦ e i)
    MvPolynomial.eval z (specialize (sphericalLagrangian hC) p)=a ∧
      ∀ i, MvPolynomial.eval z (MvPolynomial.pderiv i (specialize (sphericalLagrangian hC) p))=0 := by
  let z : Fin (d+1) → ℝ := Fin.cons (3*a/2) (fun i ↦ e i)
  have he : sphericalCoordinates z=e := by ext i; simp [sphericalCoordinates,z]
  change MvPolynomial.eval z _=a ∧ _
  constructor
  · rw [eval_sphericalLagrangian,he,hc,real_inner_smul_left,real_inner_self_eq_norm_sq,hu]
    ring
  · intro i
    let v : E := WithLp.toLp 2 (fun j : Fin d ↦ if j.succ=i then (1:ℝ) else 0)
    have hz (t : ℝ) : sphericalCoordinates (coordinateStep z i t)=e+t • v := by
      ext j
      simp [sphericalCoordinates,coordinateStep,z,v]
    have h := hasDerivAt_eval_coordinate (specialize (sphericalLagrangian hC) p) z i
    have hline := multiplier_line_stationary hu hc v (if 0=i then (1:ℝ) else 0)
    apply h.unique
    convert hline using 1
    funext t
    rw [eval_sphericalLagrangian,hz]
    rfl

theorem spherical_critical_value_gap {W : Set E} {C : E → Coeff} (hW : IsOpen W) (hn : W.Nonempty)
    (hC : ContDiffOn ℝ ∞ C W) : ∃ p ∈ W, ∀ᶠ q : E × ℝ in 𝓝 (p,amplitude (C p)),
      ∀ e : E, ‖e‖=1 → K (C q.1) e e=q.2 • e → q.2=amplitude (C q.1) := by
  obtain ⟨p,hp,hgap⟩ := critical_value_separation (sphericalLagrangian hC) hW hn
    ((continuous_amplitude (d := d)).comp_continuousOn hC.continuousOn)
  refine ⟨p,hp,?_⟩
  filter_upwards [hgap] with q h
  intro e hu hc
  obtain ⟨he,hg⟩ := spherical_critical_specialization hC q.1 hu hc
  exact h _ hg he

end EuclideanMidpointRigidity

