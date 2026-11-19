module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Tactic

/-! # Differentiating postcomposition on continuous paths -/

@[expose] public section
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace EuclideanMidpointRigidity

set_option backward.isDefEq.respectTransparency false

variable {I E F : Type} [TopologicalSpace I] [CompactSpace I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def pathApply : C(I,E →L[ℝ] F) →L[ℝ] C(I,E) →L[ℝ] C(I,F) := by
  let ev := fun (a : C(I,E →L[ℝ] F)) (h : C(I,E)) ↦
    (⟨fun i ↦ a i (h i),a.continuous.clm_apply h.continuous⟩ : C(I,F))
  let B := LinearMap.mk₂ ℝ ev (by intros; ext; rfl) (by intros; ext; rfl)
    (by intro a h k; ext i; exact (a i).map_add _ _) (by intro r a h; ext i; exact (a i).map_smul r _)
  refine LinearMap.mkContinuous₂ (E := C(I,E →L[ℝ] F)) (F := C(I,E)) (G := C(I,F))
    (σ₁₃ := RingHom.id ℝ) (σ₂₃ := RingHom.id ℝ) B 1 ?_
  intro a h
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro i
  change ‖a i (h i)‖ ≤ _
  rw [one_mul]
  exact ((a i).le_opNorm (h i)).trans (mul_le_mul (a.norm_coe_le_norm i) (h.norm_coe_le_norm i)
    (norm_nonneg (h i)) (norm_nonneg a))

theorem pathApply_apply (a : C(I,E →L[ℝ] F)) (h : C(I,E)) (i : I) : pathApply a h i=a i (h i) := rfl

/-- First derivative of the map taking a continuous path to its composition
with a continuously differentiable function, in the uniform norm. -/
theorem postcomp_hasFDerivAt {f : E → F} (hf : ContDiff ℝ 1 f) (g : C(I,E)) :
    HasFDerivAt (ContinuousMap.comp (⟨f,hf.continuous⟩ : C(E,F)))
      (pathApply ((⟨fderiv ℝ f,hf.continuous_fderiv (by decide)⟩ : C(E,E →L[ℝ] F)).comp g)) g := by
  let D : C(E,E →L[ℝ] F) := ⟨fderiv ℝ f,hf.continuous_fderiv (by decide)⟩
  let A : C(I,E) → C(I,E →L[ℝ] F) := ContinuousMap.comp D
  have ha : Continuous A := ContinuousMap.continuous_postcomp D
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ,hδ,hnear⟩ := (Metric.continuousAt_iff (f := A) (a := g)).mp ha.continuousAt ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : C(I,E)) hδ] with h hh
  have hh' : ‖h‖<δ := by simpa [Metric.mem_ball,dist_zero_right] using hh
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg h))).mpr
  intro i
  let q := fun s : ℝ ↦ g i+s • h i
  let R := fun s : ℝ ↦ f (q s)-s • (fderiv ℝ f (g i) (h i))
  let R' := fun s : ℝ ↦ (fderiv ℝ f (q s)-fderiv ℝ f (g i)) (h i)
  have hd (s : ℝ) : HasDerivAt R (R' s) s := by
    have hq : HasDerivAt q (h i) s := by simpa [q] using ((hasDerivAt_id s).smul_const (h i)).const_add (g i)
    have h₁ := ((hf.differentiable (by decide) (q s)).hasFDerivAt.comp_hasDerivAt s hq)
    have h₂ := (hasDerivAt_id s).smul_const (fderiv ℝ f (g i) (h i))
    simpa [R,R',Function.comp_def] using h₁.fun_sub h₂
  have hb (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) : ‖R' s‖≤ε*‖h‖ := by
    have hgs : dist (g+s • h) g<δ := by
      rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg hs.1]
      exact (mul_le_of_le_one_left (norm_nonneg h) hs.2.le).trans_lt hh'
    have hclose := hnear hgs
    have hpoint := (ContinuousMap.dist_apply_le_dist (f := A (g+s • h)) (g := A g) i).trans hclose.le
    change dist (fderiv ℝ f (q s)) (fderiv ℝ f (g i)) ≤ ε at hpoint
    have hnorm : ‖fderiv ℝ f (q s)-fderiv ℝ f (g i)‖≤ε := by
      rwa [dist_eq_norm (fderiv ℝ f (q s)) (fderiv ℝ f (g i))] at hpoint
    exact ((fderiv ℝ f (q s)-fderiv ℝ f (g i)).le_opNorm _).trans
      (mul_le_mul hnorm (h.norm_coe_le_norm i) (norm_nonneg _) hε.le)
  have he := norm_image_sub_le_of_norm_deriv_le_segment_01' (fun s _ ↦ (hd s).hasDerivWithinAt) hb
  change ‖f (g i+h i)-f (g i)-fderiv ℝ f (g i) (h i)‖≤ε*‖h‖
  simpa [R,q,sub_sub_sub_comm,sub_right_comm] using he

end EuclideanMidpointRigidity

