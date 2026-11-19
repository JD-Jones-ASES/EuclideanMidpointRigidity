module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Tactic

/-! # The integration operator on continuous Banach-space paths -/

@[expose] public section
noncomputable section
open Set MeasureTheory
namespace EuclideanMidpointRigidity.PathIntegral

abbrev Time := Icc (0:ℝ) 1
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def extend (f : C(Time,E)) (t : ℝ) : E := f (projIcc 0 1 zero_le_one t)

theorem continuous_extend (f : C(Time,E)) : Continuous (extend f) :=
  f.continuous.comp continuous_projIcc

theorem extend_mem (f : C(Time,E)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    extend f t=f ⟨t,ht⟩ := by simp [extend,projIcc_of_mem,ht]

def primitive (f : C(Time,E)) (t : ℝ) : E := ∫ s in (0:ℝ)..t, extend f s

theorem hasDerivAt_primitive (f : C(Time,E)) (t : ℝ) : HasDerivAt (primitive f) (extend f t) t :=
  intervalIntegral.integral_hasDerivAt_right ((continuous_extend f).intervalIntegrable _ _)
    (continuous_extend f).aestronglyMeasurable.stronglyMeasurableAtFilter (continuous_extend f).continuousAt

theorem continuous_primitive (f : C(Time,E)) : Continuous (primitive f) :=
  continuous_iff_continuousAt.mpr fun t ↦ (hasDerivAt_primitive f t).continuousAt

theorem primitive_add (f g : C(Time,E)) (t : ℝ) : primitive (f+g) t=primitive f t+primitive g t :=
  intervalIntegral.integral_add ((continuous_extend f).intervalIntegrable _ _) ((continuous_extend g).intervalIntegrable _ _)

theorem primitive_smul (r : ℝ) (f : C(Time,E)) (t : ℝ) : primitive (r • f) t=r • primitive f t :=
  intervalIntegral.integral_smul r _

def integration : C(Time,E) →L[ℝ] C(Time,E) := by
  let L : C(Time,E) →ₗ[ℝ] C(Time,E) := {
    toFun := fun f ↦ ⟨fun s ↦ primitive f s,(continuous_primitive f).comp continuous_subtype_val⟩
    map_add' := fun f g ↦ ContinuousMap.ext fun t ↦ primitive_add f g t
    map_smul' := fun r f ↦ ContinuousMap.ext fun t ↦ primitive_smul r f t }
  refine L.mkContinuous 1 (fun f ↦ ?_)
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro t
  change ‖∫ s in (0:ℝ)..t.val, extend f s‖ ≤ ‖f‖
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := t.val)
    (f := extend f) (C := ‖f‖) (fun s _ ↦ f.norm_coe_le_norm _)
  rw [sub_zero,abs_of_nonneg t.property.1] at h
  exact h.trans (by nlinarith only [mul_le_mul_of_nonneg_left t.property.2 (norm_nonneg f)])

@[simp] theorem integration_apply (f : C(Time,E)) (s : Time) : integration f s=primitive f s := rfl

end EuclideanMidpointRigidity.PathIntegral

