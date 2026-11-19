module

public import EuclideanMidpointRigidity.FlowPaths
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # Time scaling for the path-valued local flow -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
open PathIntegral

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
local notation "P" => C(Time,E)

omit [CompleteSpace E] in
private theorem smooth_autonomous_unique {F : E → E} (hF : ContDiff ℝ 1 F) {a b : ℝ → E}
    (ha : ∀ r ∈ Icc (0:ℝ) 1, HasDerivAt a (F (a r)) r)
    (hb : ∀ r ∈ Icc (0:ℝ) 1, HasDerivAt b (F (b r)) r) (h₀ : a 0=b 0) :
    EqOn a b (Icc (0:ℝ) 1) := by
  have hca := HasDerivAt.continuousOn ha
  have hcb := HasDerivAt.continuousOn hb
  let S := a '' Icc (0:ℝ) 1 ∪ b '' Icc (0:ℝ) 1
  have hS : IsCompact S := (isCompact_Icc.image_of_continuousOn hca).union (isCompact_Icc.image_of_continuousOn hcb)
  obtain ⟨K,hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hS hF.locallyLipschitz.locallyLipschitzOn
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ ↦ F) (s := fun _ ↦ S) (fun _ _ ↦ hK) hca
    (fun r hr ↦ (ha r (Ico_subset_Icc_self hr)).hasDerivWithinAt)
    (fun r hr ↦ Or.inl (mem_image_of_mem a (Ico_subset_Icc_self hr))) hcb
    (fun r hr ↦ (hb r (Ico_subset_Icc_self hr)).hasDerivWithinAt)
    (fun r hr ↦ Or.inr (mem_image_of_mem b (Ico_subset_Icc_self hr))) h₀

def flowCurve (f : C(E,E)) (y : E) (τ : ℝ) (Z : P) (r : ℝ) : E := y+τ • primitive (f.comp Z) r

theorem flowCurve_at {f : C(E,E)} {y : E} {τ : ℝ} {Z : P}
    (hZ : Z=ContinuousMap.const Time y+τ • integration (f.comp Z)) (r : Time) : flowCurve f y τ Z r=Z r := by
  exact (congrArg (fun curve : C(Time,E) ↦ curve r) hZ).symm

theorem flowCurve_derivative {f : C(E,E)} {y : E} {τ : ℝ} {Z : P}
    (hZ : Z=ContinuousMap.const Time y+τ • integration (f.comp Z)) {r : ℝ} (hr : r ∈ Icc (0:ℝ) 1) :
    HasDerivAt (flowCurve f y τ Z) (τ • f (flowCurve f y τ Z r)) r := by
  have h := ((hasDerivAt_primitive (f.comp Z) r).fun_const_smul τ).const_add y
  rw [extend_mem _ hr] at h
  have hv : flowCurve f y τ Z r=Z ⟨r,hr⟩ := flowCurve_at hZ (⟨r,hr⟩ : Time)
  rw [hv]
  exact h

/-- The short-time solution for kτ is the restriction of the solution
for τ to the fraction k of the original time interval. -/
theorem flowCurve_scale (f : C(E,E)) (hf : ContDiff ℝ 1 (f : E → E)) {y : E} {τ k : ℝ}
    (hk : k ∈ Icc (0:ℝ) 1) {Z Z' : P} (hZ : Z=ContinuousMap.const Time y+τ • integration (f.comp Z))
    (hZ' : Z'=ContinuousMap.const Time y+(k*τ) • integration (f.comp Z')) :
    Z' (⟨1,by simp⟩ : Time)=flowCurve f y τ Z k := by
  let a := flowCurve f y (k*τ) Z'
  let b := fun r ↦ flowCurve f y τ Z (k*r)
  have hb (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) : HasDerivAt b ((k*τ) • f (b r)) r := by
    have hm : k*r ∈ Icc (0:ℝ) 1 := ⟨mul_nonneg hk.1 hr.1,(mul_le_of_le_one_right hk.1 hr.2).trans hk.2⟩
    have hlin : HasDerivAt (fun s : ℝ ↦ k*s) k r := by simpa using (hasDerivAt_id r).const_mul k
    have h := (flowCurve_derivative hZ hm).scomp r hlin
    simpa [b,Function.comp_def,smul_smul] using h
  have ha : ∀ r ∈ Icc (0:ℝ) 1, HasDerivAt a ((k*τ) • f (a r)) r := fun r hr ↦ flowCurve_derivative hZ' hr
  have h₀ : a 0=b 0 := by simp [a,b,flowCurve,primitive]
  have he := smooth_autonomous_unique (hf.const_smul (k*τ)) ha hb h₀ (x := 1) (by simp)
  simpa only [a,b,mul_one,flowCurve_at hZ' (⟨1,by simp⟩ : Time)] using he

end EuclideanMidpointRigidity

