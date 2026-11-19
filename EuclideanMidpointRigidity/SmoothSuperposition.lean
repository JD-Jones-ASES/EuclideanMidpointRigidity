module

public import EuclideanMidpointRigidity.SuperpositionDerivative

/-! # Smooth postcomposition on continuous path spaces -/

public section
noncomputable section
open scoped Topology ContDiff
namespace EuclideanMidpointRigidity

variable {I E F : Type} [TopologicalSpace I] [CompactSpace I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

set_option backward.isDefEq.respectTransparency false in
theorem postcomp_contDiff_nat (n : ℕ) (f : C(E,F)) (hf : ContDiff ℝ n (f : E → F)) :
    ContDiff ℝ n (f.comp : C(I,E) → C(I,F)) := by
  induction n generalizing F with
  | zero => exact contDiff_zero.mpr (ContinuousMap.continuous_postcomp f)
  | succ n ih =>
    have hs : ContDiff ℝ ((n:ℕ∞ω)+1) (f : E → F) := hf
    obtain ⟨hfd,_,hDs⟩ := contDiff_succ_iff_fderiv.mp hs
    have h₁ : ContDiff ℝ 1 (f : E → F) := hf.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
    let D : C(E,E →L[ℝ] F) := ⟨fderiv ℝ f,hDs.continuous⟩
    let A := fun g : C(I,E) ↦ pathApply (D.comp g)
    have he (g : C(I,E)) : HasFDerivAt f.comp (A g) g := postcomp_hasFDerivAt h₁ g
    have heq : fderiv ℝ (f.comp : C(I,E) → C(I,F))=A := funext (fun g ↦ (he g).fderiv)
    change ContDiff ℝ ((n:ℕ∞ω)+1) (f.comp : C(I,E) → C(I,F))
    apply (contDiff_succ_iff_fderiv (𝕜 := ℝ) (n := (n:ℕ∞ω)) (f := (f.comp : C(I,E) → C(I,F)))).mpr
    refine ⟨fun g ↦ (he g).differentiableAt,by simp,?_⟩
    rw [heq]
    exact (pathApply (I := I) (E := E) (F := F)).contDiff.comp (ih D hDs)

theorem postcomp_contDiff (f : C(E,F)) (hf : ContDiff ℝ ∞ (f : E → F)) :
    ContDiff ℝ ∞ (f.comp : C(I,E) → C(I,F)) :=
  contDiff_infty.mpr fun n ↦ postcomp_contDiff_nat n f (contDiff_infty.mp hf n)

end EuclideanMidpointRigidity

