module

public import EuclideanMidpointRigidity.SmoothDirichlet

/-! # Linearizing the path equation and uniqueness of the forced variations -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
variable {I E F : Type} [TopologicalSpace I] [CompactSpace I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
local notation "P" => C(I,E)
local notation "Q" => C(I,F)
set_option backward.isDefEq.respectTransparency false

def pathForceDerivative (f : C(E,F)) (hf : ContDiff ℝ ∞ (f : E → F)) (y : P) : P →L[ℝ] Q :=
  pathApply ((⟨fderiv ℝ (f : E → F),hf.continuous_fderiv (by decide)⟩ : C(E,E →L[ℝ] F)).comp y)

theorem pathForceDerivative_apply (f : C(E,F)) (hf : ContDiff ℝ ∞ (f : E → F)) (y h : P) (t : I) :
    pathForceDerivative f hf y h t=fderiv ℝ (f : E → F) (y t) (h t) := rfl

theorem hasFDerivAt_pathForce (f : C(E,F)) (hf : ContDiff ℝ ∞ (f : E → F)) (y : P) :
    HasFDerivAt f.comp (pathForceDerivative f hf y) y := postcomp_hasFDerivAt (hf.of_le (by simp)) y

theorem dirichletInput_derivative (G : Q →L[ℝ] P) (f : C(E,F)) (hf : ContDiff ℝ ∞ (f : E → F)) (y : P) :
    fderiv ℝ (dirichletInput G f) y = ContinuousLinearMap.id ℝ P-G.comp (pathForceDerivative f hf y) := by
  exact ((hasFDerivAt_id y).fun_sub (G.hasFDerivAt.comp y (hasFDerivAt_pathForce f hf y))).fderiv

theorem linearized_green_unique (G : Q →L[ℝ] P) (f : C(E,F)) (hf : ContDiff ℝ ∞ (f : E → F)) {y : P}
    (hreg : (fderiv ℝ (dirichletInput G f) y).IsInvertible) {a u v : P}
    (hu : u=a+G (pathForceDerivative f hf y u)) (hv : v=a+G (pathForceDerivative f hf y v)) : u=v := by
  obtain ⟨e,he⟩ := hreg
  apply e.injective
  change (e : P →L[ℝ] P) u=(e : P →L[ℝ] P) v
  rw [he,dirichletInput_derivative G f hf,sub_apply,sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply]
  exact (sub_eq_iff_eq_add.mpr hu).trans (sub_eq_iff_eq_add.mpr hv).symm

theorem hasDerivAt_pathForceDerivative_apply (f : C(E,F)) (hf : ContDiff ℝ ∞ (f : E → F))
    {y v : ℝ → P} {y' v' : P} {t : ℝ} (dy : HasDerivAt y y' t) (dv : HasDerivAt v v' t) :
    HasDerivAt (fun s ↦ pathForceDerivative f hf (y s) (v s))
      (pathApply (pathForceDerivative (⟨fderiv ℝ (f : E → F),hf.continuous_fderiv (by decide)⟩ : C(E,E →L[ℝ] F))
        (hf.fderiv_right (by simp)) (y t) y') (v t)+pathForceDerivative f hf (y t) v') t := by
  let D : C(E,E →L[ℝ] F) := ⟨fderiv ℝ (f : E → F),hf.continuous_fderiv (by decide)⟩
  have hD : ContDiff ℝ ∞ (D : E → E →L[ℝ] F) := hf.fderiv_right (by simp)
  have h₁ := (hasFDerivAt_pathForce D hD (y t)).comp_hasDerivAt t dy
  let A : C(I,E →L[ℝ] F) →L[ℝ] (P →L[ℝ] Q) := pathApply
  have h₂ : HasDerivAt (fun s ↦ A (D.comp (y s))) (A (pathForceDerivative D hD (y t) y')) t :=
    A.hasFDerivAt.comp_hasDerivAt t h₁
  exact h₂.clm_apply dv

end EuclideanMidpointRigidity

