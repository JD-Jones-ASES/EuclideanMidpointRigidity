module

public import EuclideanMidpointRigidity.RadialMaximum
public import EuclideanMidpointRigidity.CubicPolynomial
public import EuclideanMidpointRigidity.PolynomialPartial
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! # Coordinate equations at a perturbed radial maximum -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff InnerProductSpace Topology
namespace EuclideanMidpointRigidity
open SmoothPolynomial

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

def radialPolynomial {W : Set E} {C : E → Coeff} (hC : ContDiffOn ℝ ∞ C W) :
    MvPolynomial (Fin d) (SmoothCoefficient W) :=
  (∑ i, ∑ j, ∑ k, MvPolynomial.C (cubicCoordinate hC i j k) *
    MvPolynomial.X i * MvPolynomial.X j * MvPolynomial.X k) -
    (∑ i : Fin d, MvPolynomial.X i^2)^2

theorem eval_radialPolynomial {W : Set E} {C : E → Coeff} (hC : ContDiffOn ℝ ∞ C W)
    (p : E) (z : Fin d → ℝ) :
    MvPolynomial.eval z (specialize (radialPolynomial hC) p) =
      radialObjective (C p) (WithLp.toLp 2 z) := by
  rw [radialObjective,directionProfile_apply,expand_cubic,
    show ‖(WithLp.toLp 2 z : E)‖^4=(‖(WithLp.toLp 2 z : E)‖^2)^2 by ring,
    EuclideanSpace.real_norm_sq_eq]
  simp [radialPolynomial,specialize,cubicCoordinate,evaluateCoefficient]

def evenPenalty (b : ℕ) (z : Fin d → ℝ) : ℝ :=
  (∑ j, z j^(2*b+2))/(2*(b:ℝ)+2)

theorem evenPenalty_nonneg (b : ℕ) (z : Fin d → ℝ) : 0≤evenPenalty b z := by
  apply div_nonneg _ (by positivity)
  apply Finset.sum_nonneg
  intro j _
  rw [show 2*b+2=2*(b+1) by omega,pow_mul]
  positivity

theorem hasDerivAt_evenPenalty (b : ℕ) (z : Fin d → ℝ) (i : Fin d) :
    HasDerivAt (fun s ↦ evenPenalty b (coordinateStep z i s)) (z i^(2*b+1)) 0 := by
  have h (j : Fin d) := (hasDerivAt_coordinateStep z i j).pow (2*b+2)
  have hd := (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ h j)).div_const (2*(b:ℝ)+2)
  convert hd using 1
  · rfl
  · simp [coordinateStep_zero,mul_ite,show 2*b+2-1=2*b+1 by omega]
    <;> field_simp <;> ring

theorem critical_radial_perturbation {W : Set E} {C : E → Coeff} (hC : ContDiffOn ℝ ∞ C W)
    (p : E) (b : ℕ) (t : ℝ) {z : E} (hm : ∀ v : E,
      radialObjective (C p) v-t*evenPenalty b v.ofLp ≤ radialObjective (C p) z-t*evenPenalty b z.ofLp)
    (i : Fin d) :
    t*z i^(2*b+1)=(MvPolynomial.pderiv i (radialPolynomial hC)).eval₂ (evaluateCoefficient p) z.ofLp := by
  let f := specialize (radialPolynomial hC) p
  let g := fun s ↦ MvPolynomial.eval (coordinateStep z.ofLp i s) f-t*evenPenalty b (coordinateStep z.ofLp i s)
  have hg : IsLocalMax g 0 := by
    apply Filter.Eventually.of_forall
    intro s
    change g s≤g 0
    simpa only [g,f,eval_radialPolynomial,coordinateStep_zero,WithLp.toLp_ofLp] using
      hm (WithLp.toLp 2 (coordinateStep z.ofLp i s))
  have hd := (hasDerivAt_eval_coordinate f z.ofLp i).fun_sub ((hasDerivAt_evenPenalty b z.ofLp i).const_mul t)
  have he := hg.hasDerivAt_eq_zero hd
  rw [MvPolynomial.eval₂_eq_eval_map]
  change _=MvPolynomial.eval z.ofLp (specialize (MvPolynomial.pderiv i (radialPolynomial hC)) p)
  rw [specialize_pderiv]
  exact (sub_eq_zero.mp he).symm

theorem polynomial_perturbation_limit {W : Set E} {C : E → Coeff} (hC : ContDiffOn ℝ ∞ C W)
    (p : E) (b : ℕ) :
    ∃ (w : E) (t : ℕ → ℝ) (z : ℕ → E), Tendsto t atTop (𝓝 0) ∧ (∀ j, 0<t j) ∧
      Tendsto z atTop (𝓝 w) ∧ (∀ j i, t j*(z j i)^(2*b+1) =
        (MvPolynomial.pderiv i (radialPolynomial hC)).eval₂ (evaluateCoefficient p) (z j).ofLp) ∧
      ∀ v, radialObjective (C p) v≤radialObjective (C p) w := by
  let L := fun z : E ↦ evenPenalty b z.ofLp
  have hL : Continuous L := by
    apply Continuous.div_const
    apply continuous_finsetSum
    intro i _
    exact (PiLp.continuous_apply 2 (fun _ : Fin d ↦ ℝ) i).pow _
  have h₀ : L 0=0 := by simp [L,evenPenalty]
  obtain ⟨w,t,z,ht,hpos,hz,hm,hmax⟩ := radial_perturbation_limit (C p) L hL (fun z ↦ evenPenalty_nonneg b _) h₀
  exact ⟨w,t,z,ht,hpos,hz,fun j i ↦ critical_radial_perturbation hC p b (t j) (hm j) i,hmax⟩

end EuclideanMidpointRigidity

