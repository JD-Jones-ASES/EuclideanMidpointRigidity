module

public import EuclideanMidpointRigidity.SmoothPolynomialFamily
public import Mathlib.Algebra.Polynomial.Taylor

/-! # Smooth evaluation and translation of univariate polynomial families -/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped ContDiff
namespace EuclideanMidpointRigidity.SmoothPolynomial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {W : Set E}
local notation "A" => SmoothCoefficient W

def fiber (P : Polynomial A) (x : E) : Polynomial ℝ := P.map (evaluateCoefficient x)

theorem smooth_fiber_eval (P : Polynomial A) :
    ContDiffOn ℝ ∞ (fun q : E × ℝ ↦ (fiber P q.1).eval q.2) (W ×ˢ univ) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simpa only [fiber,Polynomial.map_add,Polynomial.eval_add] using hP.add hQ
  | monomial j a =>
    simp only [fiber,Polynomial.map_monomial,Polynomial.eval_monomial]
    have proj : MapsTo (Prod.fst : E × ℝ → E) (W ×ˢ univ) W := fun _ h ↦ h.1
    exact (a.property.comp contDiffOn_fst proj).mul (contDiffOn_snd.pow j)

theorem continuous_shifted_coeff (P : Polynomial A) {a : E → ℝ} (ha : ContinuousOn a W) (j : ℕ) :
    ContinuousOn (fun x ↦ (Polynomial.taylor (a x) (fiber P x)).coeff j) W := by
  have h := (smooth_fiber_eval (Polynomial.hasseDeriv j P)).continuousOn.comp
    (continuousOn_id.prodMk ha) (fun x hx ↦ show (x,a x) ∈ W ×ˢ univ from ⟨hx,trivial⟩)
  simpa only [fiber,Polynomial.taylor_coeff,Polynomial.hasseDeriv_map,Function.comp_def,id_eq] using h

/-- The leading coefficient is one even if the lower coefficients change degree. -/
def monicEquation {N : ℕ} (c : Fin N → A) : Polynomial A :=
  X^N-∑ j : Fin N, Polynomial.monomial (j:ℕ) (c j)

theorem monicEquation_fiber_ne_zero {N : ℕ} (c : Fin N → A) (x : E) :
    fiber (monicEquation c) x≠0 := by
  intro he
  have h := congrArg (fun p : Polynomial ℝ ↦ p.coeff N) he
  have hz (i : Fin N) : (i : ℕ)≠N := Nat.ne_of_lt i.isLt
  simp [fiber,monicEquation,Polynomial.coeff_monomial,hz] at h

theorem eval_monicEquation {N : ℕ} (c : Fin N → A) (x : E) (t : ℝ) :
    (fiber (monicEquation c) x).eval t=t^N-∑ j, (c j).val x*t^(j:ℕ) := by
  simp [fiber,monicEquation,evaluateCoefficient,Polynomial.map_sum,Polynomial.eval_finsetSum]

end EuclideanMidpointRigidity.SmoothPolynomial

