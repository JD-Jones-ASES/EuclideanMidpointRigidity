module

public import EuclideanMidpointRigidity.ExponentialLine
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Constant-coefficient differential operators on an open interval -/

@[expose] public section
noncomputable section
open Set Filter Polynomial
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.Endpoint

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Smooth functions on the open set, represented by their zero extension. -/
def lineSpace (W : Set ℝ) (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] : Submodule ℝ (ℝ → V) where
  carrier := {f | ContDiffOn ℝ ∞ f W ∧ ∀ x ∉ W, f x=0}
  zero_mem' := ⟨contDiffOn_const,fun _ _ ↦ rfl⟩
  add_mem' := fun hf hg ↦ ⟨hf.1.add hg.1,fun x hx ↦ by simp only [Pi.add_apply,hf.2 x hx,hg.2 x hx,add_zero]⟩
  smul_mem' := fun r _ hf ↦ ⟨contDiffOn_const.smul hf.1,fun x hx ↦ by simp only [Pi.smul_apply,hf.2 x hx,smul_zero]⟩

namespace LineSpace
variable {W : Set ℝ}

def restrict (f : ℝ → V) (hf : ContDiffOn ℝ ∞ f W) : lineSpace W V :=
  ⟨W.indicator f,hf.congr (fun _ hx ↦ indicator_of_mem hx f),fun _ hx ↦ indicator_of_notMem hx f⟩

@[simp] theorem restrict_apply {f : ℝ → V} (hf : ContDiffOn ℝ ∞ f W) {x : ℝ} (hx : x ∈ W) :
    (restrict f hf).val x=f x := indicator_of_mem hx f

theorem ext_on {F G : lineSpace W V} (h : EqOn F.val G.val W) : F=G := by
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ W
  · exact h hx
  · exact (F.property.2 x hx).trans (G.property.2 x hx).symm

def derivative (hW : IsOpen W) : Module.End ℝ (lineSpace W V) where
  toFun F := restrict (deriv F.val) (F.property.1.deriv_of_isOpen hW (by simp))
  map_add' F G := by
    apply ext_on
    intro x hx
    change W.indicator (deriv (F.val+G.val)) x=W.indicator (deriv F.val) x+W.indicator (deriv G.val) x
    simp only [indicator_of_mem hx]
    exact deriv_add ((F.property.1.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp))
      ((G.property.1.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp))
  map_smul' r F := by
    apply ext_on
    intro x hx
    change W.indicator (deriv (r • F.val)) x=r • W.indicator (deriv F.val) x
    simp only [indicator_of_mem hx]
    exact deriv_const_smul r ((F.property.1.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp))

@[simp] theorem derivative_apply (hW : IsOpen W) (F : lineSpace W V) {x : ℝ} (hx : x ∈ W) :
    ((derivative hW) F).val x=deriv F.val x := indicator_of_mem hx _

theorem pow_derivative_apply (hW : IsOpen W) (F : lineSpace W V) (n : ℕ) {x : ℝ} (hx : x ∈ W) :
    (((derivative hW)^n) F).val x=iteratedDeriv n F.val x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',mul_apply_eq_comp,derivative_apply hW _ hx,iteratedDeriv_succ]
    have he : (((derivative hW)^n) F).val =ᶠ[𝓝 x] iteratedDeriv n F.val :=
      (show ∀ᶠ y in 𝓝 x, y ∈ W from hW.mem_nhds hx).mono fun _ hy ↦ ih hy
    exact he.deriv_eq

def operator (hW : IsOpen W) : ℝ[X] →ₐ[ℝ] Module.End ℝ (lineSpace W V) := aeval (derivative hW)

theorem operator_X_pow (hW : IsOpen W) (F : lineSpace W V) (n : ℕ) {x : ℝ} (hx : x ∈ W) :
    ((operator hW (X^n)) F).val x=iteratedDeriv n F.val x := by
  simpa only [operator,map_pow,aeval_X] using pow_derivative_apply hW F n hx

end LineSpace

/-- The polynomial in differentiation annihilates the given local function. -/
structure SolvesOn {W : Set ℝ} (hW : IsOpen W) (A : ℝ[X]) (f : ℝ → V) : Prop where
  smooth : ContDiffOn ℝ ∞ f W
  equation : LineSpace.operator hW A (LineSpace.restrict f smooth)=0

theorem SolvesOn.of_dvd {W : Set ℝ} {hW : IsOpen W} {A B : ℝ[X]} {f : ℝ → V}
    (H : SolvesOn hW A f) (h : A ∣ B) : SolvesOn hW B f := by
  obtain ⟨C,rfl⟩ := h
  refine ⟨H.smooth,?_⟩
  rw [mul_comm,map_mul,mul_apply_eq_comp,H.equation,map_zero]

end EuclideanMidpointRigidity.Endpoint

