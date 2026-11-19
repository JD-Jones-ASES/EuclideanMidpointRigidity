module

public import EuclideanMidpointRigidity.LineOperatorCalculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Bounded functions whose translates are positive affine transforms -/

public section
noncomputable section
open Set
namespace EuclideanMidpointRigidity.Endpoint

private theorem translate_supremum {f : ℝ → ℝ} {a b h : ℝ} (ha : 0<a) (hb : BddAbove (range f))
    (he : ∀ x, f (x+h)=a*f x+b) : a*sSup (range f)+b=sSup (range f) := by
  let M := sSup (range f)
  have hM (x : ℝ) : f x≤M := le_csSup hb (mem_range_self x)
  change a*M+b=M
  apply le_antisymm
  · have hupper : M≤(M-b)/a := csSup_le (range_nonempty f) (by
      rintro _ ⟨x,rfl⟩
      apply (le_div_iff₀ ha).mpr
      linarith only [he x,hM (x+h)])
    linarith only [(le_div_iff₀ ha).mp hupper]
  · apply csSup_le (range_nonempty f)
    rintro _ ⟨x,rfl⟩
    have hz := he (x-h)
    rw [sub_add_cancel] at hz
    linarith only [hz,mul_le_mul_of_nonneg_left (hM (x-h)) ha.le]

theorem bounded_affine_translates {f : ℝ → ℝ} {K : ℝ} (hb : ∀ x, |f x|≤K)
    (he : ∀ h, ∃ a b : ℝ, 0<a ∧ ∀ x, f (x+h)=a*f x+b) : ∀ x y, f x=f y := by
  let M := sSup (range f)
  let N := sSup (range (fun x ↦ -f x))
  have hup : BddAbove (range f) := ⟨K,by rintro _ ⟨x,rfl⟩; exact (le_abs_self _).trans (hb x)⟩
  have hlo : BddAbove (range (fun x ↦ -f x)) := ⟨K,by rintro _ ⟨x,rfl⟩; exact (neg_le_abs _).trans (hb x)⟩
  have bound (x : ℝ) : f x≤M ∧ -f x≤N := ⟨le_csSup hup (mem_range_self x),le_csSup hlo (mem_range_self x)⟩
  intro x y
  obtain ⟨a,b,ha,hab⟩ := he (y-x)
  have hM : a*M+b=M := translate_supremum ha hup hab
  have hN : a*N+(-b)=N := translate_supremum ha hlo (fun z ↦ by change -f (z+(y-x))=a*(-f z)+(-b); rw [hab]; ring)
  have hh : (a-1)*(M+N)=0 := by linarith only [hM,hN]
  rcases mul_eq_zero.mp hh with hr|hr
  · have ha1 : a=1 := by linarith
    rw [ha1,one_mul] at hM
    have hz := hab x
    rw [show x+(y-x)=y by ring,ha1,one_mul] at hz
    linarith
  · linarith only [hr,(bound x).1,(bound x).2,(bound y).1,(bound y).2]

theorem homogeneous_scalar_translation {g : ℝ → ℝ} {a : ℝ} (dg : ∀ x, HasDerivAt g (a*g x) x) (x h : ℝ) :
    g (x+h)=Real.exp (a*h)*g x := by
  let F := fun z ↦ Real.exp (-(a*z))*g z
  have hd (z : ℝ) : HasDerivAt F 0 z := by
    have ds := (Real.hasDerivAt_exp (-(a*z))).comp z ((hasDerivAt_id z).const_mul a).fun_neg
    convert ds.fun_mul (dg z) using 1 <;> first | rfl | dsimp; ring
  have eq := isOpen_univ.is_const_of_deriv_eq_zero isPreconnected_univ
    (fun z _ ↦ (hd z).differentiableAt.differentiableWithinAt) (fun z _ ↦ (hd z).deriv)
    (mem_univ (x+h)) (mem_univ x)
  change Real.exp (-(a*(x+h)))*g (x+h)=Real.exp (-(a*x))*g x at eq
  rw [mul_add,neg_add,Real.exp_add,Real.exp_neg,Real.exp_neg] at eq
  field_simp [(Real.exp_pos (a*x)).ne',(Real.exp_pos (a*h)).ne'] at eq
  linarith only [eq]

end EuclideanMidpointRigidity.Endpoint

