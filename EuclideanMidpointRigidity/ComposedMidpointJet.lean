module

public import EuclideanMidpointRigidity.ExactScalarJets

/-! # A chain rule for ordinary derivatives at the logarithmic chord midpoint -/

@[expose] public section
noncomputable section
open Set
open scoped ContDiff
namespace EuclideanMidpointRigidity.Endpoint

def atMidCoeff (a : ℕ → ℝ) : ℕ → ℕ → ℕ → ℝ
  | 0,k,j => if k=0 then a j else 0
  | n+1,k,j => k*atMidCoeff a n (k-1) j-k*atMidCoeff a n (k+1) j+atMidCoeff a n (k+1) (j+1)

private def composedTerm (f : ℝ → ℝ) (k j : ℕ) (x : ℝ) :=
  (Real.tanh x)^k*iteratedDeriv j f (chordMid x)

private theorem allDerivSmooth {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (j : ℕ) : ContDiff ℝ ∞ (iteratedDeriv j f) :=
  contDiffOn_univ.mp (smooth_line_derivative isOpen_univ hf.contDiffOn j)

private theorem tanhSmooth : ContDiff ℝ ∞ Real.tanh := by
  rw [show Real.tanh=fun x ↦ Real.sinh x/Real.cosh x from funext Real.tanh_eq_sinh_div_cosh]
  exact Real.contDiff_sinh.div Real.contDiff_cosh fun x ↦ (Real.cosh_pos x).ne'

private theorem termSmooth {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (k j : ℕ) : ContDiff ℝ ∞ (composedTerm f k j) :=
  (tanhSmooth.pow k).mul ((allDerivSmooth hf j).comp chordMid_smooth)

private theorem termDiff {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (k j : ℕ) :
    deriv (composedTerm f k j)=fun x ↦ (k:ℝ)*composedTerm f (k-1) j x-
      (k:ℝ)*composedTerm f (k+1) j x+composedTerm f (k+1) (j+1) x := by
  funext x
  have ht : HasDerivAt Real.tanh (1-(Real.tanh x)^2) x := by
    have h := (Real.hasDerivAt_sinh x).fun_div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
    rw [show Real.tanh=fun u ↦ Real.sinh u/Real.cosh u from funext Real.tanh_eq_sinh_div_cosh]
    convert h using 1
    field_simp [(Real.cosh_pos x).ne']
  have hd := (hasDerivAt_line_derivative isOpen_univ hf.contDiffOn (mem_univ (chordMid x)) j).comp x (chordMid_diff x)
  have h := ((ht.fun_pow k).fun_mul hd).deriv
  change deriv (fun t ↦ (Real.tanh t)^k*((iteratedDeriv j f) ∘ chordMid) t) x=_
  rw [h]
  cases k <;> simp only [composedTerm,Function.comp_apply,Nat.cast_zero,Nat.cast_add,Nat.cast_one,
    Nat.add_one_sub_one,pow_zero,pow_succ,zero_mul,one_mul,sub_self,zero_add] <;> ring

theorem atMidCoeff_correct {f : ℝ → ℝ} {a : ℕ → ℝ} (hf : ContDiff ℝ ∞ f) (ha : ∀ j, iteratedDeriv j f 0=a j)
    (n : ℕ) : iteratedDeriv n (fun x ↦ f (chordMid x)) 0=atMidCoeff a n 0 0 := by
  have calc' (m k j : ℕ) : iteratedDeriv m (composedTerm f k j) 0=atMidCoeff a m k j := by
    induction m generalizing k j with
    | zero => cases k <;> simp [composedTerm,chordMid,atMidCoeff,ha]
    | succ m ih =>
      rw [iteratedDeriv_succ',termDiff hf]
      have h₁ := (contDiff_const (c := (k:ℝ))).mul (termSmooth hf (k-1) j)
      have h₂ := (contDiff_const (c := (k:ℝ))).mul (termSmooth hf (k+1) j)
      rw [iteratedDeriv_fun_add ((h₁.sub h₂).contDiffAt.of_le (by simp)) ((termSmooth hf (k+1) (j+1)).contDiffAt.of_le (by simp)),
        iteratedDeriv_fun_sub (h₁.contDiffAt.of_le (by simp)) (h₂.contDiffAt.of_le (by simp)),
        iteratedDeriv_const_mul_field,iteratedDeriv_const_mul_field]
      simp only [ih,atMidCoeff]
  rw [← show composedTerm f 0 0=fun x ↦ f (chordMid x) by funext x; simp [composedTerm]]
  exact calc' n 0 0

end EuclideanMidpointRigidity.Endpoint

