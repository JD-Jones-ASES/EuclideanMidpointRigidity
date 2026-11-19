module

public import EuclideanMidpointRigidity.TiltedOddJet

/-! # Derivatives at the midpoint of an axial chord -/

@[expose] public section
noncomputable section
open scoped ContDiff
namespace EuclideanMidpointRigidity.Endpoint

def chordMid (x : ℝ) := Real.log (Real.cosh x)

theorem chordMid_smooth : ContDiff ℝ ∞ chordMid :=
  Real.contDiff_cosh.log fun x ↦ (Real.cosh_pos x).ne'

theorem chordMid_diff (x : ℝ) : HasDerivAt chordMid (Real.tanh x) x := by
  unfold chordMid
  simpa only [Real.tanh_eq_sinh_div_cosh] using (Real.hasDerivAt_cosh x).log (Real.cosh_pos x).ne'

private theorem tanh_diff (x : ℝ) : HasDerivAt Real.tanh (1-(Real.tanh x)^2) x := by
  have h := (Real.hasDerivAt_sinh x).fun_div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  rw [show Real.tanh=fun u ↦ Real.sinh u/Real.cosh u from funext Real.tanh_eq_sinh_div_cosh]
  convert h using 1
  field_simp [(Real.cosh_pos x).ne']

def hyperMoment : ℕ → ℕ → ℚ → ℚ
  | 0,k,_ => if k=0 then 1 else 0
  | n+1,k,b => k*hyperMoment n (k-1) b+(b-k)*hyperMoment n (k+1) b

def hyperTerm (k : ℕ) (b : ℚ) (x : ℝ) := (Real.tanh x)^k*Real.exp ((b:ℝ)*chordMid x)

private theorem hyper_smooth (k : ℕ) (b : ℚ) : ContDiff ℝ ∞ (hyperTerm k b) := by
  have ht : ContDiff ℝ ∞ Real.tanh := by
    rw [show Real.tanh=fun u ↦ Real.sinh u/Real.cosh u from funext Real.tanh_eq_sinh_div_cosh]
    exact Real.contDiff_sinh.div Real.contDiff_cosh fun x ↦ (Real.cosh_pos x).ne'
  exact (ht.pow k).mul (Real.contDiff_exp.comp (contDiff_const.mul chordMid_smooth))

private theorem hyper_diff (k : ℕ) (b : ℚ) :
    deriv (hyperTerm k b)=fun x ↦ (k:ℝ)*hyperTerm (k-1) b x+((b:ℝ)-k)*hyperTerm (k+1) b x := by
  funext x
  have de := ((chordMid_diff x).const_mul (b:ℝ)).exp
  cases k with
  | zero =>
    rw [show hyperTerm 0 b=fun t ↦ Real.exp ((b:ℝ)*chordMid t) by funext t; simp [hyperTerm]]
    simp only [Nat.cast_zero,zero_mul,zero_add,sub_zero,hyperTerm,pow_zero,one_mul,pow_one]
    convert de.deriv using 1 <;> first | rfl | ring
  | succ k =>
    have h := (((tanh_diff x).fun_pow (k+1)).fun_mul de).deriv
    change deriv (fun y ↦ _*_) x=_
    rw [h]
    simp only [hyperTerm,Nat.add_one_sub_one,Nat.cast_add,Nat.cast_one,pow_succ]
    ring

theorem hyperMoment_correct (n k : ℕ) (b : ℚ) :
    iteratedDeriv n (hyperTerm k b) 0=(hyperMoment n k b:ℝ) := by
  induction n generalizing k with
  | zero => cases k <;> simp [hyperMoment,hyperTerm,chordMid]
  | succ n ih =>
    rw [iteratedDeriv_succ',hyper_diff]
    have h₁ := ((contDiff_const (c := (k:ℝ))).mul (hyper_smooth (k-1) b)).contDiffAt (x := (0:ℝ))
    have h₂ := ((contDiff_const (c := (b:ℝ)-k)).mul (hyper_smooth (k+1) b)).contDiffAt (x := (0:ℝ))
    rw [iteratedDeriv_fun_add (h₁.of_le (by simp))
      (h₂.of_le (by simp)),iteratedDeriv_const_mul_field,iteratedDeriv_const_mul_field]
    simp only [ih,hyperMoment]
    push_cast
    <;> rfl

theorem chordMid_moment (n : ℕ) : iteratedDeriv (n+1) chordMid 0=(hyperMoment n 1 0:ℝ) := by
  rw [iteratedDeriv_succ',show deriv chordMid=hyperTerm 1 0 by
    funext x; rw [(chordMid_diff x).deriv]; simp [hyperTerm]]
  exact hyperMoment_correct n 1 0

end EuclideanMidpointRigidity.Endpoint

