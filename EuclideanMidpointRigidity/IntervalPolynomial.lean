module

public import Mathlib.Tactic

/-! # Rational polynomial inequalities on a closed interval

Coefficients are stored in ascending order. After each bisection the variable
is rescaled to the unit interval. The elementary Horner bound can then be
checked using rational arithmetic alone.
-/

@[expose] public section
namespace EuclideanMidpointRigidity.IntervalPolynomial

def eval : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => c + x * eval cs x

def plus : List ℚ → List ℚ → List ℚ
  | [], q => q
  | p, [] => p
  | c :: cs, d :: ds => (c+d) :: plus cs ds

theorem eval_plus (p q : List ℚ) (x : ℝ) :
    eval (plus p q) x = eval p x + eval q x := by
  induction p generalizing q with
  | nil => simp [plus, eval]
  | cons c cs ih =>
    cases q with
    | nil => simp [plus, eval]
    | cons d ds => simp [plus, eval, ih]; ring

theorem eval_scale (p : List ℚ) (a : ℚ) (x : ℝ) :
    eval (p.map (a*·)) x = a * eval p x := by
  induction p with
  | nil => simp [eval]
  | cons c cs ih => simp [eval, ih]; ring

/-- Coefficients after the affine change of variable `x ↦ a + b*x`. -/
def affine (a b : ℚ) : List ℚ → List ℚ
  | [] => []
  | c :: cs =>
    let q := affine a b cs
    plus (plus [c] (q.map (a*·))) (0 :: q.map (b*·))

theorem eval_affine (p : List ℚ) (a b : ℚ) (x : ℝ) :
    eval (affine a b p) x = eval p (a + b*x) := by
  induction p with
  | nil => rfl
  | cons c cs ih =>
    simp only [affine, eval_plus, eval_scale, eval, Rat.cast_zero, zero_add, mul_zero, add_zero, ih]
    ring

def lower : List ℚ → ℚ
  | [] => 0
  | c :: cs => c + min 0 (lower cs)

private theorem lower_le (p : List ℚ) {x : ℝ} (hx : 0 ≤ x) (h₁ : x ≤ 1) :
    (lower p : ℝ) ≤ eval p x := by
  induction p with
  | nil => simp [lower, eval]
  | cons c cs ih =>
    simp only [lower, eval, Rat.cast_add, add_le_add_iff_left]
    by_cases hs : 0 ≤ lower cs
    · rw [min_eq_left hs, Rat.cast_zero]
      exact mul_nonneg hx ((by exact_mod_cast hs : (0:ℝ) ≤ lower cs).trans ih)
    · rw [min_eq_right (le_of_not_ge hs)]
      have hneg : (lower cs : ℝ) ≤ 0 := by exact_mod_cast le_of_not_ge hs
      calc
        (lower cs : ℝ) ≤ x * (lower cs : ℝ) := by nlinarith [mul_nonneg (sub_nonneg.mpr h₁) (neg_nonneg.mpr hneg)]
        _ ≤ x * eval cs x := mul_le_mul_of_nonneg_left ih hx

def check : ℕ → List ℚ → Bool
  | 0, p => decide (0 ≤ lower p)
  | n+1, p => decide (0 ≤ lower p) ||
      (check n (affine 0 (1/2) p) && check n (affine (1/2) (1/2) p))

/-- A successful rational check proves the inequality for every real point. -/
theorem check_sound {n : ℕ} {p : List ℚ} (hc : check n p = true)
    {x : ℝ} (hx : 0 ≤ x) (h₁ : x ≤ 1) : 0 ≤ eval p x := by
  induction n generalizing p x with
  | zero =>
    have hp : 0 ≤ lower p := of_decide_eq_true hc
    exact (by exact_mod_cast hp : (0:ℝ) ≤ lower p).trans (lower_le p hx h₁)
  | succ n ih =>
    simp only [check, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hc
    rcases hc with hp | ⟨hl,hr⟩
    · exact (by exact_mod_cast hp : (0:ℝ) ≤ lower p).trans (lower_le p hx h₁)
    · by_cases hm : x ≤ 1/2
      · have hv := ih hl (x := 2*x) (by linarith) (by linarith)
        simpa [eval_affine] using hv
      · have hv := ih hr (x := 2*x-1) (by linarith) (by linarith)
        rw [eval_affine] at hv
        convert hv using 2
        push_cast
        ring

def times : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | c :: cs, q => plus (q.map (c*·)) (0 :: times cs q)

theorem eval_times (p q : List ℚ) (x : ℝ) :
    eval (times p q) x = eval p x * eval q x := by
  induction p with
  | nil => simp [times, eval]
  | cons c cs ih => simp [times, eval_plus, eval_scale, eval, ih]; ring

def trim : List ℚ → List ℚ
  | [] => []
  | c :: cs =>
    let q := trim cs
    if c = 0 ∧ q = [] then [] else c :: q

theorem eval_trim (p : List ℚ) (x : ℝ) : eval (trim p) x = eval p x := by
  induction p with
  | nil => rfl
  | cons c cs ih =>
    simp only [trim]
    split_ifs with h
    · obtain ⟨rfl,h⟩ := h
      rw [h] at ih
      simp only [eval] at ih
      simp [eval, ← ih]
    · simp [eval, ih]

/-- A square factor, possible endpoint factors, and a positive scale recover
the input polynomial from a smaller polynomial on the unit interval. -/
structure SignWitness where
  scale : ℚ
  leftRoot : Bool
  rightRoot : Bool
  square : List ℚ
  core : List ℚ
  depth : ℕ

def SignWitness.product (w : SignWitness) : List ℚ :=
  let l := if w.leftRoot then [1,1] else [1]
  let r := if w.rightRoot then [1,-2] else [1]
  let core := affine (2/3) (2/3) w.core
  (times (times l r) (times core (times w.square w.square))).map (w.scale*·)

def SignWitness.verify (w : SignWitness) (p : List ℚ) : Bool :=
  decide (0 ≤ w.scale) && check w.depth w.core && decide (trim p = trim w.product)

theorem SignWitness.sound {w : SignWitness} {p : List ℚ} (hv : w.verify p = true)
    {x : ℝ} (hl : -1 ≤ x) (hr : x ≤ 1/2) : 0 ≤ eval p x := by
  simp only [verify, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨hscale,hc⟩,he⟩ := hv
  rw [← eval_trim p, he, eval_trim]
  simp only [product, eval_scale, eval_times, eval_affine]
  have hy₀ : (0:ℝ) ≤ (2/3:ℚ) + (2/3:ℚ)*x := by push_cast; linarith
  have hy₁ : (2/3:ℚ) + (2/3:ℚ)*x ≤ (1:ℝ) := by push_cast; linarith
  have hcore := check_sound hc hy₀ hy₁
  have hleft : 0 ≤ eval (if w.leftRoot then [1,1] else [1]) x := by
    split <;> simp [eval] <;> linarith
  have hright : 0 ≤ eval (if w.rightRoot then [1,-2] else [1]) x := by
    split <;> norm_num [eval] <;> linarith
  exact mul_nonneg (by exact_mod_cast hscale)
    (mul_nonneg (mul_nonneg hleft hright) (mul_nonneg hcore (mul_self_nonneg _)))

end EuclideanMidpointRigidity.IntervalPolynomial
