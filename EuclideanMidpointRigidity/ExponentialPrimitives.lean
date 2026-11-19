module

public import EuclideanMidpointRigidity.DirichletBoundary

/-! # Explicit primitives for affine multiples of a real exponential -/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity.Endpoint

structure QuadraticMode where
  a : ℚ
  b : ℚ
  c : ℚ

namespace QuadraticMode

def eval (P : QuadraticMode) (s : ℝ) := (P.a:ℝ)+P.b*s+P.c*s^2

def value (P : QuadraticMode) (q : ℚ) (s : ℝ) := P.eval s*Real.exp ((q:ℝ)*s)

def diff (P : QuadraticMode) (q : ℚ) : QuadraticMode :=
  ⟨q*P.a+P.b,q*P.b+2*P.c,q*P.c⟩

theorem hasDerivAt_value (P : QuadraticMode) (q : ℚ) (s : ℝ) :
    HasDerivAt (P.value q) ((P.diff q).value q s) s := by
  have h : HasDerivAt P.eval ((P.b:ℝ)+2*P.c*s) s := by
    have hd := ((hasDerivAt_const s (P.a:ℝ)).fun_add ((hasDerivAt_id s).const_mul (P.b:ℝ))).fun_add
      (((hasDerivAt_id s).fun_pow 2).const_mul (P.c:ℝ))
    convert hd using 1 <;> first | rfl | simp [id_eq] <;> ring
  change HasDerivAt (fun t ↦ P.eval t*Real.exp ((q:ℝ)*t)) _ s
  convert h.fun_mul (exp_line_diff q s) using 1
  dsimp [diff,value,eval]
  push_cast
  ring

/-- Coefficients of a primitive for the source `(u + v s) exp(q s)`. -/
def primitive (η q u v : ℚ) : QuadraticMode :=
  let D := q*(q-η)
  let H := 2*q-η
  if D=0 then ⟨0,(u-v/H)/H,v/(2*H)⟩ else ⟨(u-H*(v/D))/D,v/D,0⟩

theorem primitive_eq (η q u v : ℚ) (hη : η≠0) :
    let P := primitive η q u v
    let D := q*(q-η)
    let H := 2*q-η
    D*P.a+H*P.b+2*P.c=u ∧ D*P.b+2*H*P.c=v ∧ D*P.c=0 := by
  dsimp only
  unfold primitive
  dsimp only
  generalize ed : q*(q-η)=D
  generalize eh : 2*q-η=H
  by_cases hd : D=0
  · have hH : H≠0 := by
      subst H
      rcases mul_eq_zero.mp (ed.trans hd) with h | h
      · rw [h]; simpa using hη
      · rw [sub_eq_zero.mp h]; simpa [two_mul] using hη
    subst D
    simp [hd] <;> constructor <;> field_simp [hH] <;> ring
  · simp [hd] <;> constructor <;> field_simp [hd] <;> ring

def linePrimitive (η q u v : ℚ) (hη : η≠0) :
    LinePrimitive (η:ℝ) (fun s ↦ ((u:ℝ)+(v:ℝ)*s)*Real.exp ((q:ℝ)*s)) where
  value := (primitive η q u v).value q
  slope := ((primitive η q u v).diff q).value q
  position := (primitive η q u v).hasDerivAt_value q
  velocity s := by
    let P := primitive η q u v
    obtain ⟨ha,hb,hc⟩ := primitive_eq η q u v hη
    have ha' : (q:ℝ)*(q-η)*(P.a:ℝ)+(2*q-η)*(P.b:ℝ)+2*P.c=u := by exact_mod_cast ha
    have hb' : (q:ℝ)*(q-η)*(P.b:ℝ)+2*(2*q-η)*(P.c:ℝ)=v := by exact_mod_cast hb
    have hc' : (q:ℝ)*(q-η)*(P.c:ℝ)=0 := by exact_mod_cast hc
    convert (P.diff q).hasDerivAt_value q s using 1
    change (η:ℝ)*((P.diff q).value q s)+_=((P.diff q).diff q).value q s
    dsimp [diff,value,eval]
    push_cast
    linear_combination -Real.exp ((q:ℝ)*s)*ha'-s*Real.exp ((q:ℝ)*s)*hb'-s^2*Real.exp ((q:ℝ)*s)*hc'

end QuadraticMode
end EuclideanMidpointRigidity.Endpoint

