module

public import EuclideanMidpointRigidity.ResponseLinearity
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # An exact boundary functional for exponential sources -/

@[expose] public section
noncomputable section
open Set
namespace EuclideanMidpointRigidity.Endpoint

structure LinePrimitive (η : ℝ) (f : ℝ → ℝ) where
  value : ℝ → ℝ
  slope : ℝ → ℝ
  position : ∀ s, HasDerivAt value (slope s) s
  velocity : ∀ s, HasDerivAt slope (η*slope s+f s) s

def LinePrimitive.add {η : ℝ} {f g : ℝ → ℝ} (P : LinePrimitive η f) (Q : LinePrimitive η g) :
    LinePrimitive η (fun s ↦ f s+g s) where
  value s := P.value s+Q.value s
  slope s := P.slope s+Q.slope s
  position s := (P.position s).fun_add (Q.position s)
  velocity s := by convert (P.velocity s).fun_add (Q.velocity s) using 1; ring

def LinePrimitive.scale {η : ℝ} {f : ℝ → ℝ} (P : LinePrimitive η f) (a : ℝ) :
    LinePrimitive η (fun s ↦ a*f s) where
  value s := a*P.value s
  slope s := a*P.slope s
  position s := (P.position s).const_mul a
  velocity s := by convert (P.velocity s).const_mul a using 1; ring

def boundaryValue (η h : ℝ) (F : ℝ → ℝ) :=
  let m := Real.log (Real.cosh h)
  (Real.exp (η*h)-Real.exp (η*(-h)))*F m-(Real.exp (η*h)-Real.exp (η*m))*F (-h)-
    (Real.exp (η*m)-Real.exp (η*(-h)))*F h

theorem boundaryValue_add (η h : ℝ) (f g : ℝ → ℝ) :
    boundaryValue η h (fun s ↦ f s+g s)=boundaryValue η h f+boundaryValue η h g := by
  dsimp [boundaryValue]; ring

theorem boundaryValue_scale (η h a : ℝ) (f : ℝ → ℝ) :
    boundaryValue η h (fun s ↦ a*f s)=a*boundaryValue η h f := by
  dsimp [boundaryValue]; ring

private theorem line_const {a b : ℝ} {F : ℝ → ℝ} (hF : ∀ s ∈ Icc a b, HasDerivAt F 0 s) :
    ∀ s ∈ Icc a b, F s=F a := by
  apply constant_of_has_deriv_right_zero
  · exact fun x hx ↦ (hF x hx).continuousAt.continuousWithinAt
  · exact fun x hx ↦ (hF x (mem_Icc_of_Ico hx)).hasDerivWithinAt

theorem exp_line_diff (q s : ℝ) :
    HasDerivAt (fun t ↦ Real.exp (q*t)) (Real.exp (q*s)*q) s := by
  simpa only [mul_one,id_eq] using ((hasDerivAt_id s).const_mul q).exp

theorem VanishingResponse.boundary {η h : ℝ} {f : ℝ → ℝ} (H : VanishingResponse η h f)
    (hη : η≠0) (hh : 0<h) (P : LinePrimitive η f) : boundaryValue η h P.value=0 := by
  obtain ⟨X,V,H,hm⟩ := H
  let c := Real.exp ((-η)*(-h))*(V (-h)-P.slope (-h))
  have hc : ∀ s ∈ Icc (-h) h, Real.exp ((-η)*s)*(V s-P.slope s)=c := by
    apply line_const (F := fun s ↦ Real.exp ((-η)*s)*(V s-P.slope s))
    intro s hs
    convert (exp_line_diff (-η) s).fun_mul ((H.velocity s hs).fun_sub (P.velocity s)) using 1
    ring
  have hv (s : ℝ) (hs : s ∈ Icc (-h) h) : V s-P.slope s=c*Real.exp (η*s) := by
    rw [← hc s hs,neg_mul,Real.exp_neg]
    field_simp [(Real.exp_pos (η*s)).ne']
  let a := X (-h)-P.value (-h)-(c/η)*Real.exp (η*(-h))
  have ha : ∀ s ∈ Icc (-h) h, X s-P.value s-(c/η)*Real.exp (η*s)=a := by
    apply line_const (F := fun s ↦ X s-P.value s-(c/η)*Real.exp (η*s))
    intro s hs
    convert ((H.position s hs).fun_sub (P.position s)).fun_sub ((exp_line_diff η s).const_mul (c/η)) using 1
    rw [hv s hs]
    field_simp [hη] <;> ring
  have hmem := chordParameter_bounds hh.le (show (1/2:ℝ) ∈ Icc 0 1 by norm_num)
  rw [chordParameter_half] at hmem
  have hl := ha (-h) (left_mem_Icc.mpr (by linarith))
  have hr := ha h (right_mem_Icc.mpr (by linarith))
  have hm' := ha _ hmem
  rw [hm] at hm'
  rw [H.left] at hl
  rw [H.right] at hr
  dsimp only [boundaryValue]
  linear_combination -(Real.exp (η*h)-Real.exp (η*(-h)))*hm'+
    (Real.exp (η*h)-Real.exp (η*Real.log (Real.cosh h)))*hl+
    (Real.exp (η*Real.log (Real.cosh h))-Real.exp (η*(-h)))*hr

end EuclideanMidpointRigidity.Endpoint

