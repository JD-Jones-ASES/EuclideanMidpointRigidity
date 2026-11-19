module

public import EuclideanMidpointRigidity.DirichletBoundary
public import EuclideanMidpointRigidity.HyperbolicMoments
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Initial-value primitives for every real Jacobi rate, including zero -/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ContDiff Interval
namespace EuclideanMidpointRigidity.Endpoint

def lineIntegral (f : ℝ → ℝ) (x : ℝ) := ∫ t in 0..x, f t

theorem lineIntegral_diff {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (lineIntegral f) (f x) x :=
  intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _) hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

theorem lineIntegral_smooth {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (lineIntegral f) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x ↦ (lineIntegral_diff hf.continuous x).differentiableAt,?_⟩
  rw [show deriv (lineIntegral f)=f from funext fun x ↦ (lineIntegral_diff hf.continuous x).deriv]
  exact hf

def rateCoordinate (k : ℝ) := lineIntegral fun x ↦ Real.exp (k*x)

theorem rateCoordinate_smooth (k : ℝ) : ContDiff ℝ ∞ (rateCoordinate k) := lineIntegral_smooth (by fun_prop)

theorem rateCoordinate_diff (k x : ℝ) : HasDerivAt (rateCoordinate k) (Real.exp (k*x)) x :=
  lineIntegral_diff (by fun_prop) x

@[simp] theorem rateCoordinate_zero (k : ℝ) : rateCoordinate k 0=0 := by simp [rateCoordinate,lineIntegral]

def ratePrimitive (η : ℝ) (f : ℝ → ℝ) := lineIntegral fun s ↦ Real.exp (η*s)*lineIntegral (fun t ↦ Real.exp ((-η)*t)*f t) s

def rateVelocity (η : ℝ) (f : ℝ → ℝ) (s : ℝ) := Real.exp (η*s)*lineIntegral (fun t ↦ Real.exp ((-η)*t)*f t) s

theorem rateVelocity_smooth (η : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (rateVelocity η f) := by
  have he (q : ℝ) : ContDiff ℝ ∞ (fun t : ℝ ↦ Real.exp (q*t)) := by fun_prop
  exact (he η).mul (lineIntegral_smooth ((he (-η)).mul hf))

theorem ratePrimitive_smooth (η : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (ratePrimitive η f) :=
  lineIntegral_smooth (rateVelocity_smooth η hf)

def ratePrimitive_solution (η : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) : LinePrimitive η f where
  value := ratePrimitive η f
  slope := rateVelocity η f
  position := lineIntegral_diff (rateVelocity_smooth η hf).continuous
  velocity s := by
    have hd := (exp_line_diff η s).fun_mul (lineIntegral_diff (f := fun t ↦ Real.exp ((-η)*t)*f t) (by fun_prop (disch := exact hf.continuous)) s)
    change HasDerivAt (fun t ↦ Real.exp (η*t)*_) _ s
    convert hd using 1
    dsimp only [rateVelocity]
    rw [neg_mul,Real.exp_neg]
    field_simp [(Real.exp_pos (η*s)).ne'] <;> ring

@[simp] theorem ratePrimitive_zero (η : ℝ) (f : ℝ → ℝ) : ratePrimitive η f 0=0 := by simp [ratePrimitive,lineIntegral]
@[simp] theorem rateVelocity_zero (η : ℝ) (f : ℝ → ℝ) : rateVelocity η f 0=0 := by simp [rateVelocity,lineIntegral]

def universalBoundary (η h : ℝ) (F : ℝ → ℝ) :=
  let A := rateCoordinate η
  let m := chordMid h
  (A h-A (-h))*F m-(A h-A m)*F (-h)-(A m-A (-h))*F h

theorem VanishingResponse.universal_boundary {η h : ℝ} {f : ℝ → ℝ} (H : VanishingResponse η h f)
    (hh : 0<h) (P : LinePrimitive η f) : universalBoundary η h P.value=0 := by
  obtain ⟨X,V,H,hm⟩ := H
  let c := Real.exp ((-η)*(-h))*(V (-h)-P.slope (-h))
  have constancy {g : ℝ → ℝ} (dg : ∀ s ∈ Icc (-h) h, HasDerivAt g 0 s) : ∀ s ∈ Icc (-h) h, g s=g (-h) :=
    constant_of_has_deriv_right_zero (fun x hx ↦ (dg x hx).continuousAt.continuousWithinAt)
      (fun x hx ↦ (dg x (mem_Icc_of_Ico hx)).hasDerivWithinAt)
  have hc : ∀ s ∈ Icc (-h) h, Real.exp ((-η)*s)*(V s-P.slope s)=c := by
    apply constancy (g := fun s ↦ Real.exp ((-η)*s)*(V s-P.slope s))
    intro s hs
    convert (exp_line_diff (-η) s).fun_mul ((H.velocity s hs).fun_sub (P.velocity s)) using 1
    ring
  have hv (s : ℝ) (hs : s ∈ Icc (-h) h) : V s-P.slope s=c*Real.exp (η*s) := by
    rw [← hc s hs,neg_mul,Real.exp_neg]
    field_simp [(Real.exp_pos (η*s)).ne']
  let a := X (-h)-P.value (-h)-c*rateCoordinate η (-h)
  have ha : ∀ s ∈ Icc (-h) h, X s-P.value s-c*rateCoordinate η s=a := by
    apply constancy (g := fun s ↦ X s-P.value s-c*rateCoordinate η s)
    intro s hs
    convert ((H.position s hs).fun_sub (P.position s)).fun_sub ((rateCoordinate_diff η s).const_mul c) using 1
    rw [hv s hs]; ring
  have hmem := chordParameter_bounds hh.le (show (1/2:ℝ) ∈ Icc 0 1 by norm_num)
  rw [chordParameter_half] at hmem
  have hl := ha (-h) (left_mem_Icc.mpr (by linarith))
  have hr := ha h (right_mem_Icc.mpr (by linarith))
  have hm' := ha _ hmem
  rw [hm] at hm'
  rw [H.left] at hl
  rw [H.right] at hr
  dsimp only [universalBoundary,chordMid]
  linear_combination -(rateCoordinate η h-rateCoordinate η (-h))*hm'+
    (rateCoordinate η h-rateCoordinate η (Real.log (Real.cosh h)))*hl+
    (rateCoordinate η (Real.log (Real.cosh h))-rateCoordinate η (-h))*hr

end EuclideanMidpointRigidity.Endpoint

