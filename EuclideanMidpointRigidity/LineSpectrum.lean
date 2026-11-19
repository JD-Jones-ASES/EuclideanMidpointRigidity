module

public import EuclideanMidpointRigidity.RulingEntries
public import EuclideanMidpointRigidity.RulingODE
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! # A smooth characteristic polynomial for all the tilt rates of a ruling -/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped ContDiff InnerProductSpace
namespace EuclideanMidpointRigidity
open Endpoint
variable {d : ℕ}
local notation "E" => Space d
local notation "B₀" => EuclideanSpace.basisFun (Fin d) ℝ

namespace LiftedSection
variable (S : LiftedSection d)

def tiltOperator (p : E) : E →L[ℝ] E := ContinuousLinearMap.id ℝ E-
  (2:ℝ) • (S.axisSlice p-InnerProductSpace.rankOne ℝ (S.axis p) (S.axis p))

def rateOperator (p : E) : E →L[ℝ] E := (21:ℝ) • (S.tiltOperator p).comp (S.tiltOperator p)+
  (42:ℝ) • S.tiltOperator p+ContinuousLinearMap.id ℝ E

theorem smooth_tiltOperator_apply {v : E → E} (hv : ContDiffOn ℝ ∞ v S.domain) :
    ContDiffOn ℝ ∞ (fun p ↦ S.tiltOperator p (v p)) S.domain := by
  change ContDiffOn ℝ ∞ (fun p ↦ v p-(2:ℝ) • (S.axisSlice p (v p)-⟪S.axis p,v p⟫_ℝ • S.axis p)) S.domain
  exact hv.sub ((contDiffOn_const (c := (2:ℝ))).smul ((S.contDiffOn_axisSlice.clm_apply hv).sub ((S.smoothAxis.inner ℝ hv).smul S.smoothAxis)))

theorem smooth_rateOperator_apply (v : E) : ContDiffOn ℝ ∞ (fun p ↦ S.rateOperator p v) S.domain := by
  have ha := S.smooth_tiltOperator_apply (v := fun _ ↦ v) contDiffOn_const
  change ContDiffOn ℝ ∞ (fun p ↦ (21:ℝ) • S.tiltOperator p (S.tiltOperator p v)+(42:ℝ) • S.tiltOperator p v+v) S.domain
  exact (((contDiffOn_const (c := (21:ℝ))).smul (S.smooth_tiltOperator_apply ha)).add ((contDiffOn_const (c := (42:ℝ))).smul ha)).add contDiffOn_const

def rateMatrix : Matrix (Fin d) (Fin d) (SmoothCoefficient S.domain) :=
  fun i j ↦ ⟨fun p ↦ ⟪B₀ i,S.rateOperator p (B₀ j)⟫_ℝ,contDiffOn_const.inner ℝ (S.smooth_rateOperator_apply _)⟩

theorem specialized_rateMatrix (p : E) : S.rateMatrix.map (SmoothPolynomial.evaluateCoefficient p)=
    LinearMap.toMatrix (B₀).toBasis (B₀).toBasis (S.rateOperator p).toLinearMap := by
  ext i j
  simp only [LinearMap.toMatrix_apply,OrthonormalBasis.coe_toBasis,OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply]
  rfl

def rulingPolynomial (p : E) : ℝ[X] :=
  X^3*(X^2-1)*((S.rateOperator p).toLinearMap.charpoly.comp (X^2))

def smoothRulingPolynomial : Polynomial (SmoothCoefficient S.domain) :=
  X^3*(X^2-1)*(S.rateMatrix.charpoly.comp (X^2))

theorem specialize_rulingPolynomial (p : E) :
    S.smoothRulingPolynomial.map (SmoothPolynomial.evaluateCoefficient p)=S.rulingPolynomial p := by
  simp only [smoothRulingPolynomial,rulingPolynomial,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_sub,
    Polynomial.map_one,Polynomial.map_X,Polynomial.map_comp,← Matrix.charpoly_map,S.specialized_rateMatrix,
    LinearMap.charpoly_toMatrix]

theorem smooth_rulingPolynomial_coeff (n : ℕ) : ContDiffOn ℝ ∞ (fun p ↦ (S.rulingPolynomial p).coeff n) S.domain := by
  have he (p : E) : (S.rulingPolynomial p).coeff n=(S.smoothRulingPolynomial.coeff n).val p := by
    rw [← S.specialize_rulingPolynomial,Polynomial.coeff_map]; rfl
  simp only [he]
  exact (S.smoothRulingPolynomial.coeff n).property

end LiftedSection

namespace LiftedSection.RulingFrame
variable {S : LiftedSection d} {p : Space d} {ι : Type*} [Fintype ι] [DecidableEq ι] (F : RulingFrame S p ι)

def exponentSquare (i : ι) := if i=F.axial then tiltRate 1 else tiltRate (1-2*F.value i)

theorem exponentSquare_pos (i : ι) : 0<F.exponentSquare i := by
  by_cases hi : i=F.axial
  · simp only [exponentSquare,ite_eq_left hi]; apply tiltRate_pos; norm_num
  · simp only [exponentSquare,ite_eq_right hi]; apply tiltRate_pos; linarith [(F.bounds i hi).2]

theorem rate_eigen (hp : p ∈ S.domain) (i : ι) : S.rateOperator p (F.basis i)=F.exponentSquare i • F.basis i := by
  let r := if i=F.axial then 1 else 1-2*F.value i
  have htilt : S.tiltOperator p (F.basis i)=r • F.basis i := by
    change F.basis i-(2:ℝ) • (S.axisSlice p (F.basis i)-⟪S.axis p,F.basis i⟫_ℝ • S.axis p)=_
    by_cases hi : i=F.axial
    · subst i
      simp only [r,ite_eq_left rfl,F.axis_eq,real_inner_self_eq_norm_sq,S.unit p hp,one_pow,one_smul]
      have he : S.axisSlice p (S.axis p)=S.axis p := by
        change K (S.cubic p) (S.axis p) (S.axis p)=S.axis p
        simpa only [one_smul] using S.normalized_axis hp
      simp [he]
    · have hz : ⟪S.axis p,F.basis i⟫_ℝ=0 := by rw [← F.axis_eq]; exact F.basis.orthonormal.inner_eq_zero (Ne.symm hi)
      rw [F.eigen,hz,zero_smul,sub_zero]
      simp only [r,ite_eq_right hi]
      module
  have her : F.exponentSquare i=tiltRate r := by by_cases hi : i=F.axial <;> simp [r,exponentSquare,hi]
  change (21:ℝ) • S.tiltOperator p (S.tiltOperator p (F.basis i))+(42:ℝ) • S.tiltOperator p (F.basis i)+F.basis i=_
  rw [htilt,map_smul,htilt,her]
  dsimp only [tiltRate]
  module

theorem charpoly_rates (hp : p ∈ S.domain) :
    (S.rateOperator p).toLinearMap.charpoly=∏ i, (X-C (F.exponentSquare i)) := by
  have e : LinearMap.toMatrix F.basis.toBasis F.basis.toBasis (S.rateOperator p).toLinearMap=Matrix.diagonal F.exponentSquare := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    simp only [OrthonormalBasis.coe_toBasis,ContinuousLinearMap.coe_coe,F.rate_eigen hp,
      map_smul,F.basis.toBasis.repr_self,Finsupp.smul_single,smul_eq_mul,mul_one,Finsupp.single_apply,Matrix.diagonal_apply]
    by_cases h : i=j <;> simp [h,Ne.symm]
  rw [← LinearMap.charpoly_toMatrix _ F.basis.toBasis,e,Matrix.charpoly_diagonal]

end LiftedSection.RulingFrame
end EuclideanMidpointRigidity

