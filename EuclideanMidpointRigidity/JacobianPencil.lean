module

public import EuclideanMidpointRigidity.AnalyticLineFamily
public import EuclideanMidpointRigidity.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Algebra.Polynomial.Roots

/-! # Determinant and adjugate of the differential of straight-line coordinates -/

@[expose] public section
noncomputable section
open Set Filter Polynomial
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
namespace EuclideanMidpointRigidity.JacobianPencil
variable {d : ℕ}
local notation "E" => Space d
local notation "M" => Matrix (Fin d) (Fin d) ℝ
abbrev coordinateBasis (d : ℕ) := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
local notation "B" => coordinateBasis d

def matrixEquiv (d : ℕ) : (Matrix (Fin d) (Fin d) ℝ) ≃ₗ[ℝ] (Space d →L[ℝ] Space d) :=
  (Matrix.toLin (EuclideanSpace.basisFun (Fin d) ℝ).toBasis (EuclideanSpace.basisFun (Fin d) ℝ).toBasis).trans LinearMap.toContinuousLinearMap

def fromMatrix (d : ℕ) : (Matrix (Fin d) (Fin d) ℝ) →L[ℝ] (Space d →L[ℝ] Space d) :=
  LinearMap.toContinuousLinearMap (matrixEquiv d).toLinearMap

def toMatrix (d : ℕ) : (Space d →L[ℝ] Space d) →L[ℝ] (Matrix (Fin d) (Fin d) ℝ) := by
  have : FiniteDimensional ℝ (Space d →L[ℝ] Space d) := ContinuousLinearMap.finiteDimensional
  exact LinearMap.toContinuousLinearMap (matrixEquiv d).symm.toLinearMap

theorem toMatrix_eq (L : E →L[ℝ] E) : toMatrix d L=LinearMap.toMatrix B B L.toLinearMap := rfl

def entry (i j : Fin d) : M →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
  { toFun := fun m ↦ m i j, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }

theorem analytic_det : ContDiff ℝ ω (fun m : M ↦ Matrix.det m) := by
  simp_rw [Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  exact contDiff_prod fun i _ ↦ (entry (σ i) i).contDiff

theorem analytic_adjugate : ContDiff ℝ ω (fun m : M ↦ (Matrix.adjugate m : M)) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp_rw [Matrix.adjugate_apply]
  apply analytic_det.comp
  apply contDiff_pi.mpr
  intro k
  apply contDiff_pi.mpr
  intro l
  by_cases h : k=j
  · subst k
    simp only [Matrix.updateRow_self]
    exact contDiff_const
  · simp only [Matrix.updateRow_ne h]
    exact (entry k l).contDiff

def jacobian (u : E → E) (p : E) (t : ℝ) : E →L[ℝ] E := ContinuousLinearMap.id ℝ E+t • fderiv ℝ u p
def determinant (u : E → E) (p : E) (t : ℝ) : ℝ := Matrix.det (toMatrix d (jacobian u p t))
def adjugate (u : E → E) (p : E) (t : ℝ) : E →L[ℝ] E := fromMatrix d (Matrix.adjugate (toMatrix d (jacobian u p t)))

def jacobianFamily {W : Set E} (hW : IsOpen W) {u : E → E} (hu : ContDiffOn ℝ ∞ u W) : AnalyticLineFamily W (jacobian u) :=
  ((AnalyticLineFamily.spatial (hu.fderiv_of_isOpen hW (by simp))).prod (AnalyticLineFamily.time W)).map
    (fun q ↦ ContinuousLinearMap.id ℝ E+q.2 • q.1) (contDiff_const.add (contDiff_snd.smul contDiff_fst))

def determinantFamily {W : Set E} (hW : IsOpen W) {u : E → E} (hu : ContDiffOn ℝ ∞ u W) : AnalyticLineFamily W (determinant u) :=
  ((jacobianFamily hW hu).map (toMatrix d) (toMatrix d).contDiff).map _ analytic_det

def adjugateFamily {W : Set E} (hW : IsOpen W) {u : E → E} (hu : ContDiffOn ℝ ∞ u W) : AnalyticLineFamily W (adjugate u) :=
  (((jacobianFamily hW hu).map (toMatrix d) (toMatrix d).contDiff).map _ analytic_adjugate).map (fromMatrix d) (fromMatrix d).contDiff

theorem fromMatrix_apply (m : M) (v : E) : fromMatrix d m v=Matrix.toLin B B m v := rfl

theorem adjugate_identity (u : E → E) (p : E) (t : ℝ) (v : E) :
    jacobian u p t (adjugate u p t v)=determinant u p t • v := by
  let J := jacobian u p t
  let m : Matrix (Fin d) (Fin d) ℝ := toMatrix d J
  have hj : Matrix.toLin B B m=J.toLinearMap := by dsimp only [m]; rw [toMatrix_eq,Matrix.toLin_toMatrix]
  change J (fromMatrix d m.adjugate v)=m.det • v
  rw [fromMatrix_apply]
  calc
    _ = Matrix.toLin B B m (Matrix.toLin B B m.adjugate v) := by rw [hj]; rfl
    _ = Matrix.toLin B B (m*m.adjugate) v := by rw [Matrix.toLin_mul B B B]; rfl
    _ = m.det • v := by rw [Matrix.mul_adjugate,map_smul,LinearMap.smul_apply,Matrix.toLin_one,LinearMap.id_apply]

theorem hasFDerivAt_chart {W : Set E} (hW : IsOpen W) {u : E → E} (hu : ContDiffOn ℝ ∞ u W) {p : E} (hp : p ∈ W) (t : ℝ) :
    HasFDerivAt (fun y ↦ y+t • u y) (jacobian u p t) p :=
  (hasFDerivAt_id p).add (((hu.contDiffAt (hW.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt.const_smul t)

theorem determinant_zero_time (u : E → E) (p : E) : determinant u p 0=1 := by
  have he : jacobian u p 0=ContinuousLinearMap.id ℝ E := by
    ext v : 1
    change v+(0:ℝ) • (fderiv ℝ u p v)=v
    rw [zero_smul,add_zero]
  rw [determinant,he,toMatrix_eq]
  change Matrix.det (LinearMap.toMatrix B B LinearMap.id)=1
  rw [LinearMap.toMatrix_id,Matrix.det_one]

theorem regular {u : E → E} {p : E} {t : ℝ} (h : determinant u p t≠0) : (jacobian u p t).IsInvertible := by
  let J := jacobian u p t
  have hd : J.det≠0 := by simpa only [determinant,toMatrix_eq,LinearMap.det_toMatrix] using h
  exact ⟨J.toContinuousLinearEquivOfDetNeZero hd,J.coe_toContinuousLinearEquivOfDetNeZero hd⟩

theorem determinant_polynomial (u : E → E) (p : E) :
    ∃ P : ℝ[X], P.eval 0=1 ∧ ∀ t, P.eval t=determinant u p t := by
  let N : Matrix (Fin d) (Fin d) ℝ := toMatrix d (fderiv ℝ u p)
  let m : Matrix (Fin d) (Fin d) ℝ[X] := fun i j ↦ C ((1 : Matrix (Fin d) (Fin d) ℝ) i j)+X*C (N i j)
  have he (t : ℝ) : m.map (evalRingHom t)=toMatrix d (jacobian u p t) := by
    rw [jacobian,map_add,map_smul]
    have hid : toMatrix d (ContinuousLinearMap.id ℝ E)=(1 : Matrix (Fin d) (Fin d) ℝ) := by
      rw [toMatrix_eq]; exact LinearMap.toMatrix_id B
    rw [hid]
    ext i j
    change (C ((1 : M) i j)+X*C (N i j)).eval t=(1 : M) i j+t*(N i j)
    simp only [eval_add,eval_C,eval_mul,eval_X]
  have hs (t : ℝ) : m.det.eval t=determinant u p t := by
    change (evalRingHom t) m.det=_
    rw [RingHom.map_det,show (evalRingHom t).mapMatrix m=m.map (evalRingHom t) from rfl,he]; rfl
  exact ⟨m.det,(hs 0).trans (determinant_zero_time u p),hs⟩

end EuclideanMidpointRigidity.JacobianPencil

