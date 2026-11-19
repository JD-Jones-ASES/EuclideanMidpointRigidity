module

public import EuclideanMidpointRigidity.CriticalSection
public import EuclideanMidpointRigidity.SmoothPolynomialFamily

/-! # Polynomial coordinates for the spherical critical-point equation -/

@[expose] public section
noncomputable section
open Set
open scoped ContDiff InnerProductSpace
namespace EuclideanMidpointRigidity
open SmoothPolynomial

variable {d : ℕ}
local notation "E" => Space d
local notation "B" => EuclideanSpace.basisFun (Fin d) ℝ
local notation "Coeff" => Cubic d

set_option backward.isDefEq.respectTransparency false in
theorem contDiffOn_cubic_entry {W : Set E} {C : E → Coeff} (hc : ContDiffOn ℝ ∞ C W) (u v w : E) :
    ContDiffOn ℝ ∞ (fun p ↦ ⟪K (C p) u v,w⟫_ℝ) W := by
  let inc : Coeff →L[ℝ] (E →L[ℝ] E →L[ℝ] E) := (cubicSubspace d).subtypeL
  have hinc := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) («E» := Coeff)
    (F := E →L[ℝ] E →L[ℝ] E) inc
  have hi : ContDiffOn ℝ ∞ (inc ∘ C) W := ContDiff.comp_contDiffOn
    («E» := E) (F := Coeff) (G := E →L[ℝ] E →L[ℝ] E) hinc hc
  exact ((hi.clm_apply contDiffOn_const).clm_apply contDiffOn_const).inner ℝ contDiffOn_const

def cubicCoordinate {W : Set E} {C : E → Coeff} (hc : ContDiffOn ℝ ∞ C W) (i j k : Fin d) :
    SmoothCoefficient W := ⟨_,contDiffOn_cubic_entry hc (B i) (B j) (B k)⟩

theorem expand_cubic (c : Coeff) (v : E) :
    ⟪K c v v,v⟫_ℝ = ∑ i, ∑ j, ∑ k, ⟪K c (B i) (B j),B k⟫_ℝ * v i * v j * v k := by
  have hv : ∑ i, v i • B i=v := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v
  have flip (i j k : Fin d) : ⟪K c (B k) (B j),B i⟫_ℝ=⟪K c (B i) (B j),B k⟫_ℝ := by
    rw [K_symm c (B k) (B j),K_selfAdjoint,real_inner_comm,K_symm c (B j) (B i)]
  calc
    _ = ⟪K c (∑ i, v i • B i) (∑ j, v j • B j),∑ k, v k • B k⟫_ℝ := by rw [hv]
    _ = _ := by
      simp only [K,map_sum,map_smul,sum_apply,smul_apply,
        sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,Finset.mul_sum]
      simp only [mul_comm,mul_left_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [show ⟪c.val (B k) (B j),B i⟫_ℝ=⟪c.val (B i) (B j),B k⟫_ℝ from flip i j k]

/-- The multiplier occupies coordinate zero and the direction occupies the remaining coordinates. -/
def sphericalLagrangian {W : Set E} {C : E → Coeff} (hc : ContDiffOn ℝ ∞ C W) :
    MvPolynomial (Fin (d+1)) (SmoothCoefficient W) :=
  (∑ i, ∑ j, ∑ k, MvPolynomial.C (cubicCoordinate hc i j k) *
    MvPolynomial.X i.succ * MvPolynomial.X j.succ * MvPolynomial.X k.succ) -
  MvPolynomial.X 0 * ((∑ i : Fin d, MvPolynomial.X i.succ ^ 2)-1)

def sphericalCoordinates (z : Fin (d+1) → ℝ) : E := WithLp.toLp 2 (fun i ↦ z i.succ)

theorem eval_sphericalLagrangian {W : Set E} {C : E → Coeff} (hc : ContDiffOn ℝ ∞ C W) (p : E)
    (z : Fin (d+1) → ℝ) :
    MvPolynomial.eval z (specialize (sphericalLagrangian hc) p) =
    ⟪K (C p) (sphericalCoordinates z) (sphericalCoordinates z),sphericalCoordinates z⟫_ℝ -
      z 0*(‖sphericalCoordinates z‖^2-1) := by
  rw [expand_cubic,EuclideanSpace.real_norm_sq_eq]
  simp [sphericalLagrangian,specialize,cubicCoordinate,evaluateCoefficient,sphericalCoordinates]

end EuclideanMidpointRigidity

