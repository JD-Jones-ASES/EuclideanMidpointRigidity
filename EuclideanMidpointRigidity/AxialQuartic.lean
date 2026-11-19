module

public import EuclideanMidpointRigidity.QuarticHighRows
public import EuclideanMidpointRigidity.WeightedRulings

/-! # Recovering all transverse entries of the axial derivative from first tilts -/

public section
noncomputable section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity
open Quartic
variable {d : ℕ}
local notation "E" => Space d

private theorem axial_quartic_pair {C : Cubic d} {J : E →L[ℝ] Cubic d} {u x y z : E} {a b c : ℝ}
    (h₄ : ∀ v, obstruction C J v=0) (hu : K C u u=u)
    (hJ : ∀ v, K (J v) u u=0) (hU : ∀ v, K (J u) u v=0)
    (hx : K C u x=a • x) (hy : K C u y=b • y) (hz : K C u z=c • z) :
    (4*c+10-8*a-8*b)*jetEntry J u x y z+
    (4*c+20*a-8*b-4)*jetEntry J x u y z+(4*c+20*b-8*a-4)*jetEntry J y u x z=0 := by
  have h := row211_zero h₄ z u x y
  have trans (v : E) : ⟪K C u v,z⟫_ℝ=c*⟪v,z⟫_ℝ := by rw [K_selfAdjoint,hz,real_inner_smul_right]
  have hz₀ (v : E) : K C v 0=0 := map_zero _
  simp only [row211,term,K_symm C x u,K_symm C y u,hu,hx,hy,trans,map_smul,K_smul_coeff,K_smul_right,
    K_symm (J u) y u,K_symm (J u) x u,K_symm (J x) y u,K_symm (J y) x u,K_symm (J u) y x,
    hU,hJ,hz₀,inner_zero_left,real_inner_smul_left,mul_zero,zero_mul,add_zero,zero_add,sub_zero] at h
  dsimp only [jetEntry,cubicEntry]
  linarith only [h]

theorem axial_quartic_recovery {C : Cubic d} {J : E →L[ℝ] Cubic d} {u x y z : E} {a b c : ℝ}
    (h₄ : ∀ v, obstruction C J v=0) (hu : K C u u=u)
    (hJ : ∀ v, K (J v) u u=0) (hU : ∀ v, K (J u) u v=0)
    (hx : K C u x=a • x) (hy : K C u y=b • y) (hz : K C u z=c • z) :
    3*(5-2*(a+b+c))*jetEntry J u x y z+
      (20*a-2*b-2*c-4)*jetEntry J x u y z+
      (20*b-2*c-2*a-4)*jetEntry J y u z x+
      (20*c-2*a-2*b-4)*jetEntry J z u x y=0 := by
  have h₁ := axial_quartic_pair h₄ hu hJ hU hx hy hz
  have h₂ := axial_quartic_pair h₄ hu hJ hU hy hz hx
  have h₃ := axial_quartic_pair h₄ hu hJ hU hz hx hy
  have cyc (l i j k : E) : jetEntry J l j k i=jetEntry J l i j k := by
    rw [jetEntry_swap₂ J l j k i,jetEntry_swap₁ J l j i k]
  rw [cyc u x y z] at h₂
  rw [← cyc u z x y] at h₃
  rw [jetEntry_swap₂ J y u x z] at h₁
  rw [jetEntry_swap₂ J z u y x] at h₂
  rw [jetEntry_swap₂ J x u z y] at h₃
  linarith only [h₁,h₂,h₃]

end EuclideanMidpointRigidity

