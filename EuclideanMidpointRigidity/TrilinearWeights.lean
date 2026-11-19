module

public import EuclideanMidpointRigidity.Basic

/-! # A weighted identity for the diagonal of a real trilinear form -/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
abbrev RealTrilinear (E : Type*) [AddCommGroup E] [Module ℝ E] := E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ

namespace RealTrilinear

def six (A : RealTrilinear E) (x y z : E) :=
  A x y z+A x z y+A y x z+A y z x+A z x y+A z y x

def symmetrize (A : RealTrilinear E) : RealTrilinear E where
  toFun x := LinearMap.mk₂ ℝ (six A x)
    (by intros; simp only [six,map_add,LinearMap.add_apply,add_apply]; ring)
    (by intros; simp only [six,map_smul,LinearMap.smul_apply,smul_apply,smul_eq_mul]; ring)
    (by intros; simp only [six,map_add,LinearMap.add_apply,add_apply]; ring)
    (by intros; simp only [six,map_smul,LinearMap.smul_apply,smul_apply,smul_eq_mul]; ring)
  map_add' x y := by ext v w; simp only [LinearMap.mk₂_apply,six,map_add,LinearMap.add_apply,add_apply]; ring
  map_smul' r x := by ext v w; simp only [LinearMap.mk₂_apply,six,map_smul,LinearMap.smul_apply,smul_apply,smul_eq_mul,RingHom.id_apply]; ring

private def defect (A : RealTrilinear E) (B : E →ₗ[ℝ] E) (v : E) :=
  5*(A (B v) v v+A v (B v) v+A v v (B v))-23*A v v v

set_option maxHeartbeats 1600000 in
theorem six_zero {A : RealTrilinear E} {B : E →ₗ[ℝ] E}
    (h : ∀ v, 5*(A (B v) v v+A v (B v) v+A v v (B v))=23*A v v v)
    {x y z : E} {a b c : ℝ} (hx : B x=a • x) (hy : B y=b • y) (hz : B z=c • z)
    (hbound : a+b+c≤3) : six A x y z=0 := by
  let f := defect A B
  have hzero (v : E) : f v=0 := sub_eq_zero.mpr (h v)
  have hpolar : (5*(a+b+c)-23)*six A x y z=
      f (x+y+z)-f (x+y)-f (x+z)-f (y+z)+f x+f y+f z := by
    simp only [f,defect,six,map_add,LinearMap.add_apply,add_apply,hx,hy,hz,map_smul,LinearMap.smul_apply,smul_apply,smul_eq_mul]
    ring
  simp only [hzero,sub_self,add_zero] at hpolar
  exact (mul_eq_zero.mp hpolar).resolve_left (by linarith)

theorem diagonal_zero {ι : Type*} (B : Module.Basis ι ℝ E) (L : E →ₗ[ℝ] E) (b : ι → ℝ)
    (he : ∀ i, L (B i)=b i • B i) (hb : ∀ i, b i≤1) (A : RealTrilinear E)
    (h : ∀ v, 5*(A (L v) v v+A v (L v) v+A v v (L v))=23*A v v v) (v : E) : A v v v=0 := by
  have hz : symmetrize A=0 := by
    apply B.ext; intro i
    apply B.ext; intro j
    apply B.ext; intro k
    change six A (B i) (B j) (B k)=0
    exact six_zero h (he i) (he j) (he k) (by linarith [hb i,hb j,hb k])
  have hh : six A v v v=0 := DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun hz v) v) v
  dsimp only [six] at hh
  linarith

end RealTrilinear
end EuclideanMidpointRigidity

