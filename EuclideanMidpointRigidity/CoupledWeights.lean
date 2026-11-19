module

public import EuclideanMidpointRigidity.TrilinearWeights

/-! # Four eigenvalue labels in the fixed-factor quartic equation -/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity.FixedAxis
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def mixedWeight (a b c d x y z : ℝ) :=
  (4*d+20*a-8*b-8*c)*x+(4*d+20*b-8*c-8*a)*y+(4*d+20*c-8*a-8*b)*z

set_option maxHeartbeats 1600000 in
theorem polar_weight (A : RealTrilinear E) (B : E →ₗ[ℝ] E) (d : ℝ)
    (hs : ∀ l i j, A l i j=A l j i)
    (h : ∀ v, 2*d*A v v v+10*A (B v) v v-8*A v v (B v)=0)
    {x y z : E} {a b c : ℝ} (hx : B x=a • x) (hy : B y=b • y) (hz : B z=c • z) :
    mixedWeight a b c d (A x y z) (A y x z) (A z x y)=0 := by
  let f := fun v ↦ 2*d*A v v v+10*A (B v) v v-8*A v v (B v)
  have he : mixedWeight a b c d (A x y z) (A y x z) (A z x y)=
      f (x+y+z)-f (x+y)-f (x+z)-f (y+z)+f x+f y+f z := by
    simp only [f,mixedWeight,map_add,LinearMap.add_apply,add_apply,hx,hy,hz,
      map_smul,LinearMap.smul_apply,smul_apply,smul_eq_mul,hs]
    ring
  simpa only [f,h,sub_self,add_zero] using he

private theorem single_weight {a b c d x y z w : ℝ}
    (h : mixedWeight a b c d x y z=0) (hW : a*x+b*y+c*z+d*w=0)
    (hL : a+b+c+d=0) (hz : d=0 → w=0) :
    10*w=if d=0 then 0 else 3*(x+y+z+w) := by
  split_ifs with hd
  · rw [hz hd,mul_zero]
  · have eqn : d*(10*w-3*(x+y+z+w))=0 := by
      dsimp only [mixedWeight] at h
      linear_combination (-h+28*hW-8*(x+y+z)*hL)/4
    exact sub_eq_zero.mp ((mul_eq_zero.mp eqn).resolve_left hd)

theorem four_weights {a b c d x y z w : ℝ}
    (h₁ : mixedWeight a b c d x y z=0) (h₂ : mixedWeight b c d a y z w=0)
    (h₃ : mixedWeight c d a b z w x=0) (h₄ : mixedWeight d a b c w x y=0)
    (hW : a*x+b*y+c*z+d*w=0)
    (hx : a=0 → x=0) (hy : b=0 → y=0) (hz : c=0 → z=0) (hw : d=0 → w=0) :
    x+y+z+w=0 := by
  by_contra hs
  have hprod : (a+b+c+d)*(x+y+z+w)=0 := by
    dsimp only [mixedWeight] at h₁ h₂ h₃ h₄
    linear_combination 6*hW-(h₁+h₂+h₃+h₄)/12
  have hL := (mul_eq_zero.mp hprod).resolve_right hs
  have e₁ := single_weight h₁ hW hL hw
  have e₂ := single_weight h₂ (by linarith only [hW]) (by linarith only [hL]) hx
  have e₃ := single_weight h₃ (by linarith only [hW]) (by linarith only [hL]) hy
  have e₄ := single_weight h₄ (by linarith only [hW]) (by linarith only [hL]) hz
  apply hs
  split_ifs at e₁ e₂ e₃ e₄ <;> linarith only [e₁,e₂,e₃,e₄]

end EuclideanMidpointRigidity.FixedAxis

