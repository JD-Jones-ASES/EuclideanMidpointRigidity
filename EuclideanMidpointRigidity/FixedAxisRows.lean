module

public import EuclideanMidpointRigidity.AxialQuartic

/-! # The two scalar quartic rows of a fixed stationary axis -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity.FixedAxis
open Quartic
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d

def entry (J : E →L[ℝ] T) (u l x y : E) := ⟪K (J l) u x,y⟫_ℝ

theorem entry_swap (J : E →L[ℝ] T) (u l x y : E) : entry J u l x y=entry J u l y x :=
  jetEntry_swap₂ J l u x y

theorem inner_slot (c : T) (x y z : E) : ⟪K c x y,z⟫_ℝ=⟪K c z x,y⟫_ℝ :=
  (cubicEntry_swap₂ c x y z).trans (cubicEntry_swap₁ c x z y)

theorem scalar_rows {c : T} {J : E →L[ℝ] T} {u : E} (hE : ∀ v, obstruction c J v=0) (hu : K c u u=u)
    (hJ : ∀ l, K (J l) u u=0) (hU : J u=0) (v : E) :
    let B := K c u
    let A := entry J u
    2*A v v v-4*A v v (B v)+10*A (B v) v v=0 ∧
      -4*A v v v-4*A v v (B v)+20*A (B v) v v=0 := by
  let B := K c u
  let A := entry J u
  have hK (x y : E) : K (0:T) x y=0 := rfl
  have hR (l x y : E) : ⟪K (J l) x y,u⟫_ℝ=A l x y := inner_slot _ _ _ _
  have hA (l x : E) : A l u x=0 := by simp only [A,entry,hJ,inner_zero_left]
  have hv (w : E) : ⟪K c v w,u⟫_ℝ=⟪w,B v⟫_ℝ := by rw [K_selfAdjoint,K_symm c v u]
  have he (w : E) : ⟪K c u w,u⟫_ℝ=⟪w,u⟫_ℝ := by rw [K_selfAdjoint,hu]
  have hw (w : E) : ⟪K c u w,v⟫_ℝ=⟪w,B v⟫_ℝ := K_selfAdjoint _ _ _ _
  have htor (l x : E) : ⟪K (J l) u x,B v⟫_ℝ=A l x (B v) := rfl
  have htv (l x : E) : ⟪K (J l) u x,v⟫_ℝ=A l x v := rfl
  have h₀ (w : E) : K c w 0=0 := map_zero _
  have ha := row31_zero hE u v u
  have hb := row22_zero hE v u v
  simp only [row31,row22,term,K_symm c v u,hu,hU,hK,hJ,h₀,hv,he,hw,hR,htor,htv,hA,
    K_symm (J v) v u,inner_zero_left,mul_zero,zero_mul,add_zero,zero_add,sub_zero] at ha hb
  change 2*A v v v-4*A v v (B v)+10*A (B v) v v=0 ∧ -4*A v v v-4*A v v (B v)+20*A (B v) v v=0
  dsimp only [A,B,entry] at ha hb ⊢
  have hz (l : E) : ⟪K (J l) u v,u⟫_ℝ=0 := by rw [K_selfAdjoint,hJ,inner_zero_right]
  have hswap : ⟪K (J v) u (K c u v),v⟫_ℝ=⟪K (J v) u v,K c u v⟫_ℝ := jetEntry_swap₂ J v u _ _
  simp only [hz,K_symm (J (K c u v)) v u,hswap,mul_zero] at ha hb
  constructor <;> linarith only [ha,hb]

end EuclideanMidpointRigidity.FixedAxis

