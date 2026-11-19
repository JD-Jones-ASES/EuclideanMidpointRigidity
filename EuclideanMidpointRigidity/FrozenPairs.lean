module

public import EuclideanMidpointRigidity.FixedAxisKilling

/-! # The first axial slot of a frozen symmetric pair of spatial derivatives -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity.FixedAxis
open Quartic
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d

def Resonant (b : ℝ) := b= -1/2 ∨ b=1/5

structure FrozenPair (c : Cubic d) (u : Space d) where
  jet : E → E →L[ℝ] T
  exchange : ∀ a l, jet a l=jet l a
  quartic : ∀ a v, obstruction c (jet a) v=0
  doubleAxis : ∀ a l, K (jet a l) u u=0
  support : ∀ {l : E} {b : ℝ}, K c u l=b • l → ¬ Resonant b → ∀ a, jet a l=0

namespace FrozenPair
variable {c : Cubic d} {u : Space d} (P : FrozenPair (d := d) c u)

def axial (a l x y : E) := entry (P.jet a) u l x y

theorem swap_source (a l x y : E) : P.axial a l x y=P.axial l a x y := by
  unfold axial entry; rw [P.exchange a l]

theorem swap_target (a l x y : E) : P.axial a l x y=P.axial a l y x := entry_swap _ _ _ _ _

theorem axis_zero (hu : K c u u=u) (a : E) : P.jet a u=0 :=
  P.support (b := 1) (by simpa only [one_smul] using hu) (by norm_num [Resonant]) a

private theorem axis_sum (F : SliceFrame c u) (hu : K c u u=u) (a x y z : E) :
    P.axial a x y z+P.axial a y x z+P.axial a z x y=0 := by
  let A := entryForm (P.jet a) u
  have h (v : E) : A v v v=0 := (diagonal_identities F (P.quartic a) hu (P.doubleAxis a) (P.axis_zero hu a) v).1
  have hs (i j k : E) : A i j k=A i k j := entry_swap _ _ _ _ _
  have h₁ := h (x+y+z)
  have h₂ := h (x+y)
  have h₃ := h (x+z)
  have h₄ := h (y+z)
  change A x y z+A y x z+A z x y=0
  simp only [map_add,LinearMap.add_apply,hs] at h₁ h₂ h₃ h₄ ⊢
  linarith only [h₁,h₂,h₃,h₄,h x,h y,h z]

theorem opposite (F : SliceFrame c u) (hu : K c u u=u) (a b i j : E) :
    P.axial a b i j=P.axial i j a b := by
  have h₁ := P.axis_sum F hu a b i j
  have h₂ := P.axis_sum F hu b a i j
  have h₃ := P.axis_sum F hu i j a b
  have h₄ := P.axis_sum F hu j i a b
  simp only [swap_source,swap_target] at h₁ h₂ h₃ h₄ ⊢
  linarith only [h₁,h₂,h₃,h₄]

private theorem eigen_pair (hu : K c u u=u) (l : E) {x y z : E} {a b s : ℝ}
    (hx : K c u x=a • x) (hy : K c u y=b • y) (hz : K c u z=s • z) :
    (4*s+20*a-8*b-4)*P.axial l x y z+(4*s+20*b-8*a-4)*P.axial l y x z=0 := by
  let J := P.jet l
  have h := row211_zero (P.quartic l) z u x y
  have ht (v : E) : ⟪K c u v,z⟫_ℝ=s*⟪v,z⟫_ℝ := by rw [K_selfAdjoint,hz,real_inner_smul_right]
  have hK (x y : E) : K (0:T) x y=0 := rfl
  have h₀ (w : E) : K c w 0=0 := map_zero _
  simp only [row211,term,K_symm c x u,K_symm c y u,hu,hx,hy,ht,map_smul,K_smul_coeff,K_smul_right,
    P.axis_zero hu,P.doubleAxis,hK,h₀,K_symm (P.jet l x) y u,K_symm (P.jet l y) x u,
    inner_zero_left,real_inner_smul_left,mul_zero,zero_mul,add_zero,zero_add,sub_zero] at h
  dsimp only [axial,entry]
  linarith only [h]

theorem axial_eigen_zero (F : SliceFrame c u) (hu : K c u u=u) (l : E)
    {x y z : E} {a b s : ℝ} (hx : K c u x=a • x) (hy : K c u y=b • y) (hz : K c u z=s • z) :
    P.axial l x y z=0 := by
  by_cases ha : Resonant a
  · by_cases hb : Resonant b
    · by_cases ht : Resonant s
      · have h₁ := P.eigen_pair hu l hx hy hz
        have h₂ := P.eigen_pair hu l hy hz hx
        have h₃ := P.eigen_pair hu l hz hx hy
        rw [P.swap_target l y z x,P.swap_target l z y x] at h₂
        rw [P.swap_target l x z y] at h₃
        rcases ha with ha|ha <;> rcases hb with hb|hb <;> rcases ht with ht|ht <;>
          rw [ha,hb,ht] at h₁ h₂ h₃ <;> linarith only [h₁,h₂,h₃]
      · rw [P.opposite F hu]
        simp [axial,entry,P.support hz ht,K]
    · rw [P.opposite F hu,P.swap_source y z]
      simp [axial,entry,P.support hy hb,K]
  · simp [axial,entry,P.support hx ha,K]

theorem axial_zero (F : SliceFrame c u) (hu : K c u u=u) (l a x : E) : K (P.jet l a) u x=0 := by
  let A := entryForm (P.jet l) u
  have h : A=0 := by
    apply F.basis.toBasis.ext; intro i
    apply F.basis.toBasis.ext; intro j
    apply F.basis.toBasis.ext; intro k
    exact P.axial_eigen_zero F hu l (F.eigen i) (F.eigen j) (F.eigen k)
  apply ext_inner_right ℝ
  intro y
  rw [inner_zero_left]
  exact DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun h a) x) y

end FrozenPair
end EuclideanMidpointRigidity.FixedAxis

