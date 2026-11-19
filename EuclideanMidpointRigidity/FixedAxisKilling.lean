module

public import EuclideanMidpointRigidity.FixedAxisRows
public import EuclideanMidpointRigidity.TrilinearWeights

/-! # The Killing equation and the exceptional diagonal weight of the axial slice -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity.FixedAxis
open Quartic
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d

def entryForm (J : E →L[ℝ] T) (u : E) : RealTrilinear E where
  toFun l := LinearMap.mk₂ ℝ (entry J u l)
    (by intros; simp [entry,K_add_right,inner_add_left])
    (by intros; simp [entry,K_smul_right,real_inner_smul_left])
    (by intros; simp [entry,inner_add_right])
    (by intros; simp [entry,real_inner_smul_right])
  map_add' x y := by ext v w; simp only [LinearMap.mk₂_apply,entry,map_add,K_add_coeff,inner_add_left,LinearMap.add_apply]
  map_smul' r x := by ext v w; simp only [LinearMap.mk₂_apply,entry,map_smul,K_smul_coeff,real_inner_smul_left,LinearMap.smul_apply,smul_eq_mul,RingHom.id_apply]

structure SliceFrame (c : T) (u : E) where
  n : ℕ
  basis : OrthonormalBasis (Unit ⊕ Fin n) ℝ E
  eigenvalue : Unit ⊕ Fin n → ℝ
  eigen : ∀ i, K c u (basis i)=eigenvalue i • basis i
  bound : ∀ i, eigenvalue i≤1

theorem diagonal_identities {c : T} {J : E →L[ℝ] T} {u : E} (F : SliceFrame c u)
    (hE : ∀ v, obstruction c J v=0) (hu : K c u u=u) (hJ : ∀ l, K (J l) u u=0) (hU : J u=0) (v : E) :
    entry J u v v v=0 ∧ entry J u (K c u v) v v=0 := by
  let B := (c.val u).toLinearMap
  let A := entryForm J u
  have h (w : E) : 5*(A (B w) w w+A w (B w) w+A w w (B w))=23*A w w w := by
    change 5*(entry J u (K c u w) w w+entry J u w (K c u w) w+entry J u w w (K c u w))=23*entry J u w w w
    rw [entry_swap J u w (K c u w) w]
    obtain ⟨h₁,h₂⟩ := scalar_rows hE hu hJ hU w
    linarith only [h₁,h₂]
  have hp : entry J u v v v=0 := RealTrilinear.diagonal_zero F.basis.toBasis B F.eigenvalue F.eigen F.bound A h v
  obtain ⟨h₁,h₂⟩ := scalar_rows hE hu hJ hU v
  exact ⟨hp,by linarith only [h₁,h₂,hp]⟩

private theorem repeated_row {c : T} {J : E →L[ℝ] T} {u x y : E} {b s : ℝ}
    (hE : ∀ v, obstruction c J v=0) (hu : K c u u=u) (hJ : ∀ l, K (J l) u u=0) (hU : J u=0)
    (hx : K c u x=b • x) (hy : K c u y=s • y) :
    (4*s+12*b-4)*entry J u x x y=0 := by
  have h := row22_zero hE y u x
  have hK (v w : E) : K (0:T) v w=0 := rfl
  have h₀ (w : E) : K c w 0=0 := map_zero _
  have he (w : E) : ⟪K c u w,y⟫_ℝ=s*⟪w,y⟫_ℝ := by rw [K_selfAdjoint,hy,real_inner_smul_right]
  simp only [row22,term,K_symm c x u,hu,hJ,hU,hK,h₀,he,hx,map_smul,K_smul_coeff,K_smul_right,K_symm (J x) x u,
    inner_zero_left,real_inner_smul_left,mul_zero,add_zero,zero_add,sub_zero] at h
  dsimp only [entry]
  linarith only [h]

theorem weighted_diagonal {c : T} {J : E →L[ℝ] T} {u : E} (F : SliceFrame c u)
    (hE : ∀ v, obstruction c J v=0) (hu : K c u u=u) (hJ : ∀ l, K (J l) u u=0) (hU : J u=0)
    {x y : E} {b s : ℝ} (hx : K c u x=b • x) (hy : K c u y=s • y) :
    (1/2-2*b)*entry J u y x x=0 := by
  let A := entryForm J u
  let B := (c.val u).toLinearMap
  have h₁ (v : E) : A v v v=0 := (diagonal_identities F hE hu hJ hU v).1
  have h₂ (v : E) : A (B v) v v=0 := (diagonal_identities F hE hu hJ hU v).2
  have he₁ : B x=b • x := hx
  have he₂ : B y=s • y := hy
  have hswap : A x y x=A x x y := entry_swap J u x y x
  have ht : 2*A x x y+A y x x=0 := by
    have hp := h₁ (x+y)
    have hm := h₁ (x-y)
    simp only [map_add,map_sub,LinearMap.add_apply,LinearMap.sub_apply,h₁,hswap] at hp hm
    linarith only [hp,hm]
  have hs : 2*b*A x x y+s*A y x x=0 := by
    have hp := h₂ (x+y)
    have hm := h₂ (x-y)
    simp only [map_add,map_sub,he₁,he₂,map_smul,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul,h₁,hswap] at hp hm
    linarith only [hp,hm]
  have hdiff : (s-b)*A y x x=0 := by linear_combination hs-b*ht
  by_cases he : s=b
  · subst s
    have hr : (4*b+12*b-4)*A x x y=0 := repeated_row hE hu hJ hU hx hy
    change (1/2-2*b)*A y x x=0
    linear_combination (1/2-2*b)*ht+hr/4
  · change (1/2-2*b)*A y x x=0
    rw [(mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr he),mul_zero]

end EuclideanMidpointRigidity.FixedAxis

