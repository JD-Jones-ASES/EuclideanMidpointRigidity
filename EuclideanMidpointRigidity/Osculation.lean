module

public import EuclideanMidpointRigidity.DiagonalCurvature
public import EuclideanMidpointRigidity.HigherOsculation

/-! # Spatial inactivity of every derivative of the maximizing section -/

public section
noncomputable section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity.HorizontalPatch
open FixedAxis Quartic
variable {d : ℕ} {S : LiftedSection d} (H : HorizontalPatch S)
local notation "E" => Space d
set_option backward.isDefEq.respectTransparency false

include H in
private theorem polarized_curvature {p : E} (hp : p ∈ S.domain) (a : E) {x y z w : E} {b : ℝ}
    (hr : Resonant b) (hx : K (S.field p) (S.idempotent p) x=b • x) (hy : K (S.field p) (S.idempotent p) y=b • y)
    (hz : K (S.field p) (S.idempotent p) z=(2*b) • z) (hw : K (S.field p) (S.idempotent p) w=b • w) :
    (H.freeze hp [] H.inactive_one).component a x y z w=0 := by
  let P := H.freeze hp [] H.inactive_one
  let B := (S.field p).val (S.idempotent p)
  let f := fun i j k : E ↦ P.component a i j z k
  have sym (i j k : E) : f i j k=f i k j := by
    dsimp only [f]
    rw [P.swap_inner₁ a i j z k,P.swap_inner₂ a i z j k,P.swap_inner₁ a i z k j]
  have skew (i j k : E) (hi : B i=b • i) (hj : B j=b • j) (hk : B k=b • k) : f i j k+f j i k=0 := by
    have he : B (i+j)=b • (i+j) := by rw [map_add,hi,hj,smul_add]
    have h := H.diagonal_curvature hp a hr he hz hk
    have h₁ := H.diagonal_curvature hp a hr hi hz hk
    have h₂ := H.diagonal_curvature hp a hr hj hz hk
    change P.component a (i+j) (i+j) z k=0 at h
    simp only [f,FrozenPair.component,jetEntry,cubicEntry,map_add,K_add_coeff,K_add_left,inner_add_left] at h h₁ h₂ ⊢
    linarith only [h,h₁,h₂]
  have h₁ := skew x y w hx hy hw
  have h₂ := skew y w x hy hw hx
  have h₃ := skew w x y hw hx hy
  change f x y w=0
  simp only [sym] at h₁ h₂ h₃ ⊢
  linarith only [h₁,h₂,h₃]

include H in
theorem inactive_two : InactiveThrough S 2 := by
  intro xs hx p hp
  match xs with
  | [] => exact H.inactive_one [] (by simp) p hp
  | [a] => exact H.inactive_one [a] (by simp) p hp
  | [a,l] =>
    let P := H.freeze hp [] H.inactive_one
    let F := (S.idempotent_frame hp (H.maximizes p hp)).some
    have hframe (i j) : P.jet (F.basis i) (F.basis j)=0 := by
      apply cubic_zero_of_frame F.basis
      intro x y z
      rw [entryFunctional_eq]
      change P.component (F.basis i) (F.basis j) (F.basis x) (F.basis y) (F.basis z)=0
      by_contra hn
      obtain ⟨hr,_,hs⟩ := P.classification F (S.idempotent_square hp) (F.eigen i) (F.eigen j)
        (F.eigen x) (F.eigen y) (F.eigen z) hn
      apply hn
      rcases hs with ⟨ex,ey,ez⟩|⟨ex,ez,ey⟩|⟨ey,ez,ex⟩
      · rw [P.swap_inner₂]
        exact H.polarized_curvature hp _ hr (F.eigen j) (ex ▸ F.eigen x) (ez ▸ F.eigen z) (ey ▸ F.eigen y)
      · exact H.polarized_curvature hp _ hr (F.eigen j) (ex ▸ F.eigen x) (ey ▸ F.eigen y) (ez ▸ F.eigen z)
      · rw [P.swap_inner₁]
        exact H.polarized_curvature hp _ hr (F.eigen j) (ey ▸ F.eigen y) (ex ▸ F.eigen x) (ez ▸ F.eigen z)
    have extend (x : E) (he : ∀ i, P.jet x (F.basis i)=0) (y : E) : P.jet x y=0 := by
      have h : (P.jet x).toLinearMap=0 := F.basis.toBasis.ext he
      exact DFunLike.congr_fun h y
    rw [← higherJet_apply hp []]
    change P.jet a l=0
    apply extend
    intro i
    rw [P.exchange]
    exact extend _ (hframe i) a
  | _::_::_::_ => simp only [List.length_cons] at hx; omega

include H in
theorem osculation {p : E} (hp : p ∈ S.domain) (xs : List E) :
    fderiv ℝ S.field p (directions S.axis xs p)=0 :=
  H.all_inactive H.inactive_two xs.length xs le_rfl p hp

end EuclideanMidpointRigidity.HorizontalPatch

