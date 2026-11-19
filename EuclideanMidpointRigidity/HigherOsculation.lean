module

public import EuclideanMidpointRigidity.FrozenField
public import EuclideanMidpointRigidity.ThirdFrozenJet

/-! # Inactivity of the second derivative implies inactivity of every higher derivative -/

public section
noncomputable section
namespace EuclideanMidpointRigidity.HorizontalPatch
variable {d : ℕ} {S : LiftedSection d} (H : HorizontalPatch S)
local notation "E" => Space d

include H in
theorem inactive_triple {p : E} (hp : p ∈ S.domain) (xs : List E) (hI : InactiveThrough S (xs.length+2)) (a b l : E) :
    fderiv ℝ S.field p (directions S.axis (a::b::l::xs) p)=0 := by
  let c := S.field p
  let u := S.idempotent p
  let F := (S.idempotent_frame hp (H.maximizes p hp)).some
  let P := fun v : E ↦ H.freeze hp (v::xs) hI
  have hP (a b l : E) : (P a).jet b l=fderiv ℝ S.field p (directions S.axis (a::b::l::xs) p) := by
    change higherJet S p (a::xs) b l=_
    rw [higherJet_apply hp]
    apply congrArg
    apply directions.perm S.isOpen S.smoothAxis _ hp
    exact ((List.Perm.swap a l xs).cons b).trans (List.Perm.swap a b (l::xs))
  have he (a b l : E) : (P a).jet b l=(P b).jet a l := by
    rw [hP,hP,directions.perm S.isOpen S.smoothAxis (List.Perm.swap b a (l::xs)) hp]
  have hframe (i j k) : (P (F.basis i)).jet (F.basis j) (F.basis k)=0 := by
    apply cubic_zero_of_frame F.basis
    intro m n t
    rw [entryFunctional_eq]
    exact FixedAxis.third_frozen_zero F (S.idempotent_square hp) P he (F.eigen i) (F.eigen j)
      (F.eigen k) (F.eigen m) (F.eigen n) (F.eigen t)
  have extend (x y : E) (hh : ∀ i, (P x).jet y (F.basis i)=0) (z : E) : (P x).jet y z=0 := by
    have h : ((P x).jet y).toLinearMap=0 := F.basis.toBasis.ext hh
    exact DFunLike.congr_fun h z
  have h₂ (i) (y z : E) : (P (F.basis i)).jet y z=0 := by
    rw [(P (F.basis i)).exchange y z]
    apply extend
    intro j
    rw [(P (F.basis i)).exchange z (F.basis j)]
    exact extend _ _ (hframe i j) z
  rw [← hP,he a b l,(P b).exchange a l]
  apply extend
  intro i
  rw [(P b).exchange l (F.basis i),he b (F.basis i) l]
  exact h₂ i b l

include H in
theorem all_inactive (h₂ : InactiveThrough S 2) (n : ℕ) : InactiveThrough S n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro xs hx p hp
    match xs with
    | [] => exact h₂ [] (by simp) p hp
    | [v] => exact h₂ [v] (by simp) p hp
    | [v,w] => exact h₂ [v,w] (by simp) p hp
    | a::b::l::ys =>
      have ht : ys.length+2<n := by simp only [List.length_cons] at hx; omega
      exact H.inactive_triple hp ys (ih _ ht) a b l

end EuclideanMidpointRigidity.HorizontalPatch

