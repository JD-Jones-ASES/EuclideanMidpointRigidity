module

public import EuclideanMidpointRigidity.OsculatingSupport
public import EuclideanMidpointRigidity.CurvatureWeights

/-! # Freezing the first possibly active spatial derivative of a horizontal maximizing direction -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d

theorem inactive_exchange {W : Set E} {C : E → T} {b : E → E} (hW : IsOpen W)
    (hC : ContDiffOn ℝ ∞ C W) (hb : ContDiffOn ℝ ∞ b W) (hI : ∀ q ∈ W, fderiv ℝ C q (b q)=0)
    {p : E} (hp : p ∈ W) :
    fderiv ℝ (fderiv ℝ C) p (b p)= -(fderiv ℝ C p).comp (fderiv ℝ b p) := by
  let J := fderiv ℝ C
  have hc := hC.contDiffAt (hW.mem_nhds hp)
  have hJ : DifferentiableAt ℝ J p := (hc.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hg : (fun y ↦ J y (b y)) =ᶠ[𝓝 p] (fun _ ↦ 0) :=
    (show ∀ᶠ q in 𝓝 p, q ∈ W from hW.mem_nhds hp).mono hI
  have hz : fderiv ℝ (fun y ↦ J y (b y)) p=0 := hg.fderiv_eq.trans (hasFDerivAt_const (0:T) p).fderiv
  ext v : 1
  have h := directions.directional_apply hJ ((hb.contDiffAt (hW.mem_nhds hp)).differentiableAt (by simp)) v
  rw [directional,hz,zero_apply] at h
  change 0=(fderiv ℝ J p v) (b p)+J p (fderiv ℝ b p v) at h
  rw [(hc.isSymmSndFDerivAt (by simp)) (b p) v]
  exact eq_neg_of_add_eq_zero_left h.symm

theorem inactive_quartic {W : Set E} {C : E → T} {b : E → E} (hW : IsOpen W)
    (hC : ContDiffOn ℝ ∞ C W) (hb : ContDiffOn ℝ ∞ b W) (hQ : QuarticOn W C)
    (hI : ∀ q ∈ W, fderiv ℝ C q (b q)=0) {p : E} (hp : p ∈ W) (v : E) :
    obstruction (C p) ((fderiv ℝ C p).comp (fderiv ℝ b p)) v=0 := by
  have hh := prolongation_of_quartic hW (hC.of_le (by simp)) hQ hp (b p) v
  rw [inactive_exchange hW hC hb hI hp,hI p hp] at hh
  have hz (J : E →L[ℝ] T) : obstruction (0:T) J v=0 := by simp [obstruction,K]
  have hn (J : E →L[ℝ] T) : obstruction (C p) (-J) v= -obstruction (C p) J v := by
    simp only [obstruction,neg_apply,K_neg_coeff,K_neg_right]; module
  simpa only [hz,hn,add_zero,neg_eq_zero] using hh

namespace HorizontalPatch
variable {S : LiftedSection d} (H : HorizontalPatch S)

def higherJet (S : LiftedSection d) (p : E) (xs : List E) (a : E) : E →L[ℝ] T :=
  (fderiv ℝ S.field p).comp (fderiv ℝ (fderiv ℝ (directions S.axis xs)) p a)

theorem higherJet_apply {p : E} (hp : p ∈ S.domain) (xs : List E) (a l : E) :
    higherJet S p xs a l=fderiv ℝ S.field p (directions S.axis (a::l::xs) p) := by
  rw [directions.two S.isOpen S.smoothAxis hp]; rfl

include H in
def freeze {p : E} (hp : p ∈ S.domain) (xs : List E) (hI : InactiveThrough S (xs.length+1)) :
    FixedAxis.FrozenPair (S.field p) (S.idempotent p) where
  jet := higherJet S p xs
  exchange a l := by
    rw [higherJet_apply hp,higherJet_apply hp,directions.perm S.isOpen S.smoothAxis (List.Perm.swap l a xs) hp]
  quartic a v := by
    let g := directions S.axis xs
    let b := directional g a
    have hb : ContDiffOn ℝ ∞ b S.domain := directions.smooth S.isOpen S.smoothAxis (a::xs)
    have hi (q : E) (hq : q ∈ S.domain) : fderiv ℝ S.field q (b q)=0 := hI (a::xs) (by simp) q hq
    have eqn : (fderiv ℝ S.field p).comp (fderiv ℝ b p)=higherJet S p xs a := by
      ext v : 1
      rw [higherJet_apply hp]
      change fderiv ℝ S.field p (directions S.axis (v::a::xs) p)=_
      rw [directions.perm S.isOpen S.smoothAxis (List.Perm.swap a v xs) hp]
    rw [← eqn]; exact inactive_quartic S.isOpen S.smooth hb S.equations.quartic hi hp v
  doubleAxis a l := by
    rw [higherJet_apply hp,LiftedSection.idempotent,K_smul_left,K_smul_right,(S.weighted_ruling hp H.maximizes).1,smul_zero,smul_zero]
  support := by
    intro l b he hn a
    rw [higherJet_apply hp]
    have hperm : (l::xs).Perm (xs++[l]) := by
      simpa only [List.append_nil] using (List.perm_middle (a := l) (l₁ := xs) (l₂ := [])).symm
    rw [directions.perm S.isOpen S.smoothAxis (hperm.cons a) hp]
    exact H.osculating_support hp (a::xs) hI he hn

end HorizontalPatch
end EuclideanMidpointRigidity

