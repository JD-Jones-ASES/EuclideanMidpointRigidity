module

public import EuclideanMidpointRigidity.FrameRates

/-! # Derivatives of the four cubic entries on the resonant plane -/

@[expose] public section
noncomputable section
open scoped Topology ContDiff InnerProductSpace
namespace EuclideanMidpointRigidity.LiftedSection
open Quartic
variable {d : ℕ} (S : LiftedSection d)
local notation "E" => Space d

theorem shape_rate {p : E} (hm : S.IsMixed p) {f g h : E → E}
    (df : DifferentiableAt ℝ f p) (dg : DifferentiableAt ℝ g p) (dh : DifferentiableAt ℝ h p) :
    let C := S.cubic p
    S.rate (S.shape f g h) p=jetEntry (S.jet p) (S.axis p) (f p) (g p) (h p)+
      cubicEntry C (g p) (h p) (S.rate f p)+cubicEntry C (f p) (h p) (S.rate g p)+
      cubicEntry C (f p) (g p) (S.rate h p) := by
  have h₀ := (S.shape_derivative hm df dg dh).deriv
  dsimp only
  change S.rate (S.shape f g h) p=_ at h₀
  simpa only [cubicEntry_swap₁,cubicEntry_swap₂] using h₀

namespace SpectralFrame
variable {S : LiftedSection d} {p : Space d}
variable {ι : Type*} [Fintype ι]
variable (B : SpectralFrame S p ι)

theorem contract_x (hm : S.IsMixed p) (z w : E) :
    let c := S.cubic p
    cubicEntry c z w (S.rate S.x p)= -(7/26)*cubicEntry c z w (S.axis p)-
      S.omega p*cubicEntry c z w (S.y p)+∑ i, cubicEntry c z w (B.w i)*(S.channel p (B.w i)).rot1 := by
  obtain ⟨xe,_,xx,_,xy,_⟩ := S.internal_rotations hm
  have h := B.contract_rate ((S.smooth_frame hm).2.2.1.differentiableAt (by simp)) z w
  dsimp only at h ⊢
  rw [xe,xx,xy,mul_zero,add_zero] at h
  change _=_+∑ i, cubicEntry _ z w (B.w i)*S.rotation p S.x (B.w i)
  linarith only [h]

theorem contract_y (hm : S.IsMixed p) (z w : E) :
    let c := S.cubic p
    cubicEntry c z w (S.rate S.y p)=S.omega p*cubicEntry c z w (S.x p)+
      ∑ i, cubicEntry c z w (B.w i)*((S.channel p (B.w i)).rot2/S.ratio p) := by
  obtain ⟨_,ye,_,yy,_,yx⟩ := S.internal_rotations hm
  have h := B.contract_rate ((S.smooth_frame hm).2.2.2.differentiableAt (by simp)) z w
  have ht : S.ratio p≠0 := (div_pos (norm_pos_iff.mpr hm.2.2) (norm_pos_iff.mpr hm.2.1)).ne'
  dsimp only at h ⊢
  rw [ye,yy,yx,mul_zero,mul_zero,zero_add,add_zero] at h
  simp only [channel,MixedChannel.ofJet,mul_div_cancel_left₀ _ ht]
  linarith only [h]

theorem shape_rates (hm : S.IsMixed p) :
    let A := S.core p
    let O := S.omega p
    let c := fun i ↦ S.channel p (B.w i)
    let t := S.ratio p
    S.rate (S.shape S.x S.x S.x) p=A.s111-3*O*A.m+3*(7/26)/2+
      ∑ i, 3*((c i).q*(c i).rot1) ∧
    S.rate (S.shape S.x S.x S.y) p=A.s112+O*(A.d1-2*A.n)+
      ∑ i, (2*(((c i).l/t)*(c i).rot1)+(c i).q*((c i).rot2/t)) ∧
    S.rate (S.shape S.x S.y S.y) p=A.s122+O*(2*A.m-A.d2)-(7/26)/5+
      ∑ i, (((c i).h/t^2)*(c i).rot1+2*(((c i).l/t)*((c i).rot2/t))) ∧
    S.rate (S.shape S.y S.y S.y) p=A.s222+3*O*A.n+
      ∑ i, 3*(((c i).h/t^2)*((c i).rot2/t)) := by
  let c := S.cubic p
  let x := S.x p
  let y := S.y p
  let e := S.axis p
  let P := S.core p
  let ch := fun i ↦ S.channel p (B.w i)
  have dx := (S.smooth_frame hm).2.2.1.differentiableAt (by simp)
  have dy := (S.smooth_frame hm).2.2.2.differentiableAt (by simp)
  have h₁ := S.shape_rate hm dx dx dx
  have h₂ := S.shape_rate hm dx dx dy
  have h₃ := S.shape_rate hm dx dy dy
  have h₄ := S.shape_rate hm dy dy dy
  dsimp only at h₁ h₂ h₃ h₄ ⊢
  simp only [B.contract_x hm,B.contract_y hm] at h₁ h₂ h₃ h₄
  have rotate (a b j : E) : cubicEntry c a b j=cubicEntry c j a b := by simp only [cubicEntry_swap₁,cubicEntry_swap₂]
  have lead := core_leading S hm
  have xx : cubicEntry c x x e= -1/2 := (rotate _ _ _).trans lead.exx
  have xy : cubicEntry c x y e=0 := (rotate _ _ _).trans lead.exy
  have yy : cubicEntry c y y e=1/5 := (rotate _ _ _).trans lead.eyy
  have xxy : cubicEntry c x y x=P.m := cubicEntry_swap₂ _ _ _ _
  have xyy : cubicEntry c y y x=P.n := rotate _ _ _
  have extQ (i : ι) : cubicEntry c x x (B.w i)=(ch i).q := (congrArg OutsideEntries.q (B.entries_eq hm i)).symm
  have extL (i : ι) : cubicEntry c x y (B.w i)=(ch i).l/S.ratio p := (congrArg OutsideEntries.l (B.entries_eq hm i)).symm
  have extH (i : ι) : cubicEntry c y y (B.w i)=(ch i).h/(S.ratio p)^2 := (congrArg OutsideEntries.h (B.entries_eq hm i)).symm
  dsimp only [c,x,y,e,P,ch] at xx xy yy xxy xyy extQ extL extH
  simp only [xx,xy,yy,xxy,xyy,extQ,extL,extH] at h₁ h₂ h₃ h₄
  dsimp only [core,CoreEntries.ofJet] at h₁ h₂ h₃ h₄ ⊢
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  exact ⟨by linear_combination h₁,by linear_combination h₂,by linear_combination h₃,by linear_combination h₄⟩

end SpectralFrame
end EuclideanMidpointRigidity.LiftedSection

