module

public import EuclideanMidpointRigidity.DiagonalRates
public import EuclideanMidpointRigidity.HighRowExpansion
public import EuclideanMidpointRigidity.NormalizedEntries

/-! # The higher rows in common channel coordinates -/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology InnerProductSpace
namespace EuclideanMidpointRigidity
open Quartic

def MixedChannel.unscaled (v : MixedChannel) (t : ℝ) : OutsideEntries :=
  ⟨v.q,v.l/t,v.h/t^2,v.r1w,v.rw1,v.z1w,v.r2w/t,v.rw2/t,v.z2w/t⟩

namespace LiftedSection.SpectralFrame
variable {d : ℕ} {S : LiftedSection d} {p : Space d}
local notation "E" => Space d
variable {ι : Type*} [Fintype ι]
variable (B : SpectralFrame S p ι)

def entries (i : ι) : OutsideEntries :=
  (S.channel p (B.w i)).unscaled (S.ratio p)

theorem entries_eq (hm : S.IsMixed p) (i : ι) :
    B.entries i=OutsideEntries.ofJet (S.cubic p) (S.jet p) (S.axis p) (S.x p) (S.y p) (B.w i) := by
  have ht : S.ratio p≠0 := (div_pos (norm_pos_iff.mpr hm.2.2) (norm_pos_iff.mpr hm.2.1)).ne'
  dsimp only [entries,channel,MixedChannel.unscaled,MixedChannel.ofJet,OutsideEntries.ofJet,jetEntry,cubicEntry]
  simp only [mul_div_cancel_left₀ _ ht,mul_div_cancel_left₀ _ (pow_ne_zero 2 ht)]
  congr 1 <;> exact real_inner_comm _ _

theorem high_equations (hm : S.IsMixed p) (r : HighRow) :
    r.core (S.core p)+∑ i, r.outside (B.entries i)=0 := by
  simpa only [core,B.entries_eq hm] using r.sum_zero hm B

theorem axis_product (hm : S.IsMixed p) (i : ι) {z : E} (hz : z=S.x p ∨ z=S.y p) (l : E) :
    cubicEntry (S.cubic p) z z (B.w i)*⟪B.w i,S.axisDerivative p l⟫_ℝ=
    cubicEntry (S.cubic p) z z (B.w i)*jetEntry (S.jet p) l (S.axis p) (S.axis p) (B.w i)/(1-2*B.value i) := by
  have h := S.axisDerivative_coordinate hm (B.transverse i).2.1 (B.physical_eigenvalue hm.1 i) l
  by_cases hs : 1-2*B.value i=0
  · have he : B.value i=1/2 := by linarith only [hs]
    have hw := B.physical_eigenvalue hm.1 i
    rw [he] at hw
    obtain ⟨hq,_,hh,_,_,_,_,_,_,_,_⟩ := S.null_channel hm hw (B.transverse i).2.1
      (B.transverse i).2.2.1 (B.transverse i).2.2.2
    have hq' := congrArg OutsideEntries.q (B.entries_eq hm i)
    have hh' := congrArg OutsideEntries.h (B.entries_eq hm i)
    change (S.channel p (B.w i)).q=cubicEntry _ _ _ _ at hq'
    change (S.channel p (B.w i)).h/(S.ratio p)^2=cubicEntry _ _ _ _ at hh'
    rcases hz with rfl|rfl
    · rw [← hq',hq,zero_mul,zero_mul,zero_div]
    · rw [← hh',hh,zero_div,zero_mul,zero_mul,zero_div]
  · rw [← h]
    field_simp

theorem diagonal_equations (hm : S.IsMixed p) :
    let P := S.core p
    let A := B.entries
    let s := B.value
    P.j1xx= -1/2-P.d1*P.r11/2-(5/3)*P.m*P.r21-(∑ i, (A i).q*(A i).rw1/(1-2*s i)) ∧
    P.j2xx= -P.t/2-P.d1*P.r12/2-(5/3)*P.m*P.r22-(∑ i, (A i).q*(A i).rw2/(1-2*s i)) ∧
    P.j1yy= 1/5-P.n*P.r11/2-(5/3)*P.d2*P.r21-(∑ i, (A i).h*(A i).rw1/(1-2*s i)) ∧
    P.j2yy= P.t/5-P.n*P.r12/2-(5/3)*P.d2*P.r22-(∑ i, (A i).h*(A i).rw2/(1-2*s i)) := by
  obtain ⟨_,_,hx,hy⟩ := S.smooth_frame hm
  obtain ⟨hxn,hyn,hxy,_,_,_,_,_⟩ := S.plane_data hm
  have hnear : ∀ᶠ q in 𝓝 p, q ∈ S.domain := S.isOpen.mem_nhds hm.1
  have hx' (l : E) := B.expand_diagonal hm (hx.differentiableAt (by simp)) hxn
    (hnear.mono fun q hq ↦ (S.eigenvectors hq).1) l
  have hy' (l : E) := B.expand_diagonal hm (hy.differentiableAt (by simp)) hyn
    (hnear.mono fun q hq ↦ (S.eigenvectors hq).2) l
  have h₁ := hx' (S.x p)
  have h₂ := hx' (S.y p)
  have h₃ := hy' (S.x p)
  have h₄ := hy' (S.y p)
  have hi (i : ι) (l : E) := B.axis_product hm i (z := S.x p) (Or.inl rfl) l
  have hj (i : ι) (l : E) := B.axis_product hm i (z := S.y p) (Or.inr rfl) l
  have hyx := inner_eq_zero_symm.mp hxy
  dsimp only at h₁ h₂ h₃ h₄ ⊢
  simp only [hi,hj,inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq,hxn,hyn,hxy,hyx,
    one_pow,mul_one,mul_zero,add_zero,zero_add] at h₁ h₂ h₃ h₄
  simp only [LiftedSection.core,CoreEntries.ofJet,B.entries_eq hm,OutsideEntries.ofJet]
  simp only [cubicEntry_swap₁,cubicEntry_swap₂] at h₁ h₂ h₃ h₄ ⊢
  exact ⟨by linarith only [h₁],by linarith only [h₂],by linarith only [h₃],by linarith only [h₄]⟩

end LiftedSection.SpectralFrame
end EuclideanMidpointRigidity
