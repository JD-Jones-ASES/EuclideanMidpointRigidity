module

public import EuclideanMidpointRigidity.ForceContraction

/-! # Coordinates of the vector force in the complete spectral basis -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace ContDiff
namespace EuclideanMidpointRigidity
open Quartic LiftedSection

namespace ForceAxis

def field {d : ℕ} (i : ForceAxis) (S : LiftedSection d) := i.pick S.x S.y

def coreColumn (i : ForceAxis) (P : CoreEntries) (O : ℝ) : Fin 3 → ForceColumn :=
  ![⟨0,-7/26,i.pick (-7/26) 0,1,7/13,i.pick (7/13) 0,i.pick (7/13) 0⟩,
    ⟨1,0,i.pick 0 O,P.r11,P.z11,i.pick P.r11 P.r21,i.pick P.z11 P.z12⟩,
    ⟨0,-O,i.pick (-O) 0,P.r21,P.z12,i.pick P.r12 P.r22,i.pick P.z12 P.z22⟩]

def outsideColumn (i : ForceAxis) (t : ℝ) (v : MixedChannel) : ForceColumn :=
  ⟨0,v.rot1,i.pick v.rot1 (v.rot2/t),v.rw1,v.z1w,i.pick v.r1w (v.r2w/t),i.pick v.z1w (v.z2w/t)⟩

def directJet (i : ForceAxis) (P : CoreEntries) : ℝ :=
  ((7/13:ℝ)^2/2)*(15*i.pick P.j1xx P.j1xy-11*i.pick P.s111 P.s112)

def coreCost (i : ForceAxis) (P : CoreEntries) (O h : ℝ) :=
  (i.coreColumn P O 0).cost h+(i.coreColumn P O 1).cost h+(i.coreColumn P O 2).cost h+i.directJet P

end ForceAxis

namespace LiftedSection
variable {d : ℕ} (S : LiftedSection d)
local notation "E" => Space d

def column (p : E) (i : ForceAxis) (w : E) := S.forceColumn p (i.field S p) (S.rate (i.field S) p) w

theorem z_pair (p v w : E) : ⟪S.zMap p v,w⟫_ℝ=⟪S.zMap p w,v⟫_ℝ := by
  change ⟪K _ _ v,w⟫_ℝ=⟪K _ _ w,v⟫_ℝ
  rw [K_selfAdjoint,real_inner_comm v]

theorem core_columns {p : E} (hm : S.IsMixed p) (i : ForceAxis) :
    let c := i.coreColumn (S.core p) (S.omega p)
    S.column p i (S.axis p)=c 0 ∧ S.column p i (S.x p)=c 1 ∧ S.column p i (S.y p)=c 2 := by
  let x := S.x p
  let y := S.y p
  let e := S.axis p
  let P := S.core p
  have dx := (S.smooth_frame hm).2.2.1.differentiableAt (by simp)
  have dy := (S.smooth_frame hm).2.2.2.differentiableAt (by simp)
  obtain ⟨xe,ye,xx,yy,xy,yx⟩ := S.internal_rotations hm
  obtain ⟨hn,_,hxy,hex,_,_,_,_⟩ := S.plane_data hm
  have hxe := inner_eq_zero_symm.mp hex
  have hxx : ⟪x,x⟫_ℝ=1 := by rw [real_inner_self_eq_norm_sq,hn]; norm_num
  have L := core_leading S hm
  have a : ⟪S.rMap p x,e⟫_ℝ=1 := L.jx
  have b : ⟪S.rMap p e,x⟫_ℝ=7/13 := L.ux
  have c : ⟪S.rMap p e,y⟫_ℝ=0 := L.uy
  have f : ⟪S.zMap p e,x⟫_ℝ=7/13 := L.ux
  have g : ⟪S.zMap p e,y⟫_ℝ=0 := L.uy
  have j : ⟪S.zMap p x,e⟫_ℝ=7/13 := (S.z_pair p x e).trans f
  have rr : ⟪S.zMap p y,x⟫_ℝ=P.z12 := (S.z_pair p y x).trans rfl
  dsimp only [x,y,e,P] at hxx a b c f g j rr
  cases i <;> simp only [column,forceColumn,ForceAxis.field,ForceAxis.pick,ForceAxis.coreColumn,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,
    S.rate_coordinate dx,S.rate_coordinate dy,xe,ye,xx,yy,xy,yx,hxe,hxx,hxy,a,b,c,f,g,j,rr]
  all_goals repeat' constructor

namespace SpectralFrame
variable {S : LiftedSection d} {p : Space d}
variable {ι : Type*} [Fintype ι]
variable (B : SpectralFrame S p ι)

theorem outside_column (hm : S.IsMixed p) (i : ForceAxis) (j : ι) :
    S.column p i (B.w j)=i.outsideColumn (S.ratio p) (S.channel p (B.w j)) := by
  have dx := (S.smooth_frame hm).2.2.1.differentiableAt (by simp)
  have dy := (S.smooth_frame hm).2.2.2.differentiableAt (by simp)
  have hx := (B.transverse j).2.2.1
  have ht : S.ratio p≠0 := (div_pos (norm_pos_iff.mpr hm.2.2) (norm_pos_iff.mpr hm.2.1)).ne'
  have zx := S.z_pair p (B.w j) (S.x p)
  have zy := S.z_pair p (B.w j) (S.y p)
  cases i <;> simp only [column,forceColumn,ForceAxis.field,ForceAxis.pick,ForceAxis.outsideColumn,
    channel,MixedChannel.ofJet,hx,S.rate_coordinate dx,S.rate_coordinate dy,zx,zy,mul_div_cancel_left₀ _ ht]
  all_goals rfl

theorem force_cost (hm : S.IsMixed p) (i : ForceAxis) :
    let f := i.field S
    ⟪S.psi p,S.rate f p⟫_ℝ+⟪S.forceTerm p,f p⟫_ℝ=
      i.coreCost (S.core p) (S.omega p) (S.drift p)+
      ∑ j, (i.outsideColumn (S.ratio p) (S.channel p (B.w j))).cost (S.drift p) := by
  let f := i.field S
  have h := S.force_contraction B.basis p (f p) (S.rate f p)
  rw [Fintype.sum_sum_type,Fin.sum_univ_three] at h
  simp only [B.internal,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at h
  have direct : (7/13:ℝ)^2/2*(15*jetEntry (S.jet p) (S.x p) (S.axis p) (S.x p) (f p)-
      11*jetEntry (S.jet p) (S.axis p) (S.x p) (S.x p) (f p))=i.directJet (S.core p) := by cases i <;> rfl
  let cost := fun z ↦ (S.column p i z).cost (S.drift p)
  change _=cost (S.axis p)+cost (S.x p)+cost (S.y p)+(∑ j, cost (B.w j))+_ at h
  dsimp only [cost] at h
  obtain ⟨a,b,c⟩ := S.core_columns hm i
  rw [a,b,c,direct] at h
  simp only [B.outside_column hm] at h
  dsimp only [ForceAxis.coreCost]
  linear_combination h

end SpectralFrame
end LiftedSection
end EuclideanMidpointRigidity

