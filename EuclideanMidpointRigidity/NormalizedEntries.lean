module

public import EuclideanMidpointRigidity.ResonantEntries

/-! # The resonant coordinates after dividing the first jet by its gradient length -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity

namespace ResonantPlane

def rescale (p : ResonantPlane) (s : ℝ) : ResonantPlane :=
  ⟨s*p.u,s*p.v,p.t111,p.t112,p.t122,p.t222,s*p.r11,s*p.r12,s*p.r21,s*p.r22,s*p.z11,s*p.z12,s*p.z22⟩

theorem LowRows.rescale {p : ResonantPlane} (h : p.LowRows) (s : ℝ) : (p.rescale s).LowRows := by
  obtain ⟨a,b,c,d,e,f,g,i,j⟩ := h
  constructor <;> dsimp only [ResonantPlane.rescale]
  · linear_combination s*a
  · linear_combination s*b
  · linear_combination s*c
  · linear_combination s*d
  · linear_combination s*e
  · linear_combination s*f
  · linear_combination s*g
  · linear_combination s*i
  · linear_combination s*j

theorem scalarSixth_rescale (p : ResonantPlane) (s : ℝ) : (p.rescale s).scalarSixth=s^3*p.scalarSixth := by
  dsimp only [rescale,scalarSixth]; ring

local instance (d : ℕ) : AddMonoid (Cubic d) :=
  (cubicNormedAddCommGroup d).toAddCommGroup.toAddCommMonoid.toAddMonoid

theorem rescale_ofJet {d : ℕ} (c : Cubic d) (J : Space d →L[ℝ] Cubic d) (e x y : Space d) (u v s : ℝ) :
    (ofJet c J e x y u v).rescale s=ofJet c (s • J) e x y (s*u) (s*v) := by
  simp only [rescale,ofJet,smul_apply,K_smul_coeff,real_inner_smul_left]

end ResonantPlane

namespace Quartic.CoreEntries

def plane (p : CoreEntries) : ResonantPlane :=
  ⟨1,p.t,p.d1,p.m,p.n,p.d2,p.r11,p.r12,p.r21,p.r22,p.z11,p.z12,p.z22⟩

theorem plane_eq {d : ℕ} (c : Cubic d) (J : Space d →L[ℝ] Cubic d) (e x y : Space d) (t : ℝ) :
    (ofJet c J e x y t).plane=ResonantPlane.ofJet c J e x y 1 t := by
  simp only [plane,ofJet,ResonantPlane.ofJet,jetEntry,cubicEntry]
  congr 1 <;> first | exact real_inner_comm _ _ | rw [K_symm c x y,K_selfAdjoint]

structure Normalized (p : CoreEntries) : Prop where
  d1 : p.d1=(650/153)*ResonantPlane.k*p.t^2*p.n
  m : p.m= -ResonantPlane.k*p.t*p.n
  d2 : p.t*p.d2= -(159/1300)*p.n
  r11 : p.r11=(70/153)*p.t*p.m
  r12 : p.r12= -(5/7059)*(634*p.m+1677*p.t*p.n)
  r21 : p.r21= -(5/4706)*(1076*p.m+1755*p.t*p.n)
  r22 : p.r22= -(21/104)*p.n
  z11 : p.z11=(175/153)*p.t*p.m
  z12 : p.z12= -(5/28236)*(5704*p.m+8385*p.t*p.n)
  z22 : p.z22= -(7/26)*p.n

theorem normalized_of_plane {p : CoreEntries} (ht : 0<p.t)
    (hl : p.plane.LowRows) (hs : p.plane.scalarSixth=0) : p.Normalized := by
  obtain ⟨a,b,c⟩ := ResonantPlane.ratio_coordinates hl hs (by norm_num [plane]) ht (t := p.t) (by simp [plane])
  obtain ⟨_,_,d,e,f,g,i,j,k⟩ := hl.solve
  dsimp only [plane] at a b c d e f g i j k
  exact ⟨a,b,c,d,by linarith only [e],by linarith only [f],by linarith only [g],
    i,by linarith only [j],by linarith only [k]⟩

end Quartic.CoreEntries

namespace LiftedSection
open Quartic
variable {d : ℕ} (S : LiftedSection d)

def core (p : Space d) : CoreEntries :=
  CoreEntries.ofJet (S.cubic p) (S.jet p) (S.axis p) (S.x p) (S.y p) (S.ratio p)

theorem normalized_entries {p : Space d} (hm : S.IsMixed p) : (S.core p).Normalized := by
  obtain ⟨_,_,_,_,_,hl,hs,_⟩ := S.plane_data hm
  have hu : 0<S.u p := norm_pos_iff.mpr hm.2.1
  have hv : 0<S.v p := norm_pos_iff.mpr hm.2.2
  have hc := hl.rescale (S.u p)⁻¹
  have h₆ := ResonantPlane.scalarSixth_rescale
    (ResonantPlane.ofJet (S.cubic p) (fderiv ℝ S.field p) (S.axis p) (S.x p) (S.y p) (S.u p) (S.v p)) (S.u p)⁻¹
  rw [hs,mul_zero] at h₆
  have ht : (S.u p)⁻¹*S.v p=S.ratio p := by rw [ratio,div_eq_inv_mul]
  rw [ResonantPlane.rescale_ofJet,inv_mul_cancel₀ hu.ne',ht] at hc h₆
  apply CoreEntries.normalized_of_plane (p := S.core p) (div_pos hv hu)
  · rw [core,CoreEntries.plane_eq]; exact hc
  · rw [core,CoreEntries.plane_eq]; exact h₆

end LiftedSection
end EuclideanMidpointRigidity
