module

public import EuclideanMidpointRigidity.AmplitudeRates
public import EuclideanMidpointRigidity.ResonantEntries

/-! # Spatial derivatives of the two diagonal axial eigenvalues -/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology InnerProductSpace
namespace EuclideanMidpointRigidity.LiftedSection
open Quartic
variable {d : ℕ}
local notation "E" => Space d
variable (S : LiftedSection d)

def axisDerivative (p l : E) := (S.a p/S.u p) • fderiv ℝ S.axis p l

theorem axisDerivative_normal {p : E} (hm : S.IsMixed p) (l : E) :
    ⟪S.axis p,S.axisDerivative p l⟫_ℝ=0 := by
  have he := (S.smoothAxis.contDiffAt (S.isOpen.mem_nhds hm.1)).differentiableAt (by simp)
  have hn : ∀ᶠ q in 𝓝 p, ‖S.axis q‖=1 :=
    (show ∀ᶠ q in 𝓝 p, q ∈ S.domain from S.isOpen.mem_nhds hm.1).mono (fun q hq ↦ S.unit q hq)
  have h := stationary_inner_derivative he he (hn.mono fun q hq ↦ show ⟪S.axis q,S.axis q⟫_ℝ=1 by
    rw [real_inner_self_eq_norm_sq,hq]; norm_num) l
  rw [show ⟪fderiv ℝ S.axis p l,S.axis p⟫_ℝ=⟪S.axis p,fderiv ℝ S.axis p l⟫_ℝ from real_inner_comm _ _] at h
  rw [axisDerivative,real_inner_smul_right,show ⟪S.axis p,fderiv ℝ S.axis p l⟫_ℝ=0 by linarith only [h],mul_zero]

theorem axisDerivative_coordinate {p : E} (hm : S.IsMixed p) {w : E} {s : ℝ}
    (hor : ⟪S.axis p,w⟫_ℝ=0) (hw : K (S.field p) (S.axis p) w=(s*S.a p) • w) (l : E) :
    (1-2*s)*⟪w,S.axisDerivative p l⟫_ℝ=jetEntry (S.jet p) l (S.axis p) (S.axis p) w := by
  have h := axis_section_coordinate S.isOpen S.smooth S.smoothAxis S.critical hm.1 hor hw l
  change S.a p*(1-2*s)*_= _ at h
  simp only [axisDerivative,jet,jetEntry,cubicEntry,smul_apply,K_smul_coeff,real_inner_smul_left,
    real_inner_smul_right,show ⟪w,fderiv ℝ S.axis p l⟫_ℝ=⟪fderiv ℝ S.axis p l,w⟫_ℝ from real_inner_comm _ _]
  linear_combination (S.u p)⁻¹*h

theorem normalized_diagonal_rate {p : E} (hm : S.IsMixed p) {f : E → E} {b : ℝ}
    (hf : DifferentiableAt ℝ f p) (hu : ‖f p‖=1)
    (he : ∀ᶠ q in 𝓝 p, K (S.field q) (S.axis q) (f q)=(b*S.a q) • f q) (l : E) :
    jetEntry (S.jet p) l (S.axis p) (f p) (f p)=
      b*⟪S.x p+S.ratio p • S.y p,l⟫_ℝ-cubicEntry (S.cubic p) (f p) (f p) (S.axisDerivative p l) := by
  have h := congrArg (fun w : E ↦ ⟪w,f p⟫_ℝ) (eigen_section_derivative S.isOpen S.smooth S.smoothAxis hm.1 hf he l)
  have hff : ⟪f p,f p⟫_ℝ=1 := by rw [real_inner_self_eq_norm_sq,hu]; norm_num
  have heq : K (S.field p) (S.axis p) (f p)=(b*sectionValue S.field S.axis p) • f p := he.self_of_nhds
  simp only [inner_add_left,real_inner_smul_left,K_selfAdjoint (S.field p) (S.axis p) (fderiv ℝ f p l) (f p),
    heq,real_inner_smul_right,hff,mul_one] at h
  have hsym : ⟪K (S.field p) (fderiv ℝ S.axis p l) (f p),f p⟫_ℝ=⟪K (S.field p) (f p) (f p),fderiv ℝ S.axis p l⟫_ℝ := by
    rw [K_symm,K_selfAdjoint,real_inner_comm]
  have hsplit := S.split_gradient hm
  unfold a at hsplit
  rw [hsym,← inner_gradient_left (f := sectionValue S.field S.axis),hsplit] at h
  simp only [inner_add_left,real_inner_smul_left] at h
  have hn : S.u p≠0 := (norm_pos_iff.mpr hm.2.1).ne'
  have ha : S.a p≠0 := (S.positive _ hm.1).ne'
  simp only [jetEntry,cubicEntry,jet,cubic,axisDerivative,ratio,smul_apply,K_smul_coeff,inner_add_left,
    real_inner_smul_left,real_inner_smul_right]
  linear_combination (norm := (field_simp [hn,ha]; ring)) (S.u p)⁻¹*h

namespace SpectralFrame
variable {S : LiftedSection d} {p : Space d}
variable {ι : Type*} [Fintype ι]
variable (B : SpectralFrame S p ι)

theorem expand_diagonal {f : E → E} {b : ℝ} (hm : S.IsMixed p)
    (hf : DifferentiableAt ℝ f p) (hu : ‖f p‖=1)
    (he : ∀ᶠ q in 𝓝 p, K (S.field q) (S.axis q) (f q)=(b*S.a q) • f q) (l : E) :
    let c := S.cubic p
    let J := S.jet p
    let e := S.axis p
    let x := S.x p
    let y := S.y p
    jetEntry J l e (f p) (f p)=b*⟪x+S.ratio p • y,l⟫_ℝ-
      (cubicEntry c (f p) (f p) x*jetEntry J l e e x/2+
       (5/3)*cubicEntry c (f p) (f p) y*jetEntry J l e e y+
       ∑ i, cubicEntry c (f p) (f p) (B.w i)*⟪B.w i,S.axisDerivative p l⟫_ℝ) := by
  obtain ⟨_,_,_,hex,hey,_,_,_⟩ := S.plane_data hm
  have hx := S.axisDerivative_coordinate hm hex (S.eigenvectors hm.1).1 l
  have hy := S.axisDerivative_coordinate hm hey (S.eigenvectors hm.1).2 l
  have hx' : ⟪S.x p,S.axisDerivative p l⟫_ℝ=jetEntry (S.jet p) l (S.axis p) (S.axis p) (S.x p)/2 := by
    linarith only [hx]
  have hy' : ⟪S.y p,S.axisDerivative p l⟫_ℝ=5/3*jetEntry (S.jet p) l (S.axis p) (S.axis p) (S.y p) := by
    linarith only [hy]
  have h := B.basis.sum_inner_mul_inner (K (S.cubic p) (f p) (f p)) (S.axisDerivative p l)
  rw [Fintype.sum_sum_type,Fin.sum_univ_three] at h
  simp only [B.internal,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at h
  let k := K (S.cubic p) (f p) (f p)
  let v := S.axisDerivative p l
  change ⟪k,S.axis p⟫_ℝ*⟪S.axis p,v⟫_ℝ+⟪k,S.x p⟫_ℝ*⟪S.x p,v⟫_ℝ+
    ⟪k,S.y p⟫_ℝ*⟪S.y p,v⟫_ℝ+(∑ i, ⟪k,B.w i⟫_ℝ*⟪B.w i,v⟫_ℝ)=⟪k,v⟫_ℝ at h
  dsimp only [k,v] at h
  rw [S.axisDerivative_normal hm,hx',hy',mul_zero,zero_add] at h
  dsimp only
  rw [S.normalized_diagonal_rate hm hf hu he l]
  dsimp only [cubicEntry]
  linear_combination h

end SpectralFrame
end EuclideanMidpointRigidity.LiftedSection
