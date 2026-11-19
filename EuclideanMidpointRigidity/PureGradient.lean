module

public import EuclideanMidpointRigidity.PureSpectrum
public import EuclideanMidpointRigidity.FrameTransport
public import EuclideanMidpointRigidity.LiftedSection
public import EuclideanMidpointRigidity.QuarticHighRows

/-! # Geometry at a persistent pure gradient on a lifted section -/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology ContDiff InnerProductSpace
namespace EuclideanMidpointRigidity.LiftedSection
open Quartic
variable {d : ℕ} (S : LiftedSection d)
local notation "E" => Space d

def gradLength (p : E) := ‖gradient S.a p‖
def gradUnit (p : E) := (S.gradLength p)⁻¹ • gradient S.a p
def gradExtension (p q : E) := (S.gradLength p)⁻¹ • gradient S.a q
def pureJet (p : E) := (S.gradLength p)⁻¹ • fderiv ℝ S.field p
def pureAxisDerivative (p l : E) := (S.a p/S.gradLength p) • fderiv ℝ S.axis p l

structure PureAt (r : PureResonance) (p : E) : Prop where
  mem : p ∈ S.domain
  nonzero : gradient S.a p≠0
  eigen : ∀ᶠ q in 𝓝 p, K (S.field q) (S.axis q) (gradient S.a q)=(r.b*S.a q) • gradient S.a q

namespace PureAt
variable {S : LiftedSection d} {r : PureResonance} {p : Space d}

theorem length_pos (h : S.PureAt r p) : 0<S.gradLength p := norm_pos_iff.mpr h.nonzero

theorem smooth_gradient (h : S.PureAt r p) : ContDiffAt ℝ ∞ (gradient S.a) p := by
  let L : (E →L[ℝ] ℝ) →L[ℝ] E := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have ha := (contDiffOn_sectionValue S.smooth S.smoothAxis).contDiffAt (S.isOpen.mem_nhds h.mem)
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ S.a) p := ha.fderiv_right (by simp)
  exact L.contDiff.contDiffAt.comp p hd

theorem extension (h : S.PureAt r p) :
    DifferentiableAt ℝ (S.gradExtension p) p ∧
    ∀ᶠ q in 𝓝 p, K (S.field q) (S.axis q) (S.gradExtension p q)=(r.b*S.a q) • S.gradExtension p q := by
  refine ⟨(h.smooth_gradient.differentiableAt (by simp)).const_smul (S.gradLength p)⁻¹,?_⟩
  filter_upwards [h.eigen] with q hq
  rw [gradExtension,K_smul_right,hq,smul_comm]

theorem unit (h : S.PureAt r p) : ‖S.gradUnit p‖=1 := by
  simp only [gradUnit,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos h.length_pos]
  exact inv_mul_cancel₀ h.length_pos.ne'

theorem section_gradient (h : S.PureAt r p) : gradient S.a p=S.gradLength p • S.gradUnit p := by
  simp only [gradUnit,smul_smul,mul_inv_cancel₀ h.length_pos.ne',one_smul]

theorem first_data (h : S.PureAt r p) :
    (∀ l, ⟪K (S.pureJet p l) (S.axis p) (S.axis p),S.axis p⟫_ℝ=⟪S.gradUnit p,l⟫_ℝ) ∧
    K (S.pureJet p (S.axis p)) (S.axis p) (S.axis p)=r.axial • S.gradUnit p := by
  let e := S.axis p
  let U := K (fderiv ℝ S.field p e) e e
  have hg (l : E) : ⟪K (fderiv ℝ S.field p l) e e,e⟫_ℝ=⟪gradient S.a p,l⟫_ℝ :=
    (sectionValue_gradient S.isOpen S.smooth S.smoothAxis S.unit h.mem (S.critical p h.mem) l).symm
  have h₄ := S.equations.quartic h.mem
  have hv := critical_gradient_product (S.critical p h.mem) h₄ hg
  change K (S.field p) e (gradient S.a p)=(S.a p/5) • gradient S.a p-(13*S.a p/10) • U at hv
  rw [h.eigen.self_of_nhds] at hv
  have ha : S.a p≠0 := (S.positive _ h.mem).ne'
  have eq : U=r.axial • gradient S.a p := by
    apply ext_inner_right ℝ
    intro w
    have hh := congrArg (fun v : E ↦ ⟪v,w⟫_ℝ) hv
    simp only [inner_sub_left,real_inner_smul_left] at hh ⊢
    cases r <;> dsimp only [PureResonance.b,PureResonance.axial] at hh ⊢ <;>
      linear_combination (norm := (field_simp [ha]; ring)) (10/(13*S.a p))*hh
  constructor
  · intro l
    simp only [pureJet,gradUnit,smul_apply,K_smul_coeff,real_inner_smul_left]
    rw [hg]
  · change K (S.pureJet p e) e e=_
    simp only [pureJet,smul_apply,K_smul_coeff,gradUnit]
    change (S.gradLength p)⁻¹ • U=_
    rw [eq,smul_comm]

theorem frame (h : S.PureAt r p) :
    ⟪S.axis p,S.gradUnit p⟫_ℝ=0 ∧
    K (S.cubic p) (S.axis p) (S.gradUnit p)=r.b • S.gradUnit p ∧
    fderiv ℝ S.axis p (S.axis p)=(r.γ*S.gradLength p/S.a p) • S.gradUnit p := by
  have heig : K (S.field p) (S.axis p) (S.gradUnit p)=(r.b*S.a p) • S.gradUnit p := h.extension.2.self_of_nhds
  have ha : 0<S.a p := S.positive p h.mem
  have hn : (1:ℝ)*S.a p≠r.b*S.a p := by
    cases r <;> dsimp [PureResonance.b] <;> linarith
  have hu := h.first_data.2
  simp only [pureJet,smul_apply,K_smul_coeff] at hu
  refine ⟨axial_eigenvectors_orthogonal hn (by simpa only [a,one_mul] using S.critical p h.mem) heig,
    S.normalized_eigenvector h.mem heig,?_⟩
  rw [S.lift p h.mem,liftStep]
  have hz := congrArg (fun v : E ↦ S.gradLength p • v) hu
  simp only [smul_smul,mul_inv_cancel₀ h.length_pos.ne',one_smul] at hz
  rw [hz,smul_smul,PureResonance.γ]
  congr 1
  unfold a
  ring

theorem quartic (h : S.PureAt r p) (w : E) : obstruction (S.cubic p) (S.pureJet p) w=0 := by
  have he := S.equations.quartic h.mem w
  rw [cubic,obstruction_smul_coeff]
  suffices obstruction (S.field p) (S.pureJet p) w=(S.gradLength p)⁻¹ • obstruction (S.field p) (fderiv ℝ S.field p) w by
    rw [this,he,smul_zero,smul_zero]
  simp only [obstruction,pureJet,smul_apply,K_smul_coeff,K_smul_right]
  module

theorem grad_transport (h : S.PureAt r p) (w : E) :
    ⟪fderiv ℝ (S.gradExtension p) p (S.axis p),w⟫_ℝ= -⟪fderiv ℝ S.axis p w,S.gradUnit p⟫_ℝ := by
  let G := S.gradLength p
  have hg : ∀ᶠ q in 𝓝 p, gradient S.a q=(fun _ : E ↦ G) q • S.gradExtension p q+
      (fun _ : E ↦ (0:ℝ)) q • (fun _ : E ↦ (0:E)) q := by
    apply Filter.Eventually.of_forall
    intro q
    simp only [gradExtension,G,smul_smul,mul_inv_cancel₀ h.length_pos.ne',one_smul,zero_smul,add_zero]
  have z := gradient_frame_transport S.isOpen S.smooth S.smoothAxis S.equations.quartic S.unit S.critical
    (fun q hq ↦ (S.positive q hq).ne') h.mem h.extension.1 (differentiableAt_const _)
    (differentiableAt_const _) (differentiableAt_const _) hg w
  simp only [fderiv_const_apply,ContinuousLinearMap.zero_apply,zero_mul,add_zero,zero_add] at z
  change G*_= -(G*⟪fderiv ℝ S.axis p w,S.gradUnit p⟫_ℝ) at z
  apply mul_left_cancel₀ h.length_pos.ne'
  simpa only [mul_neg] using z

end PureAt
end EuclideanMidpointRigidity.LiftedSection

