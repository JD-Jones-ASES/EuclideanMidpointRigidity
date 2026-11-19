module

public import EuclideanMidpointRigidity.PureGradient

/-! # Pair equations and the diagonal derivative at a pure resonance -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity.LiftedSection
open Quartic
variable {d : ℕ}
local notation "E" => Space d

def pureChannel (S : LiftedSection d) (p w : E) : PureChannel :=
  let e := S.axis p
  let f := S.gradUnit p
  let J := S.pureJet p
  ⟨jetEntry J w e e f,jetEntry J f e e w,jetEntry J e e f w,cubicEntry (S.cubic p) f f w⟩

namespace PureAt
variable {S : LiftedSection d} {p : Space d} {r : PureResonance}

theorem rotation {w : E} {s : ℝ} (h : S.PureAt r p)
    (hw : K (S.field p) (S.axis p) w=(s*S.a p) • w) :
    let v := S.pureChannel p w
    (1-2*r.b)*(v.z+r.γ*v.q)=(s-r.b)*v.x := by
  let e := S.axis p
  let f := S.gradUnit p
  let F := S.gradExtension p
  have hf : K (S.field p) e f=(r.b*S.a p) • f := h.extension.2.self_of_nhds
  have q := eigen_section_derivative S.isOpen S.smooth S.smoothAxis h.mem h.extension.1 h.extension.2 e
  rw [critical_section_value_along_axis S.isOpen S.smooth S.smoothAxis S.equations.quartic S.unit h.mem
    (S.positive _ h.mem).ne' (S.critical _ h.mem)] at q
  have eq := congrArg (fun v : E ↦ ⟪v,w⟫_ℝ) q
  change ⟪K (fderiv ℝ S.field p e) e f+K (S.field p) (fderiv ℝ S.axis p e) f+
     K (S.field p) e (fderiv ℝ F p e),w⟫_ℝ=⟪(r.b*S.a p) • fderiv ℝ F p e+(r.b*0) • f,w⟫_ℝ at eq
  have he : fderiv ℝ S.axis p e=(r.γ*S.gradLength p/S.a p) • f := h.frame.2.2
  have ht : ⟪fderiv ℝ F p e,w⟫_ℝ= -⟪fderiv ℝ S.axis p w,f⟫_ℝ := h.grad_transport w
  change K (S.field p) e w=(s*S.a p) • w at hw
  simp only [he,K_smul_left,mul_zero,zero_smul,add_zero,inner_add_left,real_inner_smul_left,
    K_selfAdjoint (S.field p) e (fderiv ℝ F p e) w,hw,real_inner_smul_right,ht] at eq
  have hc := axis_section_coordinate S.isOpen S.smooth S.smoothAxis S.critical h.mem h.frame.1 hf w
  change S.a p*(1-2*r.b)*⟪fderiv ℝ S.axis p w,f⟫_ℝ=⟪K (fderiv ℝ S.field p w) e e,f⟫_ℝ at hc
  dsimp only [pureChannel,jetEntry,cubicEntry,pureJet,cubic]
  simp only [smul_apply,K_smul_coeff,real_inner_smul_left]
  dsimp only [e,f] at eq hc
  have hu := h.length_pos.ne'
  have ha : S.a p≠0 := (S.positive _ h.mem).ne'
  linear_combination (norm := (field_simp [hu,ha]; ring)) ((1-2*r.b)/S.gradLength p)*eq+
    ((s-r.b)/S.gradLength p)*hc

theorem channel_equations {w : E} {s : ℝ} (h : S.PureAt r p)
    (hw : K (S.field p) (S.axis p) w=(s*S.a p) • w) : (S.pureChannel p w).Equations r s := by
  let e := S.axis p
  let f := S.gradUnit p
  let c := S.cubic p
  let J := S.pureJet p
  have he := S.normalized_axis h.mem
  have hf := h.frame.2.1
  have hs := S.normalized_eigenvector h.mem hw
  obtain ⟨hg,hU⟩ := h.first_data
  have hN := eigenpair_normal_row he h.quartic hg hf hs
  have hF := eigenpair_vector_row he h.quartic hs hf
  have hR := eigenpair_vector_row he h.quartic hf hs
  have z : ⟪K (J e) e w,f⟫_ℝ=⟪K (J e) e f,w⟫_ℝ := by rw [K_selfAdjoint,real_inner_comm]
  have q : ⟪f,K c f w⟫_ℝ=⟪K c f f,w⟫_ℝ := (K_selfAdjoint _ _ _ _).symm
  dsimp only [e,f,c,J] at z q
  dsimp only at hN hF hR
  simp only [hU,K_symm (S.cubic p) w (S.gradUnit p),real_inner_smul_left,q,z] at hN hF hR
  refine ⟨?_,?_,?_,h.rotation hw⟩ <;> dsimp only [pureChannel,cubicEntry,jetEntry]
  · linear_combination hN/2
  · linear_combination hF/2
  · linear_combination hR/2

theorem axis_coordinate {w : E} {s : ℝ} (h : S.PureAt r p) (hor : ⟪S.axis p,w⟫_ℝ=0)
    (hw : K (S.field p) (S.axis p) w=(s*S.a p) • w) (l : E) :
    (1-2*s)*⟪S.pureAxisDerivative p l,w⟫_ℝ=jetEntry (S.pureJet p) l (S.axis p) (S.axis p) w := by
  have q := axis_section_coordinate S.isOpen S.smooth S.smoothAxis S.critical h.mem hor hw l
  change S.a p*(1-2*s)*_= _ at q
  simp only [pureAxisDerivative,pureJet,jetEntry,cubicEntry,smul_apply,K_smul_coeff,real_inner_smul_left]
  linear_combination (S.gradLength p)⁻¹*q

theorem diagonal_rate (h : S.PureAt r p) (l : E) :
    let e := S.axis p
    let f := S.gradUnit p
    jetEntry (S.pureJet p) l e f f=r.b*⟪f,l⟫_ℝ-cubicEntry (S.cubic p) f f (S.pureAxisDerivative p l) := by
  let f := S.gradUnit p
  have F := h.extension
  have q := eigen_section_derivative S.isOpen S.smooth S.smoothAxis h.mem F.1 F.2 l
  have eq := congrArg (fun v : E ↦ ⟪v,f⟫_ℝ) q
  have hf : K (S.field p) (S.axis p) f=(r.b*S.a p) • f := F.2.self_of_nhds
  have hf₁ : ⟪f,f⟫_ℝ=1 := by rw [real_inner_self_eq_norm_sq,h.unit]; norm_num
  change ⟪K (fderiv ℝ S.field p l) (S.axis p) f+K (S.field p) (fderiv ℝ S.axis p l) f+
    K (S.field p) (S.axis p) (fderiv ℝ (S.gradExtension p) p l),f⟫_ℝ=
    ⟪(r.b*S.a p) • (fderiv ℝ (S.gradExtension p) p l)+(r.b*fderiv ℝ S.a p l) • f,f⟫_ℝ at eq
  have hsym : ⟪K (S.field p) (fderiv ℝ S.axis p l) f,f⟫_ℝ=⟪K (S.field p) f f,fderiv ℝ S.axis p l⟫_ℝ := by
    rw [K_symm,K_selfAdjoint,real_inner_comm]
  simp only [inner_add_left,real_inner_smul_left,hf₁,mul_one,hsym,K_selfAdjoint (S.field p) (S.axis p) _ f,hf,
    real_inner_smul_right,← inner_gradient_left (f := S.a),h.section_gradient] at eq
  dsimp only [f] at eq
  dsimp only [pureJet,cubic,pureAxisDerivative,jetEntry,cubicEntry]
  simp only [smul_apply,K_smul_coeff,real_inner_smul_left,real_inner_smul_right]
  have hu := h.length_pos.ne'
  have ha : S.a p≠0 := (S.positive _ h.mem).ne'
  linear_combination (norm := (field_simp [hu,ha]; ring)) (S.gradLength p)⁻¹*eq

end PureAt
end EuclideanMidpointRigidity.LiftedSection

