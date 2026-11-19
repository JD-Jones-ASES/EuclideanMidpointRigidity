module

public import EuclideanMidpointRigidity.ResonantFrame

/-! # Coordinates on a smooth positive critical section following the lift -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

structure LiftedSection (d : ℕ) where
  domain : Set (Space d)
  field : Space d → Cubic d
  axis : Space d → Space d
  isOpen : IsOpen domain
  smooth : ContDiffOn ℝ ∞ field domain
  smoothAxis : ContDiffOn ℝ ∞ axis domain
  equations : MidpointJetEquations domain field
  unit : ∀ p ∈ domain, ‖axis p‖=1
  critical : ∀ p ∈ domain, K (field p) (axis p) (axis p)=sectionValue field axis p • axis p
  positive : ∀ p ∈ domain, 0<sectionValue field axis p
  lift : ∀ p ∈ domain, fderiv ℝ axis p (axis p)=liftStep (sectionValue field axis p) (fderiv ℝ field p) (axis p)

namespace LiftedSection
variable (S : LiftedSection d)

def a := sectionValue S.field S.axis
def u (p : E) := ‖negativeComponent S.field S.axis p‖
def v (p : E) := ‖positiveComponent S.field S.axis p‖
def x (p : E) := (S.u p)⁻¹ • negativeComponent S.field S.axis p
def y (p : E) := (S.v p)⁻¹ • positiveComponent S.field S.axis p
def ratio (p : E) := S.v p/S.u p
def cubic (p : E) := (S.a p)⁻¹ • S.field p
def jet (p : E) := (S.u p)⁻¹ • fderiv ℝ S.field p

def IsMixed (p : E) : Prop :=
  p ∈ S.domain ∧ negativeComponent S.field S.axis p≠0 ∧ positiveComponent S.field S.axis p≠0

theorem eventually_mixed {p : E} (hm : S.IsMixed p) : ∀ᶠ q in 𝓝 p, S.IsMixed q := by
  have h₁ := (contDiffAt_negativeComponent (S.smooth.contDiffAt (S.isOpen.mem_nhds hm.1))
    (S.smoothAxis.contDiffAt (S.isOpen.mem_nhds hm.1))).continuousAt.eventually_ne hm.2.1
  have h₂ := (contDiffAt_positiveComponent S.isOpen S.smooth S.smoothAxis hm.1).continuousAt.eventually_ne hm.2.2
  filter_upwards [S.isOpen.mem_nhds hm.1,h₁,h₂] with q hq h₁ h₂
  exact ⟨hq,h₁,h₂⟩

theorem smooth_frame {p : E} (hm : S.IsMixed p) :
    ContDiffAt ℝ ∞ S.u p ∧ ContDiffAt ℝ ∞ S.v p ∧ ContDiffAt ℝ ∞ S.x p ∧ ContDiffAt ℝ ∞ S.y p := by
  have hn := contDiffAt_negativeComponent (S.smooth.contDiffAt (S.isOpen.mem_nhds hm.1))
    (S.smoothAxis.contDiffAt (S.isOpen.mem_nhds hm.1))
  have hh := contDiffAt_positiveComponent S.isOpen S.smooth S.smoothAxis hm.1
  have hu := hn.norm ℝ hm.2.1
  have hv := hh.norm ℝ hm.2.2
  exact ⟨hu,hv,(hu.inv (norm_pos_iff.mpr hm.2.1).ne').smul hn,
    (hv.inv (norm_pos_iff.mpr hm.2.2).ne').smul hh⟩

theorem eigenvectors {p : E} (hp : p ∈ S.domain) :
    K (S.field p) (S.axis p) (S.x p)=((-1/2:ℝ)*S.a p) • S.x p ∧
    K (S.field p) (S.axis p) (S.y p)=((1/5:ℝ)*S.a p) • S.y p := by
  obtain ⟨h₁,h₂⟩ := component_eigenvalues S.isOpen S.smooth S.smoothAxis S.equations.quartic S.unit hp (S.critical p hp)
  constructor
  · rw [x,K_smul_right,h₁,smul_comm]; rfl
  · rw [y,K_smul_right,h₂,smul_comm]; rfl

theorem split_gradient {p : E} (hm : S.IsMixed p) :
    gradient S.a p=S.u p • S.x p+S.v p • S.y p := by
  have hu : S.u p≠0 := (norm_pos_iff.mpr hm.2.1).ne'
  have hv : S.v p≠0 := (norm_pos_iff.mpr hm.2.2).ne'
  simp [x,y,smul_smul,hu,hv,positiveComponent,a]

theorem axial_jet {p : E} (hm : S.IsMixed p) :
    K (fderiv ℝ S.field p (S.axis p)) (S.axis p) (S.axis p)=(7/13*S.u p) • S.x p := by
  have hu : S.u p≠0 := (norm_pos_iff.mpr hm.2.1).ne'
  simp only [x,negativeComponent,smul_smul]
  rw [show (7/13*S.u p)*((S.u p)⁻¹*(13/7))=1 by field_simp,one_smul]

theorem normalized_eigenvector {p : E} (hp : p ∈ S.domain) {f : E} {s : ℝ}
    (hf : K (S.field p) (S.axis p) f=(s*S.a p) • f) :
    K (S.cubic p) (S.axis p) f=s • f := by
  simp only [cubic,K_smul_coeff,hf,smul_smul]
  rw [mul_left_comm,inv_mul_cancel₀ (show S.a p≠0 from (S.positive p hp).ne'),mul_one]

theorem normalized_axis {p : E} (hp : p ∈ S.domain) :
    K (S.cubic p) (S.axis p) (S.axis p)=(1:ℝ) • S.axis p :=
  S.normalized_eigenvector hp (by simpa only [a,one_mul] using S.critical p hp)

theorem normalized_obstruction {p : E} (hp : p ∈ S.domain) (w : E) : obstruction (S.cubic p) (S.jet p) w=0 := by
  have h := S.equations.quartic hp w
  rw [cubic,obstruction_smul_coeff]
  suffices obstruction (S.field p) (S.jet p) w=(S.u p)⁻¹ • obstruction (S.field p) (fderiv ℝ S.field p) w by
    rw [this,h,smul_zero,smul_zero]
  simp only [obstruction,jet,smul_apply,K_smul_coeff,K_smul_right]
  module

theorem normalized_jet_data {p : E} (hm : S.IsMixed p) :
    K (S.jet p (S.axis p)) (S.axis p) (S.axis p)=(7/13:ℝ) • S.x p ∧
      ∀ w, ⟪K (S.jet p w) (S.axis p) (S.axis p),S.axis p⟫_ℝ=⟪S.x p+S.ratio p • S.y p,w⟫_ℝ := by
  have hu : S.u p≠0 := (norm_pos_iff.mpr hm.2.1).ne'
  constructor
  · simp only [jet,smul_apply,K_smul_coeff,S.axial_jet hm,smul_smul]
    congr 1
    field_simp
  · intro w
    simp only [jet,smul_apply,K_smul_coeff,real_inner_smul_left]
    rw [← sectionValue_gradient S.isOpen S.smooth S.smoothAxis S.unit hm.1 (S.critical _ hm.1)]
    change (S.u p)⁻¹*⟪gradient S.a p,w⟫_ℝ=_
    rw [S.split_gradient hm]
    simp only [ratio,inner_add_left,real_inner_smul_left]
    field_simp

theorem plane_data {p : E} (hm : S.IsMixed p) :
    let plane := ResonantPlane.ofJet (S.cubic p) (fderiv ℝ S.field p) (S.axis p) (S.x p) (S.y p) (S.u p) (S.v p)
    ‖S.x p‖=1 ∧ ‖S.y p‖=1 ∧ ⟪S.x p,S.y p⟫_ℝ=0 ∧
      ⟪S.axis p,S.x p⟫_ℝ=0 ∧ ⟪S.axis p,S.y p⟫_ℝ=0 ∧ plane.LowRows ∧ plane.scalarSixth=0 ∧
      86354*S.u p*plane.t112+219375*S.v p*plane.t122=0 :=
  mixed_resonant_frame S.isOpen S.smooth S.smoothAxis S.equations S.unit S.critical
    (fun q hq ↦ (S.positive q hq).ne') hm.1 (S.lift p hm.1) hm.2.1 hm.2.2

end LiftedSection
end EuclideanMidpointRigidity
