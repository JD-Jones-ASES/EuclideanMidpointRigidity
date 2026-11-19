module

public import EuclideanMidpointRigidity.StraightMaxima
public import EuclideanMidpointRigidity.EigenpairRows
public import EuclideanMidpointRigidity.WeightedPair

/-! # The normalized cubic and its first derivatives on a straight maximizing section -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity.LiftedSection
variable {d : ℕ} (S : LiftedSection d)
local notation "E" => Space d

def axisSlice (p : E) : E →L[ℝ] E := (S.cubic p).val (S.axis p)
def normalizedJet (p : E) : E →L[ℝ] Cubic d := (S.a p)⁻¹ • fderiv ℝ S.field p
def sliceRate (p : E) : E →L[ℝ] E := (S.normalizedJet p (S.axis p)).val (S.axis p)

theorem normalizedJet_obstruction {p : E} (hp : p ∈ S.domain) (w : E) :
    obstruction (S.cubic p) (S.normalizedJet p) w=0 := by
  rw [cubic,obstruction_smul_coeff]
  suffices obstruction (S.field p) (S.normalizedJet p) w=(S.a p)⁻¹ • obstruction (S.field p) (fderiv ℝ S.field p) w by
    rw [this,S.equations.quartic hp w,smul_zero,smul_zero]
  simp only [obstruction,normalizedJet,smul_apply,K_smul_coeff,K_smul_right]
  module

theorem normalizedJet_axial {p : E} (hp : p ∈ S.domain) (hm : ∀ q ∈ S.domain, S.Maximizes q) :
    K (S.normalizedJet p (S.axis p)) (S.axis p) (S.axis p)=0 := by
  simp only [normalizedJet,smul_apply,K_smul_coeff,S.stationary_axial_source hp hm,smul_zero]

theorem normalizedJet_axial_inner {p : E} (hp : p ∈ S.domain) (hm : ∀ q ∈ S.domain, S.Maximizes q) (l : E) :
    ⟪K (S.normalizedJet p l) (S.axis p) (S.axis p),S.axis p⟫_ℝ=0 := by
  simp only [normalizedJet,smul_apply,K_smul_coeff,real_inner_smul_left,S.stationary_axial_component hp hm,mul_zero]

theorem normalized_critical_derivative {p : E} (hp : p ∈ S.domain) (hm : ∀ q ∈ S.domain, S.Maximizes q) (l : E) :
    K (S.normalizedJet p l) (S.axis p) (S.axis p) =
      fderiv ℝ S.axis p l - (2:ℝ) • S.axisSlice p (fderiv ℝ S.axis p l) := by
  have ha : S.a p≠0 := (S.positive _ hp).ne'
  have h := critical_section_differential S.isOpen S.smooth S.smoothAxis S.critical hp l
  change S.a p • _ - (2:ℝ) • _ = _ - (fderiv ℝ S.a p l) • _ at h
  rw [S.stationary_value hp hm,zero_apply,zero_smul,sub_zero] at h
  change K (S.normalizedJet p l) _ _ = _ - (2:ℝ) • K (S.cubic p) _ _
  simp only [normalizedJet,smul_apply,K_smul_coeff,cubic,← h,smul_sub,smul_smul,inv_mul_cancel₀ ha,one_smul]
  rw [mul_comm (S.a p)⁻¹]

theorem normalized_entry_gap {p : E} (hp : p ∈ S.domain) (hm : ∀ q ∈ S.domain, S.Maximizes q)
    (l x : E) {b : ℝ} (hx : S.axisSlice p x=b • x) :
    ⟪K (S.normalizedJet p l) (S.axis p) (S.axis p),x⟫_ℝ=(1-2*b)*⟪x,fderiv ℝ S.axis p l⟫_ℝ := by
  rw [S.normalized_critical_derivative hp hm,inner_sub_left,real_inner_smul_left]
  change ⟪fderiv ℝ S.axis p l,x⟫_ℝ-2*⟪K (S.cubic p) (S.axis p) (fderiv ℝ S.axis p l),x⟫_ℝ=_
  change K (S.cubic p) (S.axis p) x=b • x at hx
  rw [K_selfAdjoint,hx,real_inner_smul_right,real_inner_comm x]
  ring

theorem ruling_low_pair {p : E} (hp : p ∈ S.domain) (hm : ∀ q ∈ S.domain, S.Maximizes q)
    (x y : E) {b c : ℝ} (hx : S.axisSlice p x=b • x) (hy : S.axisSlice p y=c • y) :
    LowPair b c ((1-2*b)*⟪x,fderiv ℝ S.axis p y⟫_ℝ) ((1-2*c)*⟪y,fderiv ℝ S.axis p x⟫_ℝ)
      ⟪x,S.sliceRate p y⟫_ℝ := by
  let J := S.normalizedJet p
  let e := S.axis p
  let D := S.cubic p
  have h₄ : ∀ l, obstruction D J l=0 := S.normalizedJet_obstruction hp
  have ha : K D e e=(1:ℝ) • e := S.normalized_axis hp
  have hg (l : E) : ⟪K (J l) e e,e⟫_ℝ=⟪(0:E),l⟫_ℝ := by
    rw [inner_zero_left]; exact S.normalizedJet_axial_inner hp hm l
  have hU : K (J e) e e=0 := S.normalizedJet_axial hp hm
  have he₁ : K D e x=b • x := hx
  have he₂ : K D e y=c • y := hy
  have r₁ := eigenpair_vector_row ha h₄ he₂ he₁
  have r₂ := eigenpair_vector_row ha h₄ he₁ he₂
  have r₃ := eigenpair_normal_row ha h₄ hg he₂ he₁
  have hz₁ : ⟪K (J e) e x,y⟫_ℝ=⟪x,S.sliceRate p y⟫_ℝ := K_selfAdjoint _ _ _ _
  have hz₂ : ⟪K (J e) e y,x⟫_ℝ=⟪x,S.sliceRate p y⟫_ℝ := real_inner_comm _ _
  have hxy : ⟪K (J y) e e,x⟫_ℝ=_ := S.normalized_entry_gap hp hm y x hx
  have hyx : ⟪K (J x) e e,y⟫_ℝ=_ := S.normalized_entry_gap hp hm x y hy
  dsimp only at r₁ r₂ r₃
  simp only [hU,hxy,hyx,hz₁,hz₂,inner_zero_left,mul_zero,add_zero,sub_zero] at r₁ r₂ r₃
  exact ⟨by linear_combination r₃,by linear_combination r₁/2,by linear_combination r₂/2⟩

end EuclideanMidpointRigidity.LiftedSection

