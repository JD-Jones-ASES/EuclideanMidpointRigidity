module

public import EuclideanMidpointRigidity.AxialQuartic
public import EuclideanMidpointRigidity.RulingResponses

/-! # Tensor components and their forcing along a straight maximizing line -/

@[expose] public section
noncomputable section
open Set Filter Metric
open scoped ContDiff InnerProductSpace Topology
namespace EuclideanMidpointRigidity
open Quartic
variable {d : ℕ}
local notation "E" => Space d

def lineEntry (C : E → Cubic d) (p u x y z : E) (s : ℝ) := cubicEntry (C (p+s • u)) x y z

theorem hasDerivAt_lineEntry {Ω : Set E} {C : E → Cubic d} (hΩ : IsOpen Ω) (hc : ContDiffOn ℝ ∞ C Ω)
    (p u x y z : E) (t : ℝ) (ht : p+t • u ∈ Ω) :
    HasDerivAt (lineEntry C p u x y z) (jetEntry (fderiv ℝ C (p+t • u)) u x y z) t := by
  have dl : HasDerivAt (displacementLine p u) u t := by
    change HasDerivAt (fun s : ℝ ↦ p+s • u) u t
    simpa only [id_eq,one_smul] using ((hasDerivAt_id t).smul_const u).const_add p
  have dc := ((hc.contDiffAt (hΩ.mem_nhds ht)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t dl
  have dK := hasDerivAt_K dc (hasDerivAt_const t x) (hasDerivAt_const t y)
  have h := dK.inner ℝ (hasDerivAt_const t z)
  change HasDerivAt (fun s ↦ ⟪K (C (p+s • u)) x y,z⟫_ℝ) ⟪K (fderiv ℝ C (p+t • u) u) x y,z⟫_ℝ t
  simpa only [K,Function.comp_def,displacementLine,map_zero,zero_apply,zero_add,add_zero,inner_zero_right] using h

namespace LiftedSection
variable (S : LiftedSection d)

def axialDirection (p : E) := (S.a p)⁻¹ • S.axis p

theorem product_axialDirection (p : E) (v : E) : K (S.field p) (S.axialDirection p) v=S.axisSlice p v := by
  change _=K (S.cubic p) (S.axis p) v
  rw [axialDirection,K_smul_left,cubic,K_smul_coeff]

theorem normalized_line_data {p : E} (hp : p ∈ S.domain) (hm : ∀ q ∈ S.domain, S.Maximizes q) :
    let u := S.axialDirection p
    K (S.field p) u u=u ∧ (∀ l, K (fderiv ℝ S.field p l) u u=0) ∧
      ∀ v, K (fderiv ℝ S.field p u) u v=0 := by
  obtain ⟨hj,_,hRate⟩ := S.weighted_ruling hp hm
  refine ⟨?_,?_,?_⟩
  · rw [S.product_axialDirection]
    change S.axisSlice p ((S.a p)⁻¹ • S.axis p)=_
    rw [map_smul]
    have he : S.axisSlice p (S.axis p)=S.axis p := by
      change K (S.cubic p) (S.axis p) (S.axis p)=S.axis p
      simpa only [one_smul] using S.normalized_axis hp
    rw [he]
    rfl
  · intro l
    simp only [axialDirection,K_smul_left,K_smul_right,hj,smul_zero]
  · intro v
    have h := congrArg (fun B : E →L[ℝ] E ↦ B v) hRate
    change K (S.normalizedJet p (S.axis p)) (S.axis p) v=0 at h
    simp only [normalizedJet,smul_apply,K_smul_coeff] at h
    simp only [axialDirection,map_smul,K_smul_coeff,K_smul_left,h,smul_zero]

theorem local_normalized_line {p : E} (hp : p ∈ S.domain) (hm : ∀ q ∈ S.domain, S.Maximizes q) :
    let u := S.axialDirection p
    ∃ W : Set ℝ, IsOpen W ∧ 0 ∈ W ∧ ∀ t ∈ W, p+t • u ∈ S.domain ∧
      S.axialDirection (p+t • u)=u ∧ S.axisSlice (p+t • u)=S.axisSlice p := by
  obtain ⟨U,δ,_,hpU,hδ,hr⟩ := S.local_straight_rulings hp hm
  let W := (fun t : ℝ ↦ t*(S.a p)⁻¹) ⁻¹' ball 0 δ
  refine ⟨W,isOpen_ball.preimage (continuous_id.mul continuous_const),by simpa [W] using hδ,?_⟩
  intro t ht
  have hh := hr p hpU (t*(S.a p)⁻¹) ht
  change _ ∈ S.domain ∧ _ ∧ _ at hh
  simp only [displacementLine,← smul_smul] at hh
  exact ⟨hh.1,by simp only [axialDirection,hh.2.1,hh.2.2.2],hh.2.2.1⟩

theorem line_recovery {p : E} (hp : p ∈ S.domain) (hm : ∀ q ∈ S.domain, S.Maximizes q) :
    let u := S.axialDirection p
    ∃ W : Set ℝ, IsOpen W ∧ 0 ∈ W ∧ ∀ t ∈ W, ∀ (x y z : E) (a b c : ℝ),
      S.axisSlice p x=a • x → S.axisSlice p y=b • y → S.axisSlice p z=c • z →
      3*(5-2*(a+b+c))*deriv (lineEntry S.field p u x y z) t+
      (20*a-2*b-2*c-4)*tiltSource S.field p u x y z t+
      (20*b-2*c-2*a-4)*tiltSource S.field p u y z x t+
      (20*c-2*a-2*b-4)*tiltSource S.field p u z x y t=0 := by
  let u := S.axialDirection p
  obtain ⟨W,hW,h₀,hr⟩ := S.local_normalized_line hp hm
  refine ⟨W,hW,h₀,?_⟩
  intro t ht x y z a b c hx hy hz
  let q := p+t • u
  obtain ⟨hd,hu,hB⟩ := hr t ht
  obtain ⟨he,hJ,hU⟩ := S.normalized_line_data hd hm
  rw [hu] at he hJ hU
  have huq : S.axialDirection q=u := hu
  have hbq : S.axisSlice q=S.axisSlice p := hB
  have ev (v : E) : K (S.field q) u v=S.axisSlice p v := by rw [← huq,S.product_axialDirection,hbq]
  have r := axial_quartic_recovery (S.equations.quartic hd) he hJ hU ((ev x).trans hx) ((ev y).trans hy) ((ev z).trans hz)
  rw [(hasDerivAt_lineEntry S.isOpen S.smooth p u x y z t hd).deriv]
  simpa only [tiltSource,firstProduct,jetEntry,cubicEntry,real_inner_comm z,real_inner_comm x,real_inner_comm y] using r

end LiftedSection
end EuclideanMidpointRigidity

