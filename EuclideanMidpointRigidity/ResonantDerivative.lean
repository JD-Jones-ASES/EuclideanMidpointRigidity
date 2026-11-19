module

public import EuclideanMidpointRigidity.AmplitudeRates
public import EuclideanMidpointRigidity.NormalizedEntries
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-! # Directional differentiation in the normalized axial coordinate -/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology ContDiff InnerProductSpace
namespace EuclideanMidpointRigidity.LiftedSection
open Quartic
variable {d : ℕ} (S : LiftedSection d)
local notation "E" => Space d

local instance (d : ℕ) : AddMonoid (Cubic d) :=
  (cubicNormedAddCommGroup d).toAddCommGroup.toAddCommMonoid.toAddMonoid

local instance (d : ℕ) : AddZeroClass (Cubic d) :=
  (cubicNormedAddCommGroup d).toAddCommGroup.toAddCommMonoid.toAddMonoid.toAddZeroClass

def axisLine (p : E) (t : ℝ) : E := p+t • ((S.a p/S.u p) • S.axis p)

@[simp] theorem axisLine_zero (p : E) : S.axisLine p 0=p := by simp [axisLine]

theorem axisLine_derivative (p : E) : HasDerivAt (S.axisLine p) ((S.a p/S.u p) • S.axis p) 0 := by
  change HasDerivAt (fun t : ℝ ↦ p+t • ((S.a p/S.u p) • S.axis p)) _ _
  simpa using
    ((hasDerivAt_id (0:ℝ)).smul_const ((S.a p/S.u p) • S.axis p)).const_add p

def rate {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : E → V) (p : E) :=
  deriv (f ∘ S.axisLine p) 0

theorem along_axis {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {f : E → V} {p : E}
    (hf : DifferentiableAt ℝ f p) :
    HasDerivAt (f ∘ S.axisLine p) ((S.a p/S.u p) • fderiv ℝ f p (S.axis p)) 0 := by
  have h := hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 (S.axisLine_derivative p) (S.axisLine_zero p).symm
  simpa only [map_smul] using h

theorem along_axis_rate {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {f : E → V} {p : E}
    (hf : DifferentiableAt ℝ f p) : HasDerivAt (f ∘ S.axisLine p) (S.rate f p) 0 :=
  (S.along_axis hf).differentiableAt.hasDerivAt

theorem rate_a {p : E} (hp : p ∈ S.domain) : HasDerivAt (S.a ∘ S.axisLine p) 0 0 := by
  have h := S.along_axis (((contDiffOn_sectionValue S.smooth S.smoothAxis).contDiffAt
    (S.isOpen.mem_nhds hp)).differentiableAt (by simp))
  simpa only [a,critical_section_value_along_axis S.isOpen S.smooth S.smoothAxis S.equations.quartic S.unit hp
    (S.positive _ hp).ne' (S.critical _ hp),smul_zero] using h

theorem rate_cubic {p : E} (hm : S.IsMixed p) :
    HasDerivAt (S.cubic ∘ S.axisLine p) (S.jet p (S.axis p)) 0 := by
  have h := S.along_axis ((S.smooth.contDiffAt (S.isOpen.mem_nhds hm.1)).differentiableAt (by simp))
  have ha : S.a p≠0 := (S.positive _ hm.1).ne'
  have hh := ((S.rate_a hm.1).inv (show (S.a ∘ S.axisLine p) 0≠0 by simpa only [Function.comp_apply,axisLine_zero] using ha)).smul h
  change HasDerivAt (S.cubic ∘ S.axisLine p) _ 0 at hh
  change HasDerivAt _ ((S.u p)⁻¹ • fderiv ℝ S.field p (S.axis p)) _
  simpa only [Pi.inv_apply,Function.comp_apply,axisLine_zero,neg_zero,zero_div,zero_smul,add_zero,
    smul_smul,div_eq_mul_inv,zero_mul,← mul_assoc,inv_mul_cancel₀ ha,one_mul] using hh

theorem ratio_rates {p : E} (hm : S.IsMixed p) :
    S.rate S.u p/S.u p= -(1261750/734009)*(S.ratio p)^2*S.n p ∧
      S.rate S.ratio p=S.ratio p*S.n p*(4164755/4490408+(1261750/734009)*(S.ratio p)^2) := by
  obtain ⟨hu,hv,_,_⟩ := S.smooth_frame hm
  have du := S.along_axis (hu.differentiableAt (by simp))
  have dv := S.along_axis (hv.differentiableAt (by simp))
  have hn : S.u p≠0 := (norm_pos_iff.mpr hm.2.1).ne'
  have dt := dv.div du (show (S.u ∘ S.axisLine p) 0≠0 by simpa only [Function.comp_apply,axisLine_zero] using hn)
  change HasDerivAt (S.ratio ∘ S.axisLine p) _ 0 at dt
  obtain ⟨h₁,h₂⟩ := S.amplitude_rates hm
  simp only [Function.comp_apply,axisLine_zero,smul_eq_mul] at dt
  constructor
  · rw [rate,du.deriv,smul_eq_mul,ratio]
    linear_combination (norm := (field_simp [hn] <;> ring)) (S.u p)⁻¹^2*h₁
  · rw [rate,dt.deriv,ratio]
    linear_combination (norm := (field_simp [hn] <;> ring)) (S.u p)⁻¹^2*h₂ -
      (S.v p*(S.u p)⁻¹^3)*h₁

def shape (f g h : E → E) (p : E) : ℝ := cubicEntry (S.cubic p) (f p) (g p) (h p)

theorem shape_derivative {p : E} (hm : S.IsMixed p) {f g h : E → E}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (hh : DifferentiableAt ℝ h p) :
    HasDerivAt (S.shape f g h ∘ S.axisLine p)
      (jetEntry (S.jet p) (S.axis p) (f p) (g p) (h p)+
       cubicEntry (S.cubic p) (S.rate f p) (g p) (h p)+
       cubicEntry (S.cubic p) (f p) (S.rate g p) (h p)+
       cubicEntry (S.cubic p) (f p) (g p) (S.rate h p)) 0 := by
  have hk := hasDerivAt_K (S.rate_cubic hm) (S.along_axis_rate hf) (S.along_axis_rate hg)
  have hd := hk.inner ℝ (S.along_axis_rate hh)
  simp only [Function.comp_apply,axisLine_zero,inner_add_left] at hd
  change HasDerivAt _ (⟪K _ _ _,_⟫_ℝ+⟪K _ _ _,_⟫_ℝ+⟪K _ _ _,_⟫_ℝ+⟪K _ _ _,_⟫_ℝ) _
  convert hd using 1 <;> first | rfl | ring

end EuclideanMidpointRigidity.LiftedSection
