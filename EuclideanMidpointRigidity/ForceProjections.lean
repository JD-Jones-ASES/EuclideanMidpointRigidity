module

public import EuclideanMidpointRigidity.ForceNormalization
public import EuclideanMidpointRigidity.FrameRates
public import EuclideanMidpointRigidity.DifferentiatedCubic

/-! # The two resonant projections of the normalized force -/

@[expose] public section
noncomputable section
open Filter
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity.LiftedSection
open Quartic
variable {d : ℕ} (S : LiftedSection d)
local notation "E" => Space d

def phiX : ℝ := 191351125/19084234
def phiY : ℝ := -660275/2245204

theorem drift_eq {p : E} (hm : S.IsMixed p) :
    S.drift p= -(1261750/734009)*(S.ratio p)^2*(S.core p).n := by
  rw [drift,(S.ratio_rates hm).1,← S.shape_n p]
  rfl

theorem psi_components {p : E} (hm : S.IsMixed p) :
    ⟪S.psi p,S.x p⟫_ℝ=phiX*(S.ratio p)^2*(S.core p).n ∧
    ⟪S.psi p,S.y p⟫_ℝ=phiY*S.ratio p*(S.core p).n := by
  have hn := S.normalized_entries hm
  have ht : (S.core p).t=S.ratio p := rfl
  obtain ⟨hx,_,hxy,_,_,_,_,_⟩ := S.plane_data hm
  have dx := (S.smooth_frame hm).2.2.1.differentiableAt (by simp)
  obtain ⟨_,_,xx,_,xy,_⟩ := S.internal_rotations hm
  have r₁ : ⟪S.rMap p (S.x p),S.x p⟫_ℝ=(S.core p).r11 := rfl
  have r₂ : ⟪S.rMap p (S.x p),S.y p⟫_ℝ=(S.core p).r21 := rfl
  have z₁ : ⟪S.zMap p (S.x p),S.x p⟫_ℝ=(S.core p).z11 := rfl
  have z₂ : ⟪S.zMap p (S.x p),S.y p⟫_ℝ=(S.core p).z12 := rfl
  simp only [psi,theta,axialU,map_smul,inner_add_left,inner_sub_left,real_inner_smul_left,
    S.rate_coordinate dx,xx,xy,r₁,r₂,z₁,z₂,real_inner_self_eq_norm_sq,hx,hxy,S.drift_eq hm,
    omega,hn.r11,hn.r21,hn.z11,hn.z12,hn.m,ht,phiX,phiY,ResonantPlane.k]
  constructor <;> ring

theorem force_projection {p : E} (hm : S.IsMixed p) {f : E → E} (df : DifferentiableAt ℝ f p) {v : ℝ}
    (dv : HasDerivAt ((fun q ↦ ⟪S.psi q,f q⟫_ℝ) ∘ S.axisLine p) v 0) :
    v+2*S.drift p*⟪S.psi p,f p⟫_ℝ-⟪S.psi p,S.rate f p⟫_ℝ-⟪S.forceTerm p,f p⟫_ℝ=
      (S.a p)^4/(S.u p)^2*⟪S.axialU p,f p⟫_ℝ := by
  have du := S.along_axis_rate ((S.smooth_frame hm).1.differentiableAt (by simp))
  have h₁ := (S.normalized_force_rate hm).inner ℝ (S.along_axis_rate df)
  have h₂ := (du.mul du).mul dv
  have near : ∀ᶠ t in 𝓝 (0:ℝ), S.IsMixed (S.axisLine p t) :=
    (S.axisLine_derivative p).continuousAt (S.axisLine_zero p ▸ S.eventually_mixed hm)
  have eq : ∀ᶠ t in 𝓝 (0:ℝ), ⟪S.force (S.axisLine p t),f (S.axisLine p t)⟫_ℝ=
      (S.u (S.axisLine p t)*S.u (S.axisLine p t))*⟪S.psi (S.axisLine p t),f (S.axisLine p t)⟫_ℝ := by
    filter_upwards [near] with t ht
    rw [S.force_eq ht,real_inner_smul_left,pow_two]
  have h := h₁.unique (h₂.congr_of_eventuallyEq eq)
  simp only [Function.comp_apply,axisLine_zero,Pi.mul_apply,S.force_eq hm,real_inner_smul_left,inner_add_left] at h
  have hu : S.u p≠0 := (norm_pos_iff.mpr hm.2.1).ne'
  unfold drift
  linear_combination (norm := (field_simp [hu]; ring)) -((S.u p)⁻¹^2)*h

theorem projected_equations {p : E} (hm : S.IsMixed p) :
    let t := S.ratio p
    let n := (S.core p).n
    let v := S.rate S.ratio p
    let w := S.rate (S.shape S.x S.y S.y) p
    phiX*(2*t*v*n+t^2*w)+2*S.drift p*(phiX*t^2*n)-⟪S.psi p,S.rate S.x p⟫_ℝ-⟪S.forceTerm p,S.x p⟫_ℝ=
      (7/13)*(S.a p)^4/(S.u p)^2 ∧
    phiY*(v*n+t*w)+2*S.drift p*(phiY*t*n)-⟪S.psi p,S.rate S.y p⟫_ℝ-⟪S.forceTerm p,S.y p⟫_ℝ=0 := by
  obtain ⟨hu,hv,hx,hy⟩ := S.smooth_frame hm
  have dx := hx.differentiableAt (by simp)
  have dy := hy.differentiableAt (by simp)
  have dN := (S.shape_derivative hm dx dy dy).differentiableAt.hasDerivAt
  change HasDerivAt ((S.shape S.x S.y S.y) ∘ S.axisLine p) (S.rate (S.shape S.x S.y S.y) p) 0 at dN
  have dr : DifferentiableAt ℝ S.ratio p :=
    (hv.div hu (show S.u p≠0 from (norm_pos_iff.mpr hm.2.1).ne')).differentiableAt (by simp)
  have dt := S.along_axis_rate dr
  have near : ∀ᶠ z in 𝓝 (0:ℝ), S.IsMixed (S.axisLine p z) :=
    (S.axisLine_derivative p).continuousAt (S.axisLine_zero p ▸ S.eventually_mixed hm)
  have ex : ∀ᶠ z in 𝓝 (0:ℝ), ⟪S.psi (S.axisLine p z),S.x (S.axisLine p z)⟫_ℝ=
      phiX*(S.ratio (S.axisLine p z)*S.ratio (S.axisLine p z)*S.shape S.x S.y S.y (S.axisLine p z)) := by
    filter_upwards [near] with z hz
    have h := (S.psi_components hz).1
    change _=phiX*(S.ratio _)^2*S.shape S.x S.y S.y _ at h
    linear_combination h
  have ey : ∀ᶠ z in 𝓝 (0:ℝ), ⟪S.psi (S.axisLine p z),S.y (S.axisLine p z)⟫_ℝ=
      phiY*(S.ratio (S.axisLine p z)*S.shape S.x S.y S.y (S.axisLine p z)) := by
    filter_upwards [near] with z hz
    have h := (S.psi_components hz).2
    change _=phiY*S.ratio _*S.shape S.x S.y S.y _ at h
    linear_combination h
  have q₁ := S.force_projection hm dx (((((dt.mul dt).mul dN).const_mul phiX)).congr_of_eventuallyEq ex)
  have q₂ := S.force_projection hm dy (((dt.mul dN).const_mul phiY).congr_of_eventuallyEq ey)
  obtain ⟨h₀,_,hxy,_,_,_,_,_⟩ := S.plane_data hm
  simp only [Function.comp_apply,axisLine_zero,Pi.mul_apply,axialU,real_inner_smul_left,real_inner_self_eq_norm_sq,
    h₀,hxy,one_pow,mul_one,mul_zero,(S.psi_components hm).1,(S.psi_components hm).2,
    show S.shape S.x S.y S.y p=(S.core p).n from rfl] at q₁ q₂
  exact ⟨by linear_combination q₁,by linear_combination q₂⟩

end EuclideanMidpointRigidity.LiftedSection

