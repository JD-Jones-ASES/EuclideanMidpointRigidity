module

public import EuclideanMidpointRigidity.ResonantDerivative

/-! # Differential consequences of the three persistent resonant cubic identities -/

@[expose] public section
noncomputable section
open Filter
open scoped Topology ContDiff InnerProductSpace
namespace EuclideanMidpointRigidity.LiftedSection
open Quartic
variable {d : ℕ} (S : LiftedSection d)
local notation "E" => Space d

theorem shape_n (p : E) : S.shape S.x S.y S.y p=S.n p := by
  unfold shape cubicEntry n
  rw [K_symm (S.cubic p) (S.x p) (S.y p),K_selfAdjoint]

def ratioSource (t n : ℝ) := t^2*n^2*(4164755/4490408+(1261750/734009)*t^2)

theorem differentiated_relations {p : E} (hm : S.IsMixed p) :
    let t := S.ratio p
    let N := S.shape S.x S.y S.y
    let M := S.shape S.x S.x S.y
    let X := S.shape S.x S.x S.x
    let Y := S.shape S.y S.y S.y
    let k := ResonantPlane.k
    let src := ratioSource t (N p)
    t*S.rate M p+k*(t^2*S.rate N p)+k*src=0 ∧
    S.rate X p-(650/153)*k*(t^2*S.rate N p)-2*(650/153)*k*src=0 ∧
    t^3*S.rate Y p+(159/1300)*(t^2*S.rate N p)-(159/1300)*src=0 := by
  let M := S.shape S.x S.x S.y
  let N := S.shape S.x S.y S.y
  let X := S.shape S.x S.x S.x
  let Y := S.shape S.y S.y S.y
  let t := S.ratio p
  let k := ResonantPlane.k
  obtain ⟨hu,hv,hx,hy⟩ := S.smooth_frame hm
  have dx := hx.differentiableAt (by simp)
  have dy := hy.differentiableAt (by simp)
  have dm : HasDerivAt (M ∘ S.axisLine p) (S.rate M p) 0 := (S.shape_derivative hm dx dx dy).differentiableAt.hasDerivAt
  have dn : HasDerivAt (N ∘ S.axisLine p) (S.rate N p) 0 := (S.shape_derivative hm dx dy dy).differentiableAt.hasDerivAt
  have dX : HasDerivAt (X ∘ S.axisLine p) (S.rate X p) 0 := (S.shape_derivative hm dx dx dx).differentiableAt.hasDerivAt
  have dY : HasDerivAt (Y ∘ S.axisLine p) (S.rate Y p) 0 := (S.shape_derivative hm dy dy dy).differentiableAt.hasDerivAt
  have dr : DifferentiableAt ℝ S.ratio p :=
    (hv.div hu (show S.u p≠0 from (norm_pos_iff.mpr hm.2.1).ne')).differentiableAt (by simp)
  have dt := S.along_axis_rate dr
  have near : ∀ᶠ z in 𝓝 (0:ℝ), S.IsMixed (S.axisLine p z) :=
    (S.axisLine_derivative p).continuousAt (S.axisLine_zero p ▸ S.eventually_mixed hm)
  have eqm : ∀ᶠ z in 𝓝 (0:ℝ), M (S.axisLine p z)= -k*(S.ratio (S.axisLine p z)*N (S.axisLine p z)) := by
    filter_upwards [near] with z hz
    have h := (S.normalized_entries hz).m
    change M _= -k*S.ratio _*N _ at h
    linear_combination h
  have eqx : ∀ᶠ z in 𝓝 (0:ℝ), X (S.axisLine p z)= ((650/153)*k)*
      (S.ratio (S.axisLine p z)*S.ratio (S.axisLine p z)*N (S.axisLine p z)) := by
    filter_upwards [near] with z hz
    have h := (S.normalized_entries hz).d1
    change X _= (650/153)*k*(S.ratio _)^2*N _ at h
    linear_combination h
  have eqy : ∀ᶠ z in 𝓝 (0:ℝ), S.ratio (S.axisLine p z)*Y (S.axisLine p z)= -(159/1300)*N (S.axisLine p z) :=
    near.mono fun _ hz ↦ (S.normalized_entries hz).d2
  have e₁ := dm.unique (((dt.mul dn).const_mul (-k)).congr_of_eventuallyEq eqm)
  have e₂ := dX.unique ((((dt.mul dt).mul dn).const_mul ((650/153)*k)).congr_of_eventuallyEq eqx)
  have e₃ := (dt.mul dY).unique ((dn.const_mul (-(159/1300))).congr_of_eventuallyEq eqy)
  have h := (S.ratio_rates hm).2
  rw [← S.shape_n p] at h
  change S.rate S.ratio p=t*N p*(4164755/4490408+(1261750/734009)*t^2) at h
  simp only [Pi.mul_apply,Function.comp_apply,axisLine_zero] at e₁ e₂ e₃
  rw [h] at e₁ e₂ e₃
  change t*S.rate M p+k*(t^2*S.rate N p)+k*ratioSource t (N p)=0 ∧
    S.rate X p-(650/153)*k*(t^2*S.rate N p)-2*(650/153)*k*ratioSource t (N p)=0 ∧
    t^3*S.rate Y p+(159/1300)*(t^2*S.rate N p)-(159/1300)*ratioSource t (N p)=0
  have hy₀ : t*Y p= -(159/1300)*N p := (S.normalized_entries hm).d2
  dsimp only [t,ratioSource] at *
  exact ⟨by linear_combination S.ratio p*e₁,by linear_combination e₂,
    by linear_combination (S.ratio p)^2*e₃-(S.ratio p)^2*N p*(4164755/4490408+(1261750/734009)*(S.ratio p)^2)*hy₀⟩

end EuclideanMidpointRigidity.LiftedSection

