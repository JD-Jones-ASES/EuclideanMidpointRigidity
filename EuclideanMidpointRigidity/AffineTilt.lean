module

public import EuclideanMidpointRigidity.ReducedTilts
public import EuclideanMidpointRigidity.TiltRates

/-! # One tilted direction in the presence of a constant translation coefficient -/

public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.ThirdTiltLaws
open Endpoint

theorem SingleLaw.equal_derivative {W : Set ℝ} {Q P : ℝ → ℝ} {η α q : ℝ}
    (H : SingleLaw W η α Q P) (hW : IsOpen W) (hP : ContDiffOn ℝ ∞ P W) (hq : ∀ t ∈ W, Q t=q)
    (hα : α≠0) (hn : η-2*α-2≠0) {x y : ℝ} (hx : x ∈ W) (hy : y ∈ W) : deriv P x=deriv P y := by
  let U := (fun t : ℝ ↦ x+t) ⁻¹' W ∩ (fun t : ℝ ↦ y+t) ⁻¹' W
  let D := fun t : ℝ ↦ P (x+t)-P (y+t)
  have hU : IsOpen U := (hW.preimage (continuous_const.add continuous_id)).inter
    (hW.preimage (continuous_const.add continuous_id))
  have h₀ : (0:ℝ) ∈ U := by simpa [U] using And.intro hx hy
  have hs : ContDiffOn ℝ ∞ D U := (hP.comp (contDiff_const.add contDiff_id).contDiffOn (show MapsTo (fun s : ℝ ↦ x+s) U W from fun _ ht ↦ ht.1)).sub
    (hP.comp (contDiff_const.add contDiff_id).contDiffOn (show MapsTo (fun s : ℝ ↦ y+s) U W from fun _ ht ↦ ht.2))
  have hv : ∀ᶠ h in 𝓝[>] (0:ℝ), VanishingResponse η h (oddTilt α D 0) := by
    filter_upwards [H x hx,H y hy,small_segments hW hx,small_segments hW hy] with h ex ey sx sy
    apply (((ex.add (ey.smul (-1))).smul ((-2*α)⁻¹))).congr
    intro s hs'
    dsimp only [singleSource,oddTilt,D]
    rw [hq _ (sx s hs').1,hq _ (sx s hs').2,hq _ (sy s hs').1,hq _ (sy s hs').2]
    simp only [zero_add,zero_sub,← sub_eq_add_neg,tiltSlope]
    field_simp [hα] <;> ring
  have hd := (mul_eq_zero.mp (oddTilt_rate_conditions hU hs h₀ hv).1).resolve_left hn
  have df (z : ℝ) (hz : z ∈ W) : HasDerivAt (fun t : ℝ ↦ P (z+t)) (deriv P z) 0 := by
    have hp := ((hP.contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp)).hasDerivAt
    have hg := (hasDerivAt_id (0:ℝ)).const_add z
    simpa [Function.comp_def] using (show HasDerivAt P (deriv P z) (z+0) by simpa using hp).comp 0 hg
  have dd : deriv D 0=deriv P x-deriv P y := ((df x hx).fun_sub (df y hy)).deriv
  rw [iteratedDeriv_one,dd] at hd
  exact sub_eq_zero.mp hd

theorem SingleLaw.kill {W : Set ℝ} {Q P : ℝ → ℝ} {η α : ℚ} {q : ℝ} (hη : η≠0)
    (H : SingleLaw W η α Q P) (hW : IsOpen W) (hc : IsPreconnected W) (h₀ : 0 ∈ W)
    (hP : ContDiffOn ℝ ∞ P W) (hq : ∀ t ∈ W, Q t=q) (hα : α≠0) (hn : η-2*α-2≠0)
    (hdet : boundaryDet (BoundaryTest.tilted η 0 α hη) (BoundaryTest.linear η α hη)≠0) :
    q=0 ∧ ∀ t ∈ W, P t=P 0 := by
  have hα' : (α:ℝ)≠0 := by exact_mod_cast hα
  let v := deriv P 0
  have hd (t : ℝ) (ht : t ∈ W) : HasDerivAt (fun x ↦ P x-v*x) 0 t := by
    have he : deriv P t=v := H.equal_derivative hW hP hq hα' (by exact_mod_cast hn) ht h₀
    have hp := ((hP.contDiffAt (hW.mem_nhds ht)).differentiableAt (by simp)).hasDerivAt
    simpa only [he,id_eq,mul_one,sub_self] using hp.fun_sub ((hasDerivAt_id t).const_mul v)
  have affine (t : ℝ) (ht : t ∈ W) : P t=P 0+v*t := by
    have he := hW.is_const_of_deriv_eq_zero hc (fun x hx ↦ (hd x hx).differentiableAt.differentiableWithinAt)
      (fun x hx ↦ (hd x hx).deriv) ht h₀
    change P t-v*t=P 0-v*0 at he
    linarith only [he]
  let F := BoundaryTest.tilted η 0 α hη
  let G := BoundaryTest.linear η α hη
  have hz : ∀ᶠ h in 𝓝[>] (0:ℝ), VanishingResponse η h (fun s ↦ (-2*q)*F.source h s+(-4*(α:ℝ)*v)*G.source h s) := by
    filter_upwards [H 0 h₀,small_segments hW h₀] with h hh hs
    apply hh.congr
    intro s hm
    dsimp only [singleSource]
    rw [hq _ (hs s hm).1,hq _ (hs s hm).2,affine _ (hs s hm).1,affine _ (hs s hm).2]
    simp [F,G,BoundaryTest.tilted_source,BoundaryTest.linear_source,tiltAmplitude,tiltSlope]
    <;> ring
  obtain ⟨hq₀,hv⟩ := F.detect_pair G hη hdet hz
  have hv' : v=0 := (mul_eq_zero.mp hv).resolve_left (mul_ne_zero (by norm_num) hα')
  exact ⟨by linarith only [hq₀],fun t ht ↦ by simpa [hv'] using affine t ht⟩

end EuclideanMidpointRigidity.ThirdTiltLaws

