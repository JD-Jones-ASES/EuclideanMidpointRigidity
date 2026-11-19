module

public import EuclideanMidpointRigidity.RescaledEquations
public import EuclideanMidpointRigidity.SpatialSlices

/-! # The limiting quartic and quadratic-amplitude sixth equations -/

public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.HorizontalPatch
open Jet
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d
set_option backward.isDefEq.respectTransparency false

theorem continuous_quarticPart {U : Set (ℝ × E)} {F : ℝ × E → T} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (v : E) :
    ContinuousOn (fun q ↦ quarticPart F q v) U := by
  let J := fun q ↦ (fderiv ℝ F q).comp (ContinuousLinearMap.inr ℝ ℝ E)
  have hJ : ContinuousOn J U := (hF.continuousOn_fderiv_of_isOpen hU (by simp)).clm_comp continuousOn_const
  have hK {c : ℝ × E → T} {x y : ℝ × E → E} (hc : ContinuousOn c U) (hx : ContinuousOn x U) (hy : ContinuousOn y U) :
      ContinuousOn (fun q ↦ K (c q) (x q) (y q)) U := by
    let L : T →L[ℝ] (E →L[ℝ] E →L[ℝ] E) := (cubicSubspace d).subtypeL
    exact ((L.continuous.comp_continuousOn hc).clm_apply hx).clm_apply hy
  have hv : ContinuousOn (fun _ : ℝ × E ↦ v) U := continuousOn_const
  have hb := hK hF.continuousOn hv hv
  have h₁ := hK hF.continuousOn hv (hK (hJ.clm_apply hv) hv hv)
  have h₂ := hK (hJ.clm_apply hb) hv hv
  have h₃ := hK (hJ.clm_apply hv) hv hb
  have hsp (q : ℝ × E) (hq : q ∈ U) : fderiv ℝ (fun z ↦ F (q.1,z)) q.2=J q :=
    (((hF.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt.comp q.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2)).fderiv
  apply ((((continuousOn_const (c := (2:ℝ))).smul h₁).add ((continuousOn_const (c := (5:ℝ))).smul h₂)).sub ((continuousOn_const (c := (4:ℝ))).smul h₃)).congr
  intro q hq
  simp only [quarticPart,hsp q hq,obstruction,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,← Nat.cast_smul_eq_nsmul ℝ]
  norm_num

theorem limit_equations {S : LiftedSection d} (H : HorizontalPatch S) {p : Space d} (R : ShearInverse S.axis S.domain p) {z : E} (hz : (0,z) ∈ R.domain) (v : E) :
    quarticPart (sampled S R) (0,z) v=0 ∧ sixthPart (sampled S R) higherSixth (0,z) v=0 := by
  let i := fun r : ℝ ↦ (r,z)
  have hi : Continuous i := continuous_id.prodMk continuous_const
  have hver : ∀ᶠ r in 𝓝 (0:ℝ), i r ∈ R.domain := hi.continuousAt (R.isOpen.mem_nhds hz)
  let F := sampled S R
  have hF : ContDiffOn ℝ ∞ F R.domain := smooth_sampled R
  have h₄ : ContinuousAt (fun r ↦ quarticPart F (i r) v) 0 := ContinuousAt.comp (f := i) (x := (0:ℝ))
    ((continuous_quarticPart R.isOpen hF v).continuousAt (R.isOpen.mem_nhds hz)) hi.continuousAt
  have h₆ (P : TimePolynomial) : ContinuousAt (fun r ↦ sixthPart F P (i r) v) 0 :=
    ContinuousAt.comp (f := i) (x := (0:ℝ)) ((smooth_family_spatial_value R.isOpen hF P v).continuousAt (R.isOpen.mem_nhds hz)) hi.continuousAt
  constructor
  · exact eq_at_zero_of_punctured h₄ continuousAt_const (hver.mono fun r hr hn ↦ (H.sampled_equations R hr hn v).1)
  · have hc : ContinuousAt (fun r ↦ sixthPart F higherSixth (i r) v+r^2 • sixthPart F affineSixth (i r) v) 0 :=
      (h₆ higherSixth).add ((continuousAt_id.pow 2).smul (h₆ affineSixth))
    have h := eq_at_zero_of_punctured hc (continuousAt_const (y := (0:E))) (hver.mono fun r hr hn ↦ (H.sampled_equations R hr hn v).2)
    simpa only [zero_pow (by decide : 2≠0),zero_smul,add_zero] using h

theorem fixed_limit_axis {S : LiftedSection d} (H : HorizontalPatch S) {p : Space d} (R : ShearInverse S.axis S.domain p) {r : ℝ} (hr : 0<r) (hB : ∀ z ∈ ball (0:E) r, (0,z) ∈ R.domain) {z : E} (hz : z ∈ ball (0:E) r) :
    S.axis (R.inverse (0,z))=S.axis p := by
  have hder (y : E) (hy : y ∈ ball (0:E) r) : HasFDerivAt (𝕜 := ℝ) (fun w ↦ S.axis (R.inverse (0,w))) 0 y := by
    have hh := ((S.smoothAxis.contDiffAt (S.isOpen.mem_nhds (R.maps (hB y hy)))).differentiableAt (by simp)).hasFDerivAt.comp y (R.spatial (0,y) (hB y hy))
    let A := fderiv ℝ S.axis (R.inverse (0,y))
    change HasFDerivAt (𝕜 := ℝ) (fun w ↦ S.axis (R.inverse (0,w))) (A.comp ((0:ℝ) • ContinuousLinearMap.id ℝ E-A)) y at hh
    have hz : A.comp ((0:ℝ) • ContinuousLinearMap.id ℝ E-A)=0 := by
      ext v : 1
      change A ((0:ℝ) • v-A v)=0
      rw [zero_smul,zero_sub,map_neg,show A (A v)=0 from H.square_zero (R.maps (hB y hy)) v,neg_zero]
    rwa [hz] at hh
  have h := isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball _ _).isPreconnected
    (fun y hy ↦ (hder y hy).differentiableAt.differentiableWithinAt) (fun {y} hy ↦ (hder y hy).fderiv) hz (mem_ball_self hr)
  rwa [R.center 0 R.origin] at h

end EuclideanMidpointRigidity.HorizontalPatch

