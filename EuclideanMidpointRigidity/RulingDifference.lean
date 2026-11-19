module

public import EuclideanMidpointRigidity.RulingResponses
public import EuclideanMidpointRigidity.LineDifference

/-! # Removing the translation source from the coupled endpoint laws -/

public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
open Endpoint

private theorem reflectedTilt_difference (κ h t x s : ℝ) (Q P : ℝ → ℝ) :
    lineDifference t (fun y ↦ reflectedTilt κ h Q P y s) x=
      reflectedTilt κ h (lineDifference t Q) (lineDifference t P) x s := by
  have ha (a : ℝ) : x+a+s=x+s+a := by ring
  have hs (a : ℝ) : x+a-s=x-s+a := by ring
  dsimp only [lineDifference,reflectedTilt]
  rw [ha (3*t),hs (3*t),ha (2*t),hs (2*t),ha t,hs t]
  ring

theorem RulingResponseLaws.mono {W U : Set ℝ} {η κ : ℝ} {Q P : ℝ → ℝ} (H : RulingResponseLaws W η κ Q P) (hU : U ⊆ W) :
    RulingResponseLaws U η κ Q P :=
  ⟨H.smoothQ.mono hU,H.smoothP.mono hU,fun x hx ↦ H.translation x (hU hx),fun x hx ↦ H.tilt x (hU hx)⟩

theorem RulingResponseLaws.difference_tilt {W : Set ℝ} {η κ : ℝ} {Q P : ℝ → ℝ}
    (H : RulingResponseLaws W η κ Q P) (hW : IsOpen W) (hc : IsPreconnected W) (t : ℝ) :
    ∀ x ∈ differenceDomain W t, ∀ᶠ h in 𝓝[>] (0:ℝ), VanishingResponse η h (oddTilt κ (lineDifference t P) x) := by
  intro x hx
  have hode (y : ℝ) (hy : y ∈ W) : iteratedDeriv 3 Q y=(1:ℝ)^2*iteratedDeriv 1 Q y := by simpa using H.translation_equation hW y hy
  obtain ⟨a,b,c,he⟩ := exponential_form_of_third hW hc H.smoothQ hx.1.1.1 one_ne_zero hode
  have he' (y : ℝ) (hy : y ∈ W) : Q y=a+b*Real.exp y+c*Real.exp (-y) := by simpa using he y hy
  have hq (y : ℝ) (hy : y ∈ differenceDomain W t) := lineDifference_exponential hy he'
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp ((isOpen_differenceDomain hW t).mem_nhds hx)
  filter_upwards [H.tilt x hx.1.1.1,H.tilt (x+t) hx.1.1.2,H.tilt (x+2*t) hx.1.2,H.tilt (x+3*t) hx.2,
    self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)] with h h₀ h₁ h₂ h₃ hpos hsmall
  have hh : 0<h := hpos
  have hshift (hval : ℝ) (habs : |hval|≤h) : x+hval ∈ differenceDomain W t := by
    apply hball
    simpa only [mem_ball,Real.dist_eq,add_sub_cancel_left] using habs.trans_lt hsmall
  have hd := (h₃.add (h₀.smul (-1))).add (((h₂.add (h₁.smul (-1))).smul (-differenceWeight t)))
  apply (hd.smul ((-2*tiltFactor κ h)⁻¹)).congr
  intro s hs
  have eQ₁ := hq _ (hshift s (abs_le.mpr hs))
  have eQ₂ := hq _ (hshift (-s) (by simpa only [abs_neg] using abs_le.mpr hs))
  let ea := fun y ↦ reflectedTilt κ h Q P y s
  have hcomb : ea (x+3*t)+(-1)*ea x+(-differenceWeight t)*(ea (x+2*t)+(-1)*ea (x+t))=
      reflectedTilt κ h (lineDifference t Q) (lineDifference t P) x s := by
    rw [← reflectedTilt_difference]
    change _=ea (x+3*t)-ea x-differenceWeight t*(ea (x+2*t)-ea (x+t))
    ring
  change (-2*tiltFactor κ h)⁻¹*(ea (x+3*t)+(-1)*ea x+(-differenceWeight t)*(ea (x+2*t)+(-1)*ea (x+t)))=_
  rw [hcomb]
  dsimp only [reflectedTilt,oddTilt]
  rw [eQ₁,show x-s=x+(-s) by ring,eQ₂]
  field_simp [tiltFactor_ne_zero (κ := κ) hh]
  <;> ring

/-- A single sixth-order scalar equation works at every spectral parameter. -/
theorem RulingResponseLaws.difference_equation {W : Set ℝ} {η κ : ℝ} {Q P : ℝ → ℝ}
    (H : RulingResponseLaws W η κ Q P) (hW : IsOpen W) (hc : IsPreconnected W) {x t : ℝ}
    (hx : x ∈ differenceDomain W t) :
    lineDifference t (fun y ↦ iteratedDeriv 3 P y-tiltRate κ*iteratedDeriv 1 P y) x=0 := by
  have he := oddTilt_differential_equation (isOpen_differenceDomain hW t) (smooth_lineDifference H.smoothP t)
    (H.difference_tilt hW hc t) x hx
  rw [iteratedDeriv_lineDifference hW H.smoothP hx,iteratedDeriv_lineDifference hW H.smoothP hx] at he
  dsimp only [lineDifference] at he ⊢
  linarith only [he]

end EuclideanMidpointRigidity

