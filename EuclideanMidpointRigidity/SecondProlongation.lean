module

public import EuclideanMidpointRigidity.SpatialProlongation

/-! # Two spatial differentiations of the quartic with its test vector fixed -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

set_option backward.isDefEq.respectTransparency false in
theorem second_prolongation_of_quartic {Ω : Set E} {C : E → Coeff}
    (hΩ : IsOpen Ω) (smooth : ContDiffOn ℝ ∞ C Ω) (hm : QuarticOn Ω C)
    {p : E} (hp : p ∈ Ω) (l z : E) :
    let J := fderiv ℝ C
    let H := fderiv ℝ J
    let T := fderiv ℝ H
    obstruction (C p) (T p l l) z + (2:ℝ) • obstruction (J p l) (H p l) z +
      obstruction (H p l l) (J p) z = 0 := by
  let J := fderiv ℝ C
  let H := fderiv ℝ J
  let T := fderiv ℝ H
  let line := fun t : ℝ ↦ p+t • l
  have hline : HasDerivAt line l 0 := by
    simpa [line] using ((hasDerivAt_id (0:ℝ)).smul_const l).const_add p
  have h₀ : line 0=p := by simp [line]
  have hC := smooth.contDiffAt (hΩ.mem_nhds hp)
  have hJ : ContDiffAt ℝ 2 J p := hC.fderiv_right (by simp)
  have hH : ContDiffAt ℝ 1 H p := hJ.fderiv_right (by norm_num)
  have hc := (hC.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hline h₀.symm
  have hj := (hJ.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hline h₀.symm
  have hh := (hH.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hline h₀.symm
  letI : AddZeroClass Coeff :=
    (cubicNormedAddCommGroup d).toAddCommGroup.toAddCommMonoid.toAddMonoid.toAddZeroClass
  have hjl : HasDerivAt (fun t ↦ J (line t) l) (H p l l) 0 := by
    simpa only [Function.comp_apply,map_zero,add_zero] using hj.clm_apply (hasDerivAt_const 0 l)
  have hhl : HasDerivAt (fun t ↦ H (line t) l) (T p l l) 0 := by
    simpa only [Function.comp_apply,map_zero,add_zero] using hh.clm_apply (hasDerivAt_const 0 l)
  have hd := (hasDerivAt_obstruction hc hhl z).fun_add (hasDerivAt_obstruction hjl hj z)
  have hnear : ∀ᶠ t in 𝓝 (0:ℝ), line t ∈ Ω := hline.continuousAt (h₀ ▸ hΩ.mem_nhds hp)
  have hz : HasDerivAt (fun t ↦ obstruction (C (line t)) (H (line t) l) z+
      obstruction (J (line t) l) (J (line t)) z) 0 0 :=
    (hasDerivAt_const 0 (0:E)).congr_of_eventuallyEq
      (hnear.mono fun t ht ↦ prolongation_of_quartic hΩ (smooth.of_le (by simp)) hm ht l z)
  have heq := hd.unique hz
  simp only [Function.comp_apply,h₀] at heq
  change obstruction (C p) (T p l l) z + (2:ℝ) • obstruction (J p l) (H p l) z +
    obstruction (H p l l) (J p) z = 0
  linear_combination (norm := module) heq

theorem second_prolongation_of_localMidpointInvariance {Ω : Set E} {C : E → Coeff}
    (hΩ : IsOpen Ω) (smooth : ContDiffOn ℝ ∞ C Ω) (hm : LocalMidpointInvariance Ω C)
    {p : E} (hp : p ∈ Ω) (l z : E) :
    let J := fderiv ℝ C
    let H := fderiv ℝ J
    let T := fderiv ℝ H
    obstruction (C p) (T p l l) z + (2:ℝ) • obstruction (J p l) (H p l) z +
      obstruction (H p l l) (J p) z = 0 :=
  second_prolongation_of_quartic hΩ smooth (QuarticOn.of_midpoint hΩ (smooth.of_le (by simp)) hm) hp l z

end EuclideanMidpointRigidity
