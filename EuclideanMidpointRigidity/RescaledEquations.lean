module

public import EuclideanMidpointRigidity.ShearPhysicalField
public import EuclideanMidpointRigidity.DilatedJets

/-! # Equations of the rescaled field at nonzero parameter -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
open Jet
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d
set_option backward.isDefEq.respectTransparency false
local instance (d : ℕ) : AddMonoid (Cubic d) :=
  (cubicNormedAddCommGroup d).toAddCommGroup.toAddCommMonoid.toAddMonoid

theorem obstruction_dilation {U : Set E} {G F : E → T} {b z : E} {r : ℝ} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) (hp : b+r • z ∈ U) (hF : F =ᶠ[𝓝 z] (fun w ↦ G (b+r • w))) (v : E) :
    obstruction (F z) (fderiv ℝ F z) v=r • obstruction (G (b+r • z)) (fderiv ℝ G (b+r • z)) v := by
  have hd : HasFDerivAt (fun y : E ↦ b+r • y) (r • ContinuousLinearMap.id ℝ E) z := by
    simpa only [Pi.smul_apply,id_eq,zero_add] using (hasFDerivAt_const b z).fun_add ((hasFDerivAt_id z).const_smul r)
  have hg := ((hG.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt.comp z hd
  have hf : fderiv ℝ F z=r • fderiv ℝ G (b+r • z) := by
    rw [(hg.congr_of_eventuallyEq hF).fderiv]
    ext w : 1
    simp
  rw [hF.eq_of_nhds,hf]
  simp only [obstruction,smul_apply,K_smul_coeff,K_smul_right]
  module

namespace HorizontalPatch
def sampled (S : LiftedSection d) {p : E} (R : ShearInverse S.axis S.domain p) (q : ℝ × E) := S.field (R.inverse q)

theorem smooth_sampled {S : LiftedSection d} {p : Space d} (R : ShearInverse S.axis S.domain p) : ContDiffOn ℝ ∞ (sampled S R) R.domain := S.smooth.comp R.smooth R.maps

def sixthPart (F : ℝ × E → T) (P : TimePolynomial) (q : ℝ × E) (v : E) :=
  value P (Tree.realize (fieldDerivatives (fun z ↦ F (q.1,z)) q.2) v) 0

def quarticPart (F : ℝ × E → T) (q : ℝ × E) (v : E) :=
  obstruction (F q) (fderiv ℝ (fun z ↦ F (q.1,z)) q.2) v

theorem sampled_equations {S : LiftedSection d} (H : HorizontalPatch S) {p : Space d} (R : ShearInverse S.axis S.domain p) {q : ℝ × E} (hq : q ∈ R.domain) (hn : q.1≠0) (v : E) :
    quarticPart (sampled S R) q v=0 ∧
    sixthPart (sampled S R) higherSixth q v+q.1^2 • sixthPart (sampled S R) affineSixth q v=0 := by
  obtain ⟨U,G,hU,hy,hG,hQ,hF⟩ := H.rescaled_chart R hq hn
  let y := position S q.1⁻¹ p+q.1 • q.2
  have hd := dilation_jets hU hG hy hF
  have ha := value_dilation hd v affineSixth 1 affineSixth_spatialOrder
  have hh := value_dilation hd v higherSixth 3 higherSixth_spatialOrder
  let f := Tree.realize (fieldDerivatives G y) v
  have h := hQ.sixth hy v
  change value affineSixth f 0+value higherSixth f 0=0 at h
  constructor
  · have h₄ := obstruction_dilation hU hG hy hF v
    rw [hQ.quartic hy v,smul_zero] at h₄
    exact h₄
  · change sixthPart (sampled S R) higherSixth q v=q.1^3 • value higherSixth f 0 at hh
    change sixthPart (sampled S R) affineSixth q v=q.1^1 • value affineSixth f 0 at ha
    rw [hh,ha,pow_one,smul_smul,← pow_succ,← smul_add,add_comm,h,smul_zero]

end HorizontalPatch
end EuclideanMidpointRigidity

