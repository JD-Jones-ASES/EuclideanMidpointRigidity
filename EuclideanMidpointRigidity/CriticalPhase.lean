module

public import EuclideanMidpointRigidity.CriticalSection
public import EuclideanMidpointRigidity.LocalFlow

/-! # A parameter-dependent flow for critical cubic directions -/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology ContDiff InnerProductSpace
namespace EuclideanMidpointRigidity

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d
abbrev AxisPhase (d : ℕ) := (Space d × Space d) × ℝ
local notation "S" => AxisPhase d

def criticalPhaseDomain (Ω : Set E) : Set S := {v | v.1.1 ∈ Ω ∧ v.2≠0}
def criticalPhaseVector (C : E → Coeff) (v : S) : S := ((v.1.2,liftStep v.2 (fderiv ℝ C v.1.1) v.1.2),0)

theorem isOpen_criticalPhaseDomain {Ω : Set E} (hΩ : IsOpen Ω) : IsOpen (criticalPhaseDomain Ω) :=
  (hΩ.preimage (continuous_fst.comp continuous_fst)).inter (isClosed_singleton.isOpen_compl.preimage continuous_snd)

set_option backward.isDefEq.respectTransparency false in
theorem smooth_criticalPhaseVector {Ω : Set E} {C : E → Coeff} (hΩ : IsOpen Ω) (hc : ContDiffOn ℝ ∞ C Ω) :
    ContDiffOn ℝ ∞ (criticalPhaseVector C) (criticalPhaseDomain Ω) := by
  let D := criticalPhaseDomain Ω
  have hx : ContDiffOn ℝ ∞ (fun v : S ↦ v.1.1) D := (contDiff_fst.comp contDiff_fst).contDiffOn
  have he : ContDiffOn ℝ ∞ (fun v : S ↦ v.1.2) D := (contDiff_snd.comp contDiff_fst).contDiffOn
  have hm : MapsTo (fun v : S ↦ v.1.1) D Ω := fun _ hv ↦ hv.1
  have hJ : ContDiffOn ℝ ∞ (fun v : S ↦ fderiv ℝ C v.1.1) D := (hc.fderiv_of_isOpen hΩ (by simp)).comp hx hm
  have hj := hJ.clm_apply he
  let inc : Coeff →L[ℝ] (E →L[ℝ] E →L[ℝ] E) := (cubicSubspace d).subtypeL
  have hinc := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) («E» := Coeff) (F := E →L[ℝ] E →L[ℝ] E) inc
  have hB : ContDiffOn ℝ ∞ (fun v : S ↦ inc (fderiv ℝ C v.1.1 v.1.2)) D := hinc.comp_contDiffOn hj
  have hden : ContDiffOn ℝ ∞ (fun v : S ↦ (2*v.2)⁻¹) D :=
    (contDiffOn_const.mul contDiffOn_snd).inv (fun v hv ↦ mul_ne_zero (by norm_num) hv.2)
  exact (he.prodMk (hden.smul ((hB.clm_apply he).clm_apply he))).prodMk contDiffOn_const

theorem hasDerivAt_first_projection {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] {γ : ℝ → A × B} {v : A × B} {s : ℝ} (h : HasDerivAt γ v s) :
    HasDerivAt (fun t ↦ (γ t).1) v.1 s :=
  (ContinuousLinearMap.fst ℝ A B).hasFDerivAt.comp_hasDerivAt s h

theorem hasDerivAt_second_projection {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] {γ : ℝ → A × B} {v : A × B} {s : ℝ} (h : HasDerivAt γ v s) :
    HasDerivAt (fun t ↦ (γ t).2) v.2 s :=
  (ContinuousLinearMap.snd ℝ A B).hasFDerivAt.comp_hasDerivAt s h

theorem critical_phase_invariants {Ω : Set E} {C : E → Coeff} (hΩ : IsOpen Ω) (hc : ContDiffOn ℝ ∞ C Ω)
    (hQ : QuarticOn Ω C) {γ : ℝ → S} {b : ℝ} (hγ : MapsTo γ (Icc 0 b) (criticalPhaseDomain Ω))
    (hd : ∀ s ∈ Icc 0 b, HasDerivAt γ (criticalPhaseVector C (γ s)) s)
    (ha : (γ 0).2≠0) (hu : ‖(γ 0).1.2‖=1)
    (hcrit : K (C (γ 0).1.1) (γ 0).1.2 (γ 0).1.2=(γ 0).2 • (γ 0).1.2) :
    ∀ s ∈ Icc 0 b, (γ s).2=(γ 0).2 ∧ ‖(γ s).1.2‖=1 ∧
      K (C (γ s).1.1) (γ s).1.2 (γ s).1.2=(γ 0).2 • (γ s).1.2 := by
  let x := fun s ↦ (γ s).1.1
  let e := fun s ↦ (γ s).1.2
  let a := (γ 0).2
  have hda (s : ℝ) (hs : s ∈ Icc 0 b) : HasDerivAt (fun u ↦ (γ u).2) 0 s :=
    hasDerivAt_second_projection (hd s hs)
  have heq : ∀ s ∈ Icc 0 b, (γ s).2=a := constant_of_has_deriv_right_zero (HasDerivAt.continuousOn hda)
    (fun s hs ↦ (hda s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
  have hdx (s : ℝ) (hs : s ∈ Icc 0 b) : HasDerivAt x (e s) s :=
    hasDerivAt_first_projection (hasDerivAt_first_projection (hd s hs))
  have hde (s : ℝ) (hs : s ∈ Icc 0 b) : HasDerivAt e (liftStep a (fderiv ℝ C (x s)) (e s)) s := by
    rw [← heq s hs]
    exact hasDerivAt_second_projection (hasDerivAt_first_projection (hd s hs))
  have hdom : MapsTo x (Icc 0 b) Ω := fun s hs ↦ (hγ hs).1
  have hcr := critical_lift_preserves hΩ hc (fun x hx w ↦ hQ hx w) ha x e hdom hdx hde hcrit
  have hsp := critical_lift_speed ha (fun s ↦ C (x s)) (fun s ↦ fderiv ℝ C (x s)) e hcr
    (fun s hs ↦ hQ (hdom hs) (e s)) hde
  exact fun s hs ↦ ⟨heq s hs,(hsp s hs).trans hu,hcr s hs⟩

end EuclideanMidpointRigidity

