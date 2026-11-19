module

public import EuclideanMidpointRigidity.EndpointVariations

/-! # Reversing the dual chord and differentiating midpoint complementarity -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d
local notation "H" => E × E
local notation "P" => PhaseCurve d

theorem IsShortGeodesic.reverse {C : E → Cubic d} {σ r : ℝ} {p L R : E} {x v : ℝ → E}
    (h : IsShortGeodesic C σ p r L R x v) :
    IsShortGeodesic C σ p r R L (fun t ↦ x (1-t)) (fun t ↦ -v (1-t)) := by
  have rev {t : ℝ} (ht : t ∈ UnitInterval) : 1-t ∈ UnitInterval := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  refine ⟨⟨?_,?_⟩,by simpa only [sub_zero] using h.2.2.1,by simpa only [sub_self] using h.2.1,?_⟩
  · intro t ht
    simpa [Function.comp_def] using (h.1.1 (1-t) (rev ht)).scomp t ((hasDerivAt_id t).const_sub 1)
  · intro t ht
    simpa [Function.comp_def] using ((h.1.2 (1-t) (rev ht)).scomp t ((hasDerivAt_id t).const_sub 1)).fun_neg
  · intro t ht
    simpa only [norm_neg] using h.2.2.2 _ (rev ht)

theorem IsCanonicalLocalMidpoint.swap {Ω : Set E} {C : E → Cubic d} {σ r : ℝ} {p : E}
    {W : Set H} {A : E → E → E} (ha : IsCanonicalLocalMidpoint Ω C σ p r W A)
    {q : H} (hq : q ∈ W) (hr : q.swap ∈ W) : A q.2 q.1=A q.1 q.2 := by
  obtain ⟨x,v,h,hm,_⟩ := ha.2.2.2.2 q.1 q.2 hq
  obtain ⟨y,w,_,hn,hu⟩ := ha.2.2.2.2 q.2 q.1 hr
  have he := (hu _ _ h.reverse middleParameter middleParameter.property).1
  rw [hn,hm]
  change x (1-1/2)=y (1/2) at he
  rw [show (1:ℝ)-1/2=1/2 by norm_num] at he
  exact he.symm

theorem SmoothEndpointFamily.phase_unique {Ω : Set E} {C : E → Cubic d} {σ r : ℝ} {p : E}
    (F : SmoothEndpointFamily C σ p r) {W : Set H} {A : E → E → E} (ha : IsCanonicalLocalMidpoint Ω C σ p r W A)
    {q : H} (hq : q ∈ F.domain) (hw : q ∈ W) {x v : ℝ → E} (h : IsShortGeodesic C σ p r q.1 q.2 x v) (t : UnitInterval) :
    F.phase q t=(x t,v t) := by
  obtain ⟨γ,u,_,_,hu⟩ := ha.2.2.2.2 q.1 q.2 hw
  obtain ⟨h₁,h₂⟩ := hu _ _ (F.short hq) _ t.property
  obtain ⟨h₃,h₄⟩ := hu _ _ h _ t.property
  rw [← F.phase_eq hq t,h₁,h₂,h₃,h₄]

structure OrientedEndpointChart (C : E → Cubic d) (p : E) where
  plusRadius : ℝ
  minusRadius : ℝ
  positivePlus : 0<plusRadius
  positiveMinus : 0<minusRadius
  plus : SmoothEndpointFamily C 1 p plusRadius
  minus : SmoothEndpointFamily C (-1) p minusRadius
  domain : Set H
  isOpen : IsOpen domain
  center : (p,p) ∈ domain
  plusDomain : ∀ q ∈ domain, q ∈ plus.domain
  minusDomain : ∀ q ∈ domain, q.swap ∈ minus.domain
  plusUnique : ∀ q ∈ domain, ∀ x v, IsShortGeodesic C 1 p plusRadius q.1 q.2 x v →
    ∀ t : UnitInterval, plus.phase q t=(x t,v t)
  minusUnique : ∀ q ∈ domain, ∀ x v, IsShortGeodesic C (-1) p minusRadius q.2 q.1 x v →
    ∀ t : UnitInterval, minus.phase q.swap t=(x t,v t)
  law : ∀ q ∈ domain, (plus.phase q middleParameter).1 + (minus.phase q.swap middleParameter).1=q.1+q.2

theorem oriented_endpoint_chart {Ω : Set E} {C : E → Cubic d} (hΩ : IsOpen Ω) (hC : ContDiffOn ℝ ∞ C Ω)
    (hm : LocalMidpointInvariance Ω C) {p : E} (hp : p ∈ Ω) : Nonempty (OrientedEndpointChart C p) := by
  obtain ⟨r,s,W,A,B,hA,hB,hlaw⟩ := hm p hp
  obtain ⟨F⟩ := exists_smooth_endpoint_family hΩ hC hp 1 hA.1
  obtain ⟨G⟩ := exists_smooth_endpoint_family hΩ hC hp (-1) hB.1
  let D := (W ∩ F.domain) ∩ Prod.swap ⁻¹' (W ∩ G.domain)
  have hD : IsOpen D := (hA.2.2.1.inter F.isOpen).inter ((hB.2.2.1.inter G.isOpen).preimage continuous_swap)
  refine ⟨⟨r,s,hA.1,hB.1,F,G,D,hD,⟨⟨hA.2.2.2.1,F.center⟩,hB.2.2.2.1,G.center⟩,fun _ h ↦ h.1.2,fun _ h ↦ h.2.2,
    fun _ h _ _ hg ↦ F.phase_unique hA h.1.2 h.1.1 hg,fun _ h _ _ hg ↦ G.phase_unique hB h.2.2 h.2.1 hg,?_⟩⟩
  intro q hq
  rw [F.midpoint_eq hA hq.1.2 hq.1.1,G.midpoint_eq hB hq.2.2 hq.2.1]
  exact (congrArg (fun v ↦ A q.1 q.2+v) (hB.swap hq.1.1 hq.2.1)).trans (hlaw _ _ hq.1.1)

def midpointEvaluation : P →L[ℝ] E := (ContinuousLinearMap.fst ℝ E E).comp (ContinuousMap.evalCLM ℝ middleParameter)

namespace OrientedEndpointChart
variable {C : Space d → Cubic d} {p : Space d} (D : OrientedEndpointChart C p)
set_option backward.isDefEq.respectTransparency false

theorem variation_law {q : H} (hq : q ∈ D.domain) (u : H) :
    midpointEvaluation (D.plus.variation q u)+midpointEvaluation (D.minus.variation q.swap u.swap)=u.1+u.2 := by
  let S : H →L[ℝ] H := (ContinuousLinearMap.snd ℝ E E).prod (ContinuousLinearMap.fst ℝ E E)
  let L : H →L[ℝ] E := ContinuousLinearMap.fst ℝ E E+ContinuousLinearMap.snd ℝ E E
  have df := ((D.plus.smooth.contDiffAt (D.plus.isOpen.mem_nhds (D.plusDomain _ hq))).differentiableAt (by simp)).hasFDerivAt
  have dg := ((D.minus.smooth.contDiffAt (D.minus.isOpen.mem_nhds (D.minusDomain _ hq))).differentiableAt (by simp)).hasFDerivAt
  have h₁ := (midpointEvaluation (d := d)).hasFDerivAt.comp q df
  have h₂ := (midpointEvaluation (d := d)).hasFDerivAt.comp q ((dg.comp q S.hasFDerivAt))
  have he : ∀ᶠ a in 𝓝 q, L a=midpointEvaluation (D.plus.phase a)+midpointEvaluation (D.minus.phase (S a)) :=
    (show ∀ᶠ a in 𝓝 q, a ∈ D.domain from D.isOpen.mem_nhds hq).mono fun a ha ↦ (D.law a ha).symm
  have h := (h₁.fun_add h₂).congr_of_eventuallyEq he
  exact congrArg (fun A : H →L[ℝ] E ↦ A u) (h.unique L.hasFDerivAt)

theorem mixed_variation_law {q : H} (hq : q ∈ D.domain) (u v : H) :
    midpointEvaluation (D.plus.mixedVariation q u v)+midpointEvaluation (D.minus.mixedVariation q.swap u.swap v.swap)=0 := by
  let S : H →L[ℝ] H := (ContinuousLinearMap.snd ℝ E E).prod (ContinuousLinearMap.fst ℝ E E)
  have df := ((D.plus.smooth_variation (D.plusDomain q hq) u).differentiableAt (by simp)).hasFDerivAt
  have dg := ((D.minus.smooth_variation (D.minusDomain q hq) u.swap).differentiableAt (by simp)).hasFDerivAt
  have h₁ := (midpointEvaluation (d := d)).hasFDerivAt.comp q df
  have h₂ := (midpointEvaluation (d := d)).hasFDerivAt.comp q (dg.comp q S.hasFDerivAt)
  have he : ∀ᶠ a in 𝓝 q, (fun _ : H ↦ u.1+u.2) a=
      midpointEvaluation (D.plus.variation a u)+midpointEvaluation (D.minus.variation (S a) u.swap) :=
    (show ∀ᶠ a in 𝓝 q, a ∈ D.domain from D.isOpen.mem_nhds hq).mono fun a ha ↦ (D.variation_law ha u).symm
  have h := (h₁.fun_add h₂).congr_of_eventuallyEq he
  exact congrArg (fun A : H →L[ℝ] E ↦ A v) (h.unique (hasFDerivAt_const _ _))

end OrientedEndpointChart
end EuclideanMidpointRigidity

