module

public import EuclideanMidpointRigidity.HorizontalInvariants
public import EuclideanMidpointRigidity.MaximizingSlice
public import EuclideanMidpointRigidity.SelectionRankDrop

/-! # Local motions keeping the optimizing vector fixed -/

public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity.Horizontal
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d
set_option backward.isDefEq.respectTransparency false

theorem fixed_test_motion {Ω : Set E} {C : E → T} {e : E → E} {a : ℝ} (hΩ : IsOpen Ω)
    (hC : ContDiffOn ℝ ∞ C Ω) (hQ : MidpointJetEquations Ω C) (hc : ∀ q ∈ Ω, Nonempty (OrientedEndpointChart C q))
    (he : ContDiffOn ℝ ∞ e Ω) (ha : 0<a) (hamp : ∀ q ∈ Ω, amplitude (C q)=a)
    (hm : ∀ y ∈ Ω, ‖e y‖=1 ∧ directionProfile (e y) (C y)=a) {p : E} (hp : p ∈ Ω) (l : E) :
    ∃ (O : Set (E × ℝ)) (X : E × ℝ → E), IsOpen O ∧ (p,0) ∈ O ∧ ContDiffOn ℝ ∞ X O ∧
      (∀ᶠ y in 𝓝 p, X (y,0)=y) ∧ HasDerivAt (fun t ↦ X (p,t)) (transport (C p) (e p) a l) 0 ∧
      ∀ q ∈ O, X q ∈ Ω ∧ ‖e q.1‖=1 ∧ directionProfile (e q.1) (C (X q))=a := by
  let D := Ω ×ˢ (univ : Set E)
  let i := fun y : E ↦ (y,e y)
  have hi : ContDiffOn ℝ ∞ i Ω := contDiffOn_id.prodMk he
  obtain ⟨B,F,hB,hpB,hF,hrange,hstart,hd⟩ := smooth_local_flow (hΩ.prod isOpen_univ) (smooth_phaseVector hΩ hC l)
    (show i p ∈ D from ⟨hp,trivial⟩)
  let I := fun q : E × ℝ ↦ (i q.1,q.2)
  let W := Ω ×ˢ (univ : Set ℝ)
  have hW : IsOpen W := hΩ.prod isOpen_univ
  have hi' : ContDiffOn ℝ ∞ I W := (hi.comp contDiffOn_fst (fun q (h : q ∈ W) ↦ h.1)).prodMk contDiffOn_snd
  let O := W ∩ I ⁻¹' B
  have hO : IsOpen O := hi'.continuousOn.isOpen_inter_preimage hW hB
  have hpO : (p,(0:ℝ)) ∈ O := ⟨⟨hp,trivial⟩,hpB⟩
  let γ := F ∘ I
  let X := fun q ↦ (γ q).1
  let n := fun q ↦ (γ q).2
  have hγ : ContDiffOn ℝ ∞ γ O := hF.comp (hi'.mono inter_subset_left) (fun q h ↦ h.2)
  have hX : ContDiffOn ℝ ∞ X O := hγ.fst
  have hn : ContDiffOn ℝ ∞ n O := hγ.snd
  have h₀ (y : E) (hy : (y,(0:ℝ)) ∈ O) : γ (y,0)=i y := hstart _ hy.2
  have htime (q : E × ℝ) (hq : q ∈ O) : HasDerivAt (fun t ↦ γ (q.1,t)) (phaseVector C l (γ q)) q.2 := hd _ hq.2
  let J := fun q ↦ (fderiv ℝ X q).comp (.inl ℝ E ℝ)
  have hJ : ContinuousOn J O := (hX.continuousOn_fderiv_of_isOpen hO (by simp)).clm_comp continuousOn_const
  have hinitial : ∀ᶠ y in 𝓝 p, X (y,0)=y := by
    have hy : ∀ᶠ y in 𝓝 p, (y,(0:ℝ)) ∈ O := (continuous_id.prodMk continuous_const).continuousAt (hO.mem_nhds hpO)
    exact hy.mono (fun y h ↦ congrArg Prod.fst (h₀ y h))
  have hj₀ : J (p,0)=ContinuousLinearMap.id ℝ E := by
    have hid : HasFDerivAt (fun y ↦ X (y,0)) (ContinuousLinearMap.id ℝ E) p := (hasFDerivAt_id p).congr_of_eventuallyEq hinitial
    have hcomp := ((hX.contDiffAt (hO.mem_nhds hpO)).differentiableAt (by simp)).hasFDerivAt.comp p (hasFDerivAt_prodMk_left (𝕜 := ℝ) p (0:ℝ))
    exact hcomp.unique hid
  let N := O ∩ J ⁻¹' {A : E →L[ℝ] E | A.IsInvertible}
  have hN : IsOpen N := hJ.isOpen_inter_preimage hO ContinuousLinearMap.isOpen_setOfPred_isInvertible
  have hpN : (p,(0:ℝ)) ∈ N := ⟨hpO,by change (J (p,0)).IsInvertible; rw [hj₀]; exact ⟨ContinuousLinearEquiv.refl ℝ E,rfl⟩⟩
  obtain ⟨M,hM,L,hL,hmL⟩ := mem_nhds_prod_iff.mp (hN.mem_nhds hpN)
  obtain ⟨U,hUM,hU,hpU⟩ := _root_.mem_nhds_iff.mp hM
  obtain ⟨r,hr,hrL⟩ := Metric.mem_nhds_iff.mp hL
  let V := ball (0:ℝ) r
  have hv₀ : (0:ℝ) ∈ V := mem_ball_self hr
  have hsub : U ×ˢ V ⊆ N := (prod_mono hUM hrL).trans hmL
  have hgood (y : E) (hy : y ∈ U) (s : ℝ) (hs : s ∈ V) : X (y,s) ∈ Ω ∧ ‖n (y,s)‖=1 ∧ directionProfile (n (y,s)) (C (X (y,s)))=a := by
    have hb (t : ℝ) (ht : t ∈ V) := (hsub (show (y,t) ∈ U ×ˢ V from ⟨hy,ht⟩)).1
    have hbase := h₀ y (hb 0 hv₀)
    have hprops := hm y (hb 0 hv₀).1.1
    have H := phase_invariants hΩ hC hQ.quartic l isOpen_ball (convex_ball _ _).isPreconnected hv₀
      (γ := fun t ↦ γ (y,t)) (fun t ht ↦ (hrange (hb t ht).2).1) (fun t ht ↦ htime _ (hb t ht))
      (by rw [hbase]; exact hprops.1) s hs
    exact ⟨(hrange (hb s hs).2).1,H.1,H.2.trans (by rw [hbase]; exact hprops.2)⟩
  have dj (y : E) (hy : y ∈ U) (s : ℝ) (hs : s ∈ V) : HasDerivAt (fun t ↦ n (y,t)) 0 s := by
    have hentry (q : E) (hq : q ∈ U) := hsub (show (q,s) ∈ U ×ˢ V from ⟨hq,hs⟩)
    have hI : ContDiff ℝ ∞ (fun q : E ↦ (q,s)) := contDiff_id.prodMk contDiff_const
    have hmap : MapsTo (fun q : E ↦ (q,s)) U O := fun q hq ↦ (hentry q hq).1
    have hdiff := ((hX.contDiffAt (hO.mem_nhds (hentry y hy).1)).differentiableAt (by simp)).hasFDerivAt.comp y (hasFDerivAt_prodMk_left (𝕜 := ℝ) y s)
    have hi' : (fderiv ℝ (fun q ↦ X (q,s)) y).IsInvertible := by
      change HasFDerivAt (fun q ↦ X (q,s)) _ _ at hdiff
      rw [hdiff.fderiv]; exact (hentry y hy).2
    obtain ⟨h₁,h₂⟩ := maximizing_slice_jet hΩ hC hQ hc ha hamp hU (hX.comp hI.contDiffOn hmap) (hn.comp hI.contDiffOn hmap)
      (fun q hq ↦ hgood q hq s hs) hy hi'
    have hv := hasDerivAt_second_projection (htime (y,s) (hentry y hy).1)
    have hz : correction (C (X (y,s))) (fderiv ℝ C (X (y,s))) (n (y,s)) (directionProfile (n (y,s)) (C (X (y,s)))) l=0 := correction_of_zero (c := C (X (y,s))) h₁ h₂ (directionProfile (n (y,s)) (C (X (y,s)))) l
    change HasDerivAt (fun t ↦ n (y,t)) ((-1/3:ℝ) • (⟪n (y,s),n (y,s)⟫_ℝ • correction (C (X (y,s))) (fderiv ℝ C (X (y,s))) (n (y,s)) (directionProfile (n (y,s)) (C (X (y,s)))) l-⟪n (y,s),correction (C (X (y,s))) (fderiv ℝ C (X (y,s))) (n (y,s)) (directionProfile (n (y,s)) (C (X (y,s)))) l⟫_ℝ • n (y,s))) s at hv
    simpa only [hz,smul_zero,inner_zero_right,zero_smul,sub_zero] using hv
  have fixed (y : E) (hy : y ∈ U) (s : ℝ) (hs : s ∈ V) : n (y,s)=e y := by
    have H := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball _ _).isPreconnected
      (fun t ht ↦ (dj y hy t ht).differentiableAt.differentiableWithinAt) (fun {t} ht ↦ (dj y hy t ht).deriv) hs hv₀
    exact H.trans (congrArg Prod.snd (h₀ y (hsub ⟨hy,hv₀⟩).1))
  refine ⟨U ×ˢ V,X,hU.prod isOpen_ball,⟨hpU,hv₀⟩,hX.mono (hsub.trans inter_subset_left),hinitial,?_,?_⟩
  · have H := hasDerivAt_first_projection (htime (p,0) hpO)
    rw [h₀ p hpO] at H
    change HasDerivAt (fun t ↦ X (p,t)) (transport (C p) (e p) (directionProfile (e p) (C p)) l) 0 at H
    rwa [(hm p hp).2] at H
  · rintro ⟨y,s⟩ ⟨hy,hs⟩
    have H := hgood y hy s hs
    rwa [fixed y hy s hs] at H

end EuclideanMidpointRigidity.Horizontal

