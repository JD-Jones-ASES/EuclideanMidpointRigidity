module

public import EuclideanMidpointRigidity.CriticalPhase
public import EuclideanMidpointRigidity.SmoothMaximizers
public import EuclideanMidpointRigidity.SphericalCriticalValues

/-! # Local characteristics that remain spherical maximizers -/

@[expose] public section
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff InnerProductSpace
namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d
local notation "S" => AxisPhase d

/-- Position and direction along a smooth family of characteristics
starting at time zero, with the maximality assertion for forward time. -/
structure MaximizingCharacteristics (W : Set E) (C : E → Coeff) (p : E) where
  domain : Set (E × ℝ)
  position : E × ℝ → E
  axis : E × ℝ → E
  isOpen : IsOpen domain
  center : (p,0) ∈ domain
  smoothPosition : ContDiffOn ℝ ∞ position domain
  smoothAxis : ContDiffOn ℝ ∞ axis domain
  initial : ∀ y, (y,0) ∈ domain → position (y,0)=y
  unitCenter : ‖axis (p,0)‖=1
  velocity : ∀ q ∈ domain, HasDerivAt (fun t ↦ position (q.1,t)) (axis q) q.2
  forward : ∀ q ∈ domain, 0≤q.2 → position q ∈ W ∧ ‖axis q‖=1 ∧
    0<amplitude (C (position q)) ∧ directionProfile (axis q) (C (position q))=amplitude (C (position q)) ∧
    HasDerivAt (fun t ↦ axis (q.1,t)) (liftStep (amplitude (C (position q))) (fderiv ℝ C (position q)) (axis q)) q.2

set_option backward.isDefEq.respectTransparency false in
theorem maximizing_characteristics_at {W : Set E} {C : E → Coeff} (hW : IsOpen W)
    (hC : ContDiffOn ℝ ∞ C W) (hQ : QuarticOn W C) {e : E → E} (he : ContDiffOn ℝ ∞ e W)
    (ha : ∀ x ∈ W, 0<amplitude (C x)) (hm : ∀ x ∈ W, ‖e x‖=1 ∧ directionProfile (e x) (C x)=amplitude (C x))
    {p : E} (hp : p ∈ W) (hgap : ∀ᶠ q : E × ℝ in 𝓝 (p,amplitude (C p)), ∀ v : E, ‖v‖=1 →
      K (C q.1) v v=q.2 • v → q.2=amplitude (C q.1)) : Nonempty (MaximizingCharacteristics W C p) := by
  let a := sectionValue C e
  have heq (x : E) (hx : x ∈ W) : a x=amplitude (C x) := (directionProfile_apply (e x) (C x)).symm.trans (hm x hx).2
  have hapos (x : E) (hx : x ∈ W) : 0<a x := by rw [heq x hx]; exact ha x hx
  have hmax (x : E) (hx : x ∈ W) : K (C x) (e x) (e x)=a x • e x := by
    apply maximizing_axis_product (a := a x) (hapos x hx).le _ (hm x hx).1 rfl
    intro v hv
    rw [heq x hx,← directionProfile_apply]
    exact directionProfile_le_amplitude (by simp [mem_closedBall,dist_zero_right,hv]) _
  let A : E → S := fun y ↦ ((y,e y),a y)
  have hA : ContDiffOn ℝ ∞ A W := (contDiffOn_id.prodMk he).prodMk (contDiffOn_sectionValue hC he)
  have hbase : A p ∈ criticalPhaseDomain W := ⟨hp,(hapos p hp).ne'⟩
  obtain ⟨R,φ,hR,hrp,hφ,hrange,hzero,hd⟩ := smooth_local_flow (isOpen_criticalPhaseDomain hW) (smooth_criticalPhaseVector hW hC) hbase
  let I := fun q : E × ℝ ↦ (A q.1,q.2)
  let B := W ×ˢ (univ : Set ℝ)
  have hB : IsOpen B := hW.prod isOpen_univ
  have hfirst : MapsTo (Prod.fst : E × ℝ → E) B W := fun q hq ↦ hq.1
  have hI : ContDiffOn ℝ ∞ I B := (hA.comp contDiffOn_fst hfirst).prodMk contDiffOn_snd
  let J := B ∩ I ⁻¹' R
  have hJ : IsOpen J := hI.continuousOn.isOpen_inter_preimage hB hR
  have hpJ : (p,0) ∈ J := ⟨⟨hp,trivial⟩,hrp⟩
  let γ := φ ∘ I
  have hγ : ContDiffOn ℝ ∞ γ J := hφ.comp (hI.mono inter_subset_left) (fun q hq ↦ hq.2)
  let X := fun q ↦ (γ q).1.1
  let Y := fun q ↦ (γ q).1.2
  have hX : ContDiffOn ℝ ∞ X J := hγ.fst.fst
  have hY : ContDiffOn ℝ ∞ Y J := hγ.fst.snd
  have hstart (y : E) (hy : (y,0) ∈ J) : γ (y,0)=A y := hzero _ hy.2
  have hdot (q : E × ℝ) (hq : q ∈ J) : HasDerivAt (fun s ↦ γ (q.1,s)) (criticalPhaseVector C (γ q)) q.2 := hd _ hq.2
  let G := fun q : E × ℝ ↦ (X q,a q.1)
  have hG : ContinuousOn G J := hX.continuousOn.prodMk
    (((contDiffOn_sectionValue hC he).continuousOn.comp continuousOn_fst hfirst).mono inter_subset_left)
  have hGp : G (p,0)=(p,amplitude (C p)) := by
    change (((γ (p,0)).1.1),a p)=(p,_)
    rw [hstart p hpJ,heq p hp]
  have hnear : Tendsto G (𝓝 (p,0)) (𝓝 (p,amplitude (C p))) := by
    rw [← hGp]
    exact hG.continuousAt (hJ.mem_nhds hpJ)
  have hgood := (hnear.eventually hgap).and (hJ.mem_nhds hpJ)
  obtain ⟨M,hM,N,hN,hMN⟩ := mem_nhds_prod_iff.mp hgood
  obtain ⟨U,hUM,hU,hpU⟩ := _root_.mem_nhds_iff.mp hM
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hN
  let D := U ×ˢ ball (0:ℝ) δ
  have hsub : D ⊆ M ×ˢ N := Set.prod_mono hUM hball
  have hDJ : D ⊆ J := fun q hq ↦ (hMN (hsub hq)).2
  have hpD : (p,0) ∈ D := ⟨hpU,mem_ball_self hδ⟩
  refine ⟨⟨D,X,Y,hU.prod isOpen_ball,hpD,hX.mono hDJ,hY.mono hDJ,
    fun y hy ↦ congrArg (fun v : S ↦ v.1.1) (hstart y (hDJ hy)),?_,?_,?_⟩⟩
  · change ‖(γ (p,0)).1.2‖=1
    rw [hstart p hpJ]
    exact (hm p hp).1
  · intro q hq
    exact hasDerivAt_first_projection (hasDerivAt_first_projection (hdot q (hDJ hq)))
  · rintro ⟨y,t⟩ hyt ht
    have hseg (s : ℝ) (hs : s ∈ Icc 0 t) : (y,s) ∈ D := by
      refine ⟨hyt.1,?_⟩
      have htδ : t<δ := by simpa [Metric.mem_ball,Real.dist_eq,abs_of_nonneg ht] using hyt.2
      simpa [Metric.mem_ball,Real.dist_eq,abs_of_nonneg hs.1] using hs.2.trans_lt htδ
    have hγdom : MapsTo (fun s ↦ γ (y,s)) (Icc 0 t) (criticalPhaseDomain W) :=
      fun s hs ↦ hrange (hDJ (hseg s hs)).2
    have ht₀ : (y,0) ∈ J := hDJ (hseg 0 ⟨le_rfl,ht⟩)
    have hyW : y ∈ W := ht₀.1.1
    have h₀ := hstart y ht₀
    have hpos : 0<a y := (heq y hyW).symm ▸ ha y hyW
    have hinv := critical_phase_invariants hW hC hQ hγdom (fun s hs ↦ hdot (y,s) (hDJ (hseg s hs)))
      (by rw [h₀]; exact hpos.ne') (by rw [h₀]; exact (hm y hyW).1) (by rw [h₀]; exact hmax y hyW)
      t ⟨ht,le_rfl⟩
    rw [h₀] at hinv
    change (γ (y,t)).2=a y ∧ ‖Y (y,t)‖=1 ∧ K (C (X (y,t))) (Y (y,t)) (Y (y,t))=a y • Y (y,t) at hinv
    obtain ⟨hs,hu,hcr⟩ := hinv
    have hsep : a y=amplitude (C (X (y,t))) := (hMN (hsub hyt)).1 (Y (y,t)) hu hcr
    refine ⟨(hγdom (show t ∈ Icc 0 t from ⟨ht,le_rfl⟩)).1,hu,hsep ▸ hpos,?_,?_⟩
    · rw [directionProfile_apply,hcr,real_inner_smul_left,real_inner_self_eq_norm_sq,hu,one_pow,mul_one,hsep]
    · rw [← hsep,← hs]
      exact hasDerivAt_second_projection (hasDerivAt_first_projection (hdot (y,t) (hDJ hyt)))

end EuclideanMidpointRigidity

