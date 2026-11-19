module

public import EuclideanMidpointRigidity.MaximizingLineGraphs
public import EuclideanMidpointRigidity.ConstantRulings

/-! # The first jet at any point of a smooth maximizing graph -/

public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d
set_option backward.isDefEq.respectTransparency false

theorem lifted_graph_through {Ω : Set E} {C : E → T} {e : E → E} {a : ℝ} (hΩ : IsOpen Ω)
    (hC : ContDiffOn ℝ ∞ C Ω) (hQ : MidpointJetEquations Ω C) (he : ContDiffOn ℝ ∞ e Ω)
    (ha : 0<a) (hamp : ∀ q ∈ Ω, amplitude (C q)=a) (hu : ∀ q ∈ Ω, ‖e q‖=1)
    (hk : ∀ q ∈ Ω, K (C q) (e q) (e q)=a • e q) {p : E} (hp : p ∈ Ω) :
    ∃ S : LiftedSection d, S.field=C ∧ S.domain ⊆ Ω ∧ p ∈ S.domain ∧ S.axis p=e p ∧ ∀ q ∈ S.domain, S.Maximizes q := by
  obtain ⟨U,s,hU,hpU,hUΩ,hs,hline⟩ := maximizing_lines_on_strip hΩ hC hQ.quartic he ha hamp hu hk hp
  let v := e p
  let D := U ×ˢ ball (0:ℝ) s
  have hD : IsOpen D := hU.prod isOpen_ball
  have hpD : (p,(0:ℝ)) ∈ D := ⟨hpU,mem_ball_self hs⟩
  let Y := fun q : E × ℝ ↦ e q.1
  let F := fun q : E × ℝ ↦ q.1+q.2 • e q.1
  have hY : ContDiffOn ℝ ∞ Y D := he.comp contDiffOn_fst (fun q h ↦ hUΩ h.1)
  have hF : ContDiffOn ℝ ∞ F D := contDiffOn_fst.add (contDiffOn_snd.smul hY)
  let τ := transverseCoordinates p v
  let B := τ ⁻¹' D
  have hτ := contDiff_transverseCoordinates p v
  have hB : IsOpen B := hD.preimage hτ.continuous
  have hpB : p ∈ B := by change transverseCoordinates p v p ∈ D; rwa [transverseCoordinates_center]
  let X := F ∘ τ
  let test := Y ∘ τ
  have hX : ContDiffOn ℝ ∞ X B := hF.comp hτ.contDiffOn (fun _ h ↦ h)
  have ht : ContDiffOn ℝ ∞ test B := hY.comp hτ.contDiffOn (fun _ h ↦ h)
  have vel (y : E) (t : ℝ) : HasDerivAt (fun s ↦ F (y,s)) (e y) t := by
    simpa only [F,id_eq,one_smul] using ((hasDerivAt_id t).smul_const (e y)).const_add y
  have hcent : fderiv ℝ X p=ContinuousLinearMap.id ℝ E := transverse_initial_derivative
    ((hF.contDiffAt (hD.mem_nhds hpD)).differentiableAt (by simp)) (Eventually.of_forall (fun y ↦ by simp [F])) (vel p 0)
  have hi : (fderiv ℝ X p).IsInvertible := hcent ▸ ⟨ContinuousLinearEquiv.refl ℝ E,rfl⟩
  obtain ⟨V,r,hV,hpV,hrp,hr,hreg⟩ := smooth_spatial_inverse hB hX hpB hi
  let n := test ∘ r
  have hnen : ContDiffOn ℝ ∞ n V := ht.comp hr (fun q h ↦ (hreg q h).1)
  have hXp : X p=p := by simp [X,F,τ]
  rw [hXp] at hpV hrp
  have hn0 : n p=e p := by simp [n,test,Y,τ,hrp]
  have hdata (q : E) (hq : q ∈ V) : q ∈ Ω ∧ ‖n q‖=1 ∧ K (C q) (n q) (n q)=a • n q := by
    obtain ⟨hb,hx,_⟩ := hreg q hq
    have hs := hline _ hb.1 _ hb.2
    change X (r q) ∈ Ω ∧ K (C (X (r q))) (n q) (n q)=a • n q at hs
    rw [hx] at hs
    exact ⟨hs.1,hu _ (hUΩ hb.1),hs.2⟩
  have hv (q : E) (hq : q ∈ V) : sectionValue C n q=a := by
    simp only [sectionValue,(hdata q hq).2.2,real_inner_smul_left,real_inner_self_eq_norm_sq,(hdata q hq).2.1,one_pow,mul_one]
  have hlift (q : E) (hq : q ∈ V) : fderiv ℝ n q (n q)=liftStep (sectionValue C n q) (fderiv ℝ C q) (n q) := by
    rw [hv q hq,extremal_liftStep_zero hΩ hC hQ.quartic ha.ne' (fun x h ↦ (hamp x h).trans (abs_of_pos ha).symm)
      (hdata q hq).1 (hdata q hq).2.1 (hdata q hq).2.2]
    obtain ⟨hb,hx,hI⟩ := hreg q hq
    have hZ := (hF.contDiffAt (hD.mem_nhds hb)).differentiableAt (by simp)
    have hY' := (hY.contDiffAt (hD.mem_nhds hb)).differentiableAt (by simp)
    have hvx : fderiv ℝ X (r q) v=n q := transverse_axial_derivative (hu p hp) hZ (vel _ _)
    have htime : HasDerivAt (fun t ↦ Y ((τ (r q)).1,t)) 0 (τ (r q)).2 := hasDerivAt_const _ (e (τ (r q)).1)
    have hve : fderiv ℝ test (r q) v=0 := transverse_axial_derivative (hu p hp) hY' htime
    have hd := (hr.contDiffAt (hV.mem_nhds hq)).differentiableAt (by simp)
    have hDX := (hX.contDiffAt (hB.mem_nhds hb)).differentiableAt (by simp)
    have hid : HasFDerivAt (X ∘ r) (ContinuousLinearMap.id ℝ E) q :=
      (hasFDerivAt_id q).congr_of_eventuallyEq ((show ∀ᶠ y in 𝓝 q, y ∈ V from hV.mem_nhds hq).mono (fun y hy ↦ (hreg y hy).2.1))
    have hcomp := (hDX.hasFDerivAt.comp q hd.hasFDerivAt).unique hid
    have heq : fderiv ℝ r q (n q)=v := hI.injective ((congrArg (fun L : E →L[ℝ] E ↦ L (n q)) hcomp).trans hvx.symm)
    have hdT := (ht.contDiffAt (hB.mem_nhds hb)).differentiableAt (by simp)
    change fderiv ℝ (test ∘ r) q (n q)=0
    rw [(hdT.hasFDerivAt.comp q hd.hasFDerivAt).fderiv,ContinuousLinearMap.comp_apply,heq,hve]
  have hVΩ : V ⊆ Ω := fun q h ↦ (hdata q h).1
  let S : LiftedSection d := ⟨V,C,n,hV,hC.mono hVΩ,hnen,hQ.mono hVΩ,fun q h ↦ (hdata q h).2.1,
    fun q h ↦ by rw [hv q h]; exact (hdata q h).2.2,fun q h ↦ (hv q h).symm ▸ ha,hlift⟩
  refine ⟨S,rfl,hVΩ,hpV,hn0,?_⟩
  intro q hq z hz
  change ⟪K (C q) z z,z⟫_ℝ≤sectionValue C n q
  rw [hv q hq,← hamp q (hVΩ hq),← directionProfile_apply]
  exact directionProfile_le_amplitude (by simp [mem_closedBall,dist_zero_right,hz]) _

theorem maximizing_graph_jet {Ω : Set E} {C : E → T} {e : E → E} {a : ℝ} (hΩ : IsOpen Ω)
    (hC : ContDiffOn ℝ ∞ C Ω) (hQ : MidpointJetEquations Ω C) (he : ContDiffOn ℝ ∞ e Ω)
    (ha : 0<a) (hamp : ∀ q ∈ Ω, amplitude (C q)=a) (hu : ∀ q ∈ Ω, ‖e q‖=1)
    (hk : ∀ q ∈ Ω, K (C q) (e q) (e q)=a • e q) (hc : ∀ q ∈ Ω, Nonempty (OrientedEndpointChart C q)) {p : E} (hp : p ∈ Ω) :
    fderiv ℝ C p (e p)=0 ∧ ∀ l, K (fderiv ℝ C p l) (e p) (e p)=0 := by
  obtain ⟨S,hf,hs,hpS,heq,hm⟩ := lifted_graph_through hΩ hC hQ he ha hamp hu hk hp
  have hc' : ∀ q ∈ S.domain, Nonempty (OrientedEndpointChart S.field q) := by rw [hf]; exact fun q h ↦ hc q (hs h)
  have H := S.stationary_field_along_axis hm hc' hpS
  have J := (S.weighted_ruling hpS hm).1
  rw [hf,heq] at H J
  exact ⟨H,J⟩

end EuclideanMidpointRigidity

