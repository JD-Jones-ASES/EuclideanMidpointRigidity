module

public import EuclideanMidpointRigidity.MaximizingCharacteristics
public import EuclideanMidpointRigidity.TransverseCoordinates
public import EuclideanMidpointRigidity.SpatialInverse
public import EuclideanMidpointRigidity.SectionEnvelope

/-! # A lifted maximizing section in spatial coordinates -/

public section
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d
set_option backward.isDefEq.respectTransparency false

theorem MaximizingCharacteristics.exists_section {W : Set E} {C : E → Coeff} {p : E}
    (H : MaximizingCharacteristics W C p) (hC : ContDiffOn ℝ ∞ C W) (heq : MidpointJetEquations W C) :
    ∃ x ∈ W, HasMaximizingSection C x := by
  let v := H.axis (p,0)
  let T := transverseCoordinates p v
  let X := H.position ∘ T
  let e := H.axis ∘ T
  let R := T ⁻¹' H.domain
  have hT := contDiff_transverseCoordinates p v
  have hR : IsOpen R := H.isOpen.preimage hT.continuous
  have hpR : p ∈ R := by change transverseCoordinates p v p ∈ H.domain; rw [transverseCoordinates_center]; exact H.center
  have hX : ContDiffOn ℝ ∞ X R := H.smoothPosition.comp hT.contDiffOn (fun _ h ↦ h)
  have he : ContDiffOn ℝ ∞ e R := H.smoothAxis.comp hT.contDiffOn (fun _ h ↦ h)
  have hstart : ∀ᶠ y in 𝓝 p, H.position (y,0)=y := by
    have hnear : ∀ᶠ y in 𝓝 p, (y,(0:ℝ)) ∈ H.domain :=
      (continuous_id.prodMk continuous_const).continuousAt (H.isOpen.mem_nhds H.center)
    exact hnear.mono H.initial
  have hcen : fderiv ℝ X p=ContinuousLinearMap.id ℝ E := transverse_initial_derivative
    ((H.smoothPosition.contDiffAt (H.isOpen.mem_nhds H.center)).differentiableAt (by simp)) hstart (H.velocity _ H.center)
  let N := R ∩ fderiv ℝ X ⁻¹' {L : E →L[ℝ] E | L.IsInvertible}
  have hN : IsOpen N := (hX.continuousOn_fderiv_of_isOpen hR (by simp)).isOpen_inter_preimage hR
    ContinuousLinearMap.isOpen_setOfPred_isInvertible
  have hpN : p ∈ N := by
    refine ⟨hpR,?_⟩
    change (fderiv ℝ X p).IsInvertible
    rw [hcen]
    exact ⟨ContinuousLinearEquiv.refl ℝ E,rfl⟩
  let B := N ∩ (fun y ↦ (T y).2) ⁻¹' Ioi 0
  have hB : IsOpen B := hN.inter (isOpen_Ioi.preimage (continuous_snd.comp hT.continuous))
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hN.mem_nhds hpN)
  let s := δ/2
  have hs : 0<s := half_pos hδ
  let y₀ := p+s • v
  have hyN : y₀ ∈ N := hball (by
    simp only [y₀,Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hs,H.unitCenter,v,mul_one]
    exact half_lt_self hδ)
  have hyB : y₀ ∈ B := by
    refine ⟨hyN,?_⟩
    change 0<(transverseCoordinates p v (p+s • v)).2
    have hv : transverseLinear v v=(0,1) := transverseLinear_axis H.unitCenter
    simpa [transverseCoordinates,map_smul,hv] using hs
  have hBR : B ⊆ R := fun _ h ↦ h.1.1
  obtain ⟨V,r,hV,hbase,_,hr,hinv⟩ := smooth_spatial_inverse hB (hX.mono hBR) hyB hyN.2
  let axis := e ∘ r
  have hrR : MapsTo r V R := fun q hq ↦ hBR (hinv q hq).1
  have haxis : ContDiffOn ℝ ∞ axis V := he.comp hr hrR
  have hprop (q : E) (hq : q ∈ V) :
      q ∈ W ∧ ‖axis q‖=1 ∧ 0<amplitude (C q) ∧ directionProfile (axis q) (C q)=amplitude (C q) := by
    obtain ⟨hb,hpos,_⟩ := hinv q hq
    obtain ⟨hW,hu,ha,hc,_⟩ := H.forward (T (r q)) (hrR hq) (le_of_lt hb.2)
    change X (r q) ∈ W at hW
    change 0<amplitude (C (X (r q))) at ha
    change directionProfile (axis q) (C (X (r q)))=amplitude (C (X (r q))) at hc
    rw [hpos] at hW ha hc
    exact ⟨hW,hu,ha,hc⟩
  have value (q : E) (hq : q ∈ V) : sectionValue C axis q=amplitude (C q) :=
    (directionProfile_apply (axis q) (C q)).symm.trans (hprop q hq).2.2.2
  have hVW : V ⊆ W := fun q hq ↦ (hprop q hq).1
  have hub (q : E) (hq : q ∈ V) (z : E) (hz : ‖z‖=1) : ⟪K (C q) z z,z⟫_ℝ≤sectionValue C axis q := by
    rw [value q hq,← directionProfile_apply]
    exact directionProfile_le_amplitude (by simp [mem_closedBall,dist_zero_right,hz]) _
  have hlift (q : E) (hq : q ∈ V) :
      fderiv ℝ axis q (axis q)=liftStep (sectionValue C axis q) (fderiv ℝ C q) (axis q) := by
    obtain ⟨hb,hx,hreg⟩ := hinv q hq
    have hy := hrR hq
    have hZ := (H.smoothPosition.contDiffAt (H.isOpen.mem_nhds hy)).differentiableAt (by simp)
    have hY := (H.smoothAxis.contDiffAt (H.isOpen.mem_nhds hy)).differentiableAt (by simp)
    have hxv : fderiv ℝ X (r q) v=axis q := transverse_axial_derivative H.unitCenter hZ (H.velocity _ hy)
    have hd := (hr.contDiffAt (hV.mem_nhds hq)).differentiableAt (by simp)
    have hDX := (hX.contDiffAt (hR.mem_nhds hy)).differentiableAt (by simp)
    have hid : HasFDerivAt (X ∘ r) (ContinuousLinearMap.id ℝ E) q :=
      (hasFDerivAt_id q).congr_of_eventuallyEq ((show ∀ᶠ y in 𝓝 q, y ∈ V from hV.mem_nhds hq).mono
        (fun y hy' ↦ (hinv y hy').2.1))
    have hprod := (hDX.hasFDerivAt.comp q hd.hasFDerivAt).unique hid
    have hdr : fderiv ℝ r q (axis q)=v := hreg.injective
      ((congrArg (fun L : E →L[ℝ] E ↦ L (axis q)) hprod).trans hxv.symm)
    have hDy := (he.contDiffAt (hR.mem_nhds hy)).differentiableAt (by simp)
    change fderiv ℝ (e ∘ r) q (axis q)=_
    rw [(hDy.hasFDerivAt.comp q hd.hasFDerivAt).fderiv,ContinuousLinearMap.comp_apply,hdr,value q hq]
    have ht := (H.forward (T (r q)) hy (le_of_lt hb.2)).2.2.2.2
    have hey := transverse_axial_derivative H.unitCenter hY ht
    change fderiv ℝ e (r q) v=liftStep (amplitude (C (X (r q)))) (fderiv ℝ C (X (r q))) (axis q) at hey
    rwa [hx] at hey
  let S : LiftedSection d := {
    domain := V, field := C, axis := axis, isOpen := hV, smooth := hC.mono hVW, smoothAxis := haxis
    equations := heq.mono hVW, unit := fun q hq ↦ (hprop q hq).2.1
    critical := fun q hq ↦ maximizing_axis_product ((value q hq).symm ▸ (hprop q hq).2.2.1.le)
      (hub q hq) (hprop q hq).2.1 rfl
    positive := fun q hq ↦ (value q hq).symm ▸ (hprop q hq).2.2.1
    lift := hlift }
  exact ⟨X y₀,hVW hbase,S,rfl,hbase,hub⟩

end EuclideanMidpointRigidity

