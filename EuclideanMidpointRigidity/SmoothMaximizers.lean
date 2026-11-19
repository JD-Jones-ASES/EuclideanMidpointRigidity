module

public import EuclideanMidpointRigidity.PolynomialRootCharts
public import EuclideanMidpointRigidity.MaximizerCoordinates
public import EuclideanMidpointRigidity.ParameterPatches
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Smooth maximizing directions on open subregions -/

public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
open SmoothPolynomial

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

theorem continuous_joint_radialObjective :
    Continuous (fun p : Coeff × E ↦ radialObjective p.1 p.2) :=
  continuous_directionProfile.sub (continuous_snd.norm.pow _)

private theorem closed_maximizing_graph {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X × Y → ℝ) (z : X → Y) (hf : Continuous f) (hz : Continuous z) :
    IsClosed {x : X | ∀ v, f (x,v)≤f (x,z x)} := by
  have hright : Continuous (fun x ↦ f (x,z x)) := hf.comp (continuous_id.prodMk hz)
  rw [show {x : X | ∀ v, f (x,v)≤f (x,z x)}=⋂ v, {x : X | f (x,v)≤f (x,z x)} by
    ext x; simp only [mem_ofPred_eq,mem_iInter]]
  apply isClosed_iInter
  intro v
  exact isClosed_le (hf.comp (continuous_id.prodMk (continuous_const (y := v)))) hright

private theorem closed_radial_graph {X : Type} [TopologicalSpace X] (c : X → Coeff) (z : X → E)
    (hc : Continuous c) (hz : Continuous z) :
    IsClosed {x : X | ∀ v, radialObjective (c x) v ≤ radialObjective (c x) (z x)} := by
  let f := fun p : X × E ↦ radialObjective (c p.1) p.2
  have hleft : Continuous (fun p : X × E ↦ c p.1) := hc.comp continuous_fst
  have hpair : Continuous (fun p : X × E ↦ (c p.1,p.2)) := hleft.prodMk continuous_snd
  have hf : Continuous f := Continuous.comp (g := fun p : Coeff × E ↦ radialObjective p.1 p.2)
    (f := fun p : X × E ↦ (c p.1,p.2)) continuous_joint_radialObjective hpair
  exact closed_maximizing_graph f z hf hz

/-- Positive spherical maxima admit a smooth maximizing direction on an
open subregion of every nonempty open set. Repeated and nonisolated
maximizers are allowed. -/
theorem smooth_maximizing_direction_on_subpatch {W : Set E} {C : E → Coeff} (hW : IsOpen W)
    (hn : W.Nonempty) (hC : ContDiffOn ℝ ∞ C W) (ha : ∀ x ∈ W, 0<amplitude (C x)) :
    ∃ (U : Set E) (e : E → E), IsOpen U ∧ U.Nonempty ∧ U ⊆ W ∧ ContDiffOn ℝ ∞ e U ∧
      ∀ x ∈ U, ‖e x‖=1 ∧ directionProfile (e x) (C x)=amplitude (C x) := by
  classical
  obtain ⟨V,q,hV,hnV,hVW,hq,hw⟩ := maximizing_coordinate_patch hW hn hC
  choose S hS hcharts using fun i ↦ countable_root_charts (q i) hW
  let (i : Fin d) : Countable (S i) := (hS i).to_subtype
  let I := (i : Fin d) → S i
  let D := fun l : I ↦ V ∩ ⋂ i, (l i).val.domain
  let z := fun (l : I) (x : E) ↦ (WithLp.toLp 2 (fun i ↦ (l i).val.val x) : E)
  have hD (l : I) : IsOpen (D l) := hV.inter (isOpen_iInter_of_finite (fun i ↦ (l i).val.isOpen_domain))
  have hDW (l : I) : D l ⊆ W := inter_subset_left.trans hVW
  have hz (l : I) : ContDiffOn ℝ ∞ (z l) (D l) := by
    have h : ContDiffOn ℝ ∞ (fun x i ↦ (l i).val.val x) (D l) :=
      contDiffOn_pi.mpr fun i ↦ (l i).val.smooth.mono (fun x hx ↦ mem_iInter.mp hx.2 i)
    exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d ↦ ℝ)).symm.contDiff.comp_contDiffOn h
  let F := fun l : I ↦ {x : D l | ∀ v, radialObjective (C x) v ≤ radialObjective (C x) (z l x)}
  let T := fun l : I ↦ ((↑) : D l → E) '' F l
  have hT (l : I) : IsLocallyClosed (T l) := by
    have hC' := (hC.continuousOn.mono (hDW l)).domRestrict
    have hz' := (hz l).continuousOn.domRestrict
    have hF : IsClosed (F l) := closed_radial_graph (X := D l) (fun u ↦ C u.val)
      (fun u ↦ z l u.val) hC' hz'
    apply hF.isLocallyClosed.image Topology.IsInducing.subtypeVal
    rw [Subtype.range_coe]
    exact (hD l).isLocallyClosed
  have cover : V ⊆ ⋃ l, T l := by
    intro x hx
    obtain ⟨w,hroot,hm⟩ := hw x hx
    have hc (i : Fin d) : ∃ s : S i, x ∈ s.val.domain ∧ s.val.val x=w i := by
      obtain ⟨s,hs,hxD,he⟩ := hcharts i x (hVW hx) (hq x hx i) (w i) (hroot i)
      exact ⟨⟨s,hs⟩,hxD,he⟩
    choose l hxl hl using hc
    have hxD : x ∈ D l := ⟨hx,mem_iInter.mpr hxl⟩
    have he : z l x=w := by ext i; exact hl i
    exact mem_iUnion.mpr ⟨l,⟨x,hxD⟩,by change ∀ v, _; rw [he]; exact hm,rfl⟩
  obtain ⟨l,U,hU,hnU,hUV,hUT⟩ := exists_subpatch_of_locallyClosed_cover hV hnV T hT cover
  have hUD : U ⊆ D l := by
    intro x hx
    obtain ⟨u,_,rfl⟩ := hUT hx
    exact u.property
  have hnorm (x : E) (hx : x ∈ U) : z l x≠0 ∧ ‖‖z l x‖⁻¹ • z l x‖=1 ∧
      directionProfile (‖z l x‖⁻¹ • z l x) (C x)=amplitude (C x) := by
    obtain ⟨u,hu,he⟩ := hUT hx
    apply normalized_radial_max (ha x (hVW (hUV hx)))
    change ∀ v, radialObjective (C u.val) v ≤ radialObjective (C u.val) (z l u.val) at hu
    simpa only [← he] using hu
  have hzu := (hz l).mono hUD
  have hnn := hzu.norm ℝ (fun x hx ↦ (hnorm x hx).1)
  exact ⟨U,fun x ↦ ‖z l x‖⁻¹ • z l x,hU,hnU,hUV.trans hVW,
    (hnn.inv (fun x hx ↦ norm_ne_zero_iff.mpr (hnorm x hx).1)).smul hzu,fun x hx ↦ (hnorm x hx).2⟩

end EuclideanMidpointRigidity

