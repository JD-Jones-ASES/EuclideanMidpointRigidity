module

public import EuclideanMidpointRigidity.FrozenField

/-! # The Cartesian first jets and the translated derivative along a maximizing line -/

@[expose] public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.HorizontalPatch
variable {d : ℕ} {S : LiftedSection d} (H : HorizontalPatch S)
local notation "E" => Space d
local notation "T" => Cubic d
local notation "I" => ContinuousLinearMap.id ℝ E
local instance (n : ℕ) : AddMonoid (Cubic n) := (cubicNormedAddCommGroup n).toAddCommGroup.toAddCommMonoid.toAddMonoid
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 140000

include H in
theorem derivative_under_shear {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : E → Y}
    {x : E} (hx : x ∈ S.domain) (t : ℝ) (hf : DifferentiableAt ℝ f (position S t x))
    (he : f =ᶠ[𝓝 x] f ∘ position S t) (v : E) :
    fderiv ℝ f (position S t x) v=fderiv ℝ f x (v-t • fderiv ℝ S.axis x v) := by
  have hd := hf.hasFDerivAt.comp x (JacobianPencil.hasFDerivAt_chart S.isOpen S.smoothAxis hx t)
  have hh := DFunLike.congr_fun (he.fderiv_eq.trans hd.fderiv) ((I-t • fderiv ℝ S.axis x) v)
  change fderiv ℝ f x (v-t • fderiv ℝ S.axis x v)=fderiv ℝ f (position S t x) ((I+t • fderiv ℝ S.axis x) ((I-t • fderiv ℝ S.axis x) v)) at hh
  rwa [H.cancel_shear hx t v,eq_comm] at hh

structure FirstJetStrip (S : LiftedSection d) (U : Set E) (r : ℝ) : Prop where
  isOpen : IsOpen U
  positive : 0<r
  inside : U ⊆ S.domain
  maps : ∀ y ∈ U, ∀ t ∈ ball (0:ℝ) r, position S t y ∈ S.domain
  axis : ∀ y ∈ U, ∀ t ∈ ball (0:ℝ) r, S.axis (position S t y)=S.axis y
  amplitude : ∀ y ∈ U, ∀ t ∈ ball (0:ℝ) r, S.a (position S t y)=S.a y
  slice : ∀ y ∈ U, ∀ t ∈ ball (0:ℝ) r, S.axisSlice (position S t y)=S.axisSlice y
  axisJet : ∀ y ∈ U, ∀ t ∈ ball (0:ℝ) r, fderiv ℝ S.axis (position S t y)=fderiv ℝ S.axis y
  fieldJet : ∀ y ∈ U, ∀ t ∈ ball (0:ℝ) r, fderiv ℝ S.field (position S t y)=fderiv ℝ S.field y

include H in
theorem first_jet_strip {p : E} (hp : p ∈ S.domain) :
    ∃ (U : Set E) (r : ℝ), p ∈ U ∧ FirstJetStrip S U r := by
  obtain ⟨U,r,hU,hpU,hr,hC⟩ := H.invariant_strip hp
  obtain ⟨V,s,hV,hpV,hs,hE⟩ := S.local_straight_rulings hp H.maximizes
  let W := U ∩ V
  let a := min r s
  have hW : IsOpen W := hU.inter hV
  have ha : 0<a := lt_min hr hs
  have h₁ {t : ℝ} (ht : t ∈ ball 0 a) : t ∈ ball 0 r := ball_subset_ball (min_le_left _ _) ht
  have h₂ {t : ℝ} (ht : t ∈ ball 0 a) : t ∈ ball 0 s := ball_subset_ball (min_le_right _ _) ht
  have hi {y : E} (hy : y ∈ W) : y ∈ S.domain := by
    have h := (hC y hy.1 0 (mem_ball_self hr)).1
    simpa only [position,zero_smul,add_zero] using h
  refine ⟨W,a,⟨hpU,hpV⟩,⟨hW,ha,fun _ hy ↦ hi hy,fun y hy t ht ↦ (hC y hy.1 t (h₁ ht)).1,
    fun y hy t ht ↦ (hE y hy.2 t (h₂ ht)).2.1,fun y hy t ht ↦ (hE y hy.2 t (h₂ ht)).2.2.2,
    fun y hy t ht ↦ (hE y hy.2 t (h₂ ht)).2.2.1,?_,?_⟩⟩
  · intro y hy t ht
    have he : S.axis =ᶠ[𝓝 y] S.axis ∘ position S t := (show ∀ᶠ z in 𝓝 y, z ∈ W from hW.mem_nhds hy).mono
      fun z hz ↦ (hE z hz.2 t (h₂ ht)).2.1.symm
    ext v : 1
    rw [H.derivative_under_shear (hi hy) t ((S.smoothAxis.contDiffAt (S.isOpen.mem_nhds (hC y hy.1 t (h₁ ht)).1)).differentiableAt (by simp)) he,
      map_sub,map_smul,H.square_zero (hi hy),smul_zero,sub_zero]
  · intro y hy t ht
    have he : S.field =ᶠ[𝓝 y] S.field ∘ position S t := (show ∀ᶠ z in 𝓝 y, z ∈ W from hW.mem_nhds hy).mono
      fun z hz ↦ (hC z hz.1 t (h₁ ht)).2.symm
    ext v : 1
    rw [H.derivative_under_shear (hi hy) t ((S.smooth.contDiffAt (S.isOpen.mem_nhds (hC y hy.1 t (h₁ ht)).1)).differentiableAt (by simp)) he,
      map_sub,map_smul,H.inactive_slope (hi hy),smul_zero,sub_zero]

end EuclideanMidpointRigidity.HorizontalPatch

