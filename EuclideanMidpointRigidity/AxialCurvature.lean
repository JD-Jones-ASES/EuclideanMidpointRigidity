module

public import EuclideanMidpointRigidity.ShearedHessian
public import EuclideanMidpointRigidity.MovingAxialSlots

/-! # The translated field and its first jet on the base ruling -/

@[expose] public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.HorizontalPatch
variable {d : ℕ} {S : LiftedSection d} (H : HorizontalPatch S)
local notation "E" => Space d
local notation "T" => Cubic d
set_option backward.isDefEq.respectTransparency false

private theorem translation_derivative {q : E} (hq : q ∈ S.domain) (b w : E) :
    directional (directional S.field b) w q=fderiv ℝ (fderiv ℝ S.field) q w b :=
  directions.two S.isOpen S.smooth hq w b []

include H in
theorem translated_curvature {p : E} (hp : p ∈ S.domain) (l w : E) :
    directional (directional S.field (fderiv ℝ S.axis p l)) w p= -(H.freeze hp [] H.inactive_one).jet l w := by
  let b := directional S.axis l
  have hb : ContDiffOn ℝ ∞ b S.domain := directions.smooth S.isOpen S.smoothAxis [l]
  have hh := DFunLike.congr_fun (inactive_exchange S.isOpen S.smooth hb (fun q hq ↦ H.inactive_slope hq l) hp) w
  change fderiv ℝ (fderiv ℝ S.field) p (b p) w= -fderiv ℝ S.field p (directional b w p) at hh
  rw [translation_derivative hp]
  change fderiv ℝ (fderiv ℝ S.field) p w (b p)=_
  rw [((S.smooth.contDiffAt (S.isOpen.mem_nhds hp)).isSymmSndFDerivAt (by simp)) w (b p)]
  change fderiv ℝ (fderiv ℝ S.field) p (b p) w= -higherJet S p [] l w
  rw [hh,higherJet_apply hp,directions.perm S.isOpen S.smoothAxis (List.Perm.swap w l []) hp]
  rfl

include H in
theorem flat_at_slope {p : E} (hp : p ∈ S.domain) (l : E) :
    FlatAxialForce (directional S.field (fderiv ℝ S.axis p l)) p (S.idempotent p) := by
  let b := fderiv ℝ S.axis p l
  let D := directional S.field b
  let P := H.freeze hp [] H.inactive_one
  let F := (S.idempotent_frame hp (H.maximizes p hp)).some
  have hf (v w : E) : K (directions D [v] p) (S.idempotent p) w=0 := by
    change K (directional (directional S.field (fderiv ℝ S.axis p l)) v p) (S.idempotent p) w=0
    rw [H.translated_curvature hp,K_neg_coeff,P.axial_zero F (S.idempotent_square hp),neg_zero]
  have hD : ContDiffOn ℝ ∞ D S.domain := directions.smooth S.isOpen S.smooth [b]
  have ha : ContDiffOn ℝ ∞ S.a S.domain := contDiffOn_sectionValue S.smooth S.smoothAxis
  have he : ContDiffOn ℝ ∞ S.idempotent S.domain := (ha.inv (fun q hq ↦ (S.positive q hq).ne')).smul S.smoothAxis
  have hpos (q : E) (hq : q ∈ S.domain) : K (D q) (S.idempotent q) (S.idempotent q)=0 := by
    change K (fderiv ℝ S.field q b) _ _=0
    rw [LiftedSection.idempotent,K_smul_left,K_smul_right,(S.weighted_ruling hq H.maximizes).1 b,smul_zero,smul_zero]
  have h₀ : D p=0 := H.inactive_slope hp l
  exact ⟨h₀,hf,second_axial_zero S.isOpen hD he hpos hp h₀ hf⟩

include H in
theorem constant_translated_jet {p : E} {U : Set E} {r : ℝ} (R : FirstJetStrip S U r) (hp : p ∈ U)
    {t : ℝ} (ht : t ∈ ball 0 r) (l w : E) :
    let b := fderiv ℝ S.axis p l
    directional (directional S.field b) w (position S t p)=directional (directional S.field b) w p := by
  let b := fderiv ℝ S.axis p l
  let hpS := R.inside hp
  let J := fderiv ℝ S.field
  let A := fderiv ℝ S.axis p
  have he : J =ᶠ[𝓝 p] J ∘ position S t :=
    (show ∀ᶠ x in 𝓝 p, x ∈ U from R.isOpen.mem_nhds hp).mono fun x hx ↦ (R.fieldJet x hx t ht).symm
  have hJ : ContDiffOn ℝ ∞ J S.domain := S.smooth.fderiv_of_isOpen S.isOpen (by simp)
  have h := H.derivative_under_shear hpS t ((hJ.contDiffAt (S.isOpen.mem_nhds (R.maps p hp t ht))).differentiableAt (by simp)) he w
  have hs : K (S.field p) (S.idempotent p) (A w)=(1/2:ℝ) • A w :=
    (S.idempotent_slice p _).trans ((S.weighted_ruling hpS H.maximizes).2.1 w)
  let P := H.freeze hpS [] H.inactive_one
  have hz : fderiv ℝ J p (A w) b=0 := by
    rw [← translation_derivative hpS b (A w),H.translated_curvature hpS,P.support hs (by norm_num [FixedAxis.Resonant]),neg_zero]
  dsimp only
  rw [translation_derivative (R.maps p hp t ht),translation_derivative hpS]
  change fderiv ℝ J (position S t p) w b=fderiv ℝ J p w b
  rw [h,map_sub,map_smul,sub_apply,smul_apply,hz,smul_zero,sub_zero]

end EuclideanMidpointRigidity.HorizontalPatch

