module

public import EuclideanMidpointRigidity.TranslatedVariations

/-! # Translating and varying the two dual midpoints at the same endpoints -/

public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity

theorem directions.map_inputs {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {U : Set E} {V : Set F} {g : F → G} (hU : IsOpen U) (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V)
    (L : E →L[ℝ] F) (hm : MapsTo L U V) (xs : List E) :
    EqOn (directions (g ∘ L) xs) (directions g (xs.map L) ∘ L) U := by
  induction xs with
  | nil => exact fun _ _ ↦ rfl
  | cons w ws ih =>
    intro x hx
    have he : directions (g ∘ L) ws =ᶠ[𝓝 x] (directions g (ws.map L) ∘ L) :=
      (show ∀ᶠ y in 𝓝 x, y ∈ U from hU.mem_nhds hx).mono fun _ hy ↦ ih hy
    have h := (((directions.smooth hV hg (ws.map L)).contDiffAt (hV.mem_nhds (hm hx))).differentiableAt (by simp)).hasFDerivAt.comp x L.hasFDerivAt
    exact DFunLike.congr_fun (he.fderiv_eq.trans h.fderiv) w

namespace OrientedEndpointChart
variable {d : ℕ} {C : Space d → Cubic d} {p : Space d} (D : OrientedEndpointChart C p)
local notation "E" => Space d
local notation "H" => E × E
local notation "P" => PhaseCurve d
set_option backward.isDefEq.respectTransparency false

theorem translated_law {q : H} (hq : q ∈ D.domain) (b : E) (xs : List H) :
    midpointEvaluation (directions (D.plus.translatedVariation b) xs q)+
      midpointEvaluation (directions (D.minus.translatedVariation b) (xs.map Prod.swap) q.swap)=0 := by
  let S : H →L[ℝ] H := (ContinuousLinearMap.snd ℝ E E).prod (ContinuousLinearMap.fst ℝ E E)
  let L := midpointEvaluation (d := d)
  let Y := D.plus.translatedVariation b
  let Z := D.minus.translatedVariation b
  have hm : MapsTo S D.domain D.minus.domain := fun x hx ↦ D.minusDomain x hx
  have hY : ContDiffOn ℝ ∞ Y D.domain := (D.plus.smooth_translated b).mono (fun x h ↦ D.plusDomain x h)
  have hZ : ContDiffOn ℝ ∞ (Z ∘ S) D.domain := (D.minus.smooth_translated b).comp S.contDiff.contDiffOn hm
  have hzero : L ∘ (fun x ↦ Y x+Z (S x)) =ᶠ[𝓝 q] (fun _ ↦ 0) := by
    filter_upwards [D.isOpen.mem_nhds hq] with x hx
    have h := D.variation_law hx (b,b)
    change midpointEvaluation (D.plus.variation x (b,b))+midpointEvaluation (D.minus.variation x.swap (b,b))=b+b at h
    change L ((D.plus.variation x (b,b)-SmoothEndpointFamily.translationPhase b)+(D.minus.variation x.swap (b,b)-SmoothEndpointFamily.translationPhase b))=0
    rw [map_add,map_sub,map_sub,show L (SmoothEndpointFamily.translationPhase b)=b from rfl]
    change (L (D.plus.variation x (b,b))-b)+(L (D.minus.variation x.swap (b,b))-b)=0
    linear_combination (norm := abel) h
  have hh := (directions.congr_germ hzero xs).eq_of_nhds
  have hsum : ContDiffOn ℝ ∞ (fun x ↦ Y x+Z (S x)) D.domain := hY.add hZ
  rw [directions.zero,directions.linear_map D.isOpen hsum L xs hq] at hh
  change L (directions (fun x ↦ Y x+(Z ∘ S) x) xs q)=0 at hh
  rw [directions.add D.isOpen hY hZ xs hq] at hh
  change L (directions Y xs q+directions (Z ∘ S) xs q)=0 at hh
  rw [directions.map_inputs D.isOpen D.minus.isOpen (D.minus.smooth_translated b) S hm xs hq,map_add] at hh
  exact hh

end OrientedEndpointChart
end EuclideanMidpointRigidity

