module

public import EuclideanMidpointRigidity.FlatProduct
public import EuclideanMidpointRigidity.RealizedChords

/-! # Translating a field and differentiating the forced endpoint equation -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
set_option backward.isDefEq.respectTransparency false

theorem directions.leading_apply_right {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {W : Set E} (hW : IsOpen W) {p : E} (hp : p ∈ W) (xs : List E) {A : E → F →L[ℝ] G} {v : E → F}
    (hA : ContDiffOn ℝ ∞ A W) (hv : ContDiffOn ℝ ∞ v W)
    (hz : ∀ ys : List E, ys.length<xs.length → directions v ys p=0) :
    directions (fun y ↦ A y (v y)) xs p=A p (directions v xs p) := by
  let L : F →L[ℝ] (F →L[ℝ] G) →L[ℝ] G := ContinuousLinearMap.apply ℝ G
  have hc := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) («E» := F) (F := (F →L[ℝ] G) →L[ℝ] G) L
  have hL := ContDiff.comp_contDiffOn («E» := E) (F := F) (G := (F →L[ℝ] G) →L[ℝ] G) hc hv
  have ev (ys : List E) : directions (L ∘ v) ys p=L (directions v ys p) :=
    directions.linear_map («E» := E) (F := F) (G := (F →L[ℝ] G) →L[ℝ] G) hW hv L ys hp
  have h := directions.leading_apply hW hp xs hL hA (fun ys hy ↦ by rw [ev,hz ys hy,map_zero])
  rw [ev] at h
  exact h

namespace SmoothEndpointFamily
variable {d : ℕ} {C : Space d → Cubic d} {σ r : ℝ} {p : Space d} (F : SmoothEndpointFamily C σ p r)
local notation "E" => Space d
local notation "H" => E × E
local notation "P" => PhaseCurve d
local notation "Q" => AccelerationCurve d
set_option backward.isDefEq.respectTransparency false

def translationPhase (b : E) : P := ContinuousMap.const UnitInterval (b,0)
def translatedVariation (b : E) (q : H) := F.variation q (b,b)-translationPhase b
def translatedSource (b : E) (q : H) := F.linearForce q (translationPhase b)

theorem smooth_linearForce : ContDiffOn ℝ ∞ F.linearForce F.domain := by
  let D : C(H,H →L[ℝ] E) := ⟨fderiv ℝ (F.force : H → E),F.smoothForce.continuous_fderiv (by decide)⟩
  let A : C(UnitInterval,H →L[ℝ] E) →L[ℝ] (P →L[ℝ] Q) := pathApply
  have ha := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) («E» := C(UnitInterval,H →L[ℝ] E)) (F := P →L[ℝ] Q) A
  have hd : ContDiff ℝ ∞ (D : H → H →L[ℝ] E) := F.smoothForce.fderiv_right (by simp)
  exact ha.comp_contDiffOn ((postcomp_contDiff D hd).comp_contDiffOn F.smooth)

theorem smooth_translated (b : E) : ContDiffOn ℝ ∞ (F.translatedVariation b) F.domain := by
  have hv : ContDiffOn ℝ ∞ (fun q ↦ F.variation q (b,b)) F.domain := fun q hq ↦ (F.smooth_variation hq (b,b)).contDiffWithinAt
  exact hv.sub contDiffOn_const

theorem translated_equation (b : E) {q : H} (hq : q ∈ F.domain) :
    F.translatedVariation b q=greenOperator (F.translatedSource b q+F.linearForce q (F.translatedVariation b q)) := by
  have he := F.variation_equation hq (b,b)
  rw [affinePhaseMap_apply,affinePhase_diagonal] at he
  change F.variation q (b,b)-translationPhase b=greenOperator (F.linearForce q (translationPhase b)+
    F.linearForce q (F.variation q (b,b)-translationPhase b))
  rw [map_sub,add_sub_cancel]
  change F.variation q (b,b)-ContinuousMap.const UnitInterval (b,0)=_
  exact sub_eq_iff_eq_add.mpr (he.trans (add_comm _ _))

theorem translated_word (b : E) {q : H} (hq : q ∈ F.domain) (xs : List H)
    (hz : ∀ ys : List H, ys.length<xs.length → directions (F.translatedVariation b) ys q=0) :
    directions (F.translatedVariation b) xs q=greenOperator
      (directions (F.translatedSource b) xs q+F.linearForce q (directions (F.translatedVariation b) xs q)) := by
  let V := F.translatedVariation b
  let N := F.translatedSource b
  let M := F.linearForce
  have hN : ContDiffOn ℝ ∞ N F.domain := F.smooth_linearForce.clm_apply contDiffOn_const
  have hMV : ContDiffOn ℝ ∞ (fun x ↦ M x (V x)) F.domain := F.smooth_linearForce.clm_apply (F.smooth_translated b)
  have he : V =ᶠ[𝓝 q] greenOperator ∘ (fun x ↦ N x+M x (V x)) :=
    (show ∀ᶠ x in 𝓝 q, x ∈ F.domain from F.isOpen.mem_nhds hq).mono fun _ hx ↦ F.translated_equation b hx
  have hh := (directions.congr_germ he xs).eq_of_nhds
  rw [directions.linear_map F.isOpen (hN.add hMV) greenOperator xs hq] at hh
  dsimp only [Function.comp_apply] at hh
  rw [directions.add F.isOpen hN hMV xs hq] at hh
  dsimp only at hh
  rw [directions.leading_apply_right F.isOpen hq xs F.smooth_linearForce (F.smooth_translated b) hz] at hh
  exact hh

theorem translated_flat (b : E) {q : H} (hq : q ∈ F.domain) (n : ℕ)
    (hz : ∀ ys : List H, ys.length<n → directions (F.translatedSource b) ys q=0) :
    ∀ xs : List H, xs.length<n → directions (F.translatedVariation b) xs q=0 := by
  have h (k : ℕ) : ∀ xs : List H, xs.length=k → k<n → directions (F.translatedVariation b) xs q=0 := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro xs hx hk
      have he := F.translated_word b hq xs (fun ys hy ↦ ih ys.length (hy.trans_eq hx) ys rfl (hy.trans (hx ▸ hk)))
      rw [hz xs (hx ▸ hk),zero_add] at he
      apply linearized_green_unique (I := UnitInterval) («E» := H) (F := E) greenOperator F.force F.smoothForce (F.regular q hq) (a := (0:P))
      · rw [zero_add]; exact he
      · rw [map_zero,map_zero,add_zero]
  exact fun xs hn ↦ h _ xs rfl hn

end SmoothEndpointFamily
end EuclideanMidpointRigidity

