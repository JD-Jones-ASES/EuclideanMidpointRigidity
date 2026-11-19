module

public import EuclideanMidpointRigidity.LineFamilyOperations
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Clearing spatial derivatives in a family of coordinate charts -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
variable {E V Z T H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [NormedAddCommGroup H] [NormedSpace ℝ H]

structure LineChart (E V : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] where
  domain : Set E
  isOpen : IsOpen domain
  position : ℝ → E → E
  jacobian : E → ℝ → (E →L[ℝ] E)
  hasJacobian : ∀ p ∈ domain, ∀ t, HasFDerivAt (position t) (jacobian p t) p
  determinant : E → ℝ → ℝ
  detFamily : AnalyticLineFamily domain determinant
  adjugate : E → ℝ → (E →L[ℝ] E)
  adjFamily : AnalyticLineFamily domain adjugate
  adjIdentity : ∀ y ∈ domain, ∀ t v, jacobian y t (adjugate y t v)=determinant y t • v
  field : E → ℝ → V
  fieldFamily : AnalyticLineFamily domain field

/-- On any chart germ on which the field is a pullback, the numerator equals
the physical differential expression multiplied by a power of the determinant. -/
structure ClearedExpression (A : LineChart E V) (expr : (E → V) → E → Z) where
  weight : ℕ
  numerator : E → ℝ → Z
  family : AnalyticLineFamily A.domain numerator
  smooth : ∀ {Ω : Set E} {G : E → V}, IsOpen Ω → ContDiffOn ℝ ∞ G Ω → ContDiffOn ℝ ∞ (expr G) Ω
  correct : ∀ {Ω : Set E} {G : E → V} {y : E} {t : ℝ}, IsOpen Ω → ContDiffOn ℝ ∞ G Ω → y ∈ A.domain →
    A.position t y ∈ Ω → (fun z ↦ A.field z t) =ᶠ[𝓝 y] (G ∘ A.position t) →
    numerator y t=A.determinant y t^weight • expr G (A.position t y)

namespace ClearedExpression
variable {A : LineChart E V} {f g : (E → V) → E → Z} {v : (E → V) → E → T}

def field (A : LineChart E V) : ClearedExpression A (fun G ↦ G) where
  weight := 0
  numerator := A.field
  family := A.fieldFamily
  smooth _ h := h
  correct _ _ _ _ h := by simpa only [pow_zero,one_smul,Function.comp_apply] using h.eq_of_nhds

def const (A : LineChart E V) (z : Z) : ClearedExpression A (fun _ _ ↦ z) where
  weight := 0
  numerator := fun _ _ ↦ z
  family := AnalyticLineFamily.const _ _
  smooth _ _ := contDiffOn_const
  correct _ _ _ _ _ := by simp

def linear (F : ClearedExpression A f) (L : Z →L[ℝ] H) : ClearedExpression A (fun G x ↦ L (f G x)) where
  weight := F.weight
  numerator := fun y t ↦ L (F.numerator y t)
  family := F.family.linear L
  smooth hΩ hG := L.contDiff.comp_contDiffOn (F.smooth hΩ hG)
  correct hΩ hG hy hx he := by rw [F.correct hΩ hG hy hx he,map_smul]

def bilinear (F : ClearedExpression A f) (G : ClearedExpression A v) (L : Z →L[ℝ] T →L[ℝ] H) :
    ClearedExpression A (fun C x ↦ L (f C x) (v C x)) where
  weight := F.weight+G.weight
  numerator := fun y t ↦ L (F.numerator y t) (G.numerator y t)
  family := (F.family.linear L).applyCLM G.family
  smooth hΩ hC := (L.contDiff.comp_contDiffOn (F.smooth hΩ hC)).clm_apply (G.smooth hΩ hC)
  correct hΩ hC hy hx he := by
    simp only [F.correct hΩ hC hy hx he,G.correct hΩ hC hy hx he,map_smul,smul_apply,smul_smul,pow_add,mul_comm]

def add (F : ClearedExpression A f) (G : ClearedExpression A g) : ClearedExpression A (fun C x ↦ f C x+g C x) where
  weight := F.weight+G.weight
  numerator := fun y t ↦ A.determinant y t^G.weight • F.numerator y t+A.determinant y t^F.weight • G.numerator y t
  family := ((A.detFamily.pow G.weight).smul F.family).add ((A.detFamily.pow F.weight).smul G.family)
  smooth hΩ hC := (F.smooth hΩ hC).add (G.smooth hΩ hC)
  correct hΩ hC hy hx he := by
    rw [F.correct hΩ hC hy hx he,G.correct hΩ hC hy hx he,pow_add,smul_add,smul_smul,smul_smul,mul_comm (_^G.weight) (_^F.weight)]

def applyCLM {L : (E → V) → E → (T →L[ℝ] H)} (F : ClearedExpression A L) (G : ClearedExpression A v) :
    ClearedExpression A (fun C x ↦ L C x (v C x)) := F.bilinear G (ContinuousLinearMap.id ℝ (T →L[ℝ] H))

def scale (F : ClearedExpression A f) (c : ℝ) : ClearedExpression A (fun C x ↦ c • f C x) :=
  F.linear (c • ContinuousLinearMap.id ℝ Z)

def derivative (F : ClearedExpression A f) : ClearedExpression A (fun G x ↦ fderiv ℝ (f G) x) := by
  let M := fun y t ↦ A.determinant y t^F.weight
  let MF := A.detFamily.pow F.weight
  let dM := fun y t ↦ fderiv ℝ (fun z ↦ M z t) y
  let dN := fun y t ↦ fderiv ℝ (fun z ↦ F.numerator z t) y
  let N := fun y t ↦ (M y t • dN y t-(dM y t).smulRight (F.numerator y t)).comp (A.adjugate y t)
  refine ⟨F.weight+(F.weight+1),N,((MF.smul (F.family.spatialDerivative A.isOpen)).sub
    ((MF.spatialDerivative A.isOpen).smulRight F.family)).composeCLM A.adjFamily,
    fun hΩ hG ↦ (F.smooth hΩ hG).fderiv_of_isOpen hΩ (by simp),?_⟩
  intro Ω G y t hΩ hG hy hx he
  have hj := A.hasJacobian y hy t
  have hnear : (fun z ↦ F.numerator z t) =ᶠ[𝓝 y] (fun z ↦ M z t • f G (A.position t z)) := by
    filter_upwards [A.isOpen.mem_nhds hy,hj.continuousAt (hΩ.mem_nhds hx),eventually_eventually_nhds.mpr he] with z hz hv heq
    exact F.correct hΩ hG hz hv heq
  have hM : HasFDerivAt (fun z ↦ M z t) (dM y t) y := (((MF.smooth_space t).contDiffAt (A.isOpen.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
  have hf : HasFDerivAt (f G) (fderiv ℝ (f G) (A.position t y)) (A.position t y) := (((F.smooth hΩ hG).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have hdn : dN y t=M y t • (fderiv ℝ (f G) (A.position t y)).comp (A.jacobian y t)+(dM y t).smulRight (f G (A.position t y)) :=
    hnear.fderiv_eq.trans ((hM.smul (hf.comp y hj)).fderiv)
  ext b : 1
  change M y t • (dN y t (A.adjugate y t b))-(dM y t (A.adjugate y t b)) • F.numerator y t=_
  rw [hdn,F.correct hΩ hG hy hx he]
  simp only [add_apply,smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply,A.adjIdentity y hy,map_smul,smul_add,smul_smul,pow_add,pow_succ,M]
  module

end ClearedExpression
end EuclideanMidpointRigidity

