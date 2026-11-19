module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Tactic

/-! # Line-analytic families with smooth transverse parameters -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
variable {Y V Z T : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup T] [NormedSpace ℝ T]

/-- A smooth parameter substituted into a jointly real-analytic function. This
representation also controls all spatial derivatives along a parameter line. -/
structure AnalyticLineFamily (W : Set Y) (f : Y → ℝ → V) where
  Parameter : Type
  [group : NormedAddCommGroup Parameter]
  [space : NormedSpace ℝ Parameter]
  parameter : Y → Parameter
  smooth : ContDiffOn ℝ ∞ parameter W
  evaluate : Parameter × ℝ → V
  analytic : ContDiff ℝ ω evaluate
  equals : ∀ y ∈ W, ∀ s, f y s=evaluate (parameter y,s)

attribute [instance] AnalyticLineFamily.group AnalyticLineFamily.space

namespace AnalyticLineFamily
variable {W : Set Y} {f : Y → ℝ → V} {g : Y → ℝ → Z}

def spatial {p : Y → V} (hp : ContDiffOn ℝ ∞ p W) : AnalyticLineFamily W (fun y _ ↦ p y) where
  Parameter := V
  parameter := p
  smooth := hp
  evaluate := Prod.fst
  analytic := contDiff_fst
  equals _ _ _ := rfl

def time (W : Set Y) : AnalyticLineFamily W (fun _ s ↦ s) where
  Parameter := ℝ
  parameter := fun _ ↦ 0
  smooth := contDiffOn_const
  evaluate := Prod.snd
  analytic := contDiff_snd
  equals _ _ _ := rfl

def const (W : Set Y) (v : V) : AnalyticLineFamily W (fun _ _ ↦ v) := spatial (contDiffOn_const (c := v))

def congr (F : AnalyticLineFamily W f) {a : Y → ℝ → V} (he : ∀ y ∈ W, ∀ s, a y s=f y s) :
    AnalyticLineFamily W a := {F with equals := fun y hy s ↦ (he y hy s).trans (F.equals y hy s)}

def mono (F : AnalyticLineFamily W f) {U : Set Y} (hs : U ⊆ W) : AnalyticLineFamily U f :=
  {F with smooth := F.smooth.mono hs, equals := fun y hy ↦ F.equals y (hs hy)}

def prod (F : AnalyticLineFamily W f) (G : AnalyticLineFamily W g) :
    AnalyticLineFamily W (fun y s ↦ (f y s,g y s)) where
  Parameter := F.Parameter × G.Parameter
  parameter := fun y ↦ (F.parameter y,G.parameter y)
  smooth := F.smooth.prodMk G.smooth
  evaluate := fun v ↦ (F.evaluate (v.1.1,v.2),G.evaluate (v.1.2,v.2))
  analytic := (F.analytic.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)).prodMk
    (G.analytic.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd))
  equals y hy s := Prod.ext (F.equals y hy s) (G.equals y hy s)

def map (F : AnalyticLineFamily W f) (a : V → Z) (ha : ContDiff ℝ ω a) :
    AnalyticLineFamily W (fun y s ↦ a (f y s)) where
  Parameter := F.Parameter
  parameter := F.parameter
  smooth := F.smooth
  evaluate := a ∘ F.evaluate
  analytic := ha.comp F.analytic
  equals y hy s := congrArg a (F.equals y hy s)

theorem analytic_time (F : AnalyticLineFamily W f) {y : Y} (hy : y ∈ W) : ContDiff ℝ ω (f y) := by
  rw [show f y=fun s ↦ F.evaluate (F.parameter y,s) from funext (F.equals y hy)]
  exact F.analytic.comp (contDiff_const.prodMk contDiff_id)

theorem smooth_space (F : AnalyticLineFamily W f) (s : ℝ) : ContDiffOn ℝ ∞ (fun y ↦ f y s) W := by
  apply (F.analytic.of_le (show (∞:WithTop ℕ∞)≤ω by simp) |>.contDiffOn.comp (F.smooth.prodMk contDiffOn_const)
    (t := univ) (fun _ _ ↦ mem_univ _)).congr
  exact fun y hy ↦ F.equals y hy s

def spatialDerivative (F : AnalyticLineFamily W f) (hW : IsOpen W) :
    AnalyticLineFamily W (fun y s ↦ fderiv ℝ (fun z ↦ f z s) y) where
  Parameter := F.Parameter × (Y →L[ℝ] F.Parameter)
  parameter := fun y ↦ (F.parameter y,fderiv ℝ F.parameter y)
  smooth := F.smooth.prodMk (F.smooth.fderiv_of_isOpen hW (by simp))
  evaluate := fun q ↦ (fderiv ℝ F.evaluate (q.1.1,q.2)).comp (q.1.2.prod 0)
  analytic := by
    have hd : ContDiff ℝ ω (fderiv ℝ F.evaluate) := F.analytic.fderiv_right (by simp)
    have h₁ : ContDiff ℝ ω (fun q : (F.Parameter × (Y →L[ℝ] F.Parameter)) × ℝ ↦ fderiv ℝ F.evaluate (q.1.1,q.2)) :=
      hd.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
    apply ContDiff.clm_comp h₁
    change ContDiff ℝ ω (fun q : (F.Parameter × (Y →L[ℝ] F.Parameter)) × ℝ ↦ q.1.2.prod (0 : Y →L[ℝ] ℝ))
    have he (L : Y →L[ℝ] F.Parameter) : L.prod (0 : Y →L[ℝ] ℝ)=(ContinuousLinearMap.inl ℝ F.Parameter ℝ).comp L := by ext v : 1; rfl
    simp_rw [he]
    exact contDiff_const.clm_comp (contDiff_snd.comp contDiff_fst)
  equals y hy s := by
    let g := fun z ↦ (F.parameter z,s)
    have he : (fun z ↦ f z s)=ᶠ[𝓝 y] F.evaluate ∘ g :=
      (show ∀ᶠ z in 𝓝 y, z ∈ W from hW.mem_nhds hy).mono (fun z hz ↦ F.equals z hz s)
    have hp := ((F.smooth.contDiffAt (hW.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
    have dg : HasFDerivAt g ((fderiv ℝ F.parameter y).prod 0) y := hp.prodMk (hasFDerivAt_const s y)
    exact he.fderiv_eq.trans (((F.analytic.differentiable (by simp) _).hasFDerivAt.comp y dg).fderiv)

theorem extend_zero (F : AnalyticLineFamily W f) {y : Y} (hy : y ∈ W) {s : ℝ} (he : f y =ᶠ[𝓝 s] (fun _ ↦ 0)) :
    ∀ t, f y t=0 := by
  have eq := (F.analytic_time hy).analyticOnNhd.eq_of_eventuallyEq (contDiff_const (c := (0:V)) (n := ω)).analyticOnNhd he
  exact fun t ↦ congrFun eq t

end AnalyticLineFamily
end EuclideanMidpointRigidity

