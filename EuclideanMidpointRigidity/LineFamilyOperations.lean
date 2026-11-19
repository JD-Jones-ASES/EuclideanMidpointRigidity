module

public import EuclideanMidpointRigidity.AnalyticLineFamily

/-! # Algebraic operations on line-analytic families -/

@[expose] public section
noncomputable section
open Set
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.AnalyticLineFamily
variable {Y V Z T : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup T] [NormedSpace ℝ T] {W : Set Y}

def add {f g : Y → ℝ → V} (F : AnalyticLineFamily W f) (G : AnalyticLineFamily W g) :
    AnalyticLineFamily W (fun y t ↦ f y t+g y t) :=
  (F.prod G).map _ (contDiff_fst.add contDiff_snd)

def sub {f g : Y → ℝ → V} (F : AnalyticLineFamily W f) (G : AnalyticLineFamily W g) :
    AnalyticLineFamily W (fun y t ↦ f y t-g y t) :=
  (F.prod G).map _ (contDiff_fst.sub contDiff_snd)

def smul {a : Y → ℝ → ℝ} {f : Y → ℝ → V} (A : AnalyticLineFamily W a) (F : AnalyticLineFamily W f) :
    AnalyticLineFamily W (fun y t ↦ a y t • f y t) :=
  (A.prod F).map _ (contDiff_fst.smul contDiff_snd)

def pow {a : Y → ℝ → ℝ} (A : AnalyticLineFamily W a) (n : ℕ) :
    AnalyticLineFamily W (fun y t ↦ (a y t)^n) := A.map _ (contDiff_id.pow n)

def linear {f : Y → ℝ → V} (F : AnalyticLineFamily W f) (L : V →L[ℝ] Z) :
    AnalyticLineFamily W (fun y t ↦ L (f y t)) := F.map L L.contDiff

def applyCLM {f : Y → ℝ → (V →L[ℝ] Z)} {g : Y → ℝ → V} (F : AnalyticLineFamily W f) (G : AnalyticLineFamily W g) :
    AnalyticLineFamily W (fun y t ↦ f y t (g y t)) := (F.prod G).map _ (contDiff_fst.clm_apply contDiff_snd)

def composeCLM {f : Y → ℝ → (V →L[ℝ] Z)} {g : Y → ℝ → (T →L[ℝ] V)} (F : AnalyticLineFamily W f) (G : AnalyticLineFamily W g) :
    AnalyticLineFamily W (fun y t ↦ (f y t).comp (g y t)) := (F.prod G).map _ (contDiff_fst.clm_comp contDiff_snd)

def smulRight {f : Y → ℝ → (V →L[ℝ] ℝ)} {g : Y → ℝ → Z} (F : AnalyticLineFamily W f) (G : AnalyticLineFamily W g) :
    AnalyticLineFamily W (fun y t ↦ (f y t).smulRight (g y t)) := (F.prod G).map _ (contDiff_fst.smulRight contDiff_snd)

end EuclideanMidpointRigidity.AnalyticLineFamily

