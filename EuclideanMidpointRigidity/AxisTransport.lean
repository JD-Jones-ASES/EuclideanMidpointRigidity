module

public import EuclideanMidpointRigidity.CriticalSixthReduction
public import EuclideanMidpointRigidity.CriticalLift
public import EuclideanMidpointRigidity.MovingJets

/-! # The inhomogeneous vector transport equation along a critical lift -/

@[expose] public section
noncomputable section
open Set
open scoped ContDiff
namespace EuclideanMidpointRigidity

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

def axisU (C : E → Coeff) (p e : E) := firstProduct C p e e e
def axisV (C : E → Coeff) (p e : E) := secondProduct C p e e e e

def axisUDerivative (a : ℝ) (C : E → Coeff) (p e : E) : E :=
  let q := liftStep a (fderiv ℝ C p) e
  axisV C p e + firstProduct C p q e e + firstProduct C p e q e + firstProduct C p e e q

/-- For the frozen eigenvalue `a`, this is also
`a U' - 12 (DₑK)(e,U) + (25/2) (DᵤK)(e,e)`. -/
def axisMoment (a : ℝ) (C : E → Coeff) (p e : E) : E :=
  let U := axisU C p e
  a • axisV C p e + (13:ℝ) • firstProduct C p U e e - (11:ℝ) • firstProduct C p e e U

private theorem transport_algebra {a : ℝ} (ha : a≠0) (J : E →L[ℝ] Coeff)
    (H : E →L[ℝ] E →L[ℝ] Coeff) (e U V W Y : E) (hsym : H U e=H e U)
    (hW : a • W = a^3 • U + (4:ℝ) • K (J V) e e - (8:ℝ) • K (J e) e V +
      (10:ℝ) • K (H e e) e U - (14:ℝ) • K (H e U) e e) :
    let k := (2*a)⁻¹
    let q := k • U
    a • (W+K (H q e) e e+K (H e q) e e+K (H e e) q e+K (H e e) e q) +
      (13:ℝ) • (K (H e U) e e+K (J Y) e e+K (J U) q e+K (J U) e q) -
      (11:ℝ) • (K (H e e) e U+K (J q) e U+K (J e) q U+K (J e) e Y) =
    a^3 • U + (4:ℝ) • K (J V) e e - (8:ℝ) • K (J e) e V +
      (13:ℝ) • K (J Y) e e - (11:ℝ) • K (J e) e Y +
      (15*k) • K (J U) e U - (11*k) • K (J e) U U := by
  have hk : a*(2*a)⁻¹=(1/2:ℝ) := by field_simp
  letI : AddMonoid Coeff := (cubicNormedAddCommGroup d).toAddCommGroup.toAddCommMonoid.toAddMonoid
  simp only [map_smul,smul_apply,K_smul_coeff,K_smul_left,K_smul_right,
    hsym,K_symm (H e e) U e,K_symm (J U) U e,smul_add,smul_smul,hk]
  linear_combination (norm := module) hW

theorem critical_axis_transport {Ω : Set E} {C : E → Coeff} (hΩ : IsOpen Ω)
    (hC : ContDiffOn ℝ ∞ C Ω) (hm : MidpointJetEquations Ω C)
    (x e : ℝ → E) {t a : ℝ} (ha : a≠0) (ht : x t ∈ Ω)
    (haxis : K (C (x t)) (e t) (e t)=a • e t) (hx : HasDerivAt x (e t) t)
    (he : HasDerivAt e (liftStep a (fderiv ℝ C (x t)) (e t)) t) :
    let p := x t
    let z := e t
    let U := axisU C p z
    let V := axisV C p z
    let Y := axisUDerivative a C p z
    let k := (2*a)⁻¹
    HasDerivAt (fun s ↦ axisMoment a C (x s) (e s))
      (a^3 • U + (4:ℝ) • firstProduct C p V z z - (8:ℝ) • firstProduct C p z z V +
       (13:ℝ) • firstProduct C p Y z z - (11:ℝ) • firstProduct C p z z Y +
       (15*k) • firstProduct C p U z U - (11*k) • firstProduct C p z U U) t := by
  let p := x t
  let z := e t
  let U := axisU C p z
  let V := axisV C p z
  let Y := axisUDerivative a C p z
  let J := fderiv ℝ C p
  let H := fderiv ℝ (fderiv ℝ C) p
  let W := thirdProduct C p z z z z z
  have hc := hC.contDiffAt (hΩ.mem_nhds ht)
  have hu : HasDerivAt (fun s ↦ axisU C (x s) (e s)) Y t := hasDerivAt_firstProduct C hc hx he he he
  have hv := hasDerivAt_secondProduct C hc hx he he he he
  have hr := hasDerivAt_firstProduct C hc hx hu he he
  have hz := hasDerivAt_firstProduct C hc hx he he hu
  have hd := ((hv.fun_const_smul a).fun_add (hr.fun_const_smul (13:ℝ))).fun_sub (hz.fun_const_smul (11:ℝ))
  have hS : H U z=H z U := (hc.isSymmSndFDerivAt (by simp)) U z
  have heq := transport_algebra ha J H z U V W Y hS (critical_sixth_vector hΩ hC hm ht z a haxis)
  dsimp only [p,z,U,V,W,Y,J,H] at heq
  dsimp only [firstProduct,secondProduct,thirdProduct,axisU,axisV,liftStep] at hd heq ⊢
  rw [← heq]
  exact hd

end EuclideanMidpointRigidity
