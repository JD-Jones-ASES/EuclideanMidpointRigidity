module

public import EuclideanMidpointRigidity.SmoothComplementarity
public import EuclideanMidpointRigidity.LinearizedDirichlet

/-! # The first and mixed second variations of an actual endpoint family -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.SmoothEndpointFamily
variable {d : ℕ} {C : Space d → Cubic d} {σ r : ℝ} {p : Space d} (F : SmoothEndpointFamily C σ p r)
local notation "E" => Space d
local notation "H" => E × E
local notation "P" => PhaseCurve d
local notation "Q" => AccelerationCurve d
set_option backward.isDefEq.respectTransparency false

def variation (q u : H) : P := fderiv ℝ F.phase q u
def mixedVariation (q u v : H) : P := fderiv ℝ (fun a ↦ F.variation a u) q v

def linearForce (q : H) : P →L[ℝ] Q := pathForceDerivative F.force F.smoothForce (F.phase q)

def secondForce (q : H) (u v : P) : Q :=
  let D : C(H,H →L[ℝ] E) := ⟨fderiv ℝ (F.force : H → E),F.smoothForce.continuous_fderiv (by decide)⟩
  pathApply (pathForceDerivative D (F.smoothForce.fderiv_right (by simp)) (F.phase q) v) u

theorem secondForce_apply (q : H) (u v : P) (s : UnitInterval) : F.secondForce q u v s=
    fderiv ℝ (fderiv ℝ (F.force : H → E)) (F.phase q s) (v s) (u s) := rfl

theorem smooth_variation {q : H} (hq : q ∈ F.domain) (u : H) : ContDiffAt ℝ ∞ (fun x ↦ F.variation x u) q :=
  ((F.smooth.contDiffAt (F.isOpen.mem_nhds hq)).fderiv_right (by simp)).clm_apply contDiffAt_const

theorem variation_equation {q : H} (hq : q ∈ F.domain) (u : H) :
    F.variation q u=affinePhaseMap u+greenOperator (F.linearForce q (F.variation q u)) := by
  have dy := ((F.smooth.contDiffAt (F.isOpen.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt
  have df := (hasFDerivAt_pathForce F.force F.smoothForce (F.phase q)).comp q dy
  have rhs := (affinePhaseMap (d := d)).hasFDerivAt (x := q) |>.fun_add (greenOperator.hasFDerivAt.comp q df)
  have hn : ∀ᶠ a in 𝓝 q, a ∈ F.domain := F.isOpen.mem_nhds hq
  have h := dy.unique (rhs.congr_of_eventuallyEq (hn.mono fun a ha ↦ F.equation a ha))
  exact congrArg (fun L : H →L[ℝ] P ↦ L u) h

theorem variation_unique {q : H} (hq : q ∈ F.domain) (u : H) {z : P}
    (hz : z=affinePhaseMap u+greenOperator (F.linearForce q z)) : z=F.variation q u :=
  linearized_green_unique greenOperator F.force F.smoothForce (F.regular q hq) hz (F.variation_equation hq u)

theorem mixed_variation_equation {q : H} (hq : q ∈ F.domain) (u v : H) :
    F.mixedVariation q u v=greenOperator (F.secondForce q (F.variation q u) (F.variation q v)+
      F.linearForce q (F.mixedVariation q u v)) := by
  let line := fun t : ℝ ↦ q+t • v
  have h₀ : line 0=q := by simp [line]
  have dl : HasDerivAt line v 0 := by simpa [line] using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add q
  have hn : ∀ᶠ t in 𝓝 (0:ℝ), line t ∈ F.domain := dl.continuousAt (h₀ ▸ F.isOpen.mem_nhds hq)
  have dy : HasDerivAt (F.phase ∘ line) (F.variation q v) 0 :=
    ((F.smooth.contDiffAt (F.isOpen.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 dl h₀.symm
  have dw : HasDerivAt ((fun a ↦ F.variation a u) ∘ line) (F.mixedVariation q u v) 0 :=
    ((F.smooth_variation hq u).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 dl h₀.symm
  have ds := hasDerivAt_pathForceDerivative_apply F.force F.smoothForce dy dw
  have drhs := (greenOperator.hasFDerivAt.comp_hasDerivAt 0 ds).const_add (affinePhaseMap u)
  have h := dw.unique (drhs.congr_of_eventuallyEq (hn.mono fun _ ht ↦ F.variation_equation ht u))
  simpa only [Function.comp_apply,h₀,secondForce,linearForce] using h

theorem mixed_variation_unique {q : H} (hq : q ∈ F.domain) (u v : H) {z : P}
    (hz : z=greenOperator (F.secondForce q (F.variation q u) (F.variation q v)+F.linearForce q z)) :
    z=F.mixedVariation q u v := by
  have hu := F.mixed_variation_equation hq u v
  rw [map_add] at hu hz
  exact linearized_green_unique greenOperator F.force F.smoothForce (F.regular q hq) hz hu

end EuclideanMidpointRigidity.SmoothEndpointFamily

