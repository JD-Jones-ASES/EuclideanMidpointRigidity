module

public import EuclideanMidpointRigidity.ParametricLineJet
public import EuclideanMidpointRigidity.AnalyticLineFamily
public import EuclideanMidpointRigidity.RulingTensorODE

/-! # A smooth family of entire continuations of the cubic along its rulings -/

@[expose] public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
open Endpoint
namespace Endpoint
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
local notation "J" => JetState n V

theorem analytic_companion : ContDiff ℝ ω (companion (n := n) (V := V)) := by
  let L : Fin (n+1) → (J →L[ℝ] J) := fun j : Fin (n+1) ↦ ContinuousLinearMap.pi (Fin.lastCases
    (-(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n+1) ↦ V) j)) (fun _ : Fin n ↦ (0 : J →L[ℝ] V)))
  have he : companion (V := V) = fun c : Fin (n+1) → ℝ ↦ companion (fun _ ↦ (0:ℝ))+∑ j, c j • L j := by
    funext c
    ext v : 1
    funext i
    induction i using Fin.lastCases with
    | cast i =>
      simp only [companion,L,add_apply,sum_apply,smul_apply,ContinuousLinearMap.pi_apply,Fin.lastCases_castSucc,
        ContinuousLinearMap.proj_apply,Pi.smul_apply,Pi.add_apply,Finset.sum_apply,zero_apply,smul_zero,Finset.sum_const_zero,add_zero]
    | last =>
      simp only [companion,L,add_apply,sum_apply,smul_apply,ContinuousLinearMap.pi_apply,Fin.lastCases_last,
        ContinuousLinearMap.proj_apply,Pi.smul_apply,Pi.add_apply,Finset.sum_apply,zero_smul,Finset.sum_const_zero,neg_zero,zero_add,neg_apply,zero_apply,smul_neg,Finset.sum_neg_distrib]
  rw [he]
  apply contDiff_const.add
  exact ContDiff.sum fun i _ ↦ (contDiff_apply ℝ (fun _ : Fin (n+1) ↦ ℝ) i).smul (contDiff_const (c := L i))

variable [CompleteSpace V]

theorem analytic_companionSolution : ContDiff ℝ ω
    (fun q : ((Fin (n+1) → ℝ) × J) × ℝ ↦ companionSolution q.1.1 q.1.2 q.2) := by
  have hE : ContDiff ℝ ω (NormedSpace.exp : (J →L[ℝ] J) → (J →L[ℝ] J)) :=
    contDiff_omega_iff_analyticOnNhd.mpr fun x _ ↦ NormedSpace.exp_analytic (𝕂 := ℝ) x
  have hA : ContDiff ℝ ω (fun q : ((Fin (n+1) → ℝ) × J) × ℝ ↦ q.2 • (companion q.1.1 : J →L[ℝ] J)) :=
    contDiff_snd.smul (analytic_companion.comp (contDiff_fst.comp contDiff_fst))
  have h := (hE.comp hA).clm_apply (contDiff_snd.comp contDiff_fst)
  exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n+1) ↦ V) 0).contDiff.comp h

end Endpoint

namespace LiftedSection
variable {d : ℕ}
local notation "E" => Space d
variable (S : LiftedSection d)

set_option backward.isDefEq.respectTransparency false in
instance cubicCompleteSpace (d : ℕ) : CompleteSpace (Cubic d) := by
  haveI : FiniteDimensional ℝ (Space d →L[ℝ] Space d) := ContinuousLinearMap.finiteDimensional
  haveI : FiniteDimensional ℝ (Space d →L[ℝ] Space d →L[ℝ] Space d) := ContinuousLinearMap.finiteDimensional
  haveI : FiniteDimensional ℝ (Cubic d) := FiniteDimensional.finiteDimensional_submodule (K := ℝ) (V := Space d →L[ℝ] Space d →L[ℝ] Space d) (cubicSubspace d)
  exact FiniteDimensional.completeSpace ℝ (Cubic d)

def continuedField (p : E) (s : ℝ) : Cubic d := companionSolution (n := 2*d+4)
  (fun j ↦ (S.rulingPolynomial p).coeff j) (lineJet (fun t ↦ S.field (p+t • S.axialDirection p)) 0) s

theorem smooth_axialDirection : ContDiffOn ℝ ∞ S.axialDirection S.domain :=
  ((contDiffOn_sectionValue S.smooth S.smoothAxis).inv (fun p hp ↦ (S.positive p hp).ne')).smul S.smoothAxis

def continuedFamily : AnalyticLineFamily S.domain S.continuedField where
  Parameter := (Fin (2*d+4+1) → ℝ) × JetState (2*d+4) (Cubic d)
  parameter := fun p ↦ ((fun j ↦ (S.rulingPolynomial p).coeff j),lineJet (fun t ↦ S.field (p+t • S.axialDirection p)) 0)
  smooth := (contDiffOn_pi.mpr (fun j : Fin (2*d+4+1) ↦ S.smooth_rulingPolynomial_coeff j.val)).prodMk
    (smooth_line_initial_jet S.isOpen S.smooth S.smooth_axialDirection (2*d+4))
  evaluate := fun q ↦ companionSolution q.1.1 q.1.2 q.2
  analytic := analytic_companionSolution
  equals _ _ _ := rfl

theorem continuedField_germ {p : E} (hp : p ∈ S.domain) (hm : ∀ q ∈ S.domain, S.Maximizes q)
    (hc : ∀ q ∈ S.domain, Nonempty (OrientedEndpointChart S.field q)) :
    ∀ᶠ s in 𝓝 (0:ℝ), S.continuedField p s=S.field (p+s • S.axialDirection p) := by
  obtain ⟨_,W,hW,h₀,H⟩ := S.tensor_ruling_ode hp hm hc
  exact (H.eventually_companionSolution h₀ (S.rulingPolynomial_monic p) (S.rulingPolynomial_degree p)).mono (fun _ he ↦ he.symm)

end LiftedSection
end EuclideanMidpointRigidity

