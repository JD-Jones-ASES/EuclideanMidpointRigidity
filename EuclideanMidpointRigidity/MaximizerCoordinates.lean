module

public import EuclideanMidpointRigidity.RadialPolynomial
public import EuclideanMidpointRigidity.CoordinatePatches

/-! # Algebraic coordinates for a maximizing direction -/

public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
open SmoothPolynomial

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

/-- On an open subpatch each coordinate has finitely many candidates, and
at least one of the resulting tuples globally maximizes the radial objective. -/
theorem maximizing_coordinate_patch {W : Set E} {C : E → Coeff} (hW : IsOpen W)
    (hn : W.Nonempty) (hC : ContDiffOn ℝ ∞ C W) :
    ∃ (V : Set E) (q : Fin d → Polynomial (SmoothCoefficient W)), IsOpen V ∧ V.Nonempty ∧ V ⊆ W ∧
      (∀ x ∈ V, ∀ i, fiber (q i) x≠0) ∧ ∀ x ∈ V, ∃ w : E,
        (∀ i, (fiber (q i) x).eval (w i)=0) ∧ ∀ v, radialObjective (C x) v≤radialObjective (C x) w := by
  let g := fun i ↦ MvPolynomial.pderiv i (radialPolynomial hC)
  let b := Finset.univ.sup (fun i ↦ (g i).totalDegree)
  have hb (i : Fin d) : (g i).totalDegree≤b := Finset.le_sup (f := fun i ↦ (g i).totalDegree) (Finset.mem_univ i)
  obtain ⟨V,q,hV,hnV,hVW,hq,hlim⟩ := regularized_coordinate_patch g (2*b)
    (fun i ↦ by have := hb i; omega) hW hn
  refine ⟨V,q,hV,hnV,hVW,hq,?_⟩
  intro x hx
  obtain ⟨w,t,z,ht,hpos,hz,he,hm⟩ := polynomial_perturbation_limit hC x b
  refine ⟨w,hlim x hx t (fun j ↦ (z j).ofLp) w.ofLp ht (fun j ↦ (hpos j).ne') ?_ he,hm⟩
  exact fun i ↦ (PiLp.continuous_apply 2 (fun _ : Fin d ↦ ℝ) i).continuousAt.tendsto.comp hz

end EuclideanMidpointRigidity

