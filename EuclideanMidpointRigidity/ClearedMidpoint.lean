module

public import EuclideanMidpointRigidity.ClearedTaylor
public import EuclideanMidpointRigidity.MidpointJetEquations

/-! # Polynomial numerators for the two midpoint differential equations -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
open Jet
namespace Represented
variable {d : ℕ}
local notation "E" => Space d
set_option maxHeartbeats 1200000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false

theorem cubicProduct {A : LineChart (Space d) (Cubic d)} {c : (Space d → Cubic d) → Space d → Cubic d}
    {u v : (Space d → Cubic d) → Space d → Space d}
    (hc : Represented A c) (hu : Represented A u) (hv : Represented A v) :
    Represented A (fun G x ↦ K (c G x) (u G x) (v G x)) := by
  let L : Cubic d →L[ℝ] (E →L[ℝ] E →L[ℝ] E) := (cubicSubspace d).subtypeL
  have hl : Represented A (fun G x ↦ L (c G x)) := Represented.linear («E» := Space d) (V := Cubic d) (Z := Cubic d) (T := E →L[ℝ] E →L[ℝ] E) (A := A) (f := c) hc L
  have h₂ := Represented.applyCLM hl hu
  exact Represented.applyCLM h₂ hv

theorem quartic (A : LineChart E (Cubic d)) (z : E) :
    Represented A (fun G x ↦ obstruction (G x) (fderiv ℝ G x) z) := by
  let F := ClearedExpression.field A
  have C : Represented A (fun G ↦ G) := ⟨F⟩
  have J : Represented A (fun G x ↦ fderiv ℝ G x) := ⟨F.derivative⟩
  have Z : Represented A (fun _ _ ↦ z) := ⟨ClearedExpression.const A z⟩
  have b := cubicProduct C Z Z
  have j := J.applyCLM Z
  have l := cubicProduct C Z (cubicProduct j Z Z)
  have m := cubicProduct (J.applyCLM b) Z Z
  have r := cubicProduct j Z b
  apply (((l.scale 2).add (m.scale 5)).sub (r.scale 4)).congr
  intro G x
  simp only [obstruction,← Nat.cast_smul_eq_nsmul ℝ]
  norm_num

theorem realized (A : LineChart E (Cubic d)) (z : E) (tree : Tree) :
    Represented A (fun C x ↦ tree.realize (fieldDerivatives C x) z) := by
  induction tree with
  | direction => exact ⟨ClearedExpression.const A z⟩
  | k u v hu hv =>
    refine cubicProduct ?_ hu hv
    apply Represented.symmetricJet (n := 0) A (fun i C x ↦ ([] : List E).get i)
    intro i
    exact Fin.elim0 i
  | j a u v ha hu hv =>
    refine cubicProduct ?_ hu hv
    apply Represented.symmetricJet (n := 1) A (fun i C x ↦ ([a.realize (fieldDerivatives C x) z] : List E).get i)
    intro i
    fin_cases i; assumption
  | hess a b u v ha hb hu hv =>
    refine cubicProduct ?_ hu hv
    apply Represented.symmetricJet (n := 2) A (fun i C x ↦ ([a.realize (fieldDerivatives C x) z,b.realize (fieldDerivatives C x) z] : List E).get i)
    intro i
    fin_cases i <;> assumption
  | third a b c u v ha hb hc hu hv =>
    refine cubicProduct ?_ hu hv
    apply Represented.symmetricJet (n := 3) A (fun i C x ↦ ([a.realize (fieldDerivatives C x) z,b.realize (fieldDerivatives C x) z,c.realize (fieldDerivatives C x) z] : List E).get i)
    intro i
    fin_cases i <;> assumption
  | fourth a b c e u v ha hb hc he hu hv =>
    refine cubicProduct ?_ hu hv
    apply Represented.symmetricJet (n := 4) A (fun i C x ↦ ([a.realize (fieldDerivatives C x) z,b.realize (fieldDerivatives C x) z,c.realize (fieldDerivatives C x) z,e.realize (fieldDerivatives C x) z] : List E).get i)
    intro i
    fin_cases i <;> assumption

theorem timePolynomial (A : LineChart E (Cubic d)) (z : E) (t : ℝ) (P : TimePolynomial) :
    Represented A (fun C x ↦ value P (Tree.realize (fieldDerivatives C x) z) t) := by
  induction P with
  | nil => exact ⟨ClearedExpression.const A 0⟩
  | cons m ms ih => exact ((realized A z m.tree).scale ((m.coeff:ℝ)*t^m.power)).add ih

theorem sixth (A : LineChart E (Cubic d)) (z : E) :
    Represented A (fun C x ↦ value affineSixth (Tree.realize (fieldDerivatives C x) z) 0+
      value higherSixth (Tree.realize (fieldDerivatives C x) z) 0) :=
  (timePolynomial A z 0 affineSixth).add (timePolynomial A z 0 higherSixth)

end Represented
end EuclideanMidpointRigidity

