module

public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.Tactic

/-! # Detecting algebraic elements by their differential in characteristic zero -/

@[expose] public section
noncomputable section
open Algebra Polynomial IntermediateField KaehlerDifferential
open scoped TensorProduct
namespace EuclideanMidpointRigidity

/-- In an essentially finitely generated field extension in characteristic
zero, a transcendental element has nonzero relative differential. -/
theorem algebraic_of_differential_zero (k L : Type) [Field k] [CharZero k] [Field L]
    [Algebra k L] [Algebra.EssFiniteType k L] {z : L} (hz : D k L z=0) : IsAlgebraic k z := by
  classical
  by_contra h
  let T := k⟮z⟯
  let g : T := AdjoinSimple.gen k z
  let _ : Algebra k[X] T := (aeval g).toRingHom.toAlgebra
  let _ : Algebra k[X] L := (aeval z).toRingHom.toAlgebra
  let _ : IsScalarTower k k[X] L := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change algebraMap k L a = aeval z (C a)
    simp
  let _ : IsScalarTower k[X] T L := IsScalarTower.of_algebraMap_eq fun p ↦ by
    change aeval z p=(algebraMap T L) (aeval g p)
    rw [← aeval_algebraMap_apply]
    rfl
  let e : RatFunc k ≃ₐ[k[X]] T := {
    __ := (RatFunc.algEquivOfTranscendental z h).toRingEquiv
    commutes' := fun p ↦ RatFunc.algEquivOfTranscendental_algebraMap z h p }
  let _ : Algebra.FormallySmooth k[X] (RatFunc k) :=
    Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors k[X])
  let _ : Algebra.FormallySmooth k[X] T := Algebra.FormallySmooth.of_equiv e
  let _ : Algebra.EssFiniteType T L := Algebra.EssFiniteType.of_comp k T L
  let _ : Algebra.FormallySmooth k[X] L := Algebra.FormallySmooth.comp k[X] T L
  let dx := D k k[X] X
  have h₀ : mapBaseChange k k[X] L ((1:L) ⊗ₜ[k[X]] dx)=0 := by
    rw [mapBaseChange_tmul,one_smul,map_D]
    change D k L (aeval z X)=0
    simpa using hz
  obtain ⟨v,hv⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange k k[X] L _).mp h₀
  rw [show v=0 from Subsingleton.elim _ _,map_zero] at hv
  let f : Ω[k[X]⁄k] →ₗ[k[X]] L :=
    (Algebra.linearMap k[X] L).comp (polynomialEquiv k).toLinearMap
  have h₁ := congrArg (f.liftBaseChange L) hv
  simp [f,dx] at h₁

end EuclideanMidpointRigidity

