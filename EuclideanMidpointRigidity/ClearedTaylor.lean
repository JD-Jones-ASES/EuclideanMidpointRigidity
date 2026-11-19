module

public import EuclideanMidpointRigidity.ClearedExpressions
public import EuclideanMidpointRigidity.SymmetricTaylor

/-! # Taylor tensors and their contractions in line coordinates -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
variable {E V Z T : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup T] [NormedSpace ℝ T]

abbrev Represented (A : LineChart E V) (f : (E → V) → E → Z) := Nonempty (ClearedExpression A f)

namespace Represented
variable {A : LineChart E V} {f g : (E → V) → E → Z}

theorem congr (H : Represented A f) (he : ∀ C x, f C x=g C x) : Represented A g :=
  (show f=g from funext (fun C ↦ funext (he C))) ▸ H

theorem linear (H : Represented A f) (L : Z →L[ℝ] T) : Represented A (fun C x ↦ L (f C x)) :=
  ⟨H.some.linear L⟩

theorem scale (H : Represented A f) (r : ℝ) : Represented A (fun C x ↦ r • f C x) := ⟨H.some.scale r⟩

theorem add (H : Represented A f) (J : Represented A g) : Represented A (fun C x ↦ f C x+g C x) :=
  ⟨H.some.add J.some⟩

theorem sub (H : Represented A f) (J : Represented A g) : Represented A (fun C x ↦ f C x-g C x) :=
  (H.add (J.scale (-1))).congr (by intro C x; simp [sub_eq_add_neg])

theorem applyCLM {L : (E → V) → E → (Z →L[ℝ] T)} (H : Represented A L) (J : Represented A f) :
    Represented A (fun C x ↦ L C x (f C x)) := ⟨H.some.applyCLM J.some⟩

theorem sum {ι : Type*} (s : Finset ι) (f : ι → (E → V) → E → Z) (H : ∀ i, Represented A (f i)) :
    Represented A (fun C x ↦ ∑ i ∈ s, f i C x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (show Represented A (fun _ _ ↦ (0:Z)) from ⟨ClearedExpression.const A 0⟩)
  | insert i s hi ih =>
    exact ((H i).add ih).congr (fun C x ↦ (Finset.sum_insert (f := fun i ↦ f i C x) hi).symm)

theorem jet (A : LineChart E V) (n : ℕ) : Represented A (fun C x ↦ iteratedFDeriv ℝ n C x) := by
  induction n with
  | zero =>
    exact ⟨(ClearedExpression.field A).linear (continuousMultilinearCurryFin0 ℝ E V).symm.toContinuousLinearEquiv.toContinuousLinearMap⟩
  | succ n ih =>
    exact ⟨ih.some.derivative.linear (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) ↦ E) V).symm.toContinuousLinearEquiv.toContinuousLinearMap⟩

theorem evaluate {n : ℕ} {m : (E → V) → E → SpatialForm T Z n} (H : Represented A m)
    (v : Fin n → (E → V) → E → T) (hv : ∀ i, Represented A (v i)) :
    Represented A (fun C x ↦ m C x (fun i ↦ v i C x)) := by
  induction n with
  | zero =>
    apply (H.linear (continuousMultilinearCurryFin0 ℝ T Z).toContinuousLinearEquiv.toContinuousLinearMap).congr
    intro C x
    change m C x 0=_
    rw [show (0 : Fin 0 → T)=(fun i ↦ v i C x) from Subsingleton.elim _ _]
  | succ n ih =>
    let curry := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) ↦ T) Z).toContinuousLinearEquiv.toContinuousLinearMap
    have h := (H.linear curry).applyCLM (hv 0)
    apply (ih h (fun i ↦ v i.succ) (fun i ↦ hv i.succ)).congr
    intro C x
    change (m C x).curryLeft (v 0 C x) (fun i ↦ v i.succ C x)=_
    rw [ContinuousMultilinearMap.curryLeft_apply]
    congr 1
    exact Fin.cons_self_tail (fun i ↦ v i C x)

theorem symmetricJet (A : LineChart E V) {n : ℕ} (v : Fin n → (E → V) → E → E)
    (hv : ∀ i, Represented A (v i)) :
    Represented A (fun C x ↦ symmetricPart (iteratedFDeriv ℝ n C x) (fun i ↦ v i C x)) := by
  let term := fun (σ : Equiv.Perm (Fin n)) (C : E → V) (x : E) ↦ iteratedFDeriv ℝ n C x (fun i ↦ v (σ i) C x)
  have H (σ : Equiv.Perm (Fin n)) : Represented A (term σ) := (jet A n).evaluate _ (fun i ↦ hv (σ i))
  exact ((sum Finset.univ term H).scale (Fintype.card (Equiv.Perm (Fin n)):ℝ)⁻¹).congr
    (fun C x ↦ (symmetricPart_apply (iteratedFDeriv ℝ n C x) (fun i ↦ v i C x)).symm)

end Represented
end EuclideanMidpointRigidity

