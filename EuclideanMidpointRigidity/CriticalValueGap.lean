module

public import EuclideanMidpointRigidity.UniformCriticalValues
public import EuclideanMidpointRigidity.RootSeparation

/-! # Uniform separation from other polynomial critical values -/

public section
noncomputable section
open Set Filter
open scoped Topology
namespace EuclideanMidpointRigidity.SmoothPolynomial

/-- For a continuous reference value, all nearby critical values in a
product neighborhood agree with the reference there. The point and
neighborhood can be found inside every nonempty open parameter domain. -/
theorem critical_value_separation {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [BaireSpace E]
    {W : Set E} {n : ℕ} (f : MvPolynomial (Fin n) (SmoothCoefficient W))
    (hW : IsOpen W) (hn : W.Nonempty) {a : E → ℝ} (ha : ContinuousOn a W) :
    ∃ p ∈ W, ∀ᶠ q : E × ℝ in 𝓝 (p,a p), ∀ z : Fin n → ℝ,
      (∀ i, MvPolynomial.eval z (MvPolynomial.pderiv i (specialize f q.1))=0) →
      MvPolynomial.eval z (specialize f q.1)=q.2 → q.2=a q.1 := by
  obtain ⟨V,N,c,hV,hVn,hVW,hc,hrel⟩ := critical_values_on_subpatch f hW hn
  let u := fun j : Fin N ↦ (⟨c j,hc j⟩ : SmoothCoefficient V)
  obtain ⟨p,hp,hgap⟩ := root_isolated_on_subpatch (monicEquation u) hV hVn (ha.mono hVW)
    (fun x _ ↦ monicEquation_fiber_ne_zero u x)
  refine ⟨p,hVW hp,?_⟩
  have near : ∀ᶠ q : E × ℝ in 𝓝 (p,a p), q.1 ∈ V := continuousAt_fst (hV.mem_nhds hp)
  filter_upwards [near,hgap] with q hq h
  intro z hz hv
  apply h
  rw [eval_monicEquation,sub_eq_zero,← hv]
  exact hrel q.1 hq z hz

end EuclideanMidpointRigidity.SmoothPolynomial

