module

public import EuclideanMidpointRigidity.ImplicitPatches
public import EuclideanMidpointRigidity.UnivariateFamilies
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Countable smooth graphs containing the roots of a polynomial family -/

@[expose] public section
noncomputable section
open Set Filter Polynomial
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.SmoothPolynomial

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E]
variable {W : Set E}
local notation "A" => SmoothCoefficient W

structure ScalarChart (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  domain : Set E
  isOpen_domain : IsOpen domain
  val : E → ℝ
  smooth : ContDiffOn ℝ ∞ val domain

private theorem scalar_invertible {a : ℝ} (ha : a≠0) : (ContinuousLinearMap.toSpanSingleton ℝ a).IsInvertible := by
  let f := ContinuousLinearMap.toSpanSingleton ℝ a
  have hb : Function.Bijective f.toLinearMap := by
    constructor
    · intro x y h
      change x*a=y*a at h
      exact mul_right_cancel₀ ha h
    · intro y
      exact ⟨y/a,by change y/a*a=y; field_simp⟩
  refine ⟨(LinearEquiv.ofBijective f.toLinearMap hb).toContinuousLinearEquiv,?_⟩
  ext
  rfl

/-- On the simple-root locus the implicit function theorem gives a
countable collection of smooth graphs containing every root. -/
theorem countable_simple_root_charts (P : Polynomial A) (hW : IsOpen W) :
    ∃ S : Set (ScalarChart E), S.Countable ∧ ∀ x ∈ W, ∀ z : ℝ,
      (fiber P x).eval z=0 → (fiber P x).derivative.eval z≠0 →
      ∃ s ∈ S, x ∈ s.domain ∧ s.val x=z := by
  let f := fun v : E × ℝ ↦ (fiber P v.1).eval v.2
  let df := fun v : E × ℝ ↦ (fiber P v.1).derivative.eval v.2
  let O := (W ×ˢ (univ : Set ℝ)) ∩ df ⁻¹' ({0}ᶜ : Set ℝ)
  have hdf : ContinuousOn df (W ×ˢ univ) := by
    simpa only [df,fiber,Polynomial.derivative_map] using (smooth_fiber_eval P.derivative).continuousOn
  have hO : IsOpen O := hdf.isOpen_inter_preimage (hW.prod isOpen_univ) isClosed_singleton.isOpen_compl
  have hf : ContDiffOn ℝ ∞ f O := (smooth_fiber_eval P).mono inter_subset_left
  have hinv (v : E × ℝ) (hv : v ∈ O) : (fderiv ℝ f v ∘L .inr ℝ E ℝ).IsInvertible := by
    have hl := ((hf.contDiffAt (hO.mem_nhds hv)).differentiableAt (by decide)).hasFDerivAt
    have hcomp := hl.comp v.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) v.1 v.2)
    have hd := ((fiber P v.1).hasDerivAt v.2).hasFDerivAt
    have he : (fderiv ℝ f v ∘L .inr ℝ E ℝ) = ContinuousLinearMap.toSpanSingleton ℝ (df v) := hcomp.unique hd
    rw [he]
    exact scalar_invertible hv.2
  let T := {v : E × ℝ | v ∈ O ∧ f v=0}
  have charts (v : T) : ∃ (D : Set (E × ℝ)) (s : ScalarChart E), IsOpen D ∧ v.val ∈ D ∧
      ∀ y ∈ D, y.1 ∈ s.domain ∧ (f y=0 → s.val y.1=y.2) := by
    obtain ⟨V,D,s,hV,hD,hvD,hs,_,hgraph⟩ := smooth_implicit_patch hO hf hinv v.property.1
    refine ⟨D,⟨V,hV,s,hs⟩,hD,hvD,?_⟩
    intro y hy
    exact ⟨(hgraph y hy).1,fun h ↦ (hgraph y hy).2 (h.trans v.property.2.symm)⟩
  choose D s hD hbase hgraph using charts
  obtain ⟨I,hI,he⟩ := eq_open_union_countable D hD
  refine ⟨s '' I,hI.image s,?_⟩
  intro x hx z hz hd
  have hT : (x,z) ∈ T := ⟨⟨⟨hx,trivial⟩,hd⟩,hz⟩
  have hmem : (x,z) ∈ ⋃ i ∈ I, D i := he ▸ mem_iUnion.mpr ⟨⟨(x,z),hT⟩,hbase _⟩
  obtain ⟨i,hmem⟩ := mem_iUnion.mp hmem
  obtain ⟨hi,hy⟩ := mem_iUnion.mp hmem
  exact ⟨s i,mem_image_of_mem s hi,(hgraph i _ hy).1,(hgraph i _ hy).2 hz⟩

private theorem exists_simple_derived_root {P : Polynomial ℝ} (hP : P≠0) {z : ℝ} (hz : P.eval z=0) :
    ∃ j : ℕ, ((Polynomial.derivative^[j]) P).eval z=0 ∧
      ((Polynomial.derivative^[j]) P).derivative.eval z≠0 := by
  classical
  have hex : ∃ j : ℕ, ((Polynomial.derivative^[j]) P).eval z≠0 := by
    refine ⟨P.natDegree,?_⟩
    rw [← Polynomial.factorial_smul_hasseDeriv,LinearMap.smul_apply,Polynomial.hasseDeriv_natDegree_eq_C]
    simp [Polynomial.leadingCoeff_ne_zero.mpr hP,Nat.factorial_ne_zero]
  have hn := Nat.find_spec hex
  have hne : Nat.find hex ≠ 0 := by
    intro he
    rw [he,Function.iterate_zero_apply] at hn
    exact hn hz
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hne
  refine ⟨j,?_,?_⟩
  · by_contra h
    exact Nat.find_min hex (by omega : j<Nat.find hex) h
  · simpa only [hj,Function.iterate_succ_apply'] using hn

/-- Higher derivatives at a multiple root reduce the countable graph
cover to the simple-root case. The graphs need only contain the roots. -/
theorem countable_root_charts (P : Polynomial A) (hW : IsOpen W) :
    ∃ S : Set (ScalarChart E), S.Countable ∧ ∀ x ∈ W, fiber P x≠0 → ∀ z : ℝ,
      (fiber P x).eval z=0 → ∃ s ∈ S, x ∈ s.domain ∧ s.val x=z := by
  choose S hS hcover using fun j : ℕ ↦ countable_simple_root_charts ((Polynomial.derivative^[j]) P) hW
  refine ⟨⋃ j, S j,countable_iUnion hS,?_⟩
  intro x hx hP z hz
  obtain ⟨j,h₀,h₁⟩ := exists_simple_derived_root hP hz
  have he : fiber ((Polynomial.derivative^[j]) P) x=(Polynomial.derivative^[j]) (fiber P x) :=
    (Polynomial.iterate_derivative_map P (evaluateCoefficient x) j).symm
  obtain ⟨s,hs,hxD,hv⟩ := hcover j x hx z (he ▸ h₀) (he ▸ h₁)
  exact ⟨s,mem_iUnion.mpr ⟨j,hs⟩,hxD,hv⟩

end EuclideanMidpointRigidity.SmoothPolynomial

