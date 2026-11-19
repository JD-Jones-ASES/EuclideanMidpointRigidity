module

public import EuclideanMidpointRigidity.RulingFrame
public import EuclideanMidpointRigidity.RulingTransport

/-! # The vanishing derivative entries on a smooth maximizing ruling -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity
variable {d : ℕ} {ι : Type*} [Fintype ι]
local notation "E" => Space d
local notation "Op" => E →L[ℝ] E

theorem operator_zero_of_entries (F : OrthonormalBasis ι ℝ E) {A : Op} (h : ∀ i j, operatorEntry F A i j=0) : A=0 := by
  have hj (j : ι) : A (F j)=0 := by
    rw [← F.sum_repr' (A (F j))]
    exact Finset.sum_eq_zero fun i _ ↦ by rw [show ⟪F i,A (F j)⟫_ℝ=0 from h i j,zero_smul]
  ext l : 1
  change A l=0
  rw [← F.sum_repr' l,map_sum]
  simp only [map_smul,hj,smul_zero,Finset.sum_const_zero]

namespace LiftedSection
variable (S : LiftedSection d)

theorem weighted_trace_zero {p : E} (hp : p ∈ S.domain) (hm : ∀ q ∈ S.domain, S.Maximizes q) :
    operatorTrace ((weightedOperator (S.axisSlice p)).comp (fderiv ℝ S.axis p))=0 := by
  obtain ⟨n,⟨F⟩⟩ := S.exists_ruling_frame hp (hm p hp)
  rw [operatorTrace_in_basis F.basis]
  apply Finset.sum_eq_zero
  intro i _
  rw [operatorEntry_weight_left F.basis (S.axisSlice p) (fderiv ℝ S.axis p) F.value (fun x y ↦ (K_selfAdjoint _ _ x y).symm) F.eigen]
  exact F.weighted_diagonal_zero hp hm i

theorem weighted_trace_derivative_zero {p : E} (hp : p ∈ S.domain) (hm : ∀ q ∈ S.domain, S.Maximizes q) :
    let B := S.axisSlice p
    let Z := S.sliceRate p
    let A := fderiv ℝ S.axis p
    operatorTrace ((weightDerivative B Z).comp A+(weightedOperator B).comp (-(A.comp A)))=0 := by
  let line := displacementLine p (S.axis p)
  let B := S.axisSlice ∘ line
  let A := fderiv ℝ S.axis ∘ line
  have h₀ : line 0=p := displacementLine_zero _ _
  have hn₀ : S.domain ∈ 𝓝 (line 0) := by rw [h₀]; exact S.isOpen.mem_nhds hp
  have hn : ∀ᶠ t in 𝓝 (0:ℝ), line t ∈ S.domain := (hasDerivAt_displacementLine p (S.axis p)).continuousAt hn₀
  have hB : HasDerivAt B (S.sliceRate p) 0 := S.hasDerivAt_axisSlice hp hm
  have hA : HasDerivAt A (-((fderiv ℝ S.axis p).comp (fderiv ℝ S.axis p))) 0 := S.hasDerivAt_axisSlope hp hm
  obtain ⟨n,⟨F⟩⟩ := S.exists_ruling_frame hp (hm p hp)
  have h := hasDerivAt_operatorTrace F.basis ((hasDerivAt_weightedOperator hB).clm_comp hA)
  have hz : HasDerivAt (fun t ↦ operatorTrace ((weightedOperator (B t)).comp (A t))) 0 0 :=
    (hasDerivAt_const 0 (0:ℝ)).congr_of_eventuallyEq <| hn.mono fun _ ht ↦ S.weighted_trace_zero ht hm
  simpa only [B,A,Function.comp_apply,h₀] using h.unique hz

theorem ruling_entries_zero {p : E} (hp : p ∈ S.domain) (hm : ∀ q ∈ S.domain, S.Maximizes q)
    (F : RulingFrame S p ι) (i j : ι) : (1-2*F.value i)*F.slope i j=0 ∧ F.rate i j=0 := by
  let t := fun i j ↦ tracePair (F.value i) (F.value j) (F.slope i j) (F.slope j i) (F.rate i j)
  have hpos (i j : ι) : 0≤t i j := (F.pair_sign hp hm i j).1
  have hz : ∑ i, ∑ j, t i j=0 := weighted_trace_equation F.basis _ _ _ F.value
    (fun x y ↦ (K_selfAdjoint _ _ x y).symm) F.eigen F.symm_rate (S.weighted_trace_derivative_zero hp hm)
  have hrow := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ hpos i j))).mp hz i (Finset.mem_univ i)
  have hentry := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ ↦ hpos i k)).mp hrow j (Finset.mem_univ j)
  have h := (F.pair_sign hp hm i j).2 hentry
  exact ⟨h.1,h.2.2⟩

/-- Every derivative of the cubic vanishes on two copies of the axis. The range of its
direction derivative lies in the upper eigenspace, and the normalized slice has zero axial rate. -/
theorem weighted_ruling {p : E} (hp : p ∈ S.domain) (hm : ∀ q ∈ S.domain, S.Maximizes q) :
    (∀ l, K (fderiv ℝ S.field p l) (S.axis p) (S.axis p)=0) ∧
    (∀ l, S.axisSlice p (fderiv ℝ S.axis p l)=(1/2:ℝ) • fderiv ℝ S.axis p l) ∧
    S.sliceRate p=0 := by
  obtain ⟨n,⟨F⟩⟩ := S.exists_ruling_frame hp (hm p hp)
  let e := S.axis p
  let L : Op := ((ContinuousLinearMap.apply ℝ E e).comp
    ((ContinuousLinearMap.apply ℝ Op e).comp (cubicSubspace d).subtypeL)).comp (S.normalizedJet p)
  have hL : L=0 := by
    apply operator_zero_of_entries F.basis
    intro i j
    change ⟪F.basis i,K (S.normalizedJet p (F.basis j)) e e⟫_ℝ=0
    rw [real_inner_comm,S.normalized_entry_gap hp hm _ _ (F.eigen i)]
    exact (S.ruling_entries_zero hp hm F i j).1
  have hjet (l : E) : K (S.normalizedJet p l) e e=0 := congrArg (fun A : Op ↦ A l) hL
  refine ⟨?_,?_,operator_zero_of_entries F.basis (fun i j ↦ (S.ruling_entries_zero hp hm F i j).2)⟩
  · intro l
    have h := hjet l
    simp only [normalizedJet,smul_apply,K_smul_coeff] at h
    exact (smul_eq_zero.mp h).resolve_left (inv_ne_zero (S.positive _ hp).ne')
  · intro l
    have h := S.normalized_critical_derivative hp hm l
    change K (S.normalizedJet p l) e e=_ at h
    rw [hjet] at h
    linear_combination (norm := module) (1/2:ℝ) • h

end LiftedSection
end EuclideanMidpointRigidity

