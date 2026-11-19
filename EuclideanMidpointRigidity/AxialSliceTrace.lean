module

public import EuclideanMidpointRigidity.FixedAxisKilling
public import EuclideanMidpointRigidity.SpectralTrace

/-! # The weighted trace is stationary when the axis is fixed -/

@[expose] public section
noncomputable section
open scoped ContDiff InnerProductSpace
namespace EuclideanMidpointRigidity.FixedAxis
open Quartic
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d
local notation "Op" => E →L[ℝ] E

def sliceMap (u : E) : T →L[ℝ] Op := (ContinuousLinearMap.apply ℝ Op u).comp (cubicSubspace d).subtypeL

theorem trace_rate_zero {c : T} {J : E →L[ℝ] T} {u : E} (F : SliceFrame c u)
    (hE : ∀ v, obstruction c J v=0) (hu : K c u u=u) (hJ : ∀ l, K (J l) u u=0) (hU : J u=0) (v : E) :
    operatorTrace (weightDerivative (sliceMap u c) (sliceMap u (J v)))=0 := by
  rw [operatorTrace_in_basis F.basis]
  apply Finset.sum_eq_zero
  intro i _
  have he : ∀ j, sliceMap u c (F.basis j)=F.eigenvalue j • F.basis j := F.eigen
  have hs : ∀ x y, ⟪x,sliceMap u c y⟫_ℝ=⟪sliceMap u c x,y⟫_ℝ := fun x y ↦ (K_selfAdjoint c u x y).symm
  rw [operatorEntry_weight_rate F.basis (sliceMap u c) (sliceMap u (J v)) F.eigenvalue hs he]
  let x := F.basis i
  let b := F.eigenvalue i
  change (1/2-b-b)*⟪x,K (J v) u x⟫_ℝ=0
  let M := ((1/2-2*b) : ℝ) • ((innerSL ℝ x).comp (((ContinuousLinearMap.apply ℝ E x).comp (sliceMap u)).comp J))
  have hm (j) : M (F.basis j)=0 := by
    change (1/2-2*b)*⟪x,K (J (F.basis j)) u x⟫_ℝ=0
    rw [show ⟪x,K (J (F.basis j)) u x⟫_ℝ=⟪K (J (F.basis j)) u x,x⟫_ℝ from real_inner_comm _ _]
    exact weighted_diagonal F hE hu hJ hU (F.eigen i) (F.eigen j)
  rw [show 1/2-b-b=1/2-2*b by ring]
  change M v=0
  rw [← F.basis.sum_repr v,map_sum]
  exact Finset.sum_eq_zero fun j _ ↦ by rw [map_smul,hm,smul_zero]

theorem shifted_trace (B : Op) :
    operatorTrace ((B-(1/4:ℝ) • ContinuousLinearMap.id ℝ E).comp (B-(1/4:ℝ) • ContinuousLinearMap.id ℝ E))=
      operatorTrace ((1/16:ℝ) • ContinuousLinearMap.id ℝ E)-operatorTrace (weightedOperator B) := by
  have he : (B-(1/4:ℝ) • ContinuousLinearMap.id ℝ E).comp (B-(1/4:ℝ) • ContinuousLinearMap.id ℝ E)=
      (1/16:ℝ) • ContinuousLinearMap.id ℝ E-weightedOperator B := by
    ext w : 1
    simp only [weightedOperator,ContinuousLinearMap.comp_apply,smul_apply,sub_apply,ContinuousLinearMap.id_apply,map_sub,map_smul]
    module
  rw [he]
  exact map_sub (LinearMap.trace ℝ E) _ _

theorem square_sum_trace {ι : Type*} [Fintype ι] (F : OrthonormalBasis ι ℝ E) (L : Op)
    (hs : ∀ v w, ⟪L v,w⟫_ℝ=⟪v,L w⟫_ℝ) :
    (∑ i : ι × ι, (operatorEntry F L i.1 i.2)^2)=operatorTrace (L.comp L) := by
  have he (i j : ι) : operatorEntry F L j i=operatorEntry F L i j := by
    change ⟪F j,L (F i)⟫_ℝ=⟪F i,L (F j)⟫_ℝ
    rw [← hs,real_inner_comm]
  rw [operatorTrace_in_basis F,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [operatorEntry_comp]
  apply Finset.sum_congr rfl
  intro j _
  rw [he j i,sq]

end EuclideanMidpointRigidity.FixedAxis

