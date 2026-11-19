module

public import EuclideanMidpointRigidity.TraceContribution
public import EuclideanMidpointRigidity.Basic
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # The weighted trace and its derivative in a pointwise eigenbasis -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity
variable {d : ℕ} {ι : Type*} [Fintype ι]
local notation "E" => Space d
local notation "Op" => E →L[ℝ] E

def operatorEntry (F : OrthonormalBasis ι ℝ E) (A : Op) (i j : ι) := ⟪F i,A (F j)⟫_ℝ

def operatorTrace (A : Op) := LinearMap.trace ℝ E A.toLinearMap

def weightedOperator (B : Op) : Op := (1/2:ℝ) • B-B.comp B

def weightDerivative (B Z : Op) : Op := (1/2:ℝ) • Z-(Z.comp B+B.comp Z)

theorem operatorTrace_in_basis (F : OrthonormalBasis ι ℝ E) (A : Op) :
    operatorTrace A=∑ i, operatorEntry F A i i :=
  LinearMap.trace_eq_sum_inner _ F

theorem operatorEntry_comp (F : OrthonormalBasis ι ℝ E) (L M : Op) (i j : ι) :
    operatorEntry F (L.comp M) i j=∑ k, operatorEntry F L i k*operatorEntry F M k j := by
  change ⟪F i,L (M (F j))⟫_ℝ=_
  conv_lhs => rw [← F.sum_repr' (M (F j)),map_sum,inner_sum]
  simp only [map_smul,real_inner_smul_right,operatorEntry,mul_comm]

theorem operatorEntry_weight_left (F : OrthonormalBasis ι ℝ E) (B A : Op) (b : ι → ℝ)
    (hs : ∀ x y, ⟪x,B y⟫_ℝ=⟪B x,y⟫_ℝ) (he : ∀ i, B (F i)=b i • F i) (i j : ι) :
    operatorEntry F ((weightedOperator B).comp A) i j=traceWeight (b i)*operatorEntry F A i j := by
  simp only [weightedOperator,operatorEntry,ContinuousLinearMap.comp_apply,sub_apply,
    smul_apply,inner_sub_right,real_inner_smul_right,hs,he,map_smul,real_inner_smul_left,traceWeight]
  ring

theorem operatorEntry_weight_rate (F : OrthonormalBasis ι ℝ E) (B Z : Op) (b : ι → ℝ)
    (hs : ∀ x y, ⟪x,B y⟫_ℝ=⟪B x,y⟫_ℝ) (he : ∀ i, B (F i)=b i • F i) (i j : ι) :
    operatorEntry F (weightDerivative B Z) i j=(1/2-b i-b j)*operatorEntry F Z i j := by
  simp only [weightDerivative,operatorEntry,ContinuousLinearMap.comp_apply,sub_apply,
    add_apply,smul_apply,inner_sub_right,inner_add_right,real_inner_smul_right,
    he,hs,real_inner_smul_left,map_smul]
  ring

theorem hasDerivAt_operatorTrace (F : OrthonormalBasis ι ℝ E) {A : ℝ → Op} {A' : Op} {t : ℝ}
    (ha : HasDerivAt A A' t) : HasDerivAt (fun r ↦ operatorTrace (A r)) (operatorTrace A') t := by
  simp only [operatorTrace_in_basis F]
  apply HasDerivAt.fun_sum
  intro i _
  have ha' := ha.clm_apply (hasDerivAt_const t (F i))
  simpa only [operatorEntry,map_zero,add_zero,inner_zero_left,zero_add] using
    (hasDerivAt_const t (F i)).inner ℝ ha'

theorem hasDerivAt_weightedOperator {B : ℝ → Op} {Z : Op} {t : ℝ} (hb : HasDerivAt B Z t) :
    HasDerivAt (fun r ↦ weightedOperator (B r)) (weightDerivative (B t) Z) t :=
  (hb.fun_const_smul (1/2:ℝ)).fun_sub (hb.clm_comp hb)

theorem weighted_trace_equation (F : OrthonormalBasis ι ℝ E) (B A Z : Op) (b : ι → ℝ)
    (hs : ∀ x y, ⟪x,B y⟫_ℝ=⟪B x,y⟫_ℝ) (he : ∀ i, B (F i)=b i • F i)
    (hz : ∀ i j, operatorEntry F Z i j=operatorEntry F Z j i)
    (ht : operatorTrace ((weightDerivative B Z).comp A+(weightedOperator B).comp (-(A.comp A)))=0) :
    ∑ i, ∑ j, tracePair (b i) (b j) (operatorEntry F A i j) (operatorEntry F A j i) (operatorEntry F Z i j)=0 := by
  classical
  let v := operatorEntry F A
  let z := operatorEntry F Z
  let w := fun i j ↦ (1/2-b i-b j)*z i j*v j i-traceWeight (b i)*v i j*v j i
  have hdiag (i : ι) : operatorEntry F ((weightDerivative B Z).comp A+(weightedOperator B).comp (-(A.comp A))) i i =
      ∑ j, w i j := by
    change ⟪F i,((weightDerivative B Z).comp A+(weightedOperator B).comp (-(A.comp A))) (F i)⟫_ℝ=_
    rw [add_apply,inner_add_right]
    change operatorEntry F ((weightDerivative B Z).comp A) i i +
      operatorEntry F ((weightedOperator B).comp (-(A.comp A))) i i=_
    rw [operatorEntry_comp,operatorEntry_weight_left F B _ b hs he]
    have hneg : operatorEntry F (-(A.comp A)) i i = -operatorEntry F (A.comp A) i i := by simp [operatorEntry]
    rw [hneg,operatorEntry_comp,mul_neg,Finset.mul_sum,← sub_eq_add_neg,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [operatorEntry_weight_rate F B Z b hs he]
    dsimp only [v,w,z]
    ring
  rw [operatorTrace_in_basis F] at ht
  simp only [hdiag] at ht
  have hswap : (∑ i, ∑ j, w j i)=0 := by rw [Finset.sum_comm]; exact ht
  have hpair (i j : ι) : tracePair (b i) (b j) (v i j) (v j i) (z i j)=w i j+w j i := by
    have hsym : z j i=z i j := hz j i
    dsimp only [tracePair,w]
    rw [hsym]
    ring
  change (∑ i, ∑ j, tracePair (b i) (b j) (v i j) (v j i) (z i j))=0
  simp only [hpair,Finset.sum_add_distrib,ht,hswap,add_zero]

end EuclideanMidpointRigidity

