module

public import EuclideanMidpointRigidity.KillingChords
public import EuclideanMidpointRigidity.AxialSliceTrace

/-! # Rigidity of a Killing tensor of constant shifted squared norm -/

public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity.FixedAxis
variable {d : ℕ}
local notation "E" => Space d
local notation "Op" => E →L[ℝ] E

theorem killing_trace_rigidity {W : Set E} {B : E → Op} (hW : IsOpen W) (hB : DifferentiableOn ℝ B W)
    (hs : ∀ x ∈ W, ∀ a b, ⟪B x a,b⟫_ℝ=⟪a,B x b⟫_ℝ)
    (hk : ∀ x ∈ W, ∀ v, squareValue (fderiv ℝ B x v) v=0)
    (htr : ∀ x ∈ W, ∀ v, operatorTrace (weightDerivative (B x) (fderiv ℝ B x v))=0)
    {p : E} (hp : p ∈ W) : fderiv ℝ B p=0 := by
  let D : Op := (1/4:ℝ) • ContinuousLinearMap.id ℝ E
  let L := fun x ↦ B x-D
  have dL (x : E) (hx : x ∈ W) : HasFDerivAt L (fderiv ℝ B x) x := (hB.differentiableAt (hW.mem_nhds hx)).hasFDerivAt.sub_const D
  have hL (x : E) (hx : x ∈ W) (a b : E) : ⟪L x a,b⟫_ℝ=⟪a,L x b⟫_ℝ := by
    simp only [L,D,sub_apply,smul_apply,ContinuousLinearMap.id_apply,inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,hs x hx]
  obtain ⟨δ,hδ,hδW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hp)
  let V := ball p δ
  have hpV : p ∈ V := mem_ball_self hδ
  have hc (x : E) (hx : x ∈ V) (y : E) (hy : y ∈ V) : squareValue (L y) (y-x)=squareValue (L x) (y-x) :=
    killing_chord isOpen_ball (convex_ball _ _) (fun q hq ↦ (dL q (hδW hq)).differentiableAt.differentiableWithinAt)
      (fun q hq v ↦ by rw [(dL q (hδW hq)).fderiv]; exact hk q (hδW hq) v) hx hy
  let F := EuclideanSpace.basisFun (Fin d) ℝ
  ext v : 1
  let ℓ := fun t : ℝ ↦ p+t • v
  have dl (t : ℝ) : HasDerivAt ℓ v t := by
    simpa only [ℓ,zero_add,one_smul,id_eq] using (hasDerivAt_const t p).fun_add ((hasDerivAt_id t).smul_const v)
  have hl₀ : ℓ 0=p := by simp [ℓ]
  have hnear : ∀ᶠ t in 𝓝 (0:ℝ), ℓ t ∈ V := (dl 0).continuousAt (isOpen_ball.mem_nhds (hl₀.symm ▸ hpV))
  obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp hnear
  have hrW (t : ℝ) (ht : t ∈ ball (0:ℝ) r) : ℓ t ∈ W := hδW (hrV ht)
  let T := fun t ↦ operatorTrace (weightedOperator (B (ℓ t)))
  have hdt (t : ℝ) (ht : t ∈ ball (0:ℝ) r) : HasDerivAt T 0 t := by
    have h := (hB.differentiableAt (hW.mem_nhds (hrW t ht))).hasFDerivAt.comp_hasDerivAt t (dl t)
    have H := hasDerivAt_operatorTrace F (hasDerivAt_weightedOperator h)
    change HasDerivAt T (operatorTrace (weightDerivative (B (ℓ t)) (fderiv ℝ B (ℓ t) v))) t at H
    rwa [htr _ (hrW t ht) v] at H
  have hT (t : ℝ) (ht : t ∈ ball (0:ℝ) r) : T t=T 0 :=
    isOpen_ball.is_const_of_deriv_eq_zero (convex_ball _ _).isPreconnected
      (fun s hs ↦ (hdt s hs).differentiableAt.differentiableWithinAt) (fun {s} hs ↦ (hdt s hs).deriv) ht (mem_ball_self hr)
  let f := fun (i : Fin d × Fin d) (t : ℝ) ↦ operatorEntry F (L (ℓ t)) i.1 i.2
  have hf (i : Fin d × Fin d) : PolynomialGerm (f i) :=
    (polynomial_entry isOpen_ball hc (fun x hx ↦ hL x (hδW hx)) hpV v (F i.2) (F i.1)).congr
      (Eventually.of_forall fun _ ↦ real_inner_comm _ _)
  have hc' : ∀ᶠ t in 𝓝 (0:ℝ), ∑ i, (f i t)^2=operatorTrace ((1/16:ℝ) • ContinuousLinearMap.id ℝ E)-T 0 := by
    filter_upwards [ball_mem_nhds (0:ℝ) hr] with t ht
    change (∑ i : Fin d × Fin d, (operatorEntry F (L (ℓ t)) i.1 i.2)^2)=_
    rw [square_sum_trace F _ (hL _ (hrW t ht)),shifted_trace]
    exact congrArg (_-·) (hT t ht)
  have he : ∀ᶠ t in 𝓝 (0:ℝ), ∀ i, f i t=f i 0 := eventually_all.mpr fun i ↦ PolynomialGerm.constant_of_square_sum f hf _ hc' i
  have hconst : (L ∘ ℓ) =ᶠ[𝓝 (0:ℝ)] (fun _ ↦ L p) := by
    filter_upwards [he] with t ht
    apply sub_eq_zero.mp
    apply operator_zero_of_entries F
    intro i j
    have h := ht (i,j)
    change operatorEntry F (L (ℓ t)) i j=operatorEntry F (L (ℓ 0)) i j at h
    rw [hl₀] at h
    simpa only [operatorEntry,sub_apply,inner_sub_right,sub_eq_zero,Function.comp_apply] using h
  have h' : HasDerivAt (L ∘ ℓ) (fderiv ℝ B p v) 0 := by
    have H := (dL (ℓ 0) (hl₀.symm ▸ hp)).comp_hasDerivAt (0:ℝ) (dl 0)
    simpa only [hl₀] using H
  exact h'.unique ((hasDerivAt_const 0 (L p)).congr_of_eventuallyEq hconst)

end EuclideanMidpointRigidity.FixedAxis

