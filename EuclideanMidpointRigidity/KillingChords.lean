module

public import EuclideanMidpointRigidity.PolynomialGerms
public import EuclideanMidpointRigidity.SpectralTrace
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Polynomial interpolation for a Euclidean Killing tensor -/

@[expose] public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity.FixedAxis
variable {d : ℕ}
local notation "E" => Space d
local notation "Op" => E →L[ℝ] E

def squareValue (B : Op) (w : E) := ⟪B w,w⟫_ℝ

theorem killing_chord {W : Set E} {B : E → Op} (hW : IsOpen W) (hv : Convex ℝ W) (hB : DifferentiableOn ℝ B W)
    (hK : ∀ x ∈ W, ∀ w, squareValue (fderiv ℝ B x w) w=0) {x y : E} (hx : x ∈ W) (hy : y ∈ W) :
    squareValue (B y) (y-x)=squareValue (B x) (y-x) := by
  let w := y-x
  let L := fun t : ℝ ↦ x+t • w
  let f := fun t : ℝ ↦ squareValue (B (L t)) w
  have hL (t : ℝ) : HasDerivAt L w t := by
    simpa only [L,zero_add,one_smul,id_eq] using (hasDerivAt_const t x).fun_add ((hasDerivAt_id t).smul_const w)
  have hm (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : L t ∈ W := by
    have h := hv hx hy (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
    convert h using 1
    dsimp only [L,w]
    module
  have hd (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : HasDerivAt f 0 t := by
    have h := ((hB.differentiableAt (hW.mem_nhds (hm t ht))).hasFDerivAt.comp_hasDerivAt t (hL t)).clm_apply (hasDerivAt_const t w)
    have h' := h.inner ℝ (hasDerivAt_const t w)
    have hz : ⟪(fderiv ℝ B (L t) w) w,w⟫_ℝ=0 := hK _ (hm t ht) w
    simpa only [f,squareValue,Function.comp_apply,map_zero,add_zero,zero_add,inner_zero_right,hz] using h'
  obtain ⟨t,ht,he⟩ := exists_deriv_eq_slope f (by norm_num : (0:ℝ)<1)
    (fun s hs ↦ (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs ↦ (hd s ⟨hs.1.le,hs.2.le⟩).differentiableAt.differentiableWithinAt)
  rw [(hd t ⟨ht.1.le,ht.2.le⟩).deriv,sub_zero,div_one] at he
  have hh : f 1=f 0 := sub_eq_zero.mp he.symm
  simpa only [f,L,w,one_smul,zero_smul,add_zero,add_sub_cancel] using hh

private theorem quadratic_line (A : Op) (b v : E) :
    PolynomialGerm (fun t : ℝ ↦ squareValue A (b+t • v)) := by
  apply (PolynomialGerm.quadratic (squareValue A b) (⟪A b,v⟫_ℝ+⟪A v,b⟫_ℝ) (squareValue A v)).congr
  apply Eventually.of_forall; intro t
  simp only [squareValue,map_add,map_smul,inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right]
  ring

theorem polynomial_direction {W : Set E} {B : E → Op} (hW : IsOpen W)
    (hc : ∀ x ∈ W, ∀ y ∈ W, squareValue (B y) (y-x)=squareValue (B x) (y-x))
    {p : E} (hp : p ∈ W) (v w : E) : PolynomialGerm (fun t : ℝ ↦ squareValue (B (p+t • v)) w) := by
  have hnear (b : E) : ∀ᶠ t in 𝓝 (0:ℝ), p+t • b ∈ W := (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
    (hW.mem_nhds (by simpa using hp : p+(0:ℝ) • b ∈ W))
  have hm : ∀ᶠ t in 𝓝 (0:ℝ), p-t • w ∈ W := by
    simpa only [smul_neg,← sub_eq_add_neg] using hnear (-w)
  have hpos : ∀ᶠ t in 𝓝[>] (0:ℝ), 0<t := self_mem_nhdsWithin
  obtain ⟨s,hs,ha,hb⟩ := (hpos.and (((hnear w).and hm).filter_mono nhdsWithin_le_nhds)).exists
  let Q := fun (x : E) (t : ℝ) ↦ squareValue (B x) ((p-x)+t • v)
  have hQ (x : E) : PolynomialGerm (Q x) := quadratic_line _ _ _
  let a := p+s • w
  let b := p-s • w
  apply ((((hQ a).add (hQ b)).sub ((hQ p).scale 2)).scale (2*s^2)⁻¹).congr
  filter_upwards [hnear v] with t ht
  let y := p+t • v
  have h (x : E) (hx : x ∈ W) : Q x t=squareValue (B y) (y-x) := by
    have e : p-x+t • v=y-x := by dsimp only [y]; abel
    exact (congrArg (squareValue (B x)) e).trans (hc x hx y ht).symm
  have hya : y-a=t • v-s • w := by dsimp only [y,a]; abel
  have hyb : y-b=t • v+s • w := by dsimp only [y,b]; abel
  have hyp : y-p=t • v := by dsimp only [y]; abel
  change squareValue (B y) w=(2*s^2)⁻¹*((Q a t+Q b t)-2*Q p t)
  rw [h a ha,h b hb,h p hp,hya,hyb,hyp]
  simp only [squareValue,map_sub,map_add,map_smul,inner_add_left,inner_add_right,inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right]
  field_simp [hs.ne']
  ring

theorem polynomial_entry {W : Set E} {B : E → Op} (hW : IsOpen W)
    (hc : ∀ x ∈ W, ∀ y ∈ W, squareValue (B y) (y-x)=squareValue (B x) (y-x))
    (hB : ∀ x ∈ W, ∀ v w, ⟪B x v,w⟫_ℝ=⟪v,B x w⟫_ℝ) {p : E} (hp : p ∈ W) (v a b : E) :
    PolynomialGerm (fun t : ℝ ↦ ⟪B (p+t • v) a,b⟫_ℝ) := by
  have H := polynomial_direction hW hc hp v
  apply ((((H (a+b)).sub (H a)).sub (H b)).scale (1/2)).congr
  have ht : ∀ᶠ t in 𝓝 (0:ℝ), p+t • v ∈ W := (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
    (hW.mem_nhds (by simpa using hp : p+(0:ℝ) • v ∈ W))
  filter_upwards [ht] with t ht
  simp only [squareValue,map_add,inner_add_left,inner_add_right,hB _ ht b a,real_inner_comm b (B (p+t • v) a)]
  ring

end EuclideanMidpointRigidity.FixedAxis

