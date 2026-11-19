module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Tactic

/-! # A finite family of linear measurements controls a differential inequality -/

public section
noncomputable section
open Set Filter Metric
open scoped Topology
namespace EuclideanMidpointRigidity
variable {X M Y Z : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z]

theorem finite_observation_bound {ι : Type*} [Fintype ι] {l : Filter X}
    (A : ι → X → M →L[ℝ] Y) (T : ι → M →L[ℝ] Y) (R : X → M) (q : X → Z)
    (hc : ∀ i, Tendsto (A i) l (𝓝 (T i))) (hj : ∀ m, (∀ i, T i m=0) → m=0)
    (hb : ∀ i, ∃ K : ℝ, 0≤K ∧ ∀ᶠ x in l, ‖A i x (R x)‖≤K*‖q x‖) :
    ∃ L : ℝ, 0≤L ∧ ∀ᶠ x in l, ‖R x‖≤L*‖q x‖ := by
  classical
  let P : M →ₗ[ℝ] (ι → Y) := LinearMap.pi fun i ↦ (T i).toLinearMap
  have hP : Function.Injective P := by
    intro a b h
    apply sub_eq_zero.mp (hj (a-b) _)
    intro i
    rw [map_sub,sub_eq_zero]
    exact congrFun h i
  obtain ⟨c,hc₀,hanti⟩ := P.injective_iff_antilipschitz.mp hP
  have hc' : 0<(c:ℝ) := hc₀
  let δ : ℝ := 1/(2*c)
  have hδ : 0<δ := by dsimp [δ]; positivity
  choose K hK hh using hb
  let B := ∑ i, K i
  have hB : 0≤B := Finset.sum_nonneg fun i _ ↦ hK i
  have close (i : ι) : ∀ᶠ x in l, ‖A i x-T i‖<δ := by
    have ht : ∀ᶠ x in l, A i x ∈ ball (T i) δ := (hc i) (ball_mem_nhds (T i) hδ)
    exact ht.mono fun x hx ↦ by simpa only [mem_ball,dist_eq_norm] using hx
  refine ⟨2*c*B,by positivity,?_⟩
  filter_upwards [eventually_all.mpr close,eventually_all.mpr hh] with x hsmall hmeas
  have h₁ : ‖R x‖≤c*‖P (R x)‖ := by simpa [dist_eq_norm] using hanti.le_mul_dist (R x) 0
  have h₂ : ‖P (R x)‖≤δ*‖R x‖+B*‖q x‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    have ht := (A i x-T i).le_opNorm (R x)
    have hi : K i≤B := Finset.single_le_sum (fun j _ ↦ hK j) (Finset.mem_univ i)
    change ‖T i (R x)‖≤_
    calc
      _ ≤ ‖T i (R x)-A i x (R x)‖+‖A i x (R x)‖ := norm_le_norm_sub_add _ _
      _ ≤ _ := by
        rw [norm_sub_rev]
        exact add_le_add (ht.trans (mul_le_mul_of_nonneg_right (hsmall i).le (norm_nonneg _)))
          ((hmeas i).trans (mul_le_mul_of_nonneg_right hi (norm_nonneg _)))
  have h₃ := h₁.trans (mul_le_mul_of_nonneg_left h₂ hc'.le)
  have he : (c:ℝ)*δ=1/2 := by dsimp [δ]; field_simp <;> ring
  nlinarith only [h₃,congrArg (fun s : ℝ ↦ s*‖R x‖) he]

theorem local_zero_of_derivative_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {p : E} (h₀ : f p=0) (K : ℝ)
    (h : ∀ᶠ x in 𝓝 p, DifferentiableAt ℝ f x ∧ ‖fderiv ℝ f x‖≤K*‖f x‖) :
    ∀ᶠ x in 𝓝 p, f x=0 := by
  obtain ⟨r,hr,hU⟩ := Metric.mem_nhds_iff.mp h
  filter_upwards [ball_mem_nhds p hr] with x hx
  let v := x-p
  let g := fun t : ℝ ↦ p+t • v
  have he (t : ℝ) (ht : t ∈ Icc 0 1) : g t ∈ ball p r := by
    have hs := (convex_ball p r) (mem_ball_self hr) hx (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
    convert hs using 1 <;> dsimp [g,v] <;> module
  have hd (t : ℝ) (ht : t ∈ Icc 0 1) : HasDerivAt (f ∘ g) (fderiv ℝ f (g t) v) t := by
    have dg : HasDerivAt g v t := by simpa [g] using ((hasDerivAt_id t).smul_const v).const_add p
    exact (hU (he t ht)).1.hasFDerivAt.comp_hasDerivAt t dg
  have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (f := f ∘ g) (K := K*‖v‖)
    (HasDerivAt.continuousOn hd) (fun t ht ↦ (hd t (mem_Icc_of_Ico ht)).hasDerivWithinAt)
    (by simp [g,h₀]) (fun t ht ↦ by
      have H := (fderiv ℝ f (g t)).le_opNorm v
      exact H.trans ((mul_le_mul_of_nonneg_right (hU (he t (mem_Icc_of_Ico ht))).2 (norm_nonneg v)).trans_eq (by dsimp [Function.comp_def]; ring)))
    1 (right_mem_Icc.mpr (by norm_num))
  simpa [g,v] using hz

end EuclideanMidpointRigidity

