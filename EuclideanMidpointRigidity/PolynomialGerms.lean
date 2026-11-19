module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Algebra.Order.Polynomial
public import Mathlib.Tactic

/-! # Polynomial germs of bounded Euclidean coordinates -/

@[expose] public section
noncomputable section
open Set Filter Polynomial
open scoped Topology Polynomial
namespace EuclideanMidpointRigidity

def PolynomialGerm (f : ℝ → ℝ) : Prop := ∃ P : ℝ[X], f =ᶠ[𝓝 0] P.eval

namespace PolynomialGerm

theorem congr {f g : ℝ → ℝ} (hf : PolynomialGerm f) (he : g =ᶠ[𝓝 0] f) : PolynomialGerm g := by
  obtain ⟨P,hP⟩ := hf
  exact ⟨P,he.trans hP⟩

theorem quadratic (a b c : ℝ) : PolynomialGerm (fun t ↦ a+t*b+t^2*c) := by
  refine ⟨C a+X*C b+X^2*C c,Eventually.of_forall fun t ↦ ?_⟩
  simp; ring

theorem sub {f g : ℝ → ℝ} (hf : PolynomialGerm f) (hg : PolynomialGerm g) : PolynomialGerm (fun t ↦ f t-g t) := by
  obtain ⟨P,hP⟩ := hf; obtain ⟨Q,hQ⟩ := hg
  refine ⟨P-Q,?_⟩
  filter_upwards [hP,hQ] with t hp hq
  simp [hp,hq]

theorem add {f g : ℝ → ℝ} (hf : PolynomialGerm f) (hg : PolynomialGerm g) : PolynomialGerm (fun t ↦ f t+g t) := by
  obtain ⟨P,hP⟩ := hf; obtain ⟨Q,hQ⟩ := hg
  refine ⟨P+Q,?_⟩
  filter_upwards [hP,hQ] with t hp hq
  simp [hp,hq]

theorem scale {f : ℝ → ℝ} (hf : PolynomialGerm f) (c : ℝ) : PolynomialGerm (fun t ↦ c*f t) := by
  obtain ⟨P,hP⟩ := hf
  refine ⟨C c*P,hP.mono fun t ht ↦ ?_⟩
  simp [ht]

theorem eval_constant_of_bounded (P : ℝ[X]) (M : ℝ) (hb : ∀ t, |P.eval t|≤M) (t : ℝ) : P.eval t=P.eval 0 := by
  have h : P.natDegree≤0 := by
    by_contra! h
    have hd := natDegree_pos_iff_degree_pos.mp h
    rcases le_total 0 P.leadingCoeff with hp|hn
    · obtain ⟨x,hx⟩ := ((P.tendsto_atTop_of_leadingCoeff_nonneg hd hp).eventually_gt_atTop M).exists
      exact (not_lt_of_ge ((le_abs_self _).trans (hb x))) hx
    · obtain ⟨x,hx⟩ := ((P.tendsto_atBot_of_leadingCoeff_nonpos hd hn).eventually_lt_atBot (-M)).exists
      linarith [neg_le_abs (P.eval x),hb x]
  rw [eq_C_of_natDegree_le_zero h,eval_C,eval_C]

theorem constant_of_square_sum {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ) (hf : ∀ i, PolynomialGerm (f i))
    (c : ℝ) (hc : ∀ᶠ t in 𝓝 (0:ℝ), ∑ i, (f i t)^2=c) (i : ι) :
    f i =ᶠ[𝓝 0] (fun _ ↦ f i 0) := by
  classical
  choose P hP using hf
  let Q := ∑ j, (P j)^2
  have he (t : ℝ) : Q.eval t=∑ j, ((P j).eval t)^2 := by simp [Q,Polynomial.eval_finsetSum]
  have hp : ∀ᶠ t in 𝓝 (0:ℝ), ∀ j, f j t=(P j).eval t := eventually_all.mpr hP
  have hn : ∀ᶠ t in 𝓝 (0:ℝ), Q.eval t=(C c).eval t := by
    filter_upwards [hc,hp] with t ht h
    simpa only [he,eval_C,← h] using ht
  have hQ := Q.eq_of_infinite_eval_eq (C c) (infinite_of_mem_nhds 0 hn)
  have hsum (t : ℝ) : ∑ j, ((P j).eval t)^2=c := by rw [← he,hQ,eval_C]
  have hbound (t : ℝ) : |(P i).eval t|≤|c|+1 := by
    have hh : ((P i).eval t)^2≤c := (Finset.single_le_sum (fun j _ ↦ sq_nonneg ((P j).eval t)) (Finset.mem_univ i)).trans_eq (hsum t)
    have hc' := le_abs_self c
    by_cases h : 0≤(P i).eval t
    · rw [abs_of_nonneg h]; nlinarith [sq_nonneg ((P i).eval t-1/2)]
    · rw [abs_of_neg (lt_of_not_ge h)]; nlinarith [sq_nonneg ((P i).eval t+1/2)]
  exact (hP i).mono fun t ht ↦ ht.trans ((eval_constant_of_bounded (P i) _ hbound t).trans (hP i).eq_of_nhds.symm)

end PolynomialGerm
end EuclideanMidpointRigidity

