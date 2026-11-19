module

public import EuclideanMidpointRigidity.UnivariateFamilies

/-! # Local isolation of a continuous root of a polynomial family -/

public section
noncomputable section
open Set Filter Polynomial
open scoped Topology
namespace EuclideanMidpointRigidity.SmoothPolynomial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {W : Set E}
local notation "A" => SmoothCoefficient W

/-- At a point of minimal root multiplicity the factor left after removing
the root stays nonzero in a product neighborhood. No continuity of a list
of all the other roots is needed. -/
theorem root_isolated_on_subpatch (P : Polynomial A) (hW : IsOpen W) (hn : W.Nonempty)
    {a : E → ℝ} (ha : ContinuousOn a W) (hP : ∀ x ∈ W, fiber P x≠0) :
    ∃ p ∈ W, ∀ᶠ q : E × ℝ in 𝓝 (p,a p), (fiber P q.1).eval q.2=0 → q.2=a q.1 := by
  classical
  let c := fun j x ↦ (Polynomial.taylor (a x) (fiber P x)).coeff j
  have hex : ∃ j, ∃ x ∈ W, c j x≠0 := by
    obtain ⟨x,hx⟩ := hn
    by_contra h
    push Not at h
    apply hP x hx
    apply (Polynomial.taylor_eq_zero (a x) _).mp
    ext j
    exact (h j x hx).trans (Polynomial.coeff_zero j).symm
  let m := Nat.find hex
  obtain ⟨p,hp,hm⟩ := Nat.find_spec hex
  change c m p≠0 at hm
  have low {j : ℕ} (hj : j<m) (x : E) (hx : x ∈ W) : c j x=0 := by
    by_contra hne
    exact Nat.find_min hex hj ⟨x,hx,hne⟩
  let N := P.natDegree
  have degree (x : E) : (Polynomial.taylor (a x) (fiber P x)).natDegree ≤ N := by
    rw [Polynomial.natDegree_taylor]
    exact Polynomial.natDegree_map_le
  have hmN : m≤N := le_trans (Polynomial.le_natDegree_of_ne_zero hm) (degree p)
  let Q := fun q : E × ℝ ↦ ∑ j ∈ Finset.range (N+1),
    if m≤j then c j q.1*(q.2-a q.1)^(j-m) else 0
  have center : Q (p,a p)=c m p := by
    dsimp only [Q]
    rw [Finset.sum_eq_single m]
    · simp
    · intro j _ hj
      by_cases h : m≤j
      · have hnz : j-m≠0 := by omega
        simp [h,hnz]
      · simp [h]
    · intro h
      exact (h (Finset.mem_range.mpr (by omega))).elim
  have proj : MapsTo (Prod.fst : E × ℝ → E) (W ×ˢ univ) W := fun _ h ↦ h.1
  have hQ : ContinuousOn Q (W ×ˢ univ) := by
    apply continuousOn_finsetSum
    intro j _
    by_cases h : m≤j
    · simp only [ite_eq_left h]
      exact ((continuous_shifted_coeff P ha j).comp continuousOn_fst proj).mul
        ((continuousOn_snd.sub (ha.comp continuousOn_fst proj)).pow _)
    · simp only [ite_eq_right h]
      exact continuousOn_const
  have hprod : W ×ˢ (univ : Set ℝ) ∈ 𝓝 (p,a p) :=
    (hW.prod isOpen_univ).mem_nhds ⟨hp,trivial⟩
  have hnon := (hQ.continuousAt hprod).eventually_ne (center ▸ hm : Q (p,a p)≠0)
  refine ⟨p,hp,?_⟩
  filter_upwards [hprod,hnon] with q hq hnq
  intro hroot
  let s := q.2-a q.1
  have fact : (fiber P q.1).eval q.2 = s^m*Q q := by
    rw [← Polynomial.taylor_eval_sub (a q.1) (fiber P q.1)]
    rw [Polynomial.eval_eq_sum_range' (n := N+1) (by have := degree q.1; omega)]
    dsimp only [Q]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change c j q.1*s^j = s^m*(if m≤j then c j q.1*s^(j-m) else 0)
    by_cases h : m≤j
    · rw [ite_eq_left h,show s^j=s^m*s^(j-m) by rw [← pow_add,Nat.add_sub_of_le h]]
      ring
    · rw [low (lt_of_not_ge h) q.1 hq.1,ite_eq_right h,zero_mul,mul_zero]
  have hsm := (mul_eq_zero.mp (fact.symm.trans hroot)).resolve_right hnq
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hsm)

end EuclideanMidpointRigidity.SmoothPolynomial

