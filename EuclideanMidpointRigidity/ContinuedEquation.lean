module

public import EuclideanMidpointRigidity.ContinuedRulings
public import EuclideanMidpointRigidity.BoundedSplitEquation

/-! # The polynomial equation and bounded scalar observations on a continued ruling -/

public section
noncomputable section
open Set Filter Polynomial
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
open Endpoint
namespace Endpoint
variable {V Z : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem SolvesOn.apply_linear {W : Set ℝ} {hW : IsOpen W} {A : ℝ[X]} {f : ℝ → V}
    (H : SolvesOn hW A f) (L : V →L[ℝ] Z) : SolvesOn hW A (L ∘ f) := by
  apply (solvesOn_iff_sum (L.contDiff.comp_contDiffOn H.smooth) (Nat.lt_succ_self _)).mpr
  intro x hx
  have he (i : ℕ) : iteratedDeriv i (L ∘ f) x=L (iteratedDeriv i f x) := by
    rw [iteratedDeriv_eq_iteratedFDeriv,L.iteratedFDeriv_comp_left (H.smooth.contDiffAt (hW.mem_nhds hx)) (by simp)]
    rfl
  simpa only [he,map_sum,map_smul,map_zero] using congrArg L ((solvesOn_iff_sum H.smooth (Nat.lt_succ_self _)).mp H x hx)

theorem SolvesOn.analytic_extension {W : Set ℝ} {hW : IsOpen W} {A : ℝ[X]} {f g : ℝ → V}
    (H : SolvesOn hW A f) {x : ℝ} (hx : x ∈ W) (hg : ContDiff ℝ ω g) (he : g =ᶠ[𝓝 x] f) :
    SolvesOn isOpen_univ A g := by
  let R := fun t ↦ ∑ i ∈ Finset.range (A.natDegree+1), A.coeff i • iteratedDeriv i g t
  have ha (i : ℕ) : ContDiff ℝ ω (iteratedDeriv i g) := by
    induction i with
    | zero => simpa using hg
    | succ i ih =>
      rw [iteratedDeriv_succ]
      apply ContDiff.deriv'
      simpa using ih
  have hr : ContDiff ℝ ω R := ContDiff.sum fun i _ ↦ contDiff_const.smul (ha i)
  have hzero : R =ᶠ[𝓝 x] (fun _ ↦ 0) := by
    filter_upwards [hW.mem_nhds hx,eventually_eventually_nhds.mpr he] with t ht heq
    have eq : g =ᶠ[𝓝 t] f := heq
    change ∑ i ∈ _, _ • iteratedDeriv i g t=0
    simpa only [fun i ↦ eq.iteratedDeriv_eq i] using (solvesOn_iff_sum H.smooth (Nat.lt_succ_self _)).mp H t ht
  have hz := hr.analyticOnNhd.eq_of_eventuallyEq (contDiff_const (c := (0:V)) (n := ω)).analyticOnNhd hzero
  apply (solvesOn_iff_sum ((hg.of_le (show (∞:WithTop ℕ∞)≤ω by simp)).contDiffOn) (Nat.lt_succ_self _)).mpr
  exact fun t _ ↦ congrFun hz t

end Endpoint

theorem LiftedSection.continued_equation {d : ℕ} (S : LiftedSection d) {p : Space d} (hp : p ∈ S.domain)
    (hm : ∀ q ∈ S.domain, S.Maximizes q) (hc : ∀ q ∈ S.domain, Nonempty (OrientedEndpointChart S.field q)) :
    SolvesOn isOpen_univ (S.rulingPolynomial p) (S.continuedField p) := by
  obtain ⟨_,_,_,h₀,H⟩ := S.tensor_ruling_ode hp hm hc
  exact H.analytic_extension h₀ (S.continuedFamily.analytic_time hp) (S.continuedField_germ hp hm hc)

theorem LiftedSection.bounded_observation_constant {d : ℕ} (S : LiftedSection d) {p : Space d} (hp : p ∈ S.domain)
    (hm : ∀ q ∈ S.domain, S.Maximizes q) (hc : ∀ q ∈ S.domain, Nonempty (OrientedEndpointChart S.field q))
    (L : Cubic d →L[ℝ] ℝ) {K : ℝ} (hK : ∀ t, |L (S.continuedField p t)|≤K) :
    ∀ s t, L (S.continuedField p s)=L (S.continuedField p t) :=
  ((S.continued_equation hp hm hc).apply_linear L).bounded_entire_constant
    (S.rulingPolynomial_monic p) (S.tensor_ruling_ode hp hm hc).1 hK

end EuclideanMidpointRigidity

