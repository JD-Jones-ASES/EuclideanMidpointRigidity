module

public import EuclideanMidpointRigidity.MixedGradientExclusion
public import EuclideanMidpointRigidity.PureGradientExclusion

/-! # Constancy of the maximum value on a smooth lifted section -/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology ContDiff InnerProductSpace
namespace EuclideanMidpointRigidity.LiftedSection
variable {d : ℕ} (S : LiftedSection d)
local notation "E" => Space d

def Maximizes (p : E) : Prop := ∀ z : E, ‖z‖=1 → ⟪K (S.field p) z z,z⟫_ℝ≤S.a p

theorem gradient_zero {p : E} (hp : p ∈ S.domain) (hmax : ∀ᶠ q in 𝓝 p, S.Maximizes q) : gradient S.a p=0 := by
  by_contra hg
  have hn : ∀ᶠ q in 𝓝 p, q ∈ S.domain := S.isOpen.mem_nhds hp
  let N := negativeComponent S.field S.axis
  let P := positiveComponent S.field S.axis
  have hsplit (q : E) : P q=gradient S.a q-N q := rfl
  have eig (q : E) (hq : q ∈ S.domain) := component_eigenvalues S.isOpen S.smooth S.smoothAxis S.equations.quartic
    S.unit hq (S.critical q hq)
  by_cases hN : N p≠0
  · have near := (contDiffAt_negativeComponent (S.smooth.contDiffAt (S.isOpen.mem_nhds hp))
      (S.smoothAxis.contDiffAt (S.isOpen.mem_nhds hp))).continuousAt.eventually_ne hN
    apply PureAt.impossible (r := .negative) (S := S) (p := p) _ hmax.self_of_nhds
    refine ⟨hp,hg,?_⟩
    filter_upwards [hn,hmax,near] with q hq hm nz
    have hP : P q=0 := by
      by_contra hh
      exact S.not_mixed_at_maximum hm ⟨hq,nz,hh⟩
    have same := sub_eq_zero.mp ((hsplit q).symm.trans hP)
    rw [same]
    exact (eig q hq).1
  · have h₀ : N p=0 := not_ne_iff.mp hN
    have nz : P p≠0 := by simpa only [hsplit,h₀,sub_zero] using hg
    have near := (contDiffAt_positiveComponent S.isOpen S.smooth S.smoothAxis hp).continuousAt.eventually_ne nz
    apply PureAt.impossible (r := .positive) (S := S) (p := p) _ hmax.self_of_nhds
    refine ⟨hp,hg,?_⟩
    filter_upwards [hn,hmax,near] with q hq hm nonzero
    have hNq : N q=0 := by
      by_contra hh
      exact S.not_mixed_at_maximum hm ⟨hq,hh,nonzero⟩
    have same : P q=gradient S.a q := by rw [hsplit,hNq,sub_zero]
    rw [← same]
    exact (eig q hq).2

theorem amplitude_constant (hconn : IsPreconnected S.domain) (hmax : ∀ p ∈ S.domain, S.Maximizes p) :
    ∃ a : ℝ, ∀ p ∈ S.domain, S.a p=a := by
  apply S.isOpen.exists_is_const_of_fderiv_eq_zero hconn ((contDiffOn_sectionValue S.smooth S.smoothAxis).differentiableOn (by simp))
  intro p hp
  have hm := (show ∀ᶠ q in 𝓝 p, q ∈ S.domain from S.isOpen.mem_nhds hp).mono hmax
  have h := S.gradient_zero hp hm
  change fderiv ℝ S.a p=0
  rw [← toDual_gradient (f := S.a),h,map_zero]

end EuclideanMidpointRigidity.LiftedSection

