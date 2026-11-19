module

public import EuclideanMidpointRigidity.FactorGeodesics
public import EuclideanMidpointRigidity.Globalization

/-! # Nielsen–Okamura Conjecture 9.1 in finite-dimensional Euclidean space -/

public section
noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace
namespace EuclideanMidpointRigidity
open OrthogonalFactor
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d
set_option backward.isDefEq.respectTransparency false

private theorem smaller_complement {D : Submodule ℝ E} {z : E} (hz : z ∈ D) (hn : z≠0) : Module.finrank ℝ Dᗮ<d := by
  let : Nontrivial D := ⟨⟨⟨z,hz⟩,0,fun h ↦ hn (congrArg Subtype.val h)⟩⟩
  have hpos : 0<Module.finrank ℝ D := Module.finrank_pos_iff.mpr inferInstance
  have hsum := D.finrank_add_finrank_orthogonal
  rw [finrank_euclideanSpace_fin] at hsum
  omega

/-- A smooth Euclidean dual-connection pair has complementary canonical local
midpoints on a connected open domain only if its symmetric cubic is constant. -/
theorem euclidean_midpoint_rigidity (Ω : Set E) (C : E → T)
    (openΩ : IsOpen Ω) (connectedΩ : IsPreconnected Ω)
    (smoothC : ContDiffOn ℝ ∞ C Ω) (complementary : LocalMidpointInvariance Ω C) :
    ∃ c : T, ∀ p ∈ Ω, C p=c := by
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    have hQ := MidpointJetEquations.of_midpoint openΩ smoothC complementary
    obtain ⟨a,hamp⟩ := hQ.amplitude_constant openΩ connectedΩ smoothC
    by_cases ha : 0<a
    · apply constant_of_dense_zero_derivative openΩ connectedΩ (smoothC.of_le (by simp))
      intro x hx r hr
      let U := Ω ∩ ball x r
      have hU : IsOpen U := openΩ.inter isOpen_ball
      obtain ⟨S,hSC,hne,hSU,H⟩ := exists_horizontal_patch hU ⟨x,hx,mem_ball_self hr⟩
        (smoothC.mono inter_subset_left) (hQ.mono inter_subset_left)
        (fun q hq ↦ oriented_endpoint_chart openΩ smoothC complementary hq.1) ha (fun q hq ↦ hamp q hq.1)
      obtain ⟨p,hp,s,hs,hball,z,hz,hnz⟩ := H.nonzero_fixed_directions hne
      rw [hSC] at hz
      let D := fixedDirections C (ball p s)
      have hdim : Module.finrank ℝ Dᗮ<d := smaller_complement hz hnz
      have hsub : ball p s ⊆ Ω := hball.trans (hSU.trans inter_subset_left)
      have hC := smoothC.mono hsub
      have hmid := inherited_midpoint D hC (hQ.mono hsub) rfl (fun y hy ↦ localMidpointInvariance_arbitrarilyShort
        openΩ (hsub hy) (smoothC.of_le (by simp)) complementary)
      obtain ⟨c,hc⟩ := ih _ hdim (ball 0 s) (field D C p) isOpen_ball (convex_ball _ _).isPreconnected (smooth_field D hC) hmid
      exact ⟨p,(hSU hp).1,(hSU hp).2,stationary_of_constant_factor D hs hC le_rfl hc⟩
    · refine ⟨0,fun p hp ↦ (amplitude_eq_zero_iff _).mp ?_⟩
      exact le_antisymm ((hamp p hp).le.trans (le_of_not_gt ha)) (amplitude_nonneg _)

end EuclideanMidpointRigidity

