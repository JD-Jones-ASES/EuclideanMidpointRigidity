module

public import EuclideanMidpointRigidity.CanonicalMidpoints

/-! # Complementarity for a constant tensor -/

@[expose] public section

open Set Metric Filter
open scoped ContDiff Topology

namespace EuclideanMidpointRigidity

variable {d : ℕ}
local notation "E" => Space d

/-- Reflect space in the affine midpoint and reverse affine time. -/
theorem reflect_geodesic {C : E → Cubic d} {c : Cubic d} {P Q : E} {γ v : ℝ → E}
    (h : IsGeodesicSegment C 1 γ v)
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, C (γ t) = c)
    (href : ∀ t ∈ Icc (0 : ℝ) 1, C (P + Q - γ (1-t)) = c) :
    IsGeodesicSegment C (-1) (fun t ↦ P + Q - γ (1-t)) (fun t ↦ v (1-t)) := by
  have rev {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 1-t ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  constructor
  · intro t ht
    have hr := (h.1 (1-t) (rev ht)).scomp t ((hasDerivAt_id t).const_sub 1)
    simpa [Function.comp_def] using hr.const_sub (P+Q)
  · intro t ht
    have hr := (h.2 (1-t) (rev ht)).scomp t ((hasDerivAt_id t).const_sub 1)
    simpa [Function.comp_def, hγ _ (rev ht), href _ ht] using hr

private theorem IsShortGeodesic.reflect {Ω : Set E} {C : E → Cubic d} {c : Cubic d}
    {p P Q : E} {r s : ℝ} {γ v : ℝ → E}
    (h : IsShortGeodesic C 1 p s P Q γ v) (hs : 0 < s) (hr : 3*s ≤ r)
    (hball : ball p r ⊆ Ω) (hc : ∀ x ∈ Ω, C x = c)
    (hP : P ∈ ball p s) (hQ : Q ∈ ball p s) :
    IsShortGeodesic C (-1) p r P Q (fun t ↦ P+Q-γ (1-t)) (fun t ↦ v (1-t)) := by
  have rev {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 1-t ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hsr : s ≤ r := by linarith
  have hpos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖P+Q-γ (1-t)-p‖ < r := by
    have hv := (h.2.2.2 _ (rev ht)).1
    have hpn : ‖P-p‖ < s := by simpa [mem_ball, dist_eq_norm] using hP
    have hqn : ‖Q-p‖ < s := by simpa [mem_ball, dist_eq_norm] using hQ
    rw [show P+Q-γ (1-t)-p = (P-p)+(Q-p)-(γ (1-t)-p) by abel]
    calc
      _ ≤ ‖(P-p)+(Q-p)‖ + ‖γ (1-t)-p‖ := norm_sub_le _ _
      _ ≤ ‖P-p‖ + ‖Q-p‖ + ‖γ (1-t)-p‖ := by gcongr; exact norm_add_le _ _
      _ < r := by linarith
  refine ⟨reflect_geodesic h.1 (fun t ht ↦ hc _ (hball ?_))
    (fun t ht ↦ hc _ (hball ?_)), ?_, ?_, ?_⟩
  · simpa [mem_ball, dist_eq_norm] using ((h.2.2.2 t ht).1.trans_le hsr)
  · simpa [mem_ball, dist_eq_norm] using hpos t ht
  · simp [h.2.2.1]
  · simp [h.2.1]
  · exact fun t ht ↦ ⟨hpos t ht, (h.2.2.2 _ (rev ht)).2.trans_le hsr⟩

theorem IsCanonicalLocalMidpoint.restrict {Ω : Set E} {C : E → Cubic d}
    {σ r : ℝ} {p : E} {W U : Set (E × E)} {A : E → E → E}
    (h : IsCanonicalLocalMidpoint Ω C σ p r W A)
    (hU : IsOpen U) (hpp : (p,p) ∈ U) (hsub : U ⊆ W) :
    IsCanonicalLocalMidpoint Ω C σ p r U A :=
  ⟨h.1, h.2.1, hU, hpp, fun P Q hPQ ↦ h.2.2.2.2 P Q (hsub hPQ)⟩

/-- Every constant cubic on an arbitrary Euclidean open set has complementary
canonical midpoints, including when the domain is nonconvex. -/
theorem localMidpointInvariance_of_constant {Ω : Set E} (hΩ : IsOpen Ω)
    {C : E → Cubic d} {c : Cubic d} (hc : ∀ x ∈ Ω, C x = c) :
    LocalMidpointInvariance Ω C := by
  intro p hp
  have hdiff : ContDiffAt ℝ 1 C p := contDiffAt_const.congr_of_eventuallyEq
    (Filter.mem_of_superset (hΩ.mem_nhds hp) fun x hx ↦ hc x hx)
  obtain ⟨rp, Wp, A, hA⟩ := exists_canonical_local_midpoint hΩ hp hdiff 1
  obtain ⟨rm, Wm, B, hB⟩ := exists_canonical_local_midpoint hΩ hp hdiff (-1)
  let s := min rp rm / 4
  have hs : 0 < s := div_pos (lt_min hA.1 hB.1) (by norm_num)
  have hsp : s ≤ rp := by dsimp [s]; linarith [min_le_left rp rm, hA.1]
  have hsm : 3*s ≤ rm := by dsimp [s]; linarith [min_le_right rp rm, hB.1]
  obtain ⟨δ, hδ, hsmall⟩ := exists_arbitrarily_short_geodesic hdiff 1 s hs
  let U := (Wp ∩ Wm) ∩ (ball p (min s δ) ×ˢ ball p (min s δ))
  have hU : IsOpen U := (hA.2.2.1.inter hB.2.2.1).inter (isOpen_ball.prod isOpen_ball)
  have hpp : (p,p) ∈ U := ⟨⟨hA.2.2.2.1, hB.2.2.2.1⟩,
    mem_ball_self (lt_min hs hδ), mem_ball_self (lt_min hs hδ)⟩
  refine ⟨rp, rm, U, A, B, hA.restrict hU hpp (fun _ h ↦ h.1.1),
    hB.restrict hU hpp (fun _ h ↦ h.1.2), ?_⟩
  intro P Q hPQ
  obtain ⟨γ, v, hg⟩ := hsmall P Q (ball_subset_ball (min_le_right s δ) hPQ.2.1)
    (ball_subset_ball (min_le_right s δ) hPQ.2.2)
  have hg' := hg.reflect hs hsm hB.2.1 hc (ball_subset_ball (min_le_left s δ) hPQ.2.1)
    (ball_subset_ball (min_le_left s δ) hPQ.2.2)
  obtain ⟨γp, vp, _, hap, hup⟩ := hA.2.2.2.2 P Q hPQ.1.1
  obtain ⟨γm, vm, _, hbm, hum⟩ := hB.2.2.2.2 P Q hPQ.1.2
  have ht : midpointTime ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num [midpointTime]
  have h1 := (hup _ _ (hg.mono_radius hsp) midpointTime ht).1
  have h2 := (hum _ _ hg' midpointTime ht).1
  rw [hap, hbm, ←h1, ←h2]
  norm_num [midpointTime]

end EuclideanMidpointRigidity
