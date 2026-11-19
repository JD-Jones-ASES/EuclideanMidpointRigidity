module

public import EuclideanMidpointRigidity.Reflection

/-! # Complementarity of arbitrarily short pairs identifies the canonical midpoints -/

public section
open Set Metric
open scoped ContDiff
namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d

theorem localMidpointInvariance_of_pairs {Ω : Set E} {C : E → Cubic d}
    (hΩ : IsOpen Ω) (hC : ContDiffOn ℝ ∞ C Ω) (h : ∀ p ∈ Ω, ArbitrarilyShortComplementaryPairs C p) :
    LocalMidpointInvariance Ω C := by
  intro p hp
  have hd : ContDiffAt ℝ 1 C p := (hC.contDiffAt (hΩ.mem_nhds hp)).of_le (by simp)
  obtain ⟨r,U,A,hA⟩ := exists_canonical_local_midpoint hΩ hp hd 1
  obtain ⟨s,V,B,hB⟩ := exists_canonical_local_midpoint hΩ hp hd (-1)
  obtain ⟨δ,hδ,hs⟩ := h p hp (min r s) (lt_min hA.1 hB.1)
  let W := (U ∩ V) ∩ ball p δ ×ˢ ball p δ
  have hW : IsOpen W := (hA.2.2.1.inter hB.2.2.1).inter (isOpen_ball.prod isOpen_ball)
  have hpp : (p,p) ∈ W := ⟨⟨hA.2.2.2.1,hB.2.2.2.1⟩,mem_ball_self hδ,mem_ball_self hδ⟩
  refine ⟨r,s,W,A,B,hA.restrict hW hpp (fun _ h ↦ h.1.1),hB.restrict hW hpp (fun _ h ↦ h.1.2),?_⟩
  intro P Q hPQ
  obtain ⟨γ,v,η,w,h₁,h₂,hm⟩ := hs P Q hPQ.2.1 hPQ.2.2
  obtain ⟨_,_,_,ha,hu⟩ := hA.2.2.2.2 P Q hPQ.1.1
  obtain ⟨_,_,_,hb,hv⟩ := hB.2.2.2.2 P Q hPQ.1.2
  have ht : midpointTime ∈ Icc (0:ℝ) 1 := by constructor <;> norm_num [midpointTime]
  rw [ha,hb,← (hu γ v (h₁.mono_radius (min_le_left _ _)) _ ht).1,← (hv η w (h₂.mono_radius (min_le_right _ _)) _ ht).1]
  exact hm

end EuclideanMidpointRigidity

