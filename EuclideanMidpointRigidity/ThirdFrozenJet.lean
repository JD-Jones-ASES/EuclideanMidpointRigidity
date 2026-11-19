module

public import EuclideanMidpointRigidity.CurvatureWeights

/-! # A third symmetric spatial slot kills the remaining curvature component -/

public section
noncomputable section
namespace EuclideanMidpointRigidity.FixedAxis

private theorem triangle_rigidity {X : Type*} (R : X → X → X → X → X → ℝ)
    (s₁ : ∀ a b i j k, R a b i j k=R b a i j k)
    (s₂ : ∀ a b i j k, R a b i j k=R a i b j k)
    (s₃ : ∀ a b i j k, R a b i j k=R a b i k j)
    (row : ∀ a b i j k, R a b i j k+R a b j i k+R a b k i j=0)
    (a b i j k : X) : R a b i j k=0 := by
  have h01 := row a b i j k
  have h02 := row a i b j k
  have h03 := row a j b i k
  have h04 := row a k b i j
  have h12 := row b i a j k
  have h13 := row b j a i k
  have h14 := row b k a i j
  have h23 := row i j a b k
  have h24 := row i k a b j
  have h34 := row j k a b i
  simp only [s₁,s₂,s₃] at h01 h02 h03 h04 h12 h13 h14 h23 h24 h34 ⊢
  linarith only [h01,h02,h03,h04,h12,h13,h14,h23,h24,h34]

variable {d : ℕ} {c : Cubic d} {u : Space d}
local notation "E" => Space d

private theorem five_equal (F : SliceFrame c u) (hu : K c u u=u) (P : E → FrozenPair c u)
    (he : ∀ a b l, (P a).jet b l=(P b).jet a l) {a b l i j k : E} {s t : ℝ}
    (ha : K c u a=s • a) (hb : K c u b=s • b) (hl : K c u l=s • l)
    (hi : K c u i=s • i) (hj : K c u j=s • j) (hk : K c u k=t • k) (hst : s≠t) :
    (P a).component b l i j k=0 := by
  let V := {v : E // K c u v=s • v}
  let R := fun (a b l i j : V) ↦ (P a).component b l i j k
  have s₁ (a b l i j : V) : R a b l i j=R b a l i j := by
    dsimp only [R,FrozenPair.component,Quartic.jetEntry]
    rw [he]
  have s₂ (a b l i j : V) : R a b l i j=R a l b i j := (P a).swap_pair _ _ _ _ _
  have s₃ (a b l i j : V) : R a b l i j=R a b l j i := (P a).swap_inner₁ _ _ _ _ _
  have row (a b l i j : V) : R a b l i j+R a b i l j+R a b j l i=0 := by
    have h := (P a).vertex_sum F hu b l i j k
    have hz : (P a).component b k l i j=0 := by
      by_contra hn
      exact hst ((P a).pair_weights F hu b.property hk l.property i.property j.property hn).2.1
    simpa only [hz,add_zero] using h
  exact triangle_rigidity R s₁ s₂ s₃ row ⟨a,ha⟩ ⟨b,hb⟩ ⟨l,hl⟩ ⟨i,hi⟩ ⟨j,hj⟩

theorem third_frozen_zero (F : SliceFrame c u) (hu : K c u u=u) (P : E → FrozenPair c u)
    (he : ∀ a b l, (P a).jet b l=(P b).jet a l) {a b l i j k : E} {α β γ ξ η ζ : ℝ}
    (ha : K c u a=α • a) (hb : K c u b=β • b) (hl : K c u l=γ • l)
    (hi : K c u i=ξ • i) (hj : K c u j=η • j) (hk : K c u k=ζ • k) :
    (P a).component b l i j k=0 := by
  by_contra hn
  obtain ⟨hr,hβ,hcase⟩ := (P a).classification F hu hb hl hi hj hk hn
  have hswap : (P a).component b l i j k=(P b).component a l i j k := by
    dsimp only [FrozenPair.component,Quartic.jetEntry]; rw [he]
  have hα := ((P b).pair_weights F hu ha hl hi hj hk (hswap ▸ hn)).2.1
  subst α
  subst β
  have hne : γ≠2*γ := by rcases hr with h|h <;> rw [h] <;> norm_num
  rcases hcase with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩
  · exact hn (five_equal F hu P he ha hb hl hi hj hk hne)
  · apply hn
    rw [(P a).swap_inner₂ b l i j k]
    exact five_equal F hu P he ha hb hl hi hk hj hne
  · apply hn
    rw [(P a).swap_inner₁ b l i j k,(P a).swap_inner₂ b l j i k]
    exact five_equal F hu P he ha hb hl hj hk hi hne

end EuclideanMidpointRigidity.FixedAxis

