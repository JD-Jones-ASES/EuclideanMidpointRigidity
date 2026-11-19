module

public import EuclideanMidpointRigidity.WeightedPair

/-! # The differentiated trace at strict and upper spectral values -/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity

def tracePair (b c v w z : ℝ) :=
  (1/2-b-c)*z*(v+w)-(traceWeight b+traceWeight c)*v*w

theorem LowPair.trace_diagonal {b v z : ℝ}
    (h : LowPair b b ((1-2*b)*v) ((1-2*b)*v) z) (hb : -1≤b) (hb' : b≤1/2) :
    traceWeight b*v=0 := by
  dsimp [traceWeight]
  linear_combination b/2*(h.diagonal hb hb').1

private theorem upper_trace_pair {b v w z : ℝ}
    (h : LowPair b (1/2) ((1-2*b)*v) ((1-2*(1/2))*w) z) (hb : b≤1/2) :
    tracePair b (1/2) v w z=0 ∧ (1-2*b)*v=0 ∧ z=0 := by
  norm_num at h
  obtain ⟨hx,hz⟩ := h.upper hb
  refine ⟨?_,hx,hz⟩
  dsimp only [tracePair,traceWeight]
  rw [hz]
  linear_combination -b*w/2*hx

theorem LowPair.trace_pair {b c v w z : ℝ}
    (h : LowPair b c ((1-2*b)*v) ((1-2*c)*w) z)
    (hb : -1≤b) (hc : -1≤c) (hb' : b≤1/2) (hc' : c≤1/2) :
    0≤tracePair b c v w z ∧ (tracePair b c v w z=0 → (1-2*b)*v=0 ∧ (1-2*c)*w=0 ∧ z=0) := by
  rcases eq_or_lt_of_le hc' with rfl|hc₀
  · obtain ⟨hp,hx,hz⟩ := upper_trace_pair h hb'
    exact ⟨hp.ge,fun _ ↦ ⟨hx,by norm_num,hz⟩⟩
  rcases eq_or_lt_of_le hb' with rfl|hb₀
  · obtain ⟨hp,hy,hz⟩ := upper_trace_pair h.swap hc'
    have hh : tracePair (1/2) c v w z=tracePair c (1/2) w v z := by unfold tracePair; ring
    exact ⟨(hh.trans hp).ge,fun _ ↦ ⟨by norm_num,hy,hz⟩⟩
  have hg : 0<(1-2*b)*(1-2*c) := mul_pos (by linarith) (by linarith)
  have he : weightedPairNumerator b c ((1-2*b)*v) ((1-2*c)*w) z=
      ((1-2*b)*(1-2*c))*tracePair b c v w z := by unfold weightedPairNumerator tracePair; ring
  by_cases hn : (1-2*b)*v=0 ∧ (1-2*c)*w=0 ∧ z=0
  · have hv := (mul_eq_zero.mp hn.1).resolve_left (by linarith)
    have hw := (mul_eq_zero.mp hn.2.1).resolve_left (by linarith)
    exact ⟨by simp [tracePair,hv,hw],fun _ ↦ hn⟩
  · have hp := h.weighted_pos hb hc hb₀ hc₀ hn
    rw [he] at hp
    have ht := pos_of_mul_pos_right hp hg.le
    exact ⟨ht.le,fun h₀ ↦ (ht.ne' h₀).elim⟩

end EuclideanMidpointRigidity

