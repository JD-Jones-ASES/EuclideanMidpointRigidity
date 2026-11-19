module

public import EuclideanMidpointRigidity.FrozenSpectrum

/-! # A nonzero pair has four equal eigenvalue labels and a doubled fifth label -/

public section
noncomputable section
namespace EuclideanMidpointRigidity.FixedAxis.FrozenPair
variable {d : ℕ} {c : Cubic d} {u : Space d} (P : FrozenPair (d := d) c u)
local notation "E" => Space d

private theorem different_sources (F : SliceFrame c u) (hu : K c u u=u)
    {l x y z w : E} {a b s t h : ℝ}
    (hl : K c u l=a • l) (hx : K c u x=b • x) (hy : K c u y=s • y) (hz : K c u z=t • z) (hw : K c u w=h • w)
    (hab : a≠b) : P.component l x y z w=0 := by
  by_contra hn
  exact hab (P.pair_weights F hu hl hx hy hz hw hn).2.1

private theorem two_different_targets (F : SliceFrame c u) (hu : K c u u=u)
    {l x y z w : E} {b s t h : ℝ}
    (hl : K c u l=b • l) (hx : K c u x=b • x) (hy : K c u y=s • y) (hz : K c u z=t • z) (hw : K c u w=h • w)
    (hzt : b≠t) (hwt : b≠h) : P.component l x y z w=0 := by
  have h₁ := P.vertex_sum F hu l x y z w
  rw [P.different_sources F hu hl hz hx hy hw hzt,P.different_sources F hu hl hw hx hy hz hwt,add_zero,add_zero] at h₁
  by_cases hs : b=s
  · subst s
    have h₂ := P.vertex_sum F hu x l y z w
    have h₃ := P.vertex_sum F hu y l x z w
    rw [P.different_sources F hu hx hz hl hy hw hzt,P.different_sources F hu hx hw hl hy hz hwt,
      add_zero,add_zero,P.swap_pair x l] at h₂
    rw [P.different_sources F hu hy hz hl hx hw hzt,P.different_sources F hu hy hw hl hx hz hwt,
      add_zero,add_zero,P.swap_pair y l,P.swap_pair y x] at h₃
    linarith only [h₁,h₂,h₃]
  · simpa only [P.different_sources F hu hl hy hx hz hw hs,add_zero] using h₁

theorem classification (F : SliceFrame c u) (hu : K c u u=u)
    {l x y z w : E} {a b s t h : ℝ}
    (hl : K c u l=a • l) (hx : K c u x=b • x) (hy : K c u y=s • y) (hz : K c u z=t • z) (hw : K c u w=h • w)
    (hn : P.component l x y z w≠0) :
    Resonant b ∧ a=b ∧ ((s=b ∧ t=b ∧ h=2*b) ∨ (s=b ∧ h=b ∧ t=2*b) ∨ (t=b ∧ h=b ∧ s=2*b)) := by
  obtain ⟨hr,rfl,hsum⟩ := P.pair_weights F hu hl hx hy hz hw hn
  refine ⟨hr,rfl,?_⟩
  by_cases hs : s=a
  · by_cases ht : t=a
    · exact Or.inl ⟨hs,ht,by linarith only [hs,ht,hsum]⟩
    · by_cases hh : h=a
      · exact Or.inr (Or.inl ⟨hs,hh,by linarith only [hs,hh,hsum]⟩)
      · exact False.elim (hn (P.two_different_targets F hu hl hx hy hz hw (Ne.symm ht) (Ne.symm hh)))
  · by_cases ht : t=a
    · by_cases hh : h=a
      · exact Or.inr (Or.inr ⟨ht,hh,by linarith only [ht,hh,hsum]⟩)
      · have h₀ := P.two_different_targets F hu hl hx hz hy hw (Ne.symm hs) (Ne.symm hh)
        exact False.elim (hn ((P.swap_inner₁ l x y z w).trans h₀))
    · have h₀ := P.two_different_targets F hu hl hx hw hy hz (Ne.symm hs) (Ne.symm ht)
      exact False.elim (hn (((P.swap_inner₂ l x y z w).trans (P.swap_inner₁ l x y w z)).trans h₀))

end EuclideanMidpointRigidity.FixedAxis.FrozenPair

