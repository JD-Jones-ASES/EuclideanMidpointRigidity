module

public import EuclideanMidpointRigidity.FrozenPairs
public import EuclideanMidpointRigidity.CoupledKilling

/-! # The possible eigenvalues of a nonzero oscillating component -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity.FixedAxis.FrozenPair
open Quartic
variable {d : ℕ} {c : Cubic d} {u : Space d} (P : FrozenPair (d := d) c u)
local notation "E" => Space d

def component (a l x y z : E) := jetEntry (P.jet a) l x y z

theorem swap_pair (a l x y z : E) : P.component a l x y z=P.component l a x y z := by
  dsimp only [component,jetEntry]; rw [P.exchange a l]

theorem swap_inner₁ (a l x y z : E) : P.component a l x y z=P.component a l y x z := jetEntry_swap₁ _ _ _ _ _
theorem swap_inner₂ (a l x y z : E) : P.component a l x y z=P.component a l x z y := jetEntry_swap₂ _ _ _ _ _

theorem killing (F : SliceFrame c u) (hu : K c u u=u) (l w : E) : directionProfile w (P.jet l w)=0 :=
  killing_of_slice_kernel F (P.quartic l) (P.axis_zero hu l) (P.axial_zero F hu l)
    (fun x hx ↦ P.support (b := 0) (by simpa only [zero_smul] using hx) (by norm_num [Resonant]) l) w

theorem vertex_sum (F : SliceFrame c u) (hu : K c u u=u) (l x y z w : E) :
    P.component l x y z w+P.component l y x z w+P.component l z x y w+P.component l w x y z=0 :=
  symJet_of_killing (P.killing F hu l) x y z w

private theorem source_weight (F : SliceFrame c u) (hu : K c u u=u) (l : E)
    {x y z w : E} {a b s t : ℝ}
    (hx : K c u x=a • x) (hy : K c u y=b • y) (hz : K c u z=s • z) (hw : K c u w=t • w)
    (hn : P.component l x y z w≠0) : a+b+s+t=5*a := by
  let X := P.component l x y z w
  let Y := P.component l y x z w
  let Z := P.component l z x y w
  let V := P.component l w x y z
  have h₀ : X+Y+Z+V=0 := P.vertex_sum F hu l x y z w
  have hW : a*X+b*Y+s*Z+t*V=0 := by
    have h := symJet_of_killing (J := (P.jet l).comp (c.val u))
      (weighted_killing (P.quartic l) (P.axis_zero hu l) (P.axial_zero F hu l)) x y z w
    change jetEntry (P.jet l) (K c u x) y z w+jetEntry (P.jet l) (K c u y) x z w+
      jetEntry (P.jet l) (K c u z) x y w+jetEntry (P.jet l) (K c u w) x y z=0 at h
    rw [hx,hy,hz,hw] at h
    simpa only [X,Y,Z,V,component,jetEntry,cubicEntry,map_smul,K_smul_coeff,real_inner_smul_left] using h
  have hr : mixedWeight b s t a Y Z V=0 := by
    simpa only [Y,Z,V,component,jetEntry_swap₁,jetEntry_swap₂] using
      eigen_mixed (P.quartic l) (P.axis_zero hu l) (P.axial_zero F hu l) hy hz hw hx
  have hprod : (a+b+s+t-5*a)*X=0 := by
    dsimp only [mixedWeight] at hr
    linear_combination (hr-(12*a-8*(a+b+s+t))*h₀-28*hW)/8
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hn)

theorem pair_weights (F : SliceFrame c u) (hu : K c u u=u)
    {l x y z w : E} {a b s t h : ℝ}
    (hl : K c u l=a • l) (hx : K c u x=b • x) (hy : K c u y=s • y) (hz : K c u z=t • z) (hw : K c u w=h • w)
    (hn : P.component l x y z w≠0) : Resonant b ∧ a=b ∧ s+t+h=4*b := by
  have ht := P.source_weight F hu l hx hy hz hw hn
  have ht' := P.source_weight F hu x hl hy hz hw (by rwa [P.swap_pair x l])
  have hb : Resonant b := by
    by_contra hh
    exact hn (by simp [component,jetEntry,cubicEntry,P.support hx hh,K])
  exact ⟨hb,by linarith only [ht,ht'],by linarith only [ht]⟩

end EuclideanMidpointRigidity.FixedAxis.FrozenPair

