module

public import EuclideanMidpointRigidity.FlatForceJets
public import EuclideanMidpointRigidity.StraightMaxima

/-! # Differentiating two vanishing axial slots while the direction varies -/

public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d

private theorem rate_along {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {W : Set E} {f : E → Y}
    (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W) {p : E} (hp : p ∈ W) (v : E) :
    HasDerivAt (f ∘ displacementLine p v) (directional f v p) 0 :=
  differentiableAlongLine ((hf.contDiffAt (hW.mem_nhds hp)).differentiableAt (by simp)) v

theorem second_axial_zero {W : Set E} {D : E → T} {e : E → E} (hW : IsOpen W)
    (hD : ContDiffOn ℝ ∞ D W) (he : ContDiffOn ℝ ∞ e W) (hpos : ∀ q ∈ W, K (D q) (e q) (e q)=0)
    {p : E} (hp : p ∈ W) (h₀ : D p=0) (h₁ : ∀ v w, K (directions D [v] p) (e p) w=0) (l w : E) :
    K (directions D [l,w] p) (e p) (e p)=0 := by
  have hsrc (q : E) (hq : q ∈ W) :
      K (directional D w q) (e q) (e q)+K (D q) (directional e w q) (e q)+
        K (D q) (e q) (directional e w q)=0 := by
    have dc := rate_along hW hD hq w
    have de := rate_along hW he hq w
    have h := hasDerivAt_K dc de de
    have hn : ∀ᶠ t in 𝓝 (0:ℝ), displacementLine q w t ∈ W :=
      (hasDerivAt_displacementLine q w).continuousAt (by rw [displacementLine_zero]; exact hW.mem_nhds hq)
    have hz := (hasDerivAt_const (0:ℝ) (0:E)).congr_of_eventuallyEq (hn.mono fun t ht ↦ hpos _ ht)
    simpa only [Function.comp_apply,displacementLine_zero] using h.unique hz
  let γ := displacementLine p l
  have dc := rate_along hW hD hp l
  have de := rate_along hW he hp l
  have dJ := rate_along hW (directions.smooth hW hD [w]) hp l
  have dA := rate_along hW (directions.smooth hW he [w]) hp l
  have h := ((hasDerivAt_K dJ de de).fun_add (hasDerivAt_K dc dA de)).fun_add (hasDerivAt_K dc de dA)
  have hn : ∀ᶠ t in 𝓝 (0:ℝ), γ t ∈ W :=
    (hasDerivAt_displacementLine p l).continuousAt (by rw [displacementLine_zero]; exact hW.mem_nhds hp)
  have hz := (hasDerivAt_const (0:ℝ) (0:E)).congr_of_eventuallyEq (hn.mono fun t ht ↦ hsrc (γ t) ht)
  have hh := h.unique hz
  simp only [Function.comp_apply,displacementLine_zero] at hh
  have hr (v z : E) : K (directions D [v] p) z (e p)=0 := (K_symm _ _ _).trans (h₁ v z)
  have hK (a b : E) : K (0:T) a b=0 := rfl
  change K (directions D [l,w] p) (e p) (e p)+K (directions D [w] p) (directional e l p) (e p)+
    K (directions D [w] p) (e p) (directional e l p)+
    (K (directions D [l] p) (directional e w p) (e p)+K (D p) (directions e [l,w] p) (e p)+K (D p) (directional e w p) (directional e l p))+
    (K (directions D [l] p) (e p) (directional e w p)+K (D p) (directional e l p) (directional e w p)+K (D p) (e p) (directions e [l,w] p))=0 at hh
  simpa only [hr,h₁,h₀,hK,add_zero,zero_add] using hh

end EuclideanMidpointRigidity

