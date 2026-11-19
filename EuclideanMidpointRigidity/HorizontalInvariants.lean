module

public import EuclideanMidpointRigidity.HorizontalVector
public import EuclideanMidpointRigidity.CriticalPhase

/-! # Preservation of the unit sphere and the cubic value by horizontal transport -/

public section
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity.Horizontal
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d
set_option backward.isDefEq.respectTransparency false

theorem hasDerivAt_profile {c : ℝ → T} {h : ℝ → E} {t : ℝ} {b : T} {v : E}
    (hc : HasDerivAt c b t) (hh : HasDerivAt h v t) : HasDerivAt (fun s ↦ directionProfile (h s) (c s))
      (directionProfile (h t) b+3*⟪v,K (c t) (h t) (h t)⟫_ℝ) t := by
  simp only [directionProfile_apply]
  convert! (hasDerivAt_K hc hh hh).inner ℝ hh using 1
  simp only [inner_add_left,K_symm (c t) v (h t),K_selfAdjoint (c t) (h t) v (h t)]
  linarith only [real_inner_comm (K (c t) (h t) (h t)) v]

theorem phase_invariants {Ω : Set E} {C : E → T} (hΩ : IsOpen Ω) (hC : ContDiffOn ℝ ∞ C Ω) (hQ : QuarticOn Ω C)
    (l : E) {I : Set ℝ} (hI : IsOpen I) (hconn : IsPreconnected I) (h₀ : 0 ∈ I) {γ : ℝ → E × E}
    (hdom : ∀ t ∈ I, (γ t).1 ∈ Ω) (hd : ∀ s ∈ I, HasDerivAt γ (phaseVector C l (γ s)) s)
    (hu : ‖(γ 0).2‖=1) : ∀ s ∈ I, ‖(γ s).2‖=1 ∧ directionProfile (γ s).2 (C (γ s).1)=directionProfile (γ 0).2 (C (γ 0).1) := by
  let x := fun t ↦ (γ t).1
  let e := fun t ↦ (γ t).2
  let b := fun t ↦ phaseVector C l (γ t)
  have dx (t : ℝ) (ht : t ∈ I) : HasDerivAt x (b t).1 t := hasDerivAt_first_projection (hd t ht)
  have de (t : ℝ) (ht : t ∈ I) : HasDerivAt e (b t).2 t := hasDerivAt_second_projection (hd t ht)
  have dnorm (t : ℝ) (ht : t ∈ I) : HasDerivAt (fun s ↦ ⟪e s,e s⟫_ℝ) 0 t := by
    convert! (de t ht).inner ℝ (de t ht) using 1
    have hz : ⟪e t,(b t).2⟫_ℝ=0 := tangent C l (γ t)
    linarith only [hz,real_inner_comm (e t) (b t).2]
  have un (t : ℝ) (ht : t ∈ I) : ‖e t‖=1 := by
    have H := hI.is_const_of_deriv_eq_zero hconn (fun u h ↦ (dnorm u h).differentiableAt.differentiableWithinAt)
      (fun {u} h ↦ (dnorm u h).deriv) ht h₀
    simp only [real_inner_self_eq_norm_sq,show ‖e 0‖=1 from hu,one_pow] at H
    nlinarith [norm_nonneg (e t)]
  have dv (t : ℝ) (ht : t ∈ I) : HasDerivAt (fun s ↦ directionProfile (e s) (C (x s))) 0 t := by
    have dc := ((hC.contDiffAt (hΩ.mem_nhds (hdom t ht))).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (dx t ht)
    have h := hasDerivAt_profile dc (de t ht)
    exact (profile_rate l (γ t) (un t ht) (hQ (hdom t ht))) ▸ h
  exact fun t ht ↦ ⟨un t ht,hI.is_const_of_deriv_eq_zero hconn (fun u h ↦ (dv u h).differentiableAt.differentiableWithinAt)
    (fun {u} h ↦ (dv u h).deriv) ht h₀⟩

end EuclideanMidpointRigidity.Horizontal

