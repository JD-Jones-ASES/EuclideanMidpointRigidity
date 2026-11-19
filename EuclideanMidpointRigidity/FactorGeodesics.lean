module

public import EuclideanMidpointRigidity.FactorField
public import EuclideanMidpointRigidity.CanonicalPairs

/-! # Projection of short geodesics and inheritance of the midpoint law -/

public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.OrthogonalFactor
variable {d : ℕ} (D : Submodule ℝ (Space d))
local notation "E" => Space d
local notation "F" => Space (Module.finrank ℝ Dᗮ)
set_option backward.isDefEq.respectTransparency false

theorem project_lift (p : E) (a : F) : projection Dᗮ (liftPoint D p a-p)=a := by
  rw [liftPoint,add_sub_cancel_left,projection_inclusion]

theorem projected_short {p : E} {a b c : F} {σ r : ℝ} {C : E → Cubic d} {G : F → Cubic (Module.finrank ℝ Dᗮ)}
    {γ v : ℝ → E} (hg : IsShortGeodesic C σ (liftPoint D p a) r (liftPoint D p b) (liftPoint D p c) γ v)
    (hprod : ∀ t ∈ Icc (0:ℝ) 1, projection Dᗮ (K (C (γ t)) (v t) (v t))=
      K (G (projection Dᗮ (γ t-p))) (projection Dᗮ (v t)) (projection Dᗮ (v t))) :
    IsShortGeodesic G σ a r b c (fun t ↦ projection Dᗮ (γ t-p)) (fun t ↦ projection Dᗮ (v t)) := by
  let P := projection Dᗮ
  obtain ⟨⟨hγ,hv⟩,h₀,h₁,hsize⟩ := hg
  refine ⟨⟨fun t ht ↦ P.hasFDerivAt.comp_hasDerivAt t ((hγ t ht).sub_const p),?_⟩,?_,?_,?_⟩
  · intro t ht
    have hh := P.hasFDerivAt.comp_hasDerivAt t (hv t ht)
    rw [map_smul] at hh
    exact (hprod t ht) ▸ hh
  · change projection Dᗮ (γ 0-p)=b
    rw [h₀,project_lift]
  · change projection Dᗮ (γ 1-p)=c
    rw [h₁,project_lift]
  · intro t ht
    have eq : P (γ t-p)-a=P (γ t-liftPoint D p a) := by
      conv_lhs => rw [← project_lift D p a,← P.map_sub]
      congr 1
      abel
    exact ⟨eq ▸ (projection_norm Dᗮ _).trans_lt (hsize t ht).1,(projection_norm Dᗮ _).trans_lt (hsize t ht).2⟩

theorem inherited_midpoint {p : E} {r : ℝ} {C : E → Cubic d} (hC : ContDiffOn ℝ ∞ C (ball p r))
    (hQ : MidpointJetEquations (ball p r) C) (hD : D=fixedDirections C (ball p r))
    (hpairs : ∀ y ∈ ball p r, ArbitrarilyShortComplementaryPairs C y) :
    LocalMidpointInvariance (ball (0:F) r) (field D C p) := by
  apply localMidpointInvariance_of_pairs isOpen_ball (smooth_field D hC)
  intro a ha ε hε
  let x := liftPoint D p a
  have hx : x ∈ ball p r := lift_mem D ha
  obtain ⟨s,hs,hsub⟩ := Metric.isOpen_iff.mp isOpen_ball x hx
  obtain ⟨δ,hδ,hpair⟩ := hpairs x hx (min s ε) (lt_min hs hε)
  refine ⟨δ,hδ,?_⟩
  intro b c hb hc
  have lift (y : F) (hy : y ∈ ball a δ) : liftPoint D p y ∈ ball x δ :=
    mem_ball.mpr ((lift_dist D p y a).trans_lt (mem_ball.mp hy))
  obtain ⟨γ,v,η,w,h₁,h₂,hm⟩ := hpair _ _ (lift b hb) (lift c hc)
  have short {σ : ℝ} {g z : ℝ → E} (h : IsShortGeodesic C σ x (min s ε) (liftPoint D p b) (liftPoint D p c) g z) :
      IsShortGeodesic (field D C p) σ a ε b c (fun t ↦ projection Dᗮ (g t-p)) (fun t ↦ projection Dᗮ (z t)) := by
    apply IsShortGeodesic.mono_radius (s := ε) (r := min s ε) _ (min_le_right _ _)
    apply projected_short D h
    intro t ht
    have hgt := (h.2.2.2 t ht).1.trans_le (min_le_left _ _)
    have hmem : g t ∈ ball p r := hsub (by simpa only [mem_ball,dist_eq_norm] using hgt)
    have hi (a : E) (ha : a ∈ D) (v : E) : K (C (g t)) a v ∈ D := by
      rw [hD] at ha ⊢
      exact fixed_product isOpen_ball (convex_ball _ _) hC hQ ha hmem v
    rw [project_product D hi,field,value_on_slice D hC hD.le hmem]
  refine ⟨_,_,_,_,short h₁,short h₂,?_⟩
  let P := projection Dᗮ
  change P (γ (1/2)-p)+P (η (1/2)-p)=b+c
  rw [← P.map_add,show γ (1/2)-p+(η (1/2)-p)=(γ (1/2)+η (1/2))-p-p by abel,hm]
  rw [show liftPoint D p b+liftPoint D p c-p-p=(liftPoint D p b-p)+(liftPoint D p c-p) by abel,
    P.map_add,project_lift,project_lift]

end EuclideanMidpointRigidity.OrthogonalFactor

