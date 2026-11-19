module

public import EuclideanMidpointRigidity.EndpointFamily
public import EuclideanMidpointRigidity.MovingJets

/-! # The first two phase derivatives of the geodesic force -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d
local notation "H" => E × E
set_option backward.isDefEq.respectTransparency false

def firstForceJet (C : E → Cubic d) (σ : ℝ) (z u : H) : E :=
  -σ • (firstProduct C z.1 u.1 z.2 z.2+(2:ℝ) • K (C z.1) z.2 u.2)

def secondForceJet (C : E → Cubic d) (σ : ℝ) (z v u : H) : E :=
  -σ • (secondProduct C z.1 v.1 u.1 z.2 z.2+
    (2:ℝ) • firstProduct C z.1 u.1 z.2 v.2+
    (2:ℝ) • firstProduct C z.1 v.1 z.2 u.2+
    (2:ℝ) • K (C z.1) v.2 u.2)

theorem contDiffAt_geodesicForce {C : E → Cubic d} {z : H} (hC : ContDiffAt ℝ ∞ C z.1) (σ : ℝ) :
    ContDiffAt ℝ ∞ (geodesicForce C σ) z := by
  let inc : Cubic d →L[ℝ] (E →L[ℝ] E →L[ℝ] E) := (cubicSubspace d).subtypeL
  have hi := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) («E» := Cubic d) (F := E →L[ℝ] E →L[ℝ] E) inc
  have h : ContDiffAt ℝ ∞ (fun q : H ↦ inc (C q.1)) z := (hi.contDiffAt.comp z.1 hC).comp z contDiffAt_fst
  exact ((h.clm_apply contDiffAt_snd).clm_apply contDiffAt_snd).const_smul (-σ)

theorem fderiv_geodesicForce_apply {C : E → Cubic d} (σ : ℝ) (z u : H) (hC : ContDiffAt ℝ ∞ C z.1) :
    fderiv ℝ (geodesicForce C σ) z u=firstForceJet C σ z u := by
  let x := fun t : ℝ ↦ z.1+t • u.1
  let v := fun t : ℝ ↦ z.2+t • u.2
  let line := fun t ↦ (x t,v t)
  have hx : HasDerivAt x u.1 0 := by simpa [x] using ((hasDerivAt_id (0:ℝ)).smul_const u.1).const_add z.1
  have hv : HasDerivAt v u.2 0 := by simpa [v] using ((hasDerivAt_id (0:ℝ)).smul_const u.2).const_add z.2
  have hl : HasDerivAt line u 0 := hx.prodMk hv
  have h₀ : line 0=z := by simp [line,x,v]
  have hx₀ : x 0=z.1 := by simp [x]
  have hv₀ : v 0=z.2 := by simp [v]
  have dc := (hC.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hx hx₀.symm
  have df := ((contDiffAt_geodesicForce hC σ).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hl h₀.symm
  have h := df.unique ((hasDerivAt_K dc hv hv).fun_const_smul (-σ))
  simp only [Function.comp_apply,hx₀,hv₀,K_symm (C z.1) u.2 z.2] at h
  rw [h]
  unfold firstForceJet firstProduct
  module

theorem fderiv_geodesicForce_second {Ω : Set E} (hΩ : IsOpen Ω) {C : E → Cubic d}
    (hC : ContDiffOn ℝ ∞ C Ω) (σ : ℝ) (z v u : H) (hz : z.1 ∈ Ω) :
    fderiv ℝ (fderiv ℝ (geodesicForce C σ)) z v u=secondForceJet C σ z v u := by
  let x := fun t : ℝ ↦ z.1+t • v.1
  let w := fun t : ℝ ↦ z.2+t • v.2
  let line := fun t ↦ (x t,w t)
  have hx : HasDerivAt x v.1 0 := by simpa [x] using ((hasDerivAt_id (0:ℝ)).smul_const v.1).const_add z.1
  have hw : HasDerivAt w v.2 0 := by simpa [w] using ((hasDerivAt_id (0:ℝ)).smul_const v.2).const_add z.2
  have hl : HasDerivAt line v 0 := hx.prodMk hw
  have h₀ : line 0=z := by simp [line,x,w]
  have hx₀ : x 0=z.1 := by simp [x]
  have hw₀ : w 0=z.2 := by simp [w]
  have hn : ∀ᶠ t in 𝓝 (0:ℝ), x t ∈ Ω := hx.continuousAt (hx₀ ▸ hΩ.mem_nhds hz)
  have hc := hC.contDiffAt (hΩ.mem_nhds hz)
  have hD : ContDiffAt ℝ 1 (fderiv ℝ (geodesicForce C σ)) z := (contDiffAt_geodesicForce hc σ).fderiv_right (by simp)
  have dD := (hD.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hl h₀.symm
  have lhs := dD.clm_apply (hasDerivAt_const (0:ℝ) u)
  have dc := (hc.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hx hx₀.symm
  have d₁ := hasDerivAt_firstProduct C (hx₀ ▸ hc) hx (hasDerivAt_const (0:ℝ) u.1) hw hw
  have d₂ := hasDerivAt_K dc hw (hasDerivAt_const (0:ℝ) u.2)
  have rhs := (d₁.fun_add (d₂.fun_const_smul (2:ℝ))).fun_const_smul (-σ)
  have h := lhs.unique (rhs.congr_of_eventuallyEq (hn.mono fun t ht ↦ fderiv_geodesicForce_apply σ (line t) u (hC.contDiffAt (hΩ.mem_nhds ht))))
  simp only [Function.comp_apply,hx₀,hw₀,map_zero,add_zero] at h
  have hj₀ : firstProduct C z.1 0 z.2 z.2=0 := by simp [firstProduct,K]
  have hk₀ : K (C z.1) z.2 0=0 := by simp [K]
  rw [h,secondForceJet,hj₀,hk₀]
  simp only [firstProduct,add_zero,K_symm (fderiv ℝ C z.1 u.1) v.2 z.2]
  module

end EuclideanMidpointRigidity
