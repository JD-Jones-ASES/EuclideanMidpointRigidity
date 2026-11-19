module

public import EuclideanMidpointRigidity.CriticalSection
public import EuclideanMidpointRigidity.MovingJets
public import EuclideanMidpointRigidity.Resonances

/-! # Differentiating the two persistent critical-axis identities -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

theorem section_jet_transport {Ω : Set E} {C : E → Coeff} {e : E → E} (hΩ : IsOpen Ω)
    (hC : ContDiffOn ℝ ∞ C Ω) (he : ContDiffOn ℝ ∞ e Ω) (hm : QuarticOn Ω C)
    (hunit : ∀ x ∈ Ω, ‖e x‖=1) (hc : ∀ x ∈ Ω, K (C x) (e x) (e x)=sectionValue C e x • e x)
    (ha : ∀ x ∈ Ω, sectionValue C e x≠0) {p : E} (hp : p ∈ Ω) :
    let A := sectionValue C e
    let z := e p
    let q := fderiv ℝ e p z
    let U := firstProduct C p z z z
    let Y := secondProduct C p z z z z + firstProduct C p q z z +
      firstProduct C p z q z + firstProduct C p z z q
    7*(fderiv ℝ (fderiv ℝ A) p z U + fderiv ℝ A p Y) = 26*⟪U,Y⟫_ℝ ∧
      (2:ℝ) • (firstProduct C p z z U + K (C p) q U + K (C p) z Y) + A p • Y=0 := by
  let A := sectionValue C e
  let z := e p
  let q := fderiv ℝ e p z
  let U := fun x ↦ firstProduct C x (e x) (e x) (e x)
  let Y := secondProduct C p z z z z + firstProduct C p q z z +
    firstProduct C p z q z + firstProduct C p z z q
  let line := fun t : ℝ ↦ p+t • z
  have h₀ : line 0=p := by simp [line]
  have hd : HasDerivAt line z 0 := by simpa [line] using ((hasDerivAt_id (0:ℝ)).smul_const z).const_add p
  have hnear : ∀ᶠ t in 𝓝 (0:ℝ), line t ∈ Ω := hd.continuousAt (h₀ ▸ hΩ.mem_nhds hp)
  have hCp := hC.contDiffAt (hΩ.mem_nhds hp)
  have hA : ContDiffAt ℝ ∞ A p := (contDiffOn_sectionValue hC he).contDiffAt (hΩ.mem_nhds hp)
  have hD : ContDiffAt ℝ 1 (fderiv ℝ A) p := hA.fderiv_right (by simp)
  have dC := (hCp.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hd h₀.symm
  have de : HasDerivAt (e ∘ line) q 0 :=
    ((he.contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hd h₀.symm
  have dU : HasDerivAt (U ∘ line) Y 0 := by
    simpa only [U,Y,z,Function.comp_def,h₀] using hasDerivAt_firstProduct C (h₀ ▸ hCp) hd de de de
  have dD := (hD.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hd h₀.symm
  have dA : HasDerivAt (A ∘ line) 0 0 := by
    have h := (hA.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hd h₀.symm
    rwa [critical_section_value_along_axis hΩ hC he hm hunit hp (ha p hp) (hc p hp)] at h
  have hE (x : E) (hx : x ∈ Ω) := hm hx
  have hsrc (x : E) (hx : x ∈ Ω) : 7*(fderiv ℝ A x (U x))=13*⟪U x,U x⟫_ℝ := by
    rw [← inner_gradient_left,sectionValue_gradient hΩ hC he hunit hx (hc x hx)]
    exact critical_axis_source (ha x hx) (hc x hx) (hE x hx)
  have hsym : ⟪Y,U p⟫_ℝ=⟪U p,Y⟫_ℝ := real_inner_comm _ _
  have d₁ := (dD.clm_apply dU).const_mul 7
  have d₂ := (dU.inner ℝ dU).const_mul 13
  have hs := d₁.unique (d₂.congr_of_eventuallyEq (hnear.mono fun t ht ↦ hsrc (line t) ht))
  simp only [Function.comp_apply,h₀,hsym] at hs
  have d₃ := (hasDerivAt_K dC de dU).fun_const_smul (2:ℝ)
  have d₄ := dA.smul dU
  have hzero : HasDerivAt (fun t ↦ (2:ℝ) • K (C (line t)) (e (line t)) (U (line t)) +
      A (line t) • U (line t)) 0 0 := (hasDerivAt_const 0 (0:E)).congr_of_eventuallyEq
      (hnear.mono fun t ht ↦ critical_axis_eigenrelation (hc _ ht) (hE _ ht _))
  have hv := (d₃.fun_add d₄).unique hzero
  simp only [Function.comp_apply,h₀,zero_smul,add_zero,zero_add] at hv
  exact ⟨by linarith only [hs],hv⟩

end EuclideanMidpointRigidity
