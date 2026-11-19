module

public import EuclideanMidpointRigidity.ReflectedResponses
public import EuclideanMidpointRigidity.AxialRates
public import EuclideanMidpointRigidity.CubicPolynomial

/-! # The reflected equations at every center of a fixed maximizing line -/

@[expose] public section
noncomputable section
open Set Filter Metric
open scoped ContDiff InnerProductSpace Topology
namespace EuclideanMidpointRigidity
open Endpoint
variable {d : ℕ}
local notation "E" => Space d

def Endpoint.reflectedTilt (κ h : ℝ) (Q P : ℝ → ℝ) (p s : ℝ) :=
  -tiltValue κ h s*Q (p+s)+(1-tiltValue κ h s)*Q (p-s)-
    2*(tiltFactor κ h*Real.exp (κ*s))*(P (p+s)-P (p-s))

structure RulingResponseLaws (W : Set ℝ) (η κ : ℝ) (Q P : ℝ → ℝ) : Prop where
  smoothQ : ContDiffOn ℝ ∞ Q W
  smoothP : ContDiffOn ℝ ∞ P W
  translation : ∀ p ∈ W, ∀ᶠ h in 𝓝[>] (0:ℝ), VanishingResponse η h (oddTilt 0 Q p)
  tilt : ∀ p ∈ W, ∀ᶠ h in 𝓝[>] (0:ℝ), VanishingResponse η h (reflectedTilt κ h Q P p)

theorem RulingResponseLaws.translation_equation {W : Set ℝ} {η κ : ℝ} {Q P : ℝ → ℝ}
    (H : RulingResponseLaws W η κ Q P) (hW : IsOpen W) :
    ∀ x ∈ W, iteratedDeriv 3 Q x=iteratedDeriv 1 Q x := by
  simpa only [tiltRate,zero_pow (by decide : 2≠0),mul_zero,add_zero,zero_add,one_mul] using
    oddTilt_differential_equation hW H.smoothQ H.translation

theorem LiftedSection.ruling_responses (S : LiftedSection d) {p : E} (hp : p ∈ S.domain)
    (hm : ∀ q ∈ S.domain, S.Maximizes q) (hc : ∀ q ∈ S.domain, Nonempty (OrientedEndpointChart S.field q)) :
    let u := (S.a p)⁻¹ • S.axis p
    ∃ W : Set ℝ, IsOpen W ∧ 0 ∈ W ∧ ∀ (l w o : E) (b c : ℝ),
      S.axisSlice p w=b • w → S.axisSlice p o=c • o →
      RulingResponseLaws W (1-2*c) (1-2*b) (translationSource S.field p u l w o) (tiltSource S.field p u l w o) := by
  let u := (S.a p)⁻¹ • S.axis p
  let line := displacementLine p u
  obtain ⟨U,δ,_,hpU,hδ,hr⟩ := S.local_straight_rulings hp hm
  let W := (fun t : ℝ ↦ t*(S.a p)⁻¹) ⁻¹' ball 0 δ
  have hW : IsOpen W := isOpen_ball.preimage (continuous_id.mul continuous_const)
  have h₀ : 0 ∈ W := by simpa only [W,mem_preimage,zero_mul,mem_ball,dist_self] using hδ
  have hline : ContDiff ℝ ∞ line := by change ContDiff ℝ ∞ (fun t : ℝ ↦ p+t • u); fun_prop
  have rul (t : ℝ) (ht : t ∈ W) : line t ∈ S.domain ∧ S.axis (line t)=S.axis p ∧
      S.axisSlice (line t)=S.axisSlice p ∧ S.a (line t)=S.a p := by
    simpa only [line,u,displacementLine,smul_smul] using hr p hpU (t*(S.a p)⁻¹) ht
  have maps : MapsTo line W S.domain := fun t ht ↦ (rul t ht).1
  refine ⟨W,hW,h₀,?_⟩
  intro l w o b c hw ho
  have hJ : ContDiffOn ℝ ∞ (fderiv ℝ S.field) S.domain := S.smooth.fderiv_of_isOpen S.isOpen (by simp)
  have hK : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ S.field)) S.domain := hJ.fderiv_of_isOpen S.isOpen (by simp)
  have hQ := contDiffOn_cubic_entry ((hK.clm_apply (g := fun _ ↦ w) contDiffOn_const).clm_apply (g := fun _ ↦ l) contDiffOn_const) u u o
  have hP := contDiffOn_cubic_entry (hJ.clm_apply (g := fun _ ↦ l) contDiffOn_const) u w o
  have hsources (t : ℝ) (ht : t ∈ W) :
      ∀ᶠ h in 𝓝[>] (0:ℝ), VanishingResponse (1-2*c) h (oddTilt 0 (translationSource S.field p u l w o) t) ∧
        VanishingResponse (1-2*c) h (reflectedTilt (1-2*b) h (translationSource S.field p u l w o) (tiltSource S.field p u l w o) t) := by
    obtain ⟨htd,he,hB,ha⟩ := rul t ht
    obtain ⟨D⟩ := hc _ htd
    have e := S.eventually_reflected_responses htd hm D l w o (hB ▸ hw) (hB ▸ ho)
    dsimp only at e
    rw [ha,he] at e
    rw [show (S.a p)⁻¹ • S.axis p=u from rfl] at e
    have hl (s : ℝ) : line t+s • u=p+(t+s) • u := by simp [line,displacementLine,add_smul,add_assoc]
    filter_upwards [e] with h ⟨e₁,e₂⟩
    constructor
    · apply (e₁.smul (-1)).congr
      intro s _
      simp only [oddTilt,zero_mul,Real.exp_zero,one_mul,translationSource,hl,sub_eq_add_neg]
      ring
    · apply e₂.congr
      intro s _
      simp only [reflectedTilt,translationSource,tiltSource,hl,sub_eq_add_neg]
  refine ⟨?_,?_,fun t ht ↦ (hsources t ht).mono fun _ e ↦ e.1,fun t ht ↦ (hsources t ht).mono fun _ e ↦ e.2⟩
  · change ContDiffOn ℝ ∞ (fun x ↦ ⟪o,K (fderiv ℝ (fderiv ℝ S.field) (line x) w l) u u⟫_ℝ) W
    simpa only [Function.comp_def,real_inner_comm o] using hQ.comp hline.contDiffOn maps
  · change ContDiffOn ℝ ∞ (fun x ↦ ⟪o,K (fderiv ℝ S.field (line x) l) u w⟫_ℝ) W
    simpa only [Function.comp_def,real_inner_comm o] using hP.comp hline.contDiffOn maps

end EuclideanMidpointRigidity

