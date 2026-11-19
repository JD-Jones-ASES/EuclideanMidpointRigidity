module

public import EuclideanMidpointRigidity.ForceProfiles
public import EuclideanMidpointRigidity.HornerAmplitude
public import EuclideanMidpointRigidity.TensorBounds

/-! # The seventh-order acceleration residual for a smooth field -/

@[expose] public section
noncomputable section
open Set
open scoped ContDiff
namespace EuclideanMidpointRigidity.Jet

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

attribute [local irreducible] signedPaths forceIndices

theorem model_residual (σ : ℚ) (D : Derivatives d) (z : E) :
    let f := Tree.realize D z
    ∃ T : ℝ, 0≤T ∧ ∀ ε t : ℝ, |ε|≤1 → t ∈ Icc (-1:ℝ) 1 →
      ‖acceleration σ f ε t + (σ:ℝ) • K (taylorModel D 4 (displacement σ f ε t))
        (velocity σ f ε t) (velocity σ f ε t)‖ ≤ T*|ε|^7 := by
  let f := Tree.realize D z
  let paths := signedPaths σ
  let F := fun (a : ℕ × List ℕ) (t : ℝ) ↦
    forceValue σ D (positionCoefficient paths f t) (velocityCoefficient paths f t) a
  obtain ⟨T,hT,hb⟩ := uniform_remainder_after_collection (forceIndices 6 4) forceDegree F
    (isCompact_Icc (a := (-1:ℝ)) (b := 1)) 6 (fun _ ha ↦ (continuous_forceValue σ paths D z ha).continuousOn)
  refine ⟨T,hT,?_⟩
  intro ε t hε ht
  have hlow : (∑ k ∈ Finset.range 7, ε^k • degreeCoefficient (forceIndices 6 4) forceDegree
      (fun a ↦ F a t) k) = acceleration σ f ε t := by
    rw [acceleration,amplitudeSum_eq_range _ _ _ (show value (forcing σ paths 0) f t=0 from rfl)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [forcing_value σ paths k (by have := Finset.mem_range.mp hk; omega) D z t]
  have hfull : (-(σ:ℝ)) • K (taylorModel D 4 (displacement σ f ε t)) (velocity σ f ε t) (velocity σ f ε t)
      = ((forceIndices 6 4).map fun a ↦ ε^(forceDegree a) • F a t).sum := by
    dsimp only [displacement,velocity,F,paths]
    exact full_force_expansion σ D _ _ 6 4 ε
  have h := hb ε t hε ht
  rw [← hfull,hlow,norm_sub_rev,neg_smul,sub_neg_eq_add] at h
  dsimp only [f] at h
  rw [show (6:ℕ)+1=7 by decide] at h
  exact h

private theorem force_error (c a : Coeff) (x v : E) (η B ε : ℝ)
    (hη : 0≤η) (hB : 0≤B) (hε : 0≤ε) (hc : ‖c-a‖ ≤ η*‖x‖^5)
    (hx : ‖x‖≤B*ε) (hv : ‖v‖≤B*ε) :
    ‖K c v v-K a v v‖ ≤ 8*η*B^7*ε^7 := by
  rw [← K_sub_coeff]
  calc
    _ ≤ 8*‖c-a‖*‖v‖*‖v‖ := norm_K_le _ _ _
    _ ≤ 8*(η*(B*ε)^5)*(B*ε)*(B*ε) := by
      gcongr
      exact hc.trans (by gcongr)
    _ = _ := by ring

theorem actual_residual {Ω : Set E} {C : E → Coeff} (hΩ : IsOpen Ω) (hC : ContDiffOn ℝ ∞ C Ω)
    {p : E} (hp : p ∈ Ω) {σ : ℚ} (hσ : σ=1 ∨ σ= -1) (z : E) :
    let f := Tree.realize (fieldDerivatives C p) z
    ∃ δ T : ℝ, 0<δ ∧ 0≤T ∧ ∀ ε t : ℝ, 0≤ε → ε<δ → t ∈ Icc (-1:ℝ) 1 →
      ‖acceleration σ f ε t + (σ:ℝ) • K (C (p+displacement σ f ε t))
        (velocity σ f ε t) (velocity σ f ε t)‖ ≤ T*ε^7 := by
  let D := fieldDerivatives C p
  let f := Tree.realize D z
  obtain ⟨ρ,η,hρ,hη,hTaylor⟩ := exists_spatialTaylor_bound hΩ hC hp 4
  obtain ⟨B,hB,hsize⟩ := trajectory_size σ f
  have hBpos : 0<B := by linarith
  obtain ⟨T,hT,hmodel⟩ := model_residual σ D z
  refine ⟨min 1 (ρ/B),T+8*η*B^7,by positivity,by positivity,?_⟩
  intro ε t hε hδ ht
  have hε1 : |ε|≤1 := by rw [abs_of_nonneg hε]; exact (lt_min_iff.mp hδ).1.le
  obtain ⟨hx,hv⟩ := hsize ε t hε1 ht
  rw [abs_of_nonneg hε] at hx hv
  let x := displacement σ f ε t
  let v := velocity σ f ε t
  let b := acceleration σ f ε t
  let a := taylorModel D 4 x
  have hxρ : ‖x‖<ρ := hx.trans_lt (by simpa [mul_comm] using (lt_div_iff₀ hBpos).mp (lt_min_iff.mp hδ).2)
  have hc : ‖C (p+x)-a‖≤η*‖x‖^5 := by simpa [a,D,taylorModel_field] using hTaylor x hxρ
  have hdiff := force_error (C (p+x)) a x v η B ε hη hBpos.le hε hc hx hv
  have habs : |(σ:ℝ)|=1 := by rcases hσ with rfl|rfl <;> norm_num
  have hlow : ‖b+(σ:ℝ) • K a v v‖≤T*ε^7 := by
    dsimp only [b,a,x,v,f]
    have h := hmodel ε t hε1 ht
    rw [abs_of_nonneg hε] at h
    exact h
  change ‖b+(σ:ℝ) • K (C (p+x)) v v‖ ≤ _
  rw [show b+(σ:ℝ) • K (C (p+x)) v v =
      (b+(σ:ℝ) • K a v v)+(σ:ℝ) • (K (C (p+x)) v v-K a v v) by rw [smul_sub]; abel]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul,Real.norm_eq_abs,habs,one_mul,add_mul]
  exact add_le_add hlow hdiff

end EuclideanMidpointRigidity.Jet
