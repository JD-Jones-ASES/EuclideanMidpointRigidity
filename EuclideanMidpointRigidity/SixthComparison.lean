module

public import EuclideanMidpointRigidity.ForceRemainder
public import EuclideanMidpointRigidity.GeodesicEstimate
public import EuclideanMidpointRigidity.GeodesicDefinitions

/-! # Comparing a short geodesic with its sixth-order Dirichlet approximation -/

@[expose] public section
noncomputable section
open Set Metric
open scoped ContDiff
namespace EuclideanMidpointRigidity.Jet

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

attribute [local irreducible] displacement velocity acceleration signedPaths

theorem sixth_geodesic_comparison {Ω : Set E} {C : E → Coeff} (hΩ : IsOpen Ω)
    (hC : ContDiffOn ℝ ∞ C Ω) {p : E} (hp : p ∈ Ω) (z : E) {σ : ℚ} (hσ : σ=1 ∨ σ= -1)
    (r M L : ℝ) (hr : 0<r) (hM : 0≤M) (hL : 0≤L)
    (hbound : ∀ x ∈ ball p r, ‖C x‖ ≤ M)
    (hLip : ∀ x ∈ ball p r, ∀ y ∈ ball p r, ‖C x-C y‖ ≤ L*‖x-y‖)
    (hsmall : 8*L*r^2+16*M*r < 1/2) :
    let f := Tree.realize (fieldDerivatives C p) z
    ∃ δ T : ℝ, 0<δ ∧ 0≤T ∧ ∀ ε : ℝ, 0≤ε → ε<δ → ∀ γ v : ℝ → E,
      IsShortGeodesic C (σ:ℝ) p r (p-ε • z) (p+ε • z) γ v →
      ‖γ (1/2)-(p+displacement σ f ε 0)‖ ≤ T*ε^7 := by
  let f := Tree.realize (fieldDerivatives C p) z
  obtain ⟨δ,T,hδ,hT,herr⟩ := actual_residual hΩ hC hp hσ z
  obtain ⟨B,hB,hsize⟩ := trajectory_size σ f
  have hBpos : 0<B := by linarith
  refine ⟨min δ (min 1 (r/(2*B))),8*T,by positivity,by positivity,?_⟩
  intro ε hε hεsmall γ v hγ
  obtain ⟨hεδ,hmin⟩ := lt_min_iff.mp hεsmall
  obtain ⟨hε1,hεB⟩ := lt_min_iff.mp hmin
  have hεabs : |ε|≤1 := by simpa only [abs_of_nonneg hε] using hε1.le
  have hBr : 2*(B*ε)<r := by linarith only [(lt_div_iff₀ (by positivity : 0<2*B)).mp hεB]
  let τ := fun t : ℝ ↦ 2*t-1
  let y := fun t ↦ p+displacement σ f ε (τ t)
  let w := fun t ↦ (2:ℝ) • velocity σ f ε (τ t)
  let b := fun t ↦ (4:ℝ) • acceleration σ f ε (τ t)
  let Cs := fun x ↦ (σ:ℝ) • C x
  have hτ (t : ℝ) : HasDerivAt τ 2 t := by
    simpa [τ] using (((hasDerivAt_id t).const_mul (2:ℝ)).sub_const (1:ℝ))
  have hτmem (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : τ t ∈ Icc (-1:ℝ) 1 :=
    ⟨by dsimp [τ]; linarith [ht.1], by dsimp [τ]; linarith [ht.2]⟩
  have hy (t : ℝ) (_ : t ∈ Icc (0:ℝ) 1) : HasDerivAt y (w t) t := by
    simpa only [y,w,Function.comp_def] using
      (((hasDerivAt_displacement σ f ε (τ t)).scomp t (hτ t)).const_add p)
  have hw (t : ℝ) (_ : t ∈ Icc (0:ℝ) 1) : HasDerivAt w (b t) t := by
    simpa only [w,b,Function.comp_def,smul_smul,show (2:ℝ)*2=4 by norm_num] using
      (((hasDerivAt_velocity hσ f ε (τ t)).scomp t (hτ t)).fun_const_smul (2:ℝ))
  have hS (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      ‖displacement σ f ε (τ t)‖≤B*ε ∧ ‖velocity σ f ε (τ t)‖≤B*ε := by
    simpa only [abs_of_nonneg hε] using hsize ε (τ t) hεabs (hτmem t ht)
  have hyS (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : y t ∈ ball p r := by
    rw [mem_ball,dist_eq_norm]
    simpa only [y,add_sub_cancel_left] using (hS t ht).1.trans_lt
      (show B*ε<r by nlinarith [mul_nonneg hBpos.le hε])
  have hwS (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : ‖w t‖≤r := by
    simp only [w,norm_smul,Real.norm_ofNat]
    linarith [(hS t ht).2]
  have habs : |(σ:ℝ)|=1 := by rcases hσ with rfl|rfl <;> norm_num
  have hcM (x : E) (hx : x ∈ ball p r) : ‖Cs x‖≤M := by
    simpa only [Cs,norm_smul,Real.norm_eq_abs,habs,one_mul] using hbound x hx
  have hcL (x : E) (hx : x ∈ ball p r) (y : E) (hy : y ∈ ball p r) :
      ‖Cs x-Cs y‖ ≤ L*‖x-y‖ := by
    simpa only [Cs,← smul_sub,norm_smul,Real.norm_eq_abs,habs,one_mul] using hLip x hx y hy
  have hend := displacement_endpoints hσ f ε
  have hy0 : γ 0 = y 0 := by
    simpa [y,τ,hend.1,f,Tree.realize,sub_eq_add_neg] using hγ.2.1
  have hy1 : γ 1 = y 1 := by
    rw [show y 1=p+displacement σ f ε (τ 1) from rfl,show τ 1=1 by norm_num [τ],hend.2]
    exact hγ.2.2.1
  have hres (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      ‖b t+K (Cs (y t)) (w t) (w t)‖ ≤ (4*T)*ε^7 := by
    have he : b t+K (Cs (y t)) (w t) (w t) =
        (4:ℝ) • (acceleration σ f ε (τ t)+(σ:ℝ) •
          K (C (y t)) (velocity σ f ε (τ t)) (velocity σ f ε (τ t))) := by
      simp only [b,Cs,w,K_smul_coeff,K_smul_left,K_smul_right,smul_add,smul_smul]
      ring_nf
    rw [he,norm_smul,Real.norm_ofNat]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤4)
    dsimp only [y,f]
    exact herr ε (τ t) hε hεδ (hτmem t ht)
  have hc := geodesic_polynomial_comparison Cs (ball p r) M L r ((4*T)*ε^7)
    hM hL hr.le hcM hcL (by linarith) γ v y w b hγ.1.1
    (by simpa only [Cs,K_smul_coeff,neg_smul] using hγ.1.2) hy hw hy0 hy1
    (fun t ht ↦ (hγ.2.2.2 t ht).1) hyS (fun t ht ↦ (hγ.2.2.2 t ht).2.le) hwS hres
    (1/2) (by norm_num)
  have hmid : τ (1/2)=0 := by norm_num [τ]
  have hden : 0<1-8*L*r^2-16*M*r := by linarith
  have hR : 0≤4*T*ε^7 := by positivity
  have hmidBound := hc.1
  rw [show y (1/2)=p+displacement σ f ε 0 by simp only [y,hmid]] at hmidBound
  refine hmidBound.trans ((div_le_iff₀ hden).mpr ?_)
  nlinarith [mul_nonneg hR (show 0 ≤ (1-8*L*r^2-16*M*r)-(1/2) by linarith)]

end EuclideanMidpointRigidity.Jet
