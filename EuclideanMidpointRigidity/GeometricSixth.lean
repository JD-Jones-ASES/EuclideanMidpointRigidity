module

public import EuclideanMidpointRigidity.SixthComparison
public import EuclideanMidpointRigidity.CanonicalMidpoints
public import EuclideanMidpointRigidity.LocalBounds

/-! # The sixth-order obstruction for the actual canonical midpoint maps -/

@[expose] public section
noncomputable section
open Set Metric
open scoped ContDiff
namespace EuclideanMidpointRigidity
open Jet

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

theorem sixth_obstruction_of_short_complementary_pairs {Ω : Set E} {C : E → Coeff}
    (hΩ : IsOpen Ω) (hC : ContDiffOn ℝ ∞ C Ω) {p : E} (hp : p ∈ Ω)
    (hpairs : ArbitrarilyShortComplementaryPairs C p) (z : E) :
    let f := Tree.realize (fieldDerivatives C p) z
    value affineSixth f 0 + value higherSixth f 0 = 0 := by
  let f := Tree.realize (fieldDerivatives C p) z
  let X := fun i ↦ positionCoefficient (signedPaths 1) f 0 i +
    positionCoefficient (signedPaths (-1)) f 0 i
  change value affineSixth f 0 + value higherSixth f 0 = 0
  rw [← summed_sixth_midpoint]
  change X 6=0
  have h0 : X 0=0 := by change (0:E)+0=0; exact add_zero _
  obtain ⟨r,hr,M,hM,L,hL,_,hbound,hLip,hsmall⟩ :=
    local_coefficient_bounds hΩ hp (hC.of_le (by simp))
  obtain ⟨δ₁,T₁,hδ₁,hT₁,hPlus⟩ := sixth_geodesic_comparison hΩ hC hp z
    (σ := 1) (Or.inl rfl) r M L hr hM hL hbound hLip hsmall
  obtain ⟨δ₂,T₂,hδ₂,hT₂,hMinus⟩ := sixth_geodesic_comparison hΩ hC hp z
    (σ := -1) (Or.inr rfl) r M L hr hM hL hbound hLip hsmall
  obtain ⟨ρ,hρ,hpairs'⟩ := hpairs r hr
  let δ := min δ₁ (min δ₂ (ρ/(‖z‖+1)))
  have hδ : 0<δ := by dsimp [δ]; positivity
  apply last_coefficient_zero 6 X h0 (M := T₁+T₂) hδ
  intro ε hε hεδ
  obtain ⟨hε₁,hεrest⟩ := lt_min_iff.mp hεδ
  obtain ⟨hε₂,hεend⟩ := lt_min_iff.mp hεrest
  have hz : ε*‖z‖<ρ := by
    nlinarith only [(lt_div_iff₀ (by positivity : 0<‖z‖+1)).mp hεend,hε]
  have hP : p-ε • z ∈ ball p ρ := by
    rwa [mem_ball,dist_eq_norm,show p-ε • z-p = -(ε • z) by abel,
      norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos hε]
  have hQ : p+ε • z ∈ ball p ρ := by
    rwa [mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hε]
  obtain ⟨γ,v,η,w,hγ,hη,hcomp⟩ := hpairs' _ _ hP hQ
  let x := displacement 1 f ε 0
  let y := displacement (-1) f ε 0
  have hx : ‖γ (1/2)-(p+x)‖≤T₁*ε^7 :=
    hPlus ε hε.le hε₁ γ v (by simpa only [Rat.cast_one] using hγ)
  have hy : ‖η (1/2)-(p+y)‖≤T₂*ε^7 :=
    hMinus ε hε.le hε₂ η w (by simpa only [Rat.cast_neg,Rat.cast_one] using hη)
  have hxy : amplitudeSum 6 ε X = x+y :=
    amplitudeSum_add 6 ε (positionCoefficient (signedPaths 1) f 0)
      (positionCoefficient (signedPaths (-1)) f 0)
  have hsum : γ (1/2)+η (1/2)=p+p := by rw [hcomp]; abel
  have hdef : x+y = (p+x-γ (1/2))+(p+y-η (1/2)) := by
    calc
      _ = (p+x)+(p+y)-(p+p) := by abel
      _ = _ := by rw [← hsum]; abel
  rw [hxy,hdef,add_mul]
  exact (norm_add_le _ _).trans (add_le_add
    (by simpa only [norm_sub_rev] using hx) (by simpa only [norm_sub_rev] using hy))

/-- The sum of all twenty-seven terms vanishes at every interior point in
every direction. The two parts are evaluated at the same spatial jet. -/
theorem sixth_obstruction_of_localMidpointInvariance {Ω : Set E} {C : E → Coeff}
    (hΩ : IsOpen Ω) (hC : ContDiffOn ℝ ∞ C Ω) (hm : LocalMidpointInvariance Ω C)
    {p : E} (hp : p ∈ Ω) (z : E) :
    let f := Tree.realize (fieldDerivatives C p) z
    value affineSixth f 0 + value higherSixth f 0 = 0 :=
  sixth_obstruction_of_short_complementary_pairs hΩ hC hp
    (localMidpointInvariance_arbitrarilyShort hΩ hp (hC.of_le (by simp)) hm) z

end EuclideanMidpointRigidity
