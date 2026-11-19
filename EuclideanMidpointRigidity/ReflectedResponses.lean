module

public import EuclideanMidpointRigidity.ProjectedResponse
public import EuclideanMidpointRigidity.SmallRealizedChords

/-! # The two reflected scalar endpoint laws on a maximizing ruling -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff InnerProductSpace Topology
namespace EuclideanMidpointRigidity
open Endpoint
variable {d : ℕ}
local notation "E" => Space d

theorem translationSource_neg (C : E → Cubic d) (p u l w o : E) (s : ℝ) :
    translationSource C p (-u) l w o s=translationSource C p u l w o (-s) := by
  simp only [translationSource,secondProduct,smul_neg,neg_smul,K_neg_left,K_neg_right,neg_neg]

theorem tiltSource_neg (C : E → Cubic d) (p u l w o : E) (s : ℝ) :
    tiltSource C p (-u) l w o s= -tiltSource C p u l w o (-s) := by
  simp only [tiltSource,firstProduct,smul_neg,neg_smul,K_neg_left,inner_neg_right]

theorem OrientedEndpointChart.reflected_response {Ω : Set E} {C : E → Cubic d} {p u : E} {h : ℝ}
    {B : E →L[ℝ] E} (D : OrientedEndpointChart C p) (hΩ : IsOpen Ω) (hC : ContDiffOn ℝ ∞ C Ω)
    (hd : chordEnds p u h ∈ D.domain) (J : RealizedChord Ω C 1 p u h B D.plus)
    (L : RealizedChord Ω C (-1) p (-u) h B D.minus)
    (l w o : E) {b c : ℝ} (hw : B w=b • w) (ho : B o=c • o)
    (T R : ChordProfile (1-2*b)) (h₁ : R.value (-h)=T.value h) (h₂ : R.value h=T.value (-h)) :
    let Q := translationSource C p u l w o
    let P := tiltSource C p u l w o
    VanishingResponse (1-2*c) h (fun s ↦ -T.value s*Q s+R.value s*Q (-s)-
      2*(T.slope s*P s+R.slope s*P (-s))) := by
  obtain ⟨x,v,hx,ex⟩ := J.projected_response hΩ hC l w o hw ho T
  obtain ⟨y,z,hy,ey⟩ := L.projected_response hΩ hC l w o hw ho R
  refine ⟨fun s ↦ x s+y s,fun s ↦ v s+z s,?_,?_⟩
  · convert hx.add hy using 1
    funext s
    rw [translationSource_neg,tiltSource_neg]
    ring
  · change x _+y _=0
    rw [ex,ey,h₁,h₂,← chordEnds_swap,← inner_add_right]
    have he := D.mixed_variation_law hd (l,l) (T.value (-h) • w,T.value h • w)
    simp only [Prod.swap_prod_mk] at he
    rw [he,inner_zero_right]

def Endpoint.constantProfile (κ : ℝ) : ChordProfile κ where
  value := fun _ ↦ 1
  slope := fun _ ↦ 0
  first s := hasDerivAt_const s 1
  second s := by simpa only [mul_zero] using hasDerivAt_const s (0:ℝ)

/-- The two functions are actual zero-midpoint Dirichlet responses for every sufficiently
short chord, including when the scalar tilt rate vanishes. -/
theorem LiftedSection.eventually_reflected_responses (S : LiftedSection d) {p : E}
    (hp : p ∈ S.domain) (hm : ∀ q ∈ S.domain, S.Maximizes q) (D : OrientedEndpointChart S.field p)
    (l w o : E) {b c : ℝ} (hw : S.axisSlice p w=b • w) (ho : S.axisSlice p o=c • o) :
    let u := (S.a p)⁻¹ • S.axis p
    let Q := translationSource S.field p u l w o
    let P := tiltSource S.field p u l w o
    let κ := 1-2*b
    ∀ᶠ h in 𝓝[>] (0:ℝ), VanishingResponse (1-2*c) h (fun s ↦ -Q s+Q (-s)) ∧
      VanishingResponse (1-2*c) h (fun s ↦ -tiltValue κ h s*Q s+(1-tiltValue κ h s)*Q (-s)-
        2*(tiltFactor κ h*Real.exp (κ*s))*(P s-P (-s))) := by
  dsimp only
  filter_upwards [S.eventually_realized_chords hp hm D] with h ⟨hd,J,L⟩
  have hp₁ := D.reflected_response S.isOpen S.smooth hd J L l w o hw ho
    (constantProfile _) (constantProfile _) rfl rfl
  let T := rightTilt (1-2*b) h
  have hleft : T.value (-h)=0 := tiltValue_left _ _
  have hright : T.value h=1 := tiltValue_right _ J.positive
  have hp₂ := D.reflected_response S.isOpen S.smooth hd J L l w o hw ho T T.complement
    (by simp [ChordProfile.complement,hleft,hright]) (by simp [ChordProfile.complement,hleft,hright])
  refine ⟨?_,?_⟩
  · simpa only [constantProfile,neg_mul,one_mul,zero_mul,add_zero,sub_zero,mul_zero] using hp₁
  · convert hp₂ using 1
    funext s
    dsimp only [T,rightTilt,ChordProfile.complement]
    ring

end EuclideanMidpointRigidity

