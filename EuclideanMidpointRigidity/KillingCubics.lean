module

public import EuclideanMidpointRigidity.HorizontalInvariants
public import EuclideanMidpointRigidity.SpatialProlongation
public import EuclideanMidpointRigidity.MaximumEnvelope

/-! # A Euclidean Killing cubic satisfying the midpoint quartic is constant -/

public section
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d

theorem polarize_killing_jet {J : E →L[ℝ] T} (he : ∀ v, directionProfile v (J v)=0) (h l : E) :
    directionProfile h (J l)+3*⟪l,K (J h) h h⟫_ℝ=0 := by
  let v := fun t : ℝ ↦ h+t • l
  have hv : HasDerivAt v l 0 := by simpa only [v,id_eq,one_smul] using ((hasDerivAt_id (0:ℝ)).smul_const l).const_add h
  have h₀ : v 0=h := by simp [v]
  have hd := Horizontal.hasDerivAt_profile (J.hasFDerivAt.comp_hasDerivAt 0 hv) hv
  have hz : HasDerivAt (fun t ↦ directionProfile (v t) (J (v t))) 0 0 :=
    (hasDerivAt_const 0 (0:ℝ)).congr_of_eventuallyEq (Eventually.of_forall fun t ↦ he (v t))
  simpa only [Function.comp_apply,h₀] using hd.unique hz

theorem killing_cubic_rigidity {W : Set E} {C : E → T} (hW : IsOpen W) (hC : ContDiffOn ℝ 2 C W)
    (hQ : QuarticOn W C) (hK : ∀ x ∈ W, ∀ h, directionProfile h (fderiv ℝ C x h)=0) {p : E} (hp : p ∈ W) :
    fderiv ℝ C p=0 := by
  let J := fderiv ℝ C
  let H := fderiv ℝ J p
  have hc := hC.contDiffAt (hW.mem_nhds hp)
  have hj : DifferentiableAt ℝ J p := (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hd (l h : E) : directionProfile h (H l h)=0 := by
    let L := (directionProfile h).comp (ContinuousLinearMap.apply ℝ T h)
    have hf : HasFDerivAt (L ∘ J) (L.comp H) p := L.hasFDerivAt.comp p hj.hasFDerivAt
    have he : (L ∘ J) =ᶠ[𝓝 p] (fun _ ↦ 0) :=
      (show ∀ᶠ x in 𝓝 p, x ∈ W from hW.mem_nhds hp).mono fun x hx ↦ hK x hx h
    have hz := hf.unique ((hasFDerivAt_const (0:ℝ) p).congr_of_eventuallyEq he)
    exact DFunLike.congr_fun hz l
  have hus (h : E) : K (J p h) h h=0 := by
    let q := K (C p) h h
    let u := K (J p h) h h
    have hH : H h q=H q h := (hc.isSymmSndFDerivAt (by norm_num)) h q
    have h₂ : directionProfile h (H h q)=0 := hH ▸ hd q h
    have dH := polarize_killing_jet (hd h) h q
    have dJ := polarize_killing_jet (hK p hp) h u
    have he := congrArg (fun z : E ↦ ⟪z,h⟫_ℝ) (prolongation_of_quartic hW hC hQ hp h h)
    simp only [inner_add_left,inner_zero_left,contract_obstruction] at he
    rw [← directionProfile_apply,← directionProfile_apply] at he
    change 5*directionProfile h (H h q)-2*⟪q,K (H h h) h h⟫_ℝ+
      (5*directionProfile h (J p u)-2*⟪u,u⟫_ℝ)=0 at he
    change directionProfile h (J p u)+3*⟪u,u⟫_ℝ=0 at dJ
    have hz : ⟪u,u⟫_ℝ=0 := by linarith only [h₂,dH,dJ,he]
    exact inner_self_eq_zero.mp hz
  ext l : 1
  apply (amplitude_eq_zero_iff _).mp
  obtain ⟨h,_,he,_⟩ := exists_maximizing_direction (J p l)
  rw [he]
  have hh := polarize_killing_jet (hK p hp) h l
  change directionProfile h (J p l)+3*⟪l,K (J p h) h h⟫_ℝ=0 at hh
  simpa only [hus,inner_zero_right,mul_zero,add_zero] using hh

end EuclideanMidpointRigidity

