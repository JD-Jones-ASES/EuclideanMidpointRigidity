module

public import EuclideanMidpointRigidity.HorizontalQuartic
public import EuclideanMidpointRigidity.MaximumEnvelope
public import EuclideanMidpointRigidity.LocalFlow

/-! # The smooth phase-space vector field preserving the maximizing value -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity.Horizontal
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d
local notation "Op" => E →L[ℝ] E
set_option backward.isDefEq.respectTransparency false

private theorem smooth_K {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {W : Set Y} {c : Y → T} {h u : Y → E}
    (hc : ContDiffOn ℝ ∞ c W) (hh : ContDiffOn ℝ ∞ h W) (hu : ContDiffOn ℝ ∞ u W) :
    ContDiffOn ℝ ∞ (fun q ↦ K (c q) (h q) (u q)) W := by
  let inc : T →L[ℝ] (E →L[ℝ] Op) := (cubicSubspace d).subtypeL
  have hi := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) («E» := T) (F := E →L[ℝ] Op) inc
  have hs := ContDiff.comp_contDiffOn («E» := Y) (F := T) (G := E →L[ℝ] Op) hi hc
  exact (hs.clm_apply hh).clm_apply hu

private theorem smooth_spatialSlice {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {W : Set Y}
    {J : Y → (E →L[ℝ] T)} {h : Y → E} (hj : ContDiffOn ℝ ∞ J W) (hh : ContDiffOn ℝ ∞ h W) :
    ContDiffOn ℝ ∞ (fun q ↦ spatialSlice (J q) (h q)) W := by
  let B := EuclideanSpace.basisFun (Fin d) ℝ
  let F := fun (i : Fin d) (q : Y) ↦ (innerSL ℝ (B i)).smulRight (K (J q (B i)) (h q) (h q))
  have hs (i : Fin d) : ContDiffOn ℝ ∞ (F i) W := contDiffOn_const.smulRight (smooth_K (hj.clm_apply contDiffOn_const) hh hh)
  apply (ContDiffOn.sum (s := Finset.univ) (fun i _ ↦ hs i)).congr
  intro q _
  apply ContinuousLinearMap.ext
  intro v
  let A := spatialSlice (J q) (h q)
  change A v=(∑ i, F i q) v
  calc
    A v = ∑ i, ⟪B i,v⟫_ℝ • A (B i) := by
      conv_lhs => rw [← B.sum_repr' v]
      simp only [map_sum,map_smul]
    _ = _ := by simp only [F,sum_apply,ContinuousLinearMap.smulRight_apply,innerSL_apply_apply]; rfl

def phaseVector (C : E → T) (l : E) (q : E × E) : E × E :=
  let c := C q.1
  let h := q.2
  let a := directionProfile h c
  let g := correction c (fderiv ℝ C q.1) h a l
  (transport c h a l, (-1/3:ℝ) • (⟪h,h⟫_ℝ • g-⟪h,g⟫_ℝ • h))

theorem smooth_phaseVector {Ω : Set E} {C : E → T} (hΩ : IsOpen Ω) (hC : ContDiffOn ℝ ∞ C Ω) (l : E) :
    ContDiffOn ℝ ∞ (phaseVector C l) (Ω ×ˢ (univ : Set E)) := by
  let D := Ω ×ˢ (univ : Set E)
  let c := fun q : E × E ↦ C q.1
  let h := (Prod.snd : E × E → E)
  let a := fun q : E × E ↦ directionProfile (h q) (c q)
  let J := fun q : E × E ↦ fderiv ℝ C q.1
  have hp : MapsTo (Prod.fst : E × E → E) D Ω := fun _ H ↦ H.1
  have hc : ContDiffOn ℝ ∞ c D := hC.comp contDiffOn_fst hp
  have hh : ContDiffOn ℝ ∞ h D := contDiffOn_snd
  have hj : ContDiffOn ℝ ∞ J D := (hC.fderiv_of_isOpen hΩ (by simp)).comp contDiffOn_fst hp
  have ha : ContDiffOn ℝ ∞ a D := by simp only [a,directionProfile_apply]; exact (smooth_K hc hh hh).inner ℝ hh
  let v := fun q ↦ doubleShift (c q) (h q) (a q) l
  let w := fun q ↦ elevenShift (c q) (h q) (a q) l
  have hb := smooth_K hc hh (contDiffOn_const (c := l))
  have hv : ContDiffOn ℝ ∞ v D := ((contDiffOn_const (c := (2:ℝ))).smul hb).add (ha.smul contDiffOn_const)
  have hw : ContDiffOn ℝ ∞ w D := (((contDiffOn_const (c := (11:ℝ))).mul ha).smul contDiffOn_const).sub ((contDiffOn_const (c := (4:ℝ))).smul hb)
  have hx : ContDiffOn ℝ ∞ (fun q ↦ transport (c q) (h q) (a q) l) D :=
    ((contDiffOn_const (c := (10:ℝ))).smul (smooth_K hc hh hv)).sub (((contDiffOn_const (c := (2:ℝ))).mul ha).smul hv)
  let g := fun q ↦ correction (c q) (J q) (h q) (a q) l
  have hadj : ContDiffOn ℝ ∞ (fun q ↦ (spatialSlice (J q) (h q)).adjoint) D :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) («E» := E) (F := E)).toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp_contDiffOn (smooth_spatialSlice hj hh)
  have hg : ContDiffOn ℝ ∞ g D := (((hadj.clm_apply (((contDiffOn_const (c := (5:ℝ))).smul hw).sub ((contDiffOn_const (c := (15:ℝ))).smul hv))).sub
    ((contDiffOn_const (c := (4:ℝ))).smul (smooth_K (hj.clm_apply hh) hh hw))).add
    ((contDiffOn_const (c := (2:ℝ))).smul (smooth_K (hj.clm_apply hv) hh hh))).add
    ((contDiffOn_const (c := (4:ℝ))).smul (smooth_K (hj.clm_apply hh) hh hv))
  exact hx.prodMk ((contDiffOn_const (c := (-1/3:ℝ))).smul (((hh.inner ℝ hh).smul hg).sub ((hh.inner ℝ hg).smul hh)))

theorem tangent (C : E → T) (l : E) (q : E × E) : ⟪q.2,(phaseVector C l q).2⟫_ℝ=0 := by
  dsimp only [phaseVector]
  simp only [real_inner_smul_right,inner_sub_right]
  ring

theorem profile_rate {C : E → T} (l : E) (q : E × E) (hu : ‖q.2‖=1)
    (hQ : ∀ w, obstruction (C q.1) (fderiv ℝ C q.1) w=0) :
    let v := phaseVector C l q
    directionProfile q.2 (fderiv ℝ C q.1 v.1)+3*⟪v.2,K (C q.1) q.2 q.2⟫_ℝ=0 := by
  let h := q.2
  let c := C q.1
  let a := directionProfile h c
  let g := correction c (fderiv ℝ C q.1) h a l
  have he := transport_identity hQ h a l
  dsimp only
  rw [directionProfile_apply]
  change ⟪K (fderiv ℝ C q.1 (transport c h a l)) h h,h⟫_ℝ+3*⟪(-1/3:ℝ) • (⟪h,h⟫_ℝ • g-⟪h,g⟫_ℝ • h),K c h h⟫_ℝ=0
  rw [he]
  change ⟪K c h h-a • h,g⟫_ℝ+3*⟪(-1/3:ℝ) • (⟪h,h⟫_ℝ • g-⟪h,g⟫_ℝ • h),K c h h⟫_ℝ=0
  simp only [inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq,show ‖h‖=1 from hu,one_pow,one_mul]
  rw [real_inner_comm (K c h h) g,real_inner_comm (K c h h) h]
  dsimp only [a]
  rw [directionProfile_apply]
  ring

theorem correction_of_zero {c : T} {J : E →L[ℝ] T} {h : E} (hJ : J h=0) (hh : ∀ v, K (J v) h h=0) (a : ℝ) (l : E) :
    correction c J h a l=0 := by
  have he : spatialSlice J h=0 := by ext v : 1; exact hh v
  have h₀ (v : E) : K (0:T) h v=0 := rfl
  simp only [correction,he,map_zero,hJ,hh,h₀,zero_apply,smul_zero,sub_self,zero_add]

end EuclideanMidpointRigidity.Horizontal

