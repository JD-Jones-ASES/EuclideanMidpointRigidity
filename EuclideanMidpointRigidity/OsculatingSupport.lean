module

public import EuclideanMidpointRigidity.FlatProduct
public import EuclideanMidpointRigidity.InactiveSlope
public import EuclideanMidpointRigidity.FrozenPairs

/-! # Spectral support of the first possibly active derivative of the direction field -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d

theorem directions.two {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {W : Set X} {f : X → Y} (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    {p : X} (hp : p ∈ W) (w v : X) (xs : List X) :
    directions f (w::v::xs) p=fderiv ℝ (fderiv ℝ (directions f xs)) p w v := by
  let L := ContinuousLinearMap.apply ℝ Y v
  have hg := (directions.smooth hW hf xs).contDiffAt (hW.mem_nhds hp)
  have hd := L.hasFDerivAt.comp p ((hg.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  exact DFunLike.congr_fun hd.fderiv w

namespace HorizontalPatch
variable {S : LiftedSection d} (H : HorizontalPatch S)

def InactiveThrough (S : LiftedSection d) (n : ℕ) := ∀ xs : List E, xs.length≤n →
  ∀ q ∈ S.domain, fderiv ℝ S.field q (directions S.axis xs q)=0

include H in
theorem inactive_one : InactiveThrough S 1 := by
  intro xs hx q hq
  rcases xs with _|⟨v,xs⟩
  · exact S.stationary_field_along_axis H.maximizes H.charts hq
  · have h₀ : xs=[] := List.length_eq_zero_iff.mp (by simpa using hx)
    subst xs; exact H.inactive_slope hq v

private theorem smooth_transport (S : LiftedSection d) (w : E) :
    ContDiffOn ℝ ∞ (fun q ↦ Horizontal.transport (S.field q) (S.axis q) (S.a q) w) S.domain := by
  let L : T →L[ℝ] (E →L[ℝ] E →L[ℝ] E) := (cubicSubspace d).subtypeL
  have hK {v : E → E} (hv : ContDiffOn ℝ ∞ v S.domain) :
      ContDiffOn ℝ ∞ (fun q ↦ K (S.field q) (S.axis q) (v q)) S.domain :=
    by
      have hi := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) («E» := T) (F := E →L[ℝ] E →L[ℝ] E) L
      have hs := ContDiff.comp_contDiffOn («E» := E) (F := T) (G := E →L[ℝ] E →L[ℝ] E) hi S.smooth
      exact (hs.clm_apply S.smoothAxis).clm_apply hv
  have ha : ContDiffOn ℝ ∞ S.a S.domain := contDiffOn_sectionValue S.smooth S.smoothAxis
  have hv : ContDiffOn ℝ ∞ (fun q ↦ Horizontal.doubleShift (S.field q) (S.axis q) (S.a q) w) S.domain :=
    ((contDiffOn_const (c := (2:ℝ))).smul (hK contDiffOn_const)).add (ha.smul contDiffOn_const)
  exact ((contDiffOn_const (c := (10:ℝ))).smul (hK hv)).sub (((contDiffOn_const (c := (2:ℝ))).mul ha).smul hv)

private theorem differentiated_slope {S : LiftedSection d} (J : E →L[ℝ] T) (xs : List E) {p : E}
    (hp : p ∈ S.domain) (v : E) :
    directions (fun y ↦ J.comp (fderiv ℝ S.axis y)) xs p v=J (directions S.axis (xs++[v]) p) := by
  let A := fun y ↦ J.comp (fderiv ℝ S.axis y)
  have hA : ContDiffOn ℝ ∞ A S.domain := contDiffOn_const.clm_comp (S.smoothAxis.fderiv_of_isOpen S.isOpen (by simp))
  let L := ContinuousLinearMap.apply ℝ T v
  have h₁ := directions.linear_map S.isOpen hA L xs hp
  have h₂ := directions.linear_map S.isOpen (directions.smooth S.isOpen S.smoothAxis [v]) J xs hp
  rw [directions.append]
  exact h₁.symm.trans h₂

include H in
theorem osculating_support {p : E} (hp : p ∈ S.domain) (xs : List E)
    (hI : InactiveThrough S xs.length) {v : E} {b : ℝ}
    (he : K (S.field p) (S.idempotent p) v=b • v) (hn : ¬ FixedAxis.Resonant b) :
    fderiv ℝ S.field p (directions S.axis (xs++[v]) p)=0 := by
  let J := fderiv ℝ S.field p
  let A := fun y ↦ J.comp (fderiv ℝ S.axis y)
  let V := fun y ↦ Horizontal.transport (S.field y) (S.axis y) (S.a y) v
  have hA : ContDiffOn ℝ ∞ A S.domain := contDiffOn_const.clm_comp (S.smoothAxis.fderiv_of_isOpen S.isOpen (by simp))
  have hl (ys : List E) (hy : ys.length<xs.length) : directions A ys p=0 := by
    ext w : 1
    rw [differentiated_slope J ys hp w]
    exact hI _ (by simpa using hy) p hp
  have hz : (fun y ↦ A y (V y)) =ᶠ[𝓝 p] (fun _ ↦ 0) :=
    (show ∀ᶠ y in 𝓝 p, y ∈ S.domain from S.isOpen.mem_nhds hp).mono fun y hy ↦ by
      change J (fderiv ℝ S.axis y (V y))=0
      rw [show fderiv ℝ S.axis y (V y)=0 from H.horizontal y hy v,map_zero]
  have hh := directions.leading_apply S.isOpen hp xs hA (smooth_transport S v) hl
  rw [(directions.congr_germ hz xs).eq_of_nhds,directions.zero] at hh
  have ha : 0<S.a p := S.positive p hp
  have he' : K (S.field p) (S.axis p) v=(S.a p*b) • v := by
    rw [LiftedSection.idempotent,K_smul_left] at he
    have h := congrArg (fun z : E ↦ S.a p • z) he
    simpa only [smul_smul,mul_inv_cancel₀ ha.ne',one_smul] using h
  have hs : (2*(S.a p*b)+S.a p)*(10*(S.a p*b)-2*S.a p)≠0 := by
    have hb₁ : 2*b+1≠0 := fun h ↦ hn (Or.inl (by linarith))
    have hb₂ : 10*b-2≠0 := fun h ↦ hn (Or.inr (by linarith))
    have h := mul_ne_zero (mul_ne_zero ha.ne' hb₁) (mul_ne_zero ha.ne' hb₂)
    convert h using 1 <;> ring
  change 0=directions A xs p (Horizontal.transport (S.field p) (S.axis p) (S.a p) v) at hh
  rw [Horizontal.transport_eigen he',map_smul] at hh
  exact (differentiated_slope J xs hp v).symm.trans ((smul_eq_zero.mp hh.symm).resolve_left hs)

end HorizontalPatch
end EuclideanMidpointRigidity

