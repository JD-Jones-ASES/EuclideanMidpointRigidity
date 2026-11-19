module

public import EuclideanMidpointRigidity.FactorCoordinates
public import EuclideanMidpointRigidity.FixedProducts

/-! # The field on the orthogonal complement of the fixed directions -/

@[expose] public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity.OrthogonalFactor
variable {d : ℕ} (D : Submodule ℝ (Space d))
local notation "E" => Space d
local notation "F" => Space (Module.finrank ℝ Dᗮ)
set_option backward.isDefEq.respectTransparency false

theorem residual_mem (v : E) : v-inclusion Dᗮ (projection Dᗮ v) ∈ D := by
  rw [inclusion_projection]
  have h := Dᗮ.sub_starProjection_mem_orthogonal v
  rwa [D.orthogonal_orthogonal] at h

theorem project_product {c : Cubic d} (hc : ∀ a ∈ D, ∀ b, K c a b ∈ D) (v w : E) :
    projection Dᗮ (K c v w)=K (restriction Dᗮ c) (projection Dᗮ v) (projection Dᗮ w) := by
  let I := inclusion Dᗮ
  let P := projection Dᗮ
  have left (a b : E) : P (K c a b)=P (K c (I (P a)) b) := by
    let m := a-I (P a)
    have hz : P (K c m b)=0 := projection_zero_of_orthogonal Dᗮ (D.orthogonal_orthogonal.symm ▸ hc m (residual_mem D a) b)
    calc
      _ = P (K c (m+I (P a)) b) := by dsimp [m]; rw [sub_add_cancel]
      _ = _ := by rw [K_add_left,map_add,hz,zero_add]
  rw [restriction_product]
  exact (left v w).trans ((congrArg P (K_symm c (I (P v)) w)).trans ((left w (I (P v))).trans (congrArg P (K_symm c _ _))))

theorem zero_of_restriction {j : Cubic d} (hj : ∀ a ∈ D, ∀ b, K j a b=0) (hr : restriction Dᗮ j=0) : j=0 := by
  have hi (v w : E) : K j v w ∈ Dᗮ := by
    rw [Submodule.mem_orthogonal]
    intro a ha
    rw [real_inner_comm,FixedAxis.inner_slot,hj a ha,inner_zero_left]
  apply Subtype.ext
  ext v w : 2
  change K j v w=0
  have h := project_product D (fun a ha b ↦ (hj a ha b).symm ▸ D.zero_mem) v w
  rw [hr] at h
  change projection Dᗮ (K j v w)=0 at h
  have he := congrArg (inclusion Dᗮ) h
  rw [inclusion_projection,map_zero] at he
  exact ((Dᗮ.starProjection_eq_self_iff.mpr (hi v w)).symm).trans he

def liftPoint (p : E) (a : F) := p+inclusion Dᗮ a

def field (C : E → Cubic d) (p : E) (a : F) := restriction Dᗮ (C (liftPoint D p a))

theorem lift_dist (p : E) (a b : F) : dist (liftPoint D p a) (liftPoint D p b)=dist a b := by
  simp only [liftPoint,dist_eq_norm,add_sub_add_left_eq_sub,← map_sub,inclusion_norm]

theorem lift_mem {p : E} {a : F} {r : ℝ} (ha : a ∈ ball 0 r) : liftPoint D p a ∈ ball p r := by
  simpa only [liftPoint,mem_ball,dist_eq_norm,add_sub_cancel_left,inclusion_norm,sub_zero] using ha

theorem smooth_field {p : E} {r : ℝ} {C : E → Cubic d} (hC : ContDiffOn ℝ ∞ C (ball p r)) :
    ContDiffOn ℝ ∞ (field D C p) (ball 0 r) :=
  (restriction Dᗮ).contDiff.comp_contDiffOn (hC.comp ((contDiff_const.add (inclusion Dᗮ).contDiff).contDiffOn) (fun _ h ↦ lift_mem D h))

theorem value_on_slice {p x : E} {r : ℝ} {C : E → Cubic d} (hC : ContDiffOn ℝ ∞ C (ball p r))
    (hD : D ≤ fixedDirections C (ball p r)) (hx : x ∈ ball p r) :
    C (liftPoint D p (projection Dᗮ (x-p)))=C x := by
  let a := projection Dᗮ (x-p)
  let y := liftPoint D p a
  let w := x-y
  have ha : a ∈ ball 0 r := by
    rw [mem_ball,dist_zero_right]
    exact (projection_norm Dᗮ _).trans_lt (by simpa only [mem_ball,dist_eq_norm] using hx)
  have hy : y ∈ ball p r := lift_mem D ha
  have hw : w ∈ D := by
    have h := residual_mem D (x-p)
    convert h using 1
    dsimp only [w,y,liftPoint,a]
    abel
  have hh : y+(1:ℝ) • w=x := by dsimp only [w]; rw [one_smul]; abel
  exact (hh ▸ stationary_segment isOpen_ball (convex_ball _ _) hC (fun z hz ↦ (hD hw z hz).1) hy (hh.symm ▸ hx)).symm

set_option maxHeartbeats 1200000 in
theorem stationary_of_constant_factor {p : E} {r : ℝ} (hr : 0<r) {C : E → Cubic d} (hC : ContDiffOn ℝ ∞ C (ball p r))
    (hD : D ≤ fixedDirections C (ball p r)) {c : Cubic (Module.finrank ℝ Dᗮ)} (hc : ∀ a ∈ ball 0 r, field D C p a=c) :
    fderiv ℝ C p=0 := by
  let I := inclusion Dᗮ
  let P := projection Dᗮ
  let J := fderiv ℝ C p
  have hp : p ∈ ball p r := mem_ball_self hr
  have h₀ : liftPoint D p (0:F)=p := by simp [liftPoint]
  have hd := ((hC.contDiffAt (isOpen_ball.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have dl : HasFDerivAt (liftPoint D p) I 0 := I.hasFDerivAt.const_add p
  have h₁ : HasFDerivAt ((restriction Dᗮ) ∘ C) ((restriction Dᗮ).comp J) (liftPoint D p 0) := by
    rw [h₀]; exact (restriction Dᗮ).hasFDerivAt.comp p hd
  have hF := h₁.comp 0 dl
  have he : field D C p =ᶠ[𝓝 0] (fun _ ↦ c) :=
    (show ∀ᶠ a in 𝓝 (0:F), a ∈ ball 0 r from ball_mem_nhds _ hr).mono hc
  change HasFDerivAt (field D C p) (((restriction Dᗮ).comp J).comp I) (0:F) at hF
  have hJ := hF.unique ((hasFDerivAt_const c (0:F)).congr_of_eventuallyEq he)
  ext v : 1
  apply zero_of_restriction D (fun a ha b ↦ (hD ha p hp).2 v b)
  have h := DFunLike.congr_fun hJ (P v)
  change restriction Dᗮ (J (I (P v)))=0 at h
  have hh : J (v-I (P v))=0 := (hD (residual_mem D v) p hp).1
  have pull : J v=J (I (P v)) := sub_eq_zero.mp ((J.map_sub v (I (P v))).symm.trans hh)
  change restriction Dᗮ (J v)=0
  rwa [pull]

end EuclideanMidpointRigidity.OrthogonalFactor

