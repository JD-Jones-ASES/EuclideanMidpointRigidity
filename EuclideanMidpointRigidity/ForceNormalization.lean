module

public import EuclideanMidpointRigidity.AxialForceRates

/-! # Dimensionless form of the inhomogeneous vector equation -/

@[expose] public section
noncomputable section
open Filter
open scoped Topology ContDiff InnerProductSpace
namespace EuclideanMidpointRigidity.LiftedSection
variable {d : ℕ} (S : LiftedSection d)
local notation "E" => Space d

local instance (d : ℕ) : AddMonoid (Cubic d) :=
  (cubicNormedAddCommGroup d).toAddCommGroup.toAddCommMonoid.toAddMonoid

def rMap (p : E) : E →ₗ[ℝ] E where
  toFun l := K (S.jet p l) (S.axis p) (S.axis p)
  map_add' _ _ := by simp only [map_add,K_add_coeff]
  map_smul' _ _ := by simp only [map_smul,K_smul_coeff,RingHom.id_apply]

def zMap (p : E) : E →ₗ[ℝ] E := ((S.jet p (S.axis p)).val (S.axis p)).toLinearMap

def axialU (p : E) : E := (7/13:ℝ) • S.x p
def drift (p : E) : ℝ := S.rate S.u p/S.u p
def theta (p : E) : E := (7/13:ℝ) • (S.drift p • S.x p+S.rate S.x p)
def correction (p : E) : E := S.rMap p (S.axialU p)+(2:ℝ) • S.zMap p (S.axialU p)
def psi (p : E) : E := S.theta p-(12:ℝ) • S.zMap p (S.axialU p)+(25/2:ℝ) • S.rMap p (S.axialU p)
def forceTerm (p : E) : E :=
  (17:ℝ) • S.rMap p (S.theta p)-(19:ℝ) • S.zMap p (S.theta p)-
    (2:ℝ) • S.rMap p (S.correction p)+(4:ℝ) • S.zMap p (S.correction p)+
    ((7/13:ℝ)^2/2) • ((15:ℝ) • K (S.jet p (S.x p)) (S.axis p) (S.x p)-
      (11:ℝ) • K (S.jet p (S.axis p)) (S.x p) (S.x p))

theorem sectionU_eq {p : E} (hm : S.IsMixed p) : S.sectionU p=S.u p • S.axialU p := by
  change K (fderiv ℝ S.field p (S.axis p)) (S.axis p) (S.axis p)=_
  rw [S.axial_jet hm,axialU,smul_smul,mul_comm]

theorem sectionY_eq {p : E} (hm : S.IsMixed p) : S.sectionY p=((S.u p)^2/S.a p) • S.theta p := by
  have hu : S.u p≠0 := (norm_pos_iff.mpr hm.2.1).ne'
  have ha : S.a p≠0 := (S.positive _ hm.1).ne'
  obtain ⟨u,_,x,_⟩ := S.smooth_frame hm
  have dU := S.ray_rescale (S.ray_derivatives hm.1).1
  have du := S.along_axis_rate (u.differentiableAt (by simp))
  have dx := S.along_axis_rate (x.differentiableAt (by simp))
  have near : ∀ᶠ t in 𝓝 (0:ℝ), S.IsMixed (S.axisLine p t) :=
    (S.axisLine_derivative p).continuousAt (S.axisLine_zero p ▸ S.eventually_mixed hm)
  have eq : ∀ᶠ t in 𝓝 (0:ℝ), S.sectionU (S.axisLine p t)=
      (7/13:ℝ) • (S.u (S.axisLine p t) • S.x (S.axisLine p t)) := by
    filter_upwards [near] with t ht
    rw [S.sectionU_eq ht,axialU,smul_comm]
  have h := dU.unique (((du.smul dx).fun_const_smul (7/13:ℝ)).congr_of_eventuallyEq eq)
  simp only [Function.comp_apply,axisLine_zero] at h
  apply ext_inner_right ℝ
  intro w
  have hh := congrArg (fun v : E ↦ ⟪v,w⟫_ℝ) h
  simp only [theta,drift,real_inner_smul_left,inner_add_left] at hh ⊢
  linear_combination (norm := (field_simp [hu,ha]; ring)) (S.u p/S.a p)*hh

theorem first_scaled {p : E} (hm : S.IsMixed p) (z v w : E) :
    firstProduct S.field p z v w=S.u p • K (S.jet p z) v w := by
  have hu : S.u p≠0 := (norm_pos_iff.mpr hm.2.1).ne'
  simp only [firstProduct,jet,smul_apply,K_smul_coeff,smul_smul,mul_inv_cancel₀ hu,one_smul]

theorem first_r {p : E} (hm : S.IsMixed p) (z : E) :
    firstProduct S.field p z (S.axis p) (S.axis p)=S.u p • S.rMap p z := S.first_scaled hm _ _ _

theorem first_z {p : E} (hm : S.IsMixed p) (z : E) :
    firstProduct S.field p (S.axis p) (S.axis p) z=S.u p • S.zMap p z := S.first_scaled hm _ _ _

theorem sectionV_eq {p : E} (hm : S.IsMixed p) :
    S.sectionV p=((S.u p)^2/S.a p) • (S.theta p-(1/2:ℝ) • S.correction p) := by
  have ha : S.a p≠0 := (S.positive _ hm.1).ne'
  have step : liftStep (S.a p) (fderiv ℝ S.field p) (S.axis p)=(S.u p/(2*S.a p)) • S.axialU p := by
    change (2*S.a p)⁻¹ • S.sectionU p=_
    rw [S.sectionU_eq hm,smul_smul]
    congr 1
    ring
  have h : S.sectionY p=S.sectionV p+((S.u p)^2/(2*S.a p)) • S.correction p := by
    change axisUDerivative _ _ _ _=axisV _ _ _+_
    dsimp only [axisUDerivative]
    rw [step]
    simp only [S.first_scaled hm,map_smul,K_smul_coeff,K_smul_left,K_smul_right,
      K_symm (S.jet p (S.axis p)) (S.axialU p) (S.axis p)]
    change _=axisV _ _ _+_ • (K (S.jet p (S.axialU p)) (S.axis p) (S.axis p)+
      (2:ℝ) • K (S.jet p (S.axis p)) (S.axis p) (S.axialU p))
    apply ext_inner_right ℝ
    intro w
    simp only [inner_add_left,real_inner_smul_left]
    ring
  rw [S.sectionY_eq hm] at h
  apply ext_inner_right ℝ
  intro w
  have hh := congrArg (fun v : E ↦ ⟪v,w⟫_ℝ) h
  simp only [inner_add_left,inner_sub_left,real_inner_smul_left] at hh ⊢
  linear_combination (norm := (field_simp [ha]; ring)) -hh

theorem force_eq {p : E} (hm : S.IsMixed p) : S.force p=(S.u p)^2 • S.psi p := by
  have ha : S.a p≠0 := (S.positive _ hm.1).ne'
  change S.a p • S.sectionV p+(13:ℝ) • firstProduct S.field p (S.sectionU p) (S.axis p) (S.axis p)-
    (11:ℝ) • firstProduct S.field p (S.axis p) (S.axis p) (S.sectionU p)=_
  rw [S.sectionV_eq hm,S.first_r hm,S.first_z hm,S.sectionU_eq hm]
  apply ext_inner_right ℝ
  intro w
  simp only [correction,psi,map_smul,inner_add_left,inner_sub_left,real_inner_smul_left]
  field_simp [ha]
  ring

theorem forceSource_eq {p : E} (hm : S.IsMixed p) :
    (S.a p/S.u p) • S.forceSource p=(S.a p)^4 • S.axialU p+(S.u p)^2 • S.forceTerm p := by
  have hu : S.u p≠0 := (norm_pos_iff.mpr hm.2.1).ne'
  have ha : S.a p≠0 := (S.positive _ hm.1).ne'
  dsimp only [forceSource]
  simp only [S.first_r hm,S.first_z hm,S.sectionV_eq hm,S.sectionY_eq hm,S.sectionU_eq hm,map_smul,map_sub]
  simp only [S.first_scaled hm,axialU,map_smul,K_smul_coeff,K_smul_left,K_smul_right]
  apply ext_inner_right ℝ
  intro w
  simp only [forceTerm,axialU,inner_add_left,inner_sub_left,real_inner_smul_left]
  field_simp [ha,hu]
  ring

theorem normalized_force_rate {p : E} (hm : S.IsMixed p) :
    HasDerivAt (S.force ∘ S.axisLine p) ((S.a p)^4 • S.axialU p+(S.u p)^2 • S.forceTerm p) 0 := by
  rw [← S.forceSource_eq hm]
  exact S.force_derivative hm.1

end EuclideanMidpointRigidity.LiftedSection

