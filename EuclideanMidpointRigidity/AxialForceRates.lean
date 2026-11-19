module

public import EuclideanMidpointRigidity.AxisTransport
public import EuclideanMidpointRigidity.ResonantDerivative

/-! # The physical sixth-order force on a lifted section -/

@[expose] public section
noncomputable section
open Filter
open scoped Topology ContDiff InnerProductSpace
namespace EuclideanMidpointRigidity.LiftedSection
variable {d : ℕ} (S : LiftedSection d)
local notation "E" => Space d

def sectionU (p : E) := axisU S.field p (S.axis p)
def sectionV (p : E) := axisV S.field p (S.axis p)
def sectionY (p : E) := axisUDerivative (S.a p) S.field p (S.axis p)
def force (p : E) := axisMoment (S.a p) S.field p (S.axis p)

def forceSource (p : E) : E :=
  let U := S.sectionU p
  let V := S.sectionV p
  let Y := S.sectionY p
  let e := S.axis p
  let k := (2*S.a p)⁻¹
  (S.a p)^3 • U+(4:ℝ) • firstProduct S.field p V e e-(8:ℝ) • firstProduct S.field p e e V+
    (13:ℝ) • firstProduct S.field p Y e e-(11:ℝ) • firstProduct S.field p e e Y+
    (15*k) • firstProduct S.field p U e U-(11*k) • firstProduct S.field p e U U

def axisRay (p : E) (t : ℝ) := p+t • S.axis p

@[simp] theorem axisRay_zero (p : E) : S.axisRay p 0=p := by simp [axisRay]

theorem ray_rescale {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {p : E} {f : E → V} {v : V}
    (h : HasDerivAt (f ∘ S.axisRay p) v 0) : HasDerivAt (f ∘ S.axisLine p) ((S.a p/S.u p) • v) 0 := by
  let m := S.a p/S.u p
  have dt : HasDerivAt (fun z : ℝ ↦ m*z) m 0 := by simpa using (hasDerivAt_id' (0:ℝ)).const_mul m
  have hd := h.scomp_of_eq 0 dt (by simp)
  have heq : f ∘ S.axisLine p=(f ∘ S.axisRay p) ∘ (fun z : ℝ ↦ m*z) := by
    funext z
    simp only [Function.comp_apply,axisLine,axisRay,smul_smul,m,mul_comm z]
  rw [heq]
  exact hd

theorem ray_derivatives {p : E} (hp : p ∈ S.domain) :
    HasDerivAt (S.sectionU ∘ S.axisRay p) (S.sectionY p) 0 ∧
    DifferentiableAt ℝ (S.sectionV ∘ S.axisRay p) 0 ∧
    HasDerivAt ((fun q ↦ axisMoment (S.a p) S.field q (S.axis q)) ∘ S.axisRay p) (S.forceSource p) 0 := by
  let l := S.axisRay p
  let z := S.axis ∘ l
  have hl : l 0=p := S.axisRay_zero p
  have dz : z 0=S.axis p := by simp [z,hl]
  have dx : HasDerivAt l (S.axis p) 0 := by
    change HasDerivAt (fun t : ℝ ↦ p+t • S.axis p) _ _
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (S.axis p)).const_add p
  have he := (S.smoothAxis.contDiffAt (S.isOpen.mem_nhds hp)).differentiableAt (by simp)
  have de := he.hasFDerivAt.comp_hasDerivAt_of_eq 0 dx hl.symm
  rw [S.lift p hp] at de
  have dc : ContDiffAt ℝ ∞ S.field (l 0) := hl ▸ S.smooth.contDiffAt (S.isOpen.mem_nhds hp)
  have u := hasDerivAt_firstProduct S.field dc dx de de de
  have v := hasDerivAt_secondProduct S.field dc dx de de de de
  have dx' : HasDerivAt l (z 0) 0 := dz ▸ dx
  have de' : HasDerivAt z (liftStep (S.a p) (fderiv ℝ S.field (l 0)) (z 0)) 0 := by rw [hl,dz]; exact de
  have h := critical_axis_transport S.isOpen S.smooth S.equations l z (a := S.a p) (S.positive p hp).ne'
    (hl ▸ hp) (by rw [hl,dz]; exact S.critical p hp) dx' de'
  simp only [Function.comp_apply,hl] at u
  simp only [hl,dz] at h
  exact ⟨u,v.differentiableAt,h⟩

theorem force_derivative {p : E} (hp : p ∈ S.domain) :
    HasDerivAt (S.force ∘ S.axisLine p) ((S.a p/S.u p) • S.forceSource p) 0 := by
  obtain ⟨_,dv,hf⟩ := S.ray_derivatives hp
  have hF := S.ray_rescale hf
  have hV := S.ray_rescale (f := S.sectionV) dv.hasDerivAt
  have ha := (S.rate_a hp).sub_const (S.a p)
  have h := (ha.smul hV).fun_add hF
  simp only [Function.comp_apply,axisLine_zero,sub_self,zero_smul,add_zero,zero_add] at h
  convert h using 1
  funext t
  let q := S.axisLine p t
  let r := (13:ℝ) • firstProduct S.field q (S.sectionU q) (S.axis q) (S.axis q)
  let z := (11:ℝ) • firstProduct S.field q (S.axis q) (S.axis q) (S.sectionU q)
  change S.a q • S.sectionV q+r-z=(S.a q-S.a p) • S.sectionV q+(S.a p • S.sectionV q+r-z)
  module

end EuclideanMidpointRigidity.LiftedSection

