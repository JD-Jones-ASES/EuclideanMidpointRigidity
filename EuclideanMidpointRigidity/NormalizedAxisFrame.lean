module

public import EuclideanMidpointRigidity.FixedAxisKilling
public import EuclideanMidpointRigidity.RulingFrame

/-! # The normalized maximizing direction supplies an idempotent with bounded spectrum -/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity.LiftedSection
variable {d : ℕ} (S : LiftedSection d)
local notation "E" => Space d

def idempotent (p : E) := (S.a p)⁻¹ • S.axis p

theorem idempotent_slice (p w : E) : K (S.field p) (S.idempotent p) w=S.axisSlice p w := by
  change K (S.field p) ((S.a p)⁻¹ • S.axis p) w=K ((S.a p)⁻¹ • S.field p) (S.axis p) w
  rw [K_smul_left,K_smul_coeff]

theorem idempotent_square {p : E} (hp : p ∈ S.domain) :
    K (S.field p) (S.idempotent p) (S.idempotent p)=S.idempotent p := by
  rw [S.idempotent_slice,idempotent,map_smul]
  change (S.a p)⁻¹ • K (S.cubic p) (S.axis p) (S.axis p)=(S.a p)⁻¹ • S.axis p
  rw [S.normalized_axis hp,one_smul]

theorem idempotent_frame {p : E} (hp : p ∈ S.domain) (hm : S.Maximizes p) :
    Nonempty (FixedAxis.SliceFrame (S.field p) (S.idempotent p)) := by
  obtain ⟨n,⟨F⟩⟩ := S.exists_ruling_frame hp hm
  refine ⟨n,F.basis,F.value,fun i ↦ (S.idempotent_slice p _).trans (F.eigen i),?_⟩
  intro i
  by_cases hi : i=F.axial
  · subst i
    have h := (F.eigen F.axial).symm
    rw [F.axis_eq] at h
    change F.value F.axial • S.axis p=K (S.cubic p) (S.axis p) (S.axis p) at h
    rw [S.normalized_axis hp] at h
    have hz : (F.value F.axial-1) • S.axis p=0 := by rw [sub_smul,h,sub_self]
    have hn : S.axis p≠0 := norm_ne_zero_iff.mp (by rw [S.unit p hp]; norm_num)
    exact (sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hn)).le
  · linarith [(F.bounds i hi).2]

end EuclideanMidpointRigidity.LiftedSection

