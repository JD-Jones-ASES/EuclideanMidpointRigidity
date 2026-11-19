module

public import EuclideanMidpointRigidity.ChannelGeometry
public import EuclideanMidpointRigidity.ExternalEigenbasis
public import EuclideanMidpointRigidity.MaximumSpectrum
public import EuclideanMidpointRigidity.MixedNorm

/-! # A pointwise spectral basis extending the two gradient directions -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity.LiftedSection

variable {d : ℕ}
local notation "E" => Space d

structure SpectralFrame (S : LiftedSection d) (p : E) (ι : Type*) [Fintype ι] where
  basis : OrthonormalBasis (Fin 3 ⊕ ι) ℝ E
  value : ι → ℝ
  internal : ∀ i, basis (.inl i)=![S.axis p,S.x p,S.y p] i
  external : ∀ i, K (S.cubic p) (S.axis p) (basis (.inr i))=value i • basis (.inr i)

theorem exists_spectral_frame (S : LiftedSection d) {p : E} (hm : S.IsMixed p) :
    ∃ n : ℕ, Nonempty (SpectralFrame S p (Fin n)) := by
  let f : Fin 3 → E := ![S.axis p,S.x p,S.y p]
  let T : E →ₗ[ℝ] E := ((S.cubic p).val (S.axis p)).toLinearMap
  have hT : T.IsSymmetric := K_selfAdjoint _ _
  obtain ⟨hx,hy,hxy,hex,hey,_,_,_⟩ := S.plane_data hm
  have hf : Orthonormal ℝ f := by
    simp [f,orthonormal_vecCons_iff,Fin.forall_fin_succ,hx,hy,hxy,hex,hey,S.unit _ hm.1]
  let a : Fin 3 → ℝ := ![1,-1/2,1/5]
  have he (i : Fin 3) : T (f i)=a i • f i := by
    fin_cases i
    · exact S.normalized_axis hm.1
    · exact S.normalized_eigenvector hm.1 (S.eigenvectors hm.1).1
    · exact S.normalized_eigenvector hm.1 (S.eigenvectors hm.1).2
  obtain ⟨n,B,s,h₁,h₂⟩ := extend_orthonormal_eigenvectors T hT f a hf he
  exact ⟨n,⟨B,s,h₁,h₂⟩⟩

namespace SpectralFrame
variable {S : LiftedSection d} {p : Space d}
variable {ι : Type*} [Fintype ι]
variable (B : SpectralFrame S p ι)

def w (i : ι) := B.basis (.inr i)

theorem orthonormal : Orthonormal ℝ (Sum.elim ![S.axis p,S.x p,S.y p] B.w) := by
  have h : Sum.elim ![S.axis p,S.x p,S.y p] B.w=⇑B.basis := by
    funext i
    cases i with
    | inl i => exact (B.internal i).symm
    | inr i => rfl
  rw [h]
  exact B.basis.orthonormal

theorem transverse (i : ι) :
    ‖B.w i‖=1 ∧ ⟪S.axis p,B.w i⟫_ℝ=0 ∧ ⟪S.x p,B.w i⟫_ℝ=0 ∧ ⟪S.y p,B.w i⟫_ℝ=0 := by
  have h (j : Fin 3) := B.orthonormal.inner_eq_zero (i := Sum.inl j) (j := Sum.inr i) (by simp)
  exact ⟨B.basis.orthonormal.norm_eq_one (.inr i),h 0,h 1,h 2⟩

theorem physical_eigenvalue (hp : p ∈ S.domain) (i : ι) :
    K (S.field p) (S.axis p) (B.w i)=(B.value i*S.a p) • B.w i := by
  have ha : S.a p≠0 := (S.positive p hp).ne'
  have hD : S.field p=S.a p • S.cubic p := by simp [cubic,smul_smul,ha]
  rw [hD,K_smul_coeff,show K (S.cubic p) (S.axis p) (B.w i)=_ from B.external i,smul_smul,mul_comm]
  rfl

theorem channel_equations (hm : S.IsMixed p) (i : ι) : (S.channel p (B.w i)).Equations (B.value i) :=
  S.channel_equations hm (B.physical_eigenvalue hm.1 i) (B.transverse i).2.2.1 (B.transverse i).2.2.2

theorem value_bounds (hm : S.IsMixed p) (hmax : ∀ z : E, ‖z‖=1 → ⟪K (S.field p) z z,z⟫_ℝ≤S.a p) (i : ι) :
    -1≤B.value i ∧ B.value i≤1/2 := by
  obtain ⟨hn,he,_,_⟩ := B.transverse i
  have ha : 0<S.a p := S.positive p hm.1
  have h := maximizing_axis_spectral_bounds ha.le hmax (S.unit p hm.1) hn he
    (show ⟪K (S.field p) (S.axis p) (S.axis p),S.axis p⟫_ℝ=S.a p from rfl)
  rw [B.physical_eigenvalue hm.1 i,real_inner_smul_left,real_inner_self_eq_norm_sq,hn] at h
  constructor
  · apply le_of_mul_le_mul_right (a := S.a p) _ ha
    linarith only [h.1]
  · apply le_of_mul_le_mul_right (a := S.a p) _ ha
    linarith only [h.2]

theorem norm_inequality (hm : S.IsMixed p) (hmax : ∀ z : E, ‖z‖=1 → ⟪K (S.field p) z z,z⟫_ℝ≤S.a p)
    (α β : ℝ) :
    let t := S.ratio p
    let r := t^2
    let n := ⟪S.x p,K (S.cubic p) (S.y p) (S.y p)⟫_ℝ
    let P := (650/153)*ResonantPlane.k*α^2-2*ResonantPlane.k*α*β+β^2
    let J := -ResonantPlane.k*α^2+2*α*β-(159/1300)*β^2
    let ch := fun i ↦ S.channel p (B.w i)
    (∑ i, (α^2*(ch i).q+2*α*β*(ch i).l+β^2*(ch i).h)^2)+(r*P^2+J^2)*(r*n^2) ≤
      (3/4)*α^4+(11/5)*r*α^2*β^2+(24/25)*r^2*β^4 := by
  obtain ⟨_,_,_,_,_,low,six,_⟩ := S.plane_data hm
  have hu : 0<S.u p := norm_pos_iff.mpr hm.2.1
  have hv : 0<S.v p := norm_pos_iff.mpr hm.2.2
  have hr : S.v p=S.ratio p*S.u p := by simp [ratio,div_mul_cancel₀ _ hu.ne']
  have ha : 0<S.a p := S.positive p hm.1
  have hd (z : E) (hz : ‖z‖=1) : ⟪K (S.cubic p) z z,z⟫_ℝ≤1 := by
    rw [cubic,K_smul_coeff,real_inner_smul_left,← div_eq_inv_mul]
    exact (div_le_one ha).mpr (hmax z hz)
  obtain ⟨h₁,h₂,h₃⟩ := ResonantPlane.ratio_coordinates low six hu hv hr
  exact mixed_norm_inequality B.w B.orthonormal hd
    (S.normalized_eigenvector hm.1 (S.eigenvectors hm.1).1) (S.normalized_eigenvector hm.1 (S.eigenvectors hm.1).2)
    h₁ h₂ rfl h₃ α β

end SpectralFrame
end EuclideanMidpointRigidity.LiftedSection
