module

public import EuclideanMidpointRigidity.RulingCoefficients
public import EuclideanMidpointRigidity.SpectralTrace

/-! # An orthonormal pointwise eigenbasis with its maximizing direction distinguished -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity.LiftedSection
variable {d : ℕ}
local notation "E" => Space d

structure RulingFrame (S : LiftedSection d) (p : E) (ι : Type*) [Fintype ι] where
  basis : OrthonormalBasis ι ℝ E
  axial : ι
  value : ι → ℝ
  axis_eq : basis axial=S.axis p
  eigen : ∀ i, S.axisSlice p (basis i)=value i • basis i
  bounds : ∀ i, i≠axial → -1≤value i ∧ value i≤1/2

theorem exists_ruling_frame (S : LiftedSection d) {p : E} (hp : p ∈ S.domain) (hm : S.Maximizes p) :
    ∃ n : ℕ, Nonempty (RulingFrame S p (Unit ⊕ Fin n)) := by
  let f : Unit → E := fun _ ↦ S.axis p
  let a : Unit → ℝ := fun _ ↦ 1
  have hon : Orthonormal ℝ f := by
    apply orthonormal_iff_ite.mpr
    intro i j
    cases i; cases j
    simp [f,S.unit p hp]
  have he (i : Unit) : (S.axisSlice p).toLinearMap (f i)=a i • f i := S.normalized_axis hp
  obtain ⟨n,B,s,hi,ho⟩ := extend_orthonormal_eigenvectors (S.axisSlice p).toLinearMap (K_selfAdjoint _ _) f a hon he
  let eig : Unit ⊕ Fin n → ℝ := Sum.elim a s
  have ha := S.positive p hp
  have hmax (w : E) (hw : ‖w‖=1) : ⟪K (S.cubic p) w w,w⟫_ℝ≤1 := by
    rw [cubic,K_smul_coeff,real_inner_smul_left]
    calc
      _ ≤ (S.a p)⁻¹*S.a p := mul_le_mul_of_nonneg_left (hm w hw) (inv_nonneg.mpr ha.le)
      _ = 1 := inv_mul_cancel₀ ha.ne'
  have hax : ⟪K (S.cubic p) (S.axis p) (S.axis p),S.axis p⟫_ℝ=1 := by
    rw [S.normalized_axis hp,one_smul,real_inner_self_eq_norm_sq,S.unit p hp,one_pow]
  refine ⟨n,⟨B,.inl (),eig,hi (),?_,?_⟩⟩
  · rintro (i|i)
    · rw [hi]; exact S.normalized_axis hp
    · exact ho i
  · rintro (i|i) hne
    · cases i; exact (hne rfl).elim
    · have hw := B.orthonormal.norm_eq_one (.inr i)
      have horth : ⟪S.axis p,B (.inr i)⟫_ℝ=0 := by
        rw [← show B (.inl ())=S.axis p from hi ()]
        exact B.orthonormal.inner_eq_zero (by simp)
      have h := maximizing_axis_spectral_bounds (by norm_num : (0:ℝ)≤1) hmax (S.unit p hp) hw horth hax
      have heig : K (S.cubic p) (S.axis p) (B (.inr i))=s i • B (.inr i) := ho i
      change -1≤s i ∧ s i≤1/2
      simpa only [heig,real_inner_smul_left,real_inner_self_eq_norm_sq,hw,one_pow,mul_one] using h

namespace RulingFrame
variable {S : LiftedSection d} {p : Space d} {ι : Type*} [Fintype ι] (F : RulingFrame S p ι)

def slope := operatorEntry F.basis (fderiv ℝ S.axis p)
def rate := operatorEntry F.basis (S.sliceRate p)

theorem symm_rate (i j : ι) : F.rate i j=F.rate j i := by
  change ⟪F.basis i,K _ _ (F.basis j)⟫_ℝ=⟪F.basis j,K _ _ (F.basis i)⟫_ℝ
  rw [← K_selfAdjoint,real_inner_comm]

theorem pair_equations (hp : p ∈ S.domain) (hm : ∀ q ∈ S.domain, S.Maximizes q) (i j : ι) :
    LowPair (F.value i) (F.value j) ((1-2*F.value i)*F.slope i j) ((1-2*F.value j)*F.slope j i) (F.rate i j) :=
  S.ruling_low_pair hp hm _ _ (F.eigen i) (F.eigen j)

theorem axial_entries (hp : p ∈ S.domain) (hm : ∀ q ∈ S.domain, S.Maximizes q) (i : ι) :
    F.slope F.axial i=0 ∧ F.slope i F.axial=0 ∧ F.rate i F.axial=0 := by
  constructor
  · change ⟪F.basis F.axial,fderiv ℝ S.axis p (F.basis i)⟫_ℝ=0
    rw [F.axis_eq,real_inner_comm]; exact S.axis_derivative_transverse hp _
  constructor
  · change ⟪F.basis i,fderiv ℝ S.axis p (F.basis F.axial)⟫_ℝ=0
    rw [F.axis_eq,S.straight_axis hp hm,inner_zero_right]
  · change ⟪F.basis i,K (S.normalizedJet p (S.axis p)) (S.axis p) (F.basis F.axial)⟫_ℝ=0
    rw [F.axis_eq,S.normalizedJet_axial hp hm,inner_zero_right]

theorem weighted_diagonal_zero (hp : p ∈ S.domain) (hm : ∀ q ∈ S.domain, S.Maximizes q) (i : ι) :
    traceWeight (F.value i)*F.slope i i=0 := by
  by_cases hi : i=F.axial
  · subst i; rw [(F.axial_entries hp hm F.axial).1,mul_zero]
  · exact (F.pair_equations hp hm i i).trace_diagonal (F.bounds i hi).1 (F.bounds i hi).2

theorem pair_sign (hp : p ∈ S.domain) (hm : ∀ q ∈ S.domain, S.Maximizes q) (i j : ι) :
    let t := tracePair (F.value i) (F.value j) (F.slope i j) (F.slope j i) (F.rate i j)
    0≤t ∧ (t=0 → (1-2*F.value i)*F.slope i j=0 ∧ (1-2*F.value j)*F.slope j i=0 ∧ F.rate i j=0) := by
  dsimp only
  by_cases hi : i=F.axial
  · subst i
    obtain ⟨h₁,h₂,h₃⟩ := F.axial_entries hp hm j
    rw [F.symm_rate F.axial j,h₁,h₂,h₃]
    simp [tracePair]
  by_cases hj : j=F.axial
  · subst j
    obtain ⟨h₁,h₂,h₃⟩ := F.axial_entries hp hm i
    rw [h₁,h₂,h₃]
    simp [tracePair]
  exact (F.pair_equations hp hm i j).trace_pair (F.bounds i hi).1 (F.bounds j hj).1
    (F.bounds i hi).2 (F.bounds j hj).2

end RulingFrame
end EuclideanMidpointRigidity.LiftedSection

