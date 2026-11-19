module

public import EuclideanMidpointRigidity.CertificatePullback

/-! # Exclusion of a mixed gradient at a lifted spherical maximum -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity.LiftedSection
open Spectral IntervalPolynomial

variable {d : ℕ}
local notation "E" => Space d
namespace SpectralFrame
variable {S : LiftedSection d} {p : Space d}
variable {ι : Type*} [Fintype ι]
variable (B : SpectralFrame S p ι)

def observations : ChannelData ι :=
  ⟨B.value,fun j ↦ S.channel p (B.w j),(S.ratio p)^2,(S.ratio p)^2*(S.core p).n^2,
    ForceAxis.negative.source (S.a p) (S.u p)/ForceRows.scale .negative⟩

theorem quartic_residual (hm : S.IsMixed p) (i : Fin 4) : (PhysicalRow.quartic i).residual B.observations=0 := by
  have h := QuarticRows.geometric_row hm B i
  dsimp only at h
  simp only [show (S.core p).t=S.ratio p from rfl] at h
  simp only [PhysicalRow.residual,observations,PhysicalRow.quartic,Rat.cast_zero,zero_mul,sub_zero]
  linear_combination h

theorem derivative_residual (hm : S.IsMixed p) (i : Fin 3) : (PhysicalRow.differentiated i).residual B.observations=0 := by
  have h := DerivativeRows.geometric_row hm B i
  dsimp only at h
  simp only [show (S.core p).t=S.ratio p from rfl] at h
  simp only [PhysicalRow.residual,observations,PhysicalRow.differentiated,Rat.cast_zero,zero_mul,sub_zero]
  linear_combination h

theorem force_residual (hm : S.IsMixed p) (i : ForceAxis) : (PhysicalRow.force i).residual B.observations=0 := by
  have h := ForceRows.geometric_row hm B i
  dsimp only at h
  cases i <;> simp only [PhysicalRow.residual,observations,PhysicalRow.force,ForceAxis.source,ForceAxis.pick,
    Rat.cast_zero,Rat.cast_one,zero_mul,one_mul,zero_div,add_zero,sub_zero] at h ⊢ <;> linear_combination h

theorem physical_residuals (hm : S.IsMixed p) (a : PhysicalRow) (ha : a ∈ PhysicalRow.physical) :
    a.residual B.observations=0 := by
  simp only [PhysicalRow.physical,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with h|h|h|h|h|h|h|h|h <;> subst a
  · exact B.quartic_residual hm 0
  · exact B.quartic_residual hm 1
  · exact B.quartic_residual hm 2
  · exact B.quartic_residual hm 3
  · exact B.derivative_residual hm 0
  · exact B.derivative_residual hm 1
  · exact B.derivative_residual hm 2
  · exact B.force_residual hm .positive
  · exact B.force_residual hm .negative

theorem test_residual (hm : S.IsMixed p) (hmax : ∀ z : E, ‖z‖=1 → ⟪K (S.field p) z z,z⟫_ℝ≤S.a p)
    (T : NormTest) (ht : 0<T.x^2+T.z^2) : (PhysicalRow.test T).residual B.observations≤0 := by
  have h := NormTest.geometric_bound hm hmax B T ht
  change (∑ j, T.raw (S.channel p (B.w j)))+eval T.row.internal ((S.ratio p)^2)*((S.ratio p)^2*(S.n p)^2)≤_ at h
  rw [← S.shape_n p] at h
  change (∑ j, T.raw (S.channel p (B.w j)))+eval T.row.internal ((S.ratio p)^2)*((S.ratio p)^2*(S.core p).n^2)≤_ at h
  simp only [PhysicalRow.residual,PhysicalRow.test,observations,Rat.cast_zero,zero_mul,sub_zero]
  linear_combination h

end SpectralFrame

/-- A smooth, positive unit critical section following the critical lift
cannot have both resonant gradient components nonzero at a spherical maximum. -/
theorem not_mixed_at_maximum (S : LiftedSection d) {p : E}
    (hmax : ∀ z : E, ‖z‖=1 → ⟪K (S.field p) z z,z⟫_ℝ≤S.a p) : ¬ S.IsMixed p := by
  intro hm
  obtain ⟨n,⟨B⟩⟩ := S.exists_spectral_frame hm
  let D := B.observations
  have hr : 0≤D.ratioSq := sq_nonneg _
  have hn : 0≤D.internalWeight := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hs : 0≤D.extraSource := by
    change 0≤((7/13)*(S.a p)^4/(S.u p)^2)/ForceRows.scale .negative
    exact div_nonneg (by positivity) (ForceRows.scale_pos _).le
  obtain ⟨w,hw,hlo,hhi⟩ := certificate_cover hr
  have hbounds := w.lifted_residual hw D (B.physical_residuals hm) (B.test_residual hm hmax)
  have hpos (j : Fin n) : 0≤w.lifted.raw (D.eigenvalue j) (D.channel j) := by
    obtain ⟨lo,hi⟩ := B.value_bounds hm hmax j
    exact w.channel_nonnegative hw lo hi (B.channel_equations hm j) (B.channel_at_half hm j)
  have hsum : 0≤∑ j, w.lifted.raw (D.eigenvalue j) (D.channel j) := Finset.sum_nonneg fun j _ ↦ hpos j
  obtain ⟨⟨hlen,hlast⟩,_⟩ := w.geometric_weights hw
  have hy : (w.weights.getLastD 0 : ℝ)≤0 := by exact_mod_cast hlast
  have hw' := hw
  simp only [MixedCertificate.verify,Bool.and_eq_true] at hw'
  have signs := RatioWitness.signs hw'.1.1.1.2 hr hlo hhi
  simp only [PhysicalRow.residual,w.lifted_table,w.lifted_coefficient hlen] at hbounds
  linarith only [hbounds,hsum,mul_nonneg signs.1.le hn,signs.2,mul_nonpos_of_nonpos_of_nonneg hy hs]

end EuclideanMidpointRigidity.LiftedSection

