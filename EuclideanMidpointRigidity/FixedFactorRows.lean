module

public import EuclideanMidpointRigidity.FixedAxisKilling
public import EuclideanMidpointRigidity.MaximumEnvelope

/-! # Quartic identities in directions coupled to a fixed axis -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity.FixedAxis
open Quartic
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d

theorem factor_rows {c : T} {J : E →L[ℝ] T} {u : E}
    (hQ : ∀ v, obstruction c J v=0) (hu : J u=0) (hJ : ∀ l v, K (J l) u v=0) (y o : E) :
    let B := K c u
    ⟪K (J y) y y,B y⟫_ℝ=0 ∧
    2*⟪K (J y) y y,B o⟫_ℝ+10*jetEntry J (B y) y y o-8*jetEntry J y y (B y) o=0 := by
  have hlast (l x z : E) : ⟪K (J l) x z,u⟫_ℝ=0 := by rw [inner_slot,hJ,inner_zero_left]
  have hK (x z : E) : K (0:T) x z=0 := rfl
  have hzero (x : E) : K c x 0=0 := map_zero _
  have hscalar := congrArg (fun z : E ↦ ⟪z,u⟫_ℝ) (hQ y)
  simp only [obstruction,inner_add_left,inner_sub_left,← Nat.cast_smul_eq_nsmul ℝ,real_inner_smul_left,
    inner_zero_left,hlast,K_selfAdjoint c y _ u,K_symm c y u] at hscalar
  have hv := row31_zero hQ o y u
  simp only [row31,term,hu,hK,K_symm (J _) y u,hJ,hzero,K_symm c y u,K_selfAdjoint c u _ o,
    inner_zero_left,mul_zero,zero_add,add_zero,sub_zero] at hv
  dsimp only [jetEntry,cubicEntry]
  constructor
  · norm_num at hscalar
    linarith only [hscalar]
  · linarith only [hv]

theorem weighted_killing {c : T} {J : E →L[ℝ] T} {u : E}
    (hQ : ∀ v, obstruction c J v=0) (hu : J u=0) (hJ : ∀ l v, K (J l) u v=0) (y : E) :
    directionProfile y (J (K c u y))=0 := by
  obtain ⟨h₁,h₂⟩ := factor_rows hQ hu hJ y y
  rw [jetEntry_swap₂ J y y (K c u y) y] at h₂
  dsimp only [jetEntry,cubicEntry] at h₂
  rw [directionProfile_apply]
  linarith only [h₁,h₂]

theorem weighted_row {c : T} {J : E →L[ℝ] T} {u o : E} {b : ℝ}
    (hQ : ∀ v, obstruction c J v=0) (hu : J u=0) (hJ : ∀ l v, K (J l) u v=0)
    (ho : K c u o=b • o) (y : E) :
    let A := entryForm J o
    let B := K c u
    2*b*A y y y+10*A (B y) y y-8*A y y (B y)=0 := by
  have hh := (factor_rows hQ hu hJ y o).2
  rw [ho,real_inner_smul_right,inner_slot,jetEntry_swap₂ J (K c u y) y y o,
    jetEntry_swap₁ J (K c u y) y o y,jetEntry_swap₂ J y y (K c u y) o,jetEntry_swap₁ J y y o (K c u y)] at hh
  change 2*b*entry J o y y y+10*entry J o (K c u y) y y-8*entry J o y y (K c u y)=0
  dsimp only [entry,jetEntry,cubicEntry] at hh ⊢
  linarith only [hh]

end EuclideanMidpointRigidity.FixedAxis

