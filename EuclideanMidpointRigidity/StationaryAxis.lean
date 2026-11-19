module

public import EuclideanMidpointRigidity.Osculation
public import EuclideanMidpointRigidity.FixedOsculatingSpace

/-! # A locally fixed spatial direction taken from the maximizing section -/

public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d

theorem HorizontalPatch.fixed_stationary_axis {S : LiftedSection d} (H : HorizontalPatch S) (hne : S.domain.Nonempty) :
    ∃ p ∈ S.domain, ∃ r : ℝ, 0<r ∧ ball p r ⊆ S.domain ∧
      ∀ x ∈ ball p r, fderiv ℝ S.field x (S.idempotent p)=0 := by
  obtain ⟨p,hp,hmax⟩ := maximum_dimension_point hne (osculatingSpace S.axis)
  obtain ⟨r,hr,hU,hfixed⟩ := fixed_osculating_space S.isOpen S.smoothAxis hp hmax
  refine ⟨p,hp,r,hr,hU,?_⟩
  intro x hx
  have hker : osculatingSpace S.axis x ≤ LinearMap.ker (fderiv ℝ S.field x).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨xs,rfl⟩
    exact H.osculation (hU hx) xs
  apply hker
  rw [hfixed x hx]
  exact (osculatingSpace S.axis p).smul_mem _ (direction_mem_osculating S.axis p [])

theorem stationary_segment {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {W : Set E} {f : E → Y} {u : E} (hW : IsOpen W) (hc : Convex ℝ W) (hf : ContDiffOn ℝ ∞ f W)
    (hz : ∀ x ∈ W, fderiv ℝ f x u=0) {x : E} {t : ℝ} (hx : x ∈ W) (ht : x+t • u ∈ W) : f (x+t • u)=f x := by
  let line := fun s : ℝ ↦ x+s • (t • u)
  have hline (s : ℝ) (hs : s ∈ Icc 0 1) : line s ∈ W := by
    have h := hc hx ht (sub_nonneg.mpr hs.2) hs.1 (sub_add_cancel 1 s)
    convert h using 1 <;> dsimp [line] <;> module
  have hdiff (s : ℝ) (hs : s ∈ Icc 0 1) : HasDerivAt (f ∘ line) 0 s := by
    have hl : HasDerivAt line (t • u) s := by
      simpa [line] using ((hasDerivAt_id s).smul_const (t • u)).const_add x
    have h := ((hf.contDiffAt (hW.mem_nhds (hline s hs))).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s hl
    simpa only [map_smul,hz _ (hline s hs),smul_zero] using h
  have h := constant_of_has_deriv_right_zero (HasDerivAt.continuousOn hdiff) (fun y hy ↦ (hdiff y (mem_Icc_of_Ico hy)).hasDerivWithinAt)
    1 (right_mem_Icc.mpr (by norm_num))
  simpa [Function.comp_def,line] using h

theorem stationary_field_jet {W : Set E} {C : E → Cubic d} {u : E} (hW : IsOpen W) (hc : Convex ℝ W)
    (hC : ContDiffOn ℝ ∞ C W) (hz : ∀ x ∈ W, fderiv ℝ C x u=0)
    {x : E} {t : ℝ} (hx : x ∈ W) (ht : x+t • u ∈ W) :
    C (x+t • u)=C x ∧ fderiv ℝ C (x+t • u)=fderiv ℝ C x := by
  refine ⟨stationary_segment hW hc hC hz hx ht,?_⟩
  apply stationary_segment hW hc (hC.fderiv_of_isOpen hW (by simp)) _ hx ht
  intro y hy
  have h := inactive_exchange hW hC (contDiffOn_const (c := u)) hz hy
  simpa using h

end EuclideanMidpointRigidity

