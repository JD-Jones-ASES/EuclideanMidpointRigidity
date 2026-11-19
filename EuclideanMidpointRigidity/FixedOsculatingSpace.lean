module

public import EuclideanMidpointRigidity.OsculatingSpaces
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # A space spanned by all jets is fixed near a point of maximum rank -/

public section
noncomputable section
open Set Filter Metric ContinuousLinearMap
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d

theorem fixed_osculating_space {W : Set E} {e : E → E} (hW : IsOpen W) (he : ContDiffOn ℝ ∞ e W)
    {p : E} (hp : p ∈ W) (hmax : ∀ x ∈ W, Module.finrank ℝ (osculatingSpace e x)≤Module.finrank ℝ (osculatingSpace e p)) :
    ∃ r : ℝ, 0<r ∧ ball p r ⊆ W ∧ ∀ x ∈ ball p r, osculatingSpace e x=osculatingSpace e p := by
  classical
  let V := osculatingSpace e p
  let B := stdOrthonormalBasis ℝ V
  let π := V.orthogonalProjectionOnto
  choose f hf hS using fun i ↦ osculating_extension hW he p (B i).property
  let F := fun x : E ↦ ∑ i, (innerSL ℝ (B i)).smulRight (f i x)
  have F_apply (x : E) (v : V) : F x v=∑ i, ⟪B i,v⟫_ℝ • f i x := by
    simp only [F,sum_apply,smulRight_apply,innerSL_apply_apply]
  have fp (v : V) : F p v=(v:E) := by
    rw [F_apply]
    simpa only [hf,Submodule.coe_sum,Submodule.coe_smul_of_tower] using congrArg ((↑) : V → E) (B.sum_repr' v)
  have hF : ContDiffOn ℝ ∞ F W := ContDiffOn.sum (s := Finset.univ) (fun i _ ↦ contDiffOn_const.smulRight (hS i).smooth)
  let T := fun x ↦ π.comp (F x)
  have hT : ContDiffOn ℝ ∞ T W := contDiffOn_const.clm_comp hF
  have hTp : T p=ContinuousLinearMap.id ℝ V := by
    ext v : 1
    change π (F p v)=v
    rw [fp]; exact V.orthogonalProjectionOnto_mem_subspace_eq_self v
  have ht : (T p).IsInvertible := hTp ▸ ⟨ContinuousLinearEquiv.refl ℝ V,rfl⟩
  have hnear : ∀ᶠ x in 𝓝 p, (T x).IsInvertible :=
    (hT.contDiffAt (hW.mem_nhds hp)).continuousAt (ContinuousLinearMap.isOpen_setOfPred_isInvertible.mem_nhds ht)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (hW.mem_nhds hp) hnear)
  let U := ball p r
  have hi : U ⊆ W := fun _ hx ↦ (hball hx).1
  have hinv (x : E) (hx : x ∈ U) : (T x).IsInvertible := (hball hx).2
  have range_eq (x : E) (hx : x ∈ U) : LinearMap.range (F x).toLinearMap=osculatingSpace e x := by
    apply Submodule.eq_of_le_of_finrank_le
    · rintro _ ⟨v,rfl⟩
      change F x v ∈ _
      rw [F_apply]
      exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ ((hS i).value x (hi hx))
    · have hj : Function.Injective (F x) := fun a b hh ↦ (hinv x hx).injective (congrArg π hh)
      rw [LinearMap.finrank_range_of_inj (show Function.Injective (F x).toLinearMap from hj)]
      exact hmax x (hi hx)
  have inj (x : E) (hx : x ∈ U) {w : E} (hw : w ∈ osculatingSpace e x) (hz : π w=0) : w=0 := by
    rw [← range_eq x hx] at hw
    obtain ⟨v,rfl⟩ := hw
    have h₀ : T x v=T x 0 := (show T x v=0 from hz).trans (map_zero _).symm
    rw [(hinv x hx).injective h₀,map_zero]
  have normalized (v : V) : ∀ x ∈ U, (v:E) ∈ osculatingSpace e x := by
    let c := fun x : E ↦ (T x).inverse v
    let g := fun x : E ↦ F x (c x)
    have hI : ContDiffOn ℝ ∞ (fun x ↦ (T x).inverse) U := fun x hx ↦
      ((hinv x hx).contDiffAt_map_inverse.comp x (hT.contDiffAt (hW.mem_nhds (hi hx)))).contDiffWithinAt
    have hc : ContDiffOn ℝ ∞ c U := hI.clm_apply contDiffOn_const
    have hg : ParallelSection U (osculatingSpace e) g := by
      rw [show g=fun x ↦ ∑ i, ⟪B i,c x⟫_ℝ • f i x from funext fun x ↦ F_apply x _]
      exact ParallelSection.sum isOpen_ball _ _ fun i _ ↦ ParallelSection.smul isOpen_ball ((hS i).mono hi)
        (contDiffOn_const.inner ℝ hc)
    have fixed (x : E) (hx : x ∈ U) : π (g x)=v := (hinv x hx).self_apply_inverse v
    have hd (x : E) (hx : x ∈ U) : fderiv ℝ g x=0 := by
      have hn : π ∘ g =ᶠ[𝓝 x] fun _ ↦ v := (show ∀ᶠ y in 𝓝 x, y ∈ U from isOpen_ball.mem_nhds hx).mono fixed
      have dπ := π.hasFDerivAt.comp x ((hg.smooth.contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
      have hh := dπ.fderiv.symm.trans (hn.fderiv_eq.trans (hasFDerivAt_const v x).fderiv)
      ext w : 1
      exact inj x hx (hg.tangent x hx w) (DFunLike.congr_fun hh w)
    intro x hx
    have hp' : p ∈ U := mem_ball_self hr
    have eq := isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball p r).isPreconnected
      (hg.smooth.differentiableOn (by simp)) hd hx hp'
    have gp : g p=(v:E) := by simp [g,c,hTp,fp]
    rw [← gp,← eq]
    exact hg.value x hx
  refine ⟨r,hr,hi,fun x hx ↦ Eq.symm (Submodule.eq_of_le_of_finrank_le (fun v hv ↦ normalized ⟨v,hv⟩ x hx) (hmax x (hi hx)))⟩

end EuclideanMidpointRigidity

