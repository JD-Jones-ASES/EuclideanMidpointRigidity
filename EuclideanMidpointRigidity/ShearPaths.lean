module

public import EuclideanMidpointRigidity.LocalFlow
public import EuclideanMidpointRigidity.Basic

/-! # Smooth radial paths for the rescaled inverse of a shear -/

public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]

/-- The parameter stays in a fixed open neighborhood of the origin even at zero scale. -/
theorem smooth_shear_paths {W : Set E} {e : E → E} (hW : IsOpen W) (he : ContDiffOn ℝ ∞ e W)
    (hA : ∀ x ∈ W, ∀ z, fderiv ℝ e x (fderiv ℝ e x z)=0) {p : E} (hp : p ∈ W) :
    ∃ (U : Set (ℝ × E)) (g : ℝ × E → E), IsOpen U ∧ (0,0) ∈ U ∧ ContDiffOn ℝ ∞ g U ∧ MapsTo g U W ∧
      (∀ ρ, (ρ,0) ∈ U → g (ρ,0)=p) ∧
      ∀ q ∈ U, q.1 • g q+e (g q)=q.1 • p+e p+q.1^2 • q.2 := by
  let A := fderiv ℝ e
  let D := W ×ˢ (univ : Set (ℝ × E))
  let V := fun q : E × (ℝ × E) ↦ (q.2.1 • q.2.2-A q.1 q.2.2,(0 : ℝ × E))
  have hV : ContDiffOn ℝ ∞ V D := by
    have hpr : MapsTo (Prod.fst : E × (ℝ × E) → E) D W := fun _ h ↦ h.1
    have hder : ContDiffOn ℝ ∞ (fun q : E × (ℝ × E) ↦ A q.1) D := (he.fderiv_of_isOpen hW (by simp)).comp contDiffOn_fst hpr
    exact ((contDiffOn_snd.fst.smul contDiffOn_snd.snd).sub (hder.clm_apply contDiffOn_snd.snd)).prodMk contDiffOn_const
  let i := fun q : ℝ × E ↦ (p,q)
  have hi : ContDiff ℝ ∞ i := contDiff_const.prodMk contDiff_id
  obtain ⟨O,φ,hO,hpO,hφ,hm,h₀,hd⟩ := smooth_local_flow (hW.prod isOpen_univ) hV (show i (0,0) ∈ D from ⟨hp,mem_univ _⟩)
  let j := fun q : (ℝ × E) × ℝ ↦ (i q.1,q.2)
  have hj : ContDiff ℝ ∞ j := (hi.comp contDiff_fst).prodMk contDiff_snd
  have hnb := (hO.preimage hj.continuous).mem_nhds (show ((0,0),(0:ℝ)) ∈ j ⁻¹' O from hpO)
  obtain ⟨M,hM,N,hN,hMN⟩ := mem_nhds_prod_iff.mp hnb
  obtain ⟨U,hUM,hU,h₀U⟩ := _root_.mem_nhds_iff.mp hM
  obtain ⟨r,hr,hrN⟩ := Metric.mem_nhds_iff.mp hN
  let B := ball (0:ℝ) r
  have h₀B : (0:ℝ) ∈ B := mem_ball_self hr
  let γ := fun (q : ℝ × E) (s : ℝ) ↦ φ (i q,s)
  have hg (q : ℝ × E) (hq : q ∈ U) (s : ℝ) (hs : s ∈ B) : (i q,s) ∈ O := hMN (show (q,s) ∈ M ×ˢ N from ⟨hUM hq,hrN hs⟩)
  have hpar (q : ℝ × E) (hq : q ∈ U) (s : ℝ) (hs : s ∈ B) : (γ q s).2=q := by
    have dh (t : ℝ) (ht : t ∈ B) : HasDerivAt (fun t ↦ (γ q t).2) 0 t :=
      ((ContinuousLinearMap.snd ℝ E (ℝ × E)).hasFDerivAt).comp_hasDerivAt t (hd _ (hg q hq t ht))
    have H := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball _ _).isPreconnected
      (fun t ht ↦ (dh t ht).differentiableAt.differentiableWithinAt) (fun {t} ht ↦ (dh t ht).deriv) hs h₀B
    exact H.trans (congrArg Prod.snd (h₀ (i q) (hg q hq 0 h₀B)))
  let x := fun (q : ℝ × E) (s : ℝ) ↦ (γ q s).1
  have hx (q : ℝ × E) (hq : q ∈ U) (s : ℝ) (hs : s ∈ B) : x q s ∈ W := (hm (hg q hq s hs)).1
  have dx (q : ℝ × E) (hq : q ∈ U) (s : ℝ) (hs : s ∈ B) :
      HasDerivAt (x q) (q.1 • q.2-A (x q s) q.2) s := by
    have H := (ContinuousLinearMap.fst ℝ E (ℝ × E)).hasFDerivAt.comp_hasDerivAt s (hd _ (hg q hq s hs))
    change HasDerivAt (x q) ((γ q s).2.1 • (γ q s).2.2-A (x q s) (γ q s).2.2) s at H
    rwa [hpar q hq s hs] at H
  have hx₀ (q : ℝ × E) (hq : q ∈ U) : x q 0=p := congrArg Prod.fst (h₀ (i q) (hg q hq 0 h₀B))
  let s := r/2
  have hs₁ : 0<s := half_pos hr
  have hs : s ∈ B := by simpa only [B,mem_ball,Real.dist_eq,sub_zero,abs_of_pos hs₁] using half_lt_self hr
  let L := fun q : ℝ × E ↦ (q.1,s⁻¹ • q.2)
  have hL : ContDiff ℝ ∞ L := contDiff_fst.prodMk (contDiff_const.smul contDiff_snd)
  let G := fun q : ℝ × E ↦ x (L q) s
  have hj' : ContDiff ℝ ∞ (fun q ↦ (i (L q),s)) := (hi.comp hL).prodMk contDiff_const
  refine ⟨L ⁻¹' U,G,hU.preimage hL.continuous,by simpa only [mem_preimage,L,smul_zero] using h₀U,
    (hφ.comp hj'.contDiffOn (fun q hq ↦ hg (L q) hq s hs)).fst,fun q hq ↦ hx (L q) hq s hs,?_,?_⟩
  · intro ρ hρ
    let q := L (ρ,0)
    have hq : q ∈ U := hρ
    have dz (t : ℝ) (ht : t ∈ B) : HasDerivAt (x q) 0 t := by
      have H := dx q hq t ht
      simpa only [q,L,smul_zero,map_zero,sub_self] using H
    have H := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball _ _).isPreconnected
      (fun t ht ↦ (dz t ht).differentiableAt.differentiableWithinAt) (fun {t} ht ↦ (dz t ht).deriv) hs h₀B
    exact H.trans (hx₀ q hq)
  · intro z hz
    let q := L z
    let u := fun t ↦ q.1 • x q t+e (x q t)-t • (q.1^2 • q.2)
    have hq : q ∈ U := hz
    have dz (t : ℝ) (ht : t ∈ B) : HasDerivAt u 0 t := by
      have H := dx q hq t ht
      have H' := ((he.contDiffAt (hW.mem_nhds (hx q hq t ht))).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t H
      have HH := ((H.const_smul q.1).add H').fun_sub ((hasDerivAt_id t).smul_const (q.1^2 • q.2))
      change HasDerivAt u (q.1 • (q.1 • q.2-A (x q t) q.2)+A (x q t) (q.1 • q.2-A (x q t) q.2)-1 • (q.1^2 • q.2)) t at HH
      simp only [A,map_sub,map_smul,hA _ (hx q hq t ht),sub_zero,smul_sub,smul_smul,one_smul,sq] at HH
      convert HH using 1 <;> module
    have H := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball _ _).isPreconnected
      (fun t ht ↦ (dz t ht).differentiableAt.differentiableWithinAt) (fun {t} ht ↦ (dz t ht).deriv) hs h₀B
    change u s=u 0 at H
    simp only [u,hx₀ q hq,zero_smul,sub_zero] at H
    have hsc : s • (q.1^2 • q.2)=z.1^2 • z.2 := by
      change s • (z.1^2 • (s⁻¹ • z.2))=z.1^2 • z.2
      simp only [smul_smul]
      congr 1
      field_simp
    rw [← hsc]
    exact sub_eq_iff_eq_add.mp H

end EuclideanMidpointRigidity

