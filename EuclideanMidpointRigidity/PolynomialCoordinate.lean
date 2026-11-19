module

public import EuclideanMidpointRigidity.CubicTransport
public import EuclideanMidpointRigidity.ClearedMidpoint
public import EuclideanMidpointRigidity.ConstantAmplitude
public import EuclideanMidpointRigidity.PolynomialGerms

/-! # Extinction of polynomial variation in one spatial coordinate -/

@[expose] public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Polynomial
namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d
set_option backward.isDefEq.respectTransparency false

private def translationChart {W : Set E} {C : E → T} (hW : IsOpen W) (hC : ContDiffOn ℝ ∞ C W) (w : E) :
    LineChart E T where
  domain := W
  isOpen := hW
  position t x := x+t • w
  jacobian _ _ := ContinuousLinearMap.id ℝ E
  hasJacobian y _ t := (hasFDerivAt_id (𝕜 := ℝ) y).add_const (t • w)
  determinant _ _ := 1
  detFamily := AnalyticLineFamily.const _ 1
  adjugate _ _ := ContinuousLinearMap.id ℝ E
  adjFamily := AnalyticLineFamily.const _ _
  adjIdentity _ _ _ _ := (one_smul _ _).symm
  field := cubicTranslate C w
  fieldFamily := cubicTranslateFamily hW hC w

theorem polynomial_coordinate_stationary {W : Set E} {C : E → T} (hW : IsOpen W) (hv : Convex ℝ W)
    (hC : ContDiffOn ℝ ∞ C W) (hQ : MidpointJetEquations W C) (w : E) (hz : ∀ x ∈ W, directions C [w,w,w,w] x=0)
    {p : E} (hp : p ∈ W) : fderiv ℝ C p w=0 := by
  let F := cubicTranslate C w
  let A := translationChart hW hC w
  have transport := fun {x : E} {t : ℝ} (hx : x ∈ W) (ht : x+t • w ∈ W) ↦ cubicTranslate_transport hW hv hC w hz hx ht
  have F₀ (x : E) : F x 0=C x := cubicTranslate_zero C w x
  have germ (x : E) (hx : x ∈ W) (t : ℝ) (ht : x+t • w ∈ W) : F x t=C (x+t • w) := by
    have hh := transport hx ht t
    simpa only [sub_self,← show ∀ y s, F y s=cubicTranslate C w y s from fun _ _ ↦ rfl,F₀] using hh.symm
  have small (x : E) (hx : x ∈ W) : ∀ᶠ t in 𝓝 (0:ℝ), x+t • w ∈ W :=
    (continuous_const.add (continuous_id.smul continuous_const)).continuousAt (hW.mem_nhds (by simpa using hx : x+(0:ℝ) • w ∈ W))
  have extend {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {g : (E → T) → E → Z}
      (R : ClearedExpression A g) (hg : ∀ x ∈ W, g C x=0) (x : E) (hx : x ∈ W) : ∀ t, R.numerator x t=0 := by
    apply R.family.extend_zero hx
    filter_upwards [small x hx] with t ht
    have near : ∀ᶠ y in 𝓝 x, y+t • w ∈ W := (continuous_id.add continuous_const).continuousAt (hW.mem_nhds ht)
    have he : (fun z ↦ A.field z t) =ᶠ[𝓝 x] C ∘ A.position t :=
      ((show ∀ᶠ z in 𝓝 x, z ∈ W from hW.mem_nhds hx).and near).mono fun y hy ↦ germ y hy.1 t hy.2
    rw [R.correct hW hC hx ht he,hg (A.position t x) ht,smul_zero]
  have localAmp (t : ℝ) : (fun s ↦ amplitude (F p s)) =ᶠ[𝓝 t] (fun _ ↦ amplitude (F p t)) := by
    let V := (fun z : E ↦ z-t • w) ⁻¹' W
    let G := fun z : E ↦ F (z-t • w) t
    have hV : IsOpen V := hW.preimage (continuous_id.sub continuous_const)
    have hG : ContDiffOn ℝ ∞ G V := ((cubicTranslateFamily hW hC w).smooth_space t).comp
      ((contDiff_id.sub contDiff_const).contDiffOn) (fun _ h ↦ h)
    have transfer {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {g : (E → T) → E → Z}
        (hR : Represented A g) (hg : ∀ x ∈ W, g C x=0) (z : E) (hzV : z ∈ V) : g G z=0 := by
      let R := hR.some
      have he (y : E) : A.field y t=G (A.position t y) := by change F y t=F (y+t • w-t • w) t; rw [add_sub_cancel_right]
      have hm : A.position t (z-t • w)=z := sub_add_cancel _ _
      have hh := R.correct hV hG hzV (hm.symm ▸ hzV) (Eventually.of_forall he)
      rw [extend R hg _ hzV t,hm] at hh
      simpa only [A,translationChart,one_pow,one_smul] using hh.symm
    have eq : MidpointJetEquations V G :=
      ⟨fun z hzV v ↦ transfer (Represented.quartic A v) (fun y hy ↦ hQ.quartic hy v) z hzV,
       fun z hzV v ↦ transfer (Represented.sixth A v) (fun y hy ↦ hQ.sixth hy v) z hzV⟩
    have hpt : p+t • w ∈ V := by change p+t • w-t • w ∈ W; rwa [add_sub_cancel_right]
    obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hpt)
    obtain ⟨b,hb⟩ := (eq.mono hrV).amplitude_constant isOpen_ball (convex_ball _ _).isPreconnected (hG.mono hrV)
    have hnear : ∀ᶠ s in 𝓝 t, p+s • w ∈ ball (p+t • w) r :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousAt (ball_mem_nhds _ hr)
    filter_upwards [hnear] with s hs
    have pos : p+s • w-t • w=p+(s-t) • w := by rw [sub_smul]; abel
    have hw := hrV hs
    change p+s • w-t • w ∈ W at hw
    rw [pos] at hw
    have h := transport hp hw s
    change F (p+(s-t) • w) (s-(s-t))=F p s at h
    rw [sub_sub_cancel] at h
    have eqAmp := (hb _ hs).trans (hb _ (mem_ball_self hr)).symm
    change amplitude (F (p+s • w-t • w) t)=amplitude (F (p+t • w-t • w) t) at eqAmp
    rwa [pos,h,add_sub_cancel_right] at eqAmp
  have hd (t : ℝ) : HasDerivAt (fun s ↦ amplitude (F p s)) 0 t :=
    (hasDerivAt_const t _).congr_of_eventuallyEq (localAmp t)
  obtain ⟨b,hb⟩ := isOpen_univ.exists_is_const_of_deriv_eq_zero isPreconnected_univ
    (fun t _ ↦ (hd t).differentiableAt.differentiableWithinAt) (fun {t} _ ↦ (hd t).deriv)
  have same (s : ℝ) : F p s=F p 0 := by
    apply sub_eq_zero.mp
    apply (amplitude_eq_zero_iff _).mp
    obtain ⟨z,hz,he,_⟩ := exists_maximizing_direction (F p s-F p 0)
    let L := directionProfile z
    let P : ℝ[X] := Polynomial.C (L (C p))+Polynomial.X*Polynomial.C (L (directions C [w] p))+
      Polynomial.X^2*Polynomial.C (L (directions C [w,w] p)/2)+Polynomial.X^3*Polynomial.C (L (directions C [w,w,w] p)/6)
    have hP (t : ℝ) : P.eval t=L (F p t) := by simp [P,F,cubicTranslate]; ring
    have hbd (t : ℝ) : |P.eval t|≤b := by
      rw [hP]
      have hneg : -z ∈ closedBall (0:E) 1 := by simpa only [mem_closedBall,dist_zero_right,norm_neg] using hz
      have hl := directionProfile_le_amplitude hneg (F p t)
      have hr := directionProfile_le_amplitude hz (F p t)
      rw [hb t (mem_univ _)] at hl hr
      have he' : directionProfile (-z) (F p t)= -L (F p t) := by simp [L,directionProfile_apply,K]
      rw [he'] at hl
      exact abs_le.mpr ⟨by linarith,hr⟩
    rw [he,map_sub,← show L (F p s)=directionProfile z (F p s) from rfl,← show L (F p 0)=directionProfile z (F p 0) from rfl,
      ← hP,← hP,PolynomialGerm.eval_constant_of_bounded P b hbd s,sub_self]
  have he : (fun t : ℝ ↦ C (p+t • w)) =ᶠ[𝓝 0] (fun _ ↦ C p) :=
    (small p hp).mono fun t ht ↦ (germ p hp t ht).symm.trans ((same t).trans (F₀ p))
  have dl : HasDerivAt (fun t : ℝ ↦ p+t • w) w 0 := by simpa only [one_smul,id_eq] using ((hasDerivAt_id (0:ℝ)).smul_const w).const_add p
  have hC' := ((hC.contDiffAt (hW.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  exact (hC'.comp_hasDerivAt_of_eq 0 dl (by simp)).unique ((hasDerivAt_const (0:ℝ) (C p)).congr_of_eventuallyEq he)

end EuclideanMidpointRigidity

