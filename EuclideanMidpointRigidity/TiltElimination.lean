module

public import EuclideanMidpointRigidity.AffineTilt

/-! # Elimination of the constant curvature coefficient from reflected tilts -/

@[expose] public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
open Endpoint
namespace ThirdTiltLaws

structure DiagonalData (W : Set ℝ) (A : ℝ → TiltData) (r : ℝ) : Prop where
  smoothQ : ContDiffOn ℝ ∞ (fun t ↦ (A t).q) W
  smoothP : ContDiffOn ℝ ∞ (fun t ↦ (A t).p₁) W
  smoothZ : ContDiffOn ℝ ∞ (fun t ↦ (A t).p₃) W
  pair : ∀ t ∈ W, (A t).p₂=(A t).p₁
  curvature : ∀ t ∈ W, (A t).r₁=r ∧ (A t).r₂=r ∧ (A t).r₃=0

theorem constant_translation {W : Set ℝ} {A : ℝ → TiltData} {k n : ℚ} {q r : ℝ}
    (E : TiltRates k n) (H : ThirdTiltLaws W k n A) (D : DiagonalData W A r)
    (hW : IsOpen W) (hc : IsPreconnected W) (h₀ : 0 ∈ W) (hq : ∀ t ∈ W, (A t).q=q) : r=0 := by
  obtain ⟨hzero,hp⟩ := H.singles.1.kill E.eta_ne hW hc h₀ D.smoothP hq E.eta_ne E.rate₁ E.single₁
  have hz := (H.singles.2.kill E.eta_ne hW hc h₀ D.smoothZ hq E.lambda_ne E.rate₂ E.single₂).2
  subst q
  let p := (A 0).p₁
  let z := (A 0).p₃
  let F := BoundaryTest.tilted k k n E.eta_ne
  let G := BoundaryTest.tilted k n k E.eta_ne
  have mixed : ∀ᶠ h in 𝓝[>] (0:ℝ), VanishingResponse k h (fun s ↦ (-4*(k:ℝ)*p)*F.source h s+(-4*(n:ℝ)*z)*G.source h s) := by
    filter_upwards [H 0 h₀,small_segments hW h₀] with h hh hs
    apply (hh true false true).congr
    intro s hm
    obtain ⟨ha,hb⟩ := hs s hm
    change TiltData.test _ _ _ _ _ _ _ _ _=_
    rw [mixed_source _ _ _ _ _ _ (hq _ ha) (hq _ hb) (hp _ ha) (hp _ hb) (hz _ ha) (hz _ hb)
      ((D.curvature _ ha).2.1.trans (D.curvature _ hb).2.1.symm)]
    simp only [F,G,BoundaryTest.tilted_source,tiltAmplitude,p,z]; ring
  obtain ⟨hp₀,hz₀⟩ := F.detect_pair G E.eta_ne E.double mixed
  have hk : (k:ℝ)≠0 := by exact_mod_cast E.eta_ne
  have hn : (n:ℝ)≠0 := by exact_mod_cast E.lambda_ne
  have hkp : p=0 := (mul_eq_zero.mp hp₀).resolve_left (mul_ne_zero (by norm_num) hk)
  have hnz : z=0 := (mul_eq_zero.mp hz₀).resolve_left (mul_ne_zero (by norm_num) hn)
  let T := BoundaryTest.tilted k (k+n) k E.eta_ne
  have triple : ∀ᶠ h in 𝓝[>] (0:ℝ), VanishingResponse k h (fun s ↦ (-8*(k:ℝ)*n*r)*T.source h s) := by
    filter_upwards [H 0 h₀,small_segments hW h₀] with h hh hs
    apply (hh true true true).congr
    intro s hm
    obtain ⟨ha,hb⟩ := hs s hm
    obtain ⟨ra,sa,ta⟩ := D.curvature _ ha
    obtain ⟨rb,sb,tb⟩ := D.curvature _ hb
    change TiltData.test _ _ _ _ _ _ _ _ _=_
    rw [triple_source _ _ _ _ r _ _ ⟨hq _ ha,hq _ hb⟩
      ⟨(hp _ ha).trans hkp,(hp _ hb).trans hkp,(D.pair _ ha).trans ((hp _ ha).trans hkp),
        (D.pair _ hb).trans ((hp _ hb).trans hkp),(hz _ ha).trans hnz,(hz _ hb).trans hnz⟩ ⟨ra,rb,sa,sb,ta,tb⟩]
    simp only [T,BoundaryTest.tilted_source,Rat.cast_add,tiltAmplitude]; ring
  exact (mul_eq_zero.mp (T.detect_single E.eta_ne 7 E.triple triple)).resolve_left
    (mul_ne_zero (mul_ne_zero (by norm_num) hk) hn)

def filterData (d : ℝ) (A : ℝ → TiltData) (x : ℝ) :=
  TiltData.combine 1 (-2*Real.cosh d) (TiltData.combine 1 1 (A (x+d)) (A (x+(-d)))) (A x)

private theorem filter_exponentials (a b c x d : ℝ) :
    let f := fun y ↦ a+b*Real.exp y+c*Real.exp (-y)
    f (x+d)+f (x+(-d))-2*Real.cosh d*f x=(2-2*Real.cosh d)*a := by
  dsimp only
  simp only [Real.cosh_eq,neg_add_rev,neg_neg,Real.exp_add]
  ring

theorem eliminate {W : Set ℝ} {A : ℝ → TiltData} {k n : ℚ} {r : ℝ} (E : TiltRates k n)
    (H : ThirdTiltLaws W k n A) (D : DiagonalData W A r) (hW : IsOpen W) (h₀ : 0 ∈ W) : r=0 := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds h₀)
  let V := ball (0:ℝ) ε
  have eQ (x : ℝ) (hx : x ∈ V) : iteratedDeriv 3 (fun t ↦ (A t).q) x=(1:ℝ)^2*iteratedDeriv 1 (fun t ↦ (A t).q) x := by
    simpa [tiltRate] using oddTilt_differential_equation hW D.smoothQ H.translation x (hball hx)
  obtain ⟨a,b,c,hf⟩ := exponential_form_of_third isOpen_ball (convex_ball _ _).isPreconnected (D.smoothQ.mono hball)
    (mem_ball_self hε) one_ne_zero eQ
  have hf' (x : ℝ) (hx : x ∈ V) : (A x).q=a+b*Real.exp x+c*Real.exp (-x) := by simpa using hf x hx
  let d := ε/4
  let U := ball (0:ℝ) d
  have hd : 0<d := by dsimp [d]; positivity
  have inc (x : ℝ) (hx : x ∈ U) : x ∈ V ∧ x+d ∈ V ∧ x+(-d) ∈ V := by
    simp only [U,mem_ball,Real.dist_eq,sub_zero,abs_lt] at hx
    simp only [V,mem_ball,Real.dist_eq,sub_zero,abs_lt]
    dsimp [d] at *
    exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩
  have iz : U ⊆ W := fun x hx ↦ hball (inc x hx).1
  have ip : ∀ x ∈ U, x+d ∈ W := fun x hx ↦ hball (inc x hx).2.1
  have im : ∀ x ∈ U, x+(-d) ∈ W := fun x hx ↦ hball (inc x hx).2.2
  have hF : ThirdTiltLaws U k n (filterData d A) := ((H.shift ip).combine (H.shift im) 1 1).combine (H.mono iz) 1 (-2*Real.cosh d)
  have smoothF {f : ℝ → ℝ} (hs : ContDiffOn ℝ ∞ f W) :
      ContDiffOn ℝ ∞ (fun x ↦ 1*(1*f (x+d)+1*f (x+(-d)))+(-2*Real.cosh d)*f x) U :=
    (contDiffOn_const.mul ((contDiffOn_const.mul (hs.comp (contDiff_id.add contDiff_const).contDiffOn ip)).add
      (contDiffOn_const.mul (hs.comp (contDiff_id.add contDiff_const).contDiffOn im)))).add (contDiffOn_const.mul (hs.mono iz))
  have hD : DiagonalData U (filterData d A) ((2-2*Real.cosh d)*r) := by
    refine ⟨smoothF D.smoothQ,smoothF D.smoothP,smoothF D.smoothZ,?_,?_⟩
    · intro x hx
      simp [filterData,TiltData.combine,D.pair _ (iz hx),D.pair _ (ip _ hx),D.pair _ (im _ hx)]
    · intro x hx
      obtain ⟨a₁,a₂,a₃⟩ := D.curvature _ (iz hx)
      obtain ⟨b₁,b₂,b₃⟩ := D.curvature _ (ip _ hx)
      obtain ⟨c₁,c₂,c₃⟩ := D.curvature _ (im _ hx)
      simp [filterData,TiltData.combine,a₁,a₂,a₃,b₁,b₂,b₃,c₁,c₂,c₃]
      ring
  have hq (x : ℝ) (hx : x ∈ U) : (filterData d A x).q=(2-2*Real.cosh d)*a := by
    simp only [filterData,TiltData.combine,one_mul,hf' _ (inc x hx).1,hf' _ (inc x hx).2.1,hf' _ (inc x hx).2.2]
    linarith only [filter_exponentials a b c x d]
  have hr := constant_translation E hF hD isOpen_ball (convex_ball _ _).isPreconnected (mem_ball_self hd) hq
  have hc := Real.one_lt_cosh.mpr hd.ne'
  exact (mul_eq_zero.mp hr).resolve_left (by linarith)

end ThirdTiltLaws
end EuclideanMidpointRigidity

