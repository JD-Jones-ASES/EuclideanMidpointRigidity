module

public import EuclideanMidpointRigidity.ChannelCharts
public import EuclideanMidpointRigidity.SpectralTable
public import Mathlib.Algebra.Polynomial.Roots

/-! # Regular and angular coordinates at exceptional spectral values -/

@[expose] public section
noncomputable section
open Filter
open scoped Topology
namespace EuclideanMidpointRigidity.MixedChannel
open IntervalPolynomial

theorem charts_cover {s : ℝ} (hs : s<1) : regularDenominator s≠0 ∨ angularDenominator s≠0 := by
  by_contra! h
  apply hs.ne
  have hz : s-1=0 := by
    dsimp only [regularDenominator,angularDenominator] at h
    linear_combination
      (-2*(1295256191907379888716600*s^3-634519150785269947133800*s^2-
        1788139569897362973448352*s-1398297125001887949214245)/6265856580782496416618041935)*h.1 +
      ((458736567967197043920462500*s^5-102035987725222955706454000*s^4-47585359102656904315537450*s^3-
        13257128894786467204938140*s^2-147286490699618687429338912*s+
        54864555288835445483017011)/6265856580782496416618041935)*h.2
  exact sub_eq_zero.mp hz

theorem denominator_eq (s : ℝ) : eval Spectral.denominator s=regularDenominator s := by
  norm_num [Spectral.denominator,eval,regularDenominator]
  ring

theorem numerators_eq (s l h : ℝ) :
    eval Spectral.firstNumerator s*l+eval Spectral.secondNumerator s*h=regular_q s l h := by
  norm_num [Spectral.firstNumerator,Spectral.secondNumerator,eval,regular_q]
  ring

theorem cubic_transport {v : MixedChannel} {s : ℝ} (he : v.Equations s) :
    eval Spectral.denominator s*v.q=eval Spectral.firstNumerator s*v.l+eval Spectral.secondNumerator s*v.h := by
  rw [denominator_eq,numerators_eq]
  exact (regular_coordinates he).1

def inRegular (s l h : ℝ) : MixedChannel :=
  let D := regularDenominator s
  ⟨regular_q s l h/D,l,h,regular_r1w s l h/D,regular_rw1 s l h/D,regular_z1w s l h/D,
    regular_r2w s l h/D,regular_rw2 s l h/D,regular_z2w s l h/D,regular_rot1 s l h/D,regular_rot2 s l h/D⟩

theorem inRegular_eq {v : MixedChannel} {s : ℝ} (he : v.Equations s) (hs : regularDenominator s≠0) :
    inRegular s v.l v.h=v := by
  obtain ⟨a,b,c,d,e,f,g,h,i⟩ := regular_coordinates he
  cases v
  dsimp only [inRegular] at *
  congr 1 <;> apply (div_eq_iff hs).mpr <;> linarith only [a,b,c,d,e,f,g,h,i]

def inAngular (s o p : ℝ) : MixedChannel :=
  let D := angularDenominator s
  ⟨angular_q s o p/D,angular_l s o p/D,angular_h s o p/D,
    angular_r1w s o p/D,angular_rw1 s o p/D,angular_z1w s o p/D,
    angular_r2w s o p/D,angular_rw2 s o p/D,angular_z2w s o p/D,o,p⟩

theorem inAngular_eq {v : MixedChannel} {s : ℝ} (he : v.Equations s) (hs : angularDenominator s≠0) :
    inAngular s v.rot1 v.rot2=v := by
  obtain ⟨a,b,c,d,e,f,g,h,i⟩ := angular_coordinates he
  cases v
  dsimp only [inAngular] at *
  congr 1 <;> apply (div_eq_iff hs).mpr <;> linarith only [a,b,c,d,e,f,g,h,i]

theorem inAngular_equations {s : ℝ} (hs : angularDenominator s≠0) (o p : ℝ) :
    (inAngular s o p).Equations s := by
  refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_,?_⟩ <;>
    dsimp only [inAngular] <;> field_simp [hs] <;>
    simp only [angularDenominator,angular_q,angular_l,angular_h,angular_r1w,angular_rw1,angular_z1w,
      angular_r2w,angular_rw2,angular_z2w] <;> ring

theorem eventually_regular (s : ℝ) : ∀ᶠ t in 𝓝[≠] s, regularDenominator t≠0 := by
  let X := Polynomial.X (R := ℝ)
  let f := (X-1)*(2*X-1)*(5*X-1)*(125*X^2+5*X-74)*(170*X^2+16*X+93)
  have heval (t : ℝ) : f.eval t=regularDenominator t := by
    simp [f,X,regularDenominator]
  have hn : f≠0 := by
    intro hz
    have h := heval 0
    rw [hz] at h
    norm_num [regularDenominator] at h
  exact ((Polynomial.eventually_eval_ne_zero_cofinite hn).filter_mono (nhdsNE_le_cofinite s)).mono
    (fun t ht ↦ heval t ▸ ht)

/-- Positivity of a continuous raw angular quadratic at a chart singularity
follows by testing nearby algebraic channels with the same two rotations. -/
theorem nonnegative_on_channels {F : ℝ → MixedChannel → ℝ} {s : ℝ} (hl : -1<s) (hr : s<1/2)
    {v : MixedChannel} (hv : v.Equations s)
    (hcont : ∀ o p, angularDenominator s≠0 → ContinuousAt (fun t ↦ F t (inAngular t o p)) s)
    (hreg : ∀ t, -1<t → t<1/2 → regularDenominator t≠0 → ∀ w : MixedChannel, w.Equations t → 0≤F t w) :
    0≤F s v := by
  by_cases hs : regularDenominator s≠0
  · exact hreg s hl hr hs v hv
  have ha := (charts_cover (lt_trans hr (by norm_num))).resolve_left hs
  have hc := (hcont v.rot1 v.rot2 ha).continuousWithinAt (s := {s}ᶜ)
  have hd : ContinuousAt angularDenominator s := by unfold angularDenominator; fun_prop
  have hne : ∀ᶠ t in 𝓝[≠] s, angularDenominator t≠0 :=
    (hd.eventually_ne ha).filter_mono nhdsWithin_le_nhds
  have bounds : ∀ᶠ t in 𝓝[≠] s, -1<t ∧ t<1/2 :=
    ((lt_mem_nhds hl).and (gt_mem_nhds hr)).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ t in 𝓝[≠] s, 0≤F t (inAngular t v.rot1 v.rot2) := by
    filter_upwards [eventually_regular s,hne,bounds] with t ht hd hb
    exact hreg t hb.1 hb.2 ht _ (inAngular_equations hd _ _)
  simpa only [inAngular_eq hv ha] using ge_of_tendsto hc hpos

end EuclideanMidpointRigidity.MixedChannel
