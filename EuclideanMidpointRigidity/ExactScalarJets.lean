module

public import EuclideanMidpointRigidity.HyperbolicMoments
public import EuclideanMidpointRigidity.ExponentialLine

/-! # Exact rational derivatives of the elementary boundary functions -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.Endpoint

structure RationalJet where
  value : ℝ → ℝ
  coeff : ℕ → ℚ
  smooth : ContDiff ℝ ∞ value
  correct : ∀ n, iteratedDeriv n value 0=(coeff n:ℝ)

namespace RationalJet

def const (c : ℚ) : RationalJet where
  value _ := c
  coeff n := if n=0 then c else 0
  smooth := contDiff_const
  correct n := by cases n <;> simp [iteratedDeriv_const]

def time : RationalJet where
  value x := x
  coeff n := if n=1 then 1 else 0
  smooth := contDiff_id
  correct n := by rw [iteratedDeriv_fun_id_zero]; split <;> norm_num

def mid : RationalJet where
  value := chordMid
  coeff
    | 0 => 0
    | n+1 => hyperMoment n 1 0
  smooth := chordMid_smooth
  correct n := by cases n with
    | zero => simp [chordMid]
    | succ n => exact chordMid_moment n

def expTime (a : ℚ) : RationalJet where
  value x := Real.exp ((a:ℝ)*x)
  coeff n := a^n
  smooth := by fun_prop
  correct n := by simp [iteratedDeriv_exp_const_mul]

def expMid (a : ℚ) : RationalJet where
  value x := Real.exp ((a:ℝ)*chordMid x)
  coeff n := hyperMoment n 0 a
  smooth := Real.contDiff_exp.comp (contDiff_const.mul chordMid_smooth)
  correct n := by
    rw [← show hyperTerm 0 a=fun x ↦ Real.exp ((a:ℝ)*chordMid x) by funext x; simp [hyperTerm]]
    exact hyperMoment_correct n 0 a

def add (f g : RationalJet) : RationalJet where
  value x := f.value x+g.value x
  coeff n := f.coeff n+g.coeff n
  smooth := f.smooth.add g.smooth
  correct n := by
    rw [iteratedDeriv_fun_add (f.smooth.contDiffAt.of_le (by simp)) (g.smooth.contDiffAt.of_le (by simp)),f.correct,g.correct]
    push_cast
    rfl

def scale (c : ℚ) (f : RationalJet) : RationalJet where
  value x := c*f.value x
  coeff n := c*f.coeff n
  smooth := contDiff_const.mul f.smooth
  correct n := by rw [iteratedDeriv_const_mul_field]; simp [f.correct]

def sub (f g : RationalJet) : RationalJet where
  value x := f.value x-g.value x
  coeff n := f.coeff n-g.coeff n
  smooth := f.smooth.sub g.smooth
  correct n := by
    rw [iteratedDeriv_fun_sub (f.smooth.contDiffAt.of_le (by simp)) (g.smooth.contDiffAt.of_le (by simp)),f.correct,g.correct]
    push_cast
    rfl

def mul (f g : RationalJet) : RationalJet where
  value x := f.value x*g.value x
  coeff n := ∑ i ∈ Finset.range (n+1), (n.choose i:ℚ)*f.coeff i*g.coeff (n-i)
  smooth := f.smooth.mul g.smooth
  correct n := by
    rw [iteratedDeriv_fun_mul (f.smooth.contDiffAt.of_le (by simp)) (g.smooth.contDiffAt.of_le (by simp))]
    simp only [f.correct,g.correct]
    push_cast
    rfl

def coshTime (a : ℚ) := scale (1/2) ((expTime a).add (expTime (-a)))

theorem coshTime_value (a : ℚ) (h : ℝ) : (coshTime a).value h=Real.cosh ((a:ℝ)*h) := by
  simp [coshTime,scale,add,expTime,Real.cosh_eq,neg_mul]
  <;> ring

/-- A smooth identity on all sufficiently short positive chords determines the ordinary jet at zero. -/
theorem iterated_zero_of_right {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hz : ∀ᶠ x in 𝓝[>] (0:ℝ), f x=0) (n : ℕ) : iteratedDeriv n f 0=0 := by
  obtain ⟨ε,hε,hx⟩ := (mem_nhdsGT_iff_exists_Ioc_subset.mp hz)
  have near : ∀ᶠ x in 𝓝[>] (0:ℝ), x ∈ Ioo 0 ε :=
    inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hε))
  have hd : ∀ᶠ x in 𝓝[>] (0:ℝ), iteratedDeriv n f x=0 := by
    filter_upwards [near] with x hxi
    have he : f =ᶠ[𝓝 x] fun _ ↦ 0 := Filter.mem_of_superset (isOpen_Ioo.mem_nhds hxi)
      fun y hy ↦ hx ⟨hy.1,hy.2.le⟩
    rw [he.iteratedDeriv_eq (n := n)]
    simp [iteratedDeriv_const]
  have hc : Continuous (iteratedDeriv n f) :=
    (contDiffOn_univ.mp (smooth_line_derivative isOpen_univ hf.contDiffOn n)).continuous
  exact tendsto_nhds_unique (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_const_nhds.congr' (hd.mono fun _ he ↦ he.symm))

theorem two_moments (f g : RationalJet) {a b : ℝ}
    (hz : ∀ᶠ h in 𝓝[>] (0:ℝ), a*f.value h+b*g.value h=0) (n : ℕ) :
    a*(f.coeff n:ℝ)+b*(g.coeff n:ℝ)=0 := by
  have H := iterated_zero_of_right ((contDiff_const.mul f.smooth).add (contDiff_const.mul g.smooth)) hz n
  rwa [iteratedDeriv_fun_add (by exact (contDiff_const.mul f.smooth).contDiffAt.of_le (by simp))
    (by exact (contDiff_const.mul g.smooth).contDiffAt.of_le (by simp)),iteratedDeriv_const_mul_field,
    iteratedDeriv_const_mul_field,f.correct,g.correct] at H

theorem independent (f g : RationalJet) (hdet : f.coeff 5*g.coeff 7-f.coeff 7*g.coeff 5≠0) {a b : ℝ}
    (hz : ∀ᶠ h in 𝓝[>] (0:ℝ), a*f.value h+b*g.value h=0) : a=0 ∧ b=0 := by
  have eq₁ := two_moments f g hz 5
  have eq₂ := two_moments f g hz 7
  have hD : (f.coeff 5:ℝ)*(g.coeff 7:ℝ)-(f.coeff 7:ℝ)*(g.coeff 5:ℝ)≠0 := by exact_mod_cast hdet
  constructor
  · apply (mul_eq_zero.mp (show a*((f.coeff 5:ℝ)*(g.coeff 7:ℝ)-(f.coeff 7:ℝ)*(g.coeff 5:ℝ))=0 by
      linear_combination (g.coeff 7:ℝ)*eq₁-(g.coeff 5:ℝ)*eq₂)).resolve_right hD
  · apply (mul_eq_zero.mp (show b*((f.coeff 5:ℝ)*(g.coeff 7:ℝ)-(f.coeff 7:ℝ)*(g.coeff 5:ℝ))=0 by
      linear_combination (f.coeff 5:ℝ)*eq₂-(f.coeff 7:ℝ)*eq₁)).resolve_right hD

end RationalJet
end EuclideanMidpointRigidity.Endpoint

