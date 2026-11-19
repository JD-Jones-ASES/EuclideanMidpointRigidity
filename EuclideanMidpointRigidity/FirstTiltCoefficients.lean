module

public import EuclideanMidpointRigidity.PrimitiveFlow
public import EuclideanMidpointRigidity.ComposedMidpointJet

/-! # Ordinary derivatives of the first-tilt boundary functional -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.Endpoint

def coordinateCoeff (k : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => k^n

def solutionCoeff (η : ℝ) (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | n+2 => η*solutionCoeff η a (n+1)+a n

def oneCoeff (n : ℕ) : ℝ := if n=0 then 1 else 0

theorem coordinateCoeff_correct (k : ℝ) (n : ℕ) : iteratedDeriv n (rateCoordinate k) 0=coordinateCoeff k n := by
  cases n with
  | zero => simp [coordinateCoeff]
  | succ n =>
    rw [iteratedDeriv_succ',show deriv (rateCoordinate k)=fun t ↦ Real.exp (k*t) from funext fun x ↦ (rateCoordinate_diff k x).deriv]
    simp [iteratedDeriv_exp_const_mul,coordinateCoeff]

theorem solutionCoeff_correct {f : ℝ → ℝ} {a : ℕ → ℝ} (η : ℝ) (hf : ContDiff ℝ ∞ f)
    (ha : ∀ n, iteratedDeriv n f 0=a n) (n : ℕ) :
    iteratedDeriv n (ratePrimitive η f) 0=solutionCoeff η a n := by
  have dx : deriv (ratePrimitive η f)=rateVelocity η f := funext fun s ↦ ((ratePrimitive_solution η hf).position s).deriv
  have dv : deriv (rateVelocity η f)=fun s ↦ η*rateVelocity η f s+f s := funext fun s ↦ ((ratePrimitive_solution η hf).velocity s).deriv
  induction n with
  | zero => simp [solutionCoeff]
  | succ n ih =>
    cases n with
    | zero => change iteratedDeriv 1 (ratePrimitive η f) 0=0; rw [iteratedDeriv_one,dx,rateVelocity_zero]
    | succ n =>
      rw [iteratedDeriv_succ',dx,iteratedDeriv_succ',dv,iteratedDeriv_fun_add
        ((contDiff_const.mul (rateVelocity_smooth η hf)).contDiffAt.of_le (by simp)) (hf.contDiffAt.of_le (by simp)),iteratedDeriv_const_mul_field]
      rw [iteratedDeriv_succ',dx] at ih
      rw [ih,ha,solutionCoeff]

structure RealJet where
  value : ℝ → ℝ
  coeff : ℕ → ℝ
  smooth : ContDiff ℝ ∞ value
  correct : ∀ n, iteratedDeriv n value 0=coeff n

namespace RealJet

def coord (k : ℝ) : RealJet := ⟨rateCoordinate k,coordinateCoeff k,rateCoordinate_smooth k,coordinateCoeff_correct k⟩
def forced (η : ℝ) (F : RealJet) : RealJet := ⟨ratePrimitive η F.value,solutionCoeff η F.coeff,
  ratePrimitive_smooth η F.smooth,solutionCoeff_correct η F.smooth F.correct⟩
def one : RealJet := ⟨fun _ ↦ 1,oneCoeff,contDiff_const,fun n ↦ by cases n <;> simp [oneCoeff,iteratedDeriv_const]⟩

def sub (F G : RealJet) : RealJet := ⟨fun x ↦ F.value x-G.value x,fun n ↦ F.coeff n-G.coeff n,
  F.smooth.sub G.smooth,fun n ↦ by rw [iteratedDeriv_fun_sub (F.smooth.contDiffAt.of_le (by simp)) (G.smooth.contDiffAt.of_le (by simp)),F.correct,G.correct]⟩

def halfSum (F G : RealJet) : RealJet := ⟨fun x ↦ (F.value x+G.value x)/2,fun n ↦ (F.coeff n+G.coeff n)/2,
  (F.smooth.add G.smooth).div_const _,fun n ↦ by rw [iteratedDeriv_div_const,iteratedDeriv_fun_add
    (F.smooth.contDiffAt.of_le (by simp)) (G.smooth.contDiffAt.of_le (by simp)),F.correct,G.correct]⟩

def productCoeff (a b : ℕ → ℝ) (n : ℕ) := ∑ i ∈ Finset.range (n+1), (n.choose i:ℝ)*a i*b (n-i)

def mul (F G : RealJet) : RealJet := ⟨fun x ↦ F.value x*G.value x,productCoeff F.coeff G.coeff,F.smooth.mul G.smooth,fun n ↦ by
  rw [iteratedDeriv_fun_mul (F.smooth.contDiffAt.of_le (by simp)) (G.smooth.contDiffAt.of_le (by simp))]
  simp only [productCoeff,F.correct,G.correct]⟩

def atMinus (F : RealJet) : RealJet := ⟨fun x ↦ F.value (-x),fun n ↦ (-1)^n*F.coeff n,F.smooth.comp contDiff_id.neg,fun n ↦ by simp [iteratedDeriv_comp_neg,F.correct]⟩

def atMid (F : RealJet) : RealJet := ⟨fun x ↦ F.value (chordMid x),fun n ↦ atMidCoeff F.coeff n 0 0,
  F.smooth.comp chordMid_smooth,atMidCoeff_correct F.smooth F.correct⟩

def boundary (η : ℝ) (F : RealJet) : RealJet :=
  let A := coord η
  ((((A.sub A.atMinus).mul F.atMid).sub ((A.sub A.atMid).mul F.atMinus))).sub ((A.atMid.sub A.atMinus).mul F)

theorem boundary_value (η h : ℝ) (F : RealJet) : (boundary η F).value h=universalBoundary η h F.value := rfl

end RealJet

def centeredCoordinate (k h s : ℝ) := rateCoordinate k s-(rateCoordinate k h+rateCoordinate k (-h))/2

def firstTiltJet (η k : ℝ) : RealJet :=
  let Q := RealJet.coord k
  (RealJet.boundary η (RealJet.forced η Q)).sub
    ((Q.halfSum Q.atMinus).mul (RealJet.boundary η (RealJet.forced η RealJet.one)))

theorem firstTiltJet_law (η k : ℝ) (hv : ∀ᶠ h in 𝓝[>] (0:ℝ), VanishingResponse η h (centeredCoordinate k h))
    (n : ℕ) : (firstTiltJet η k).coeff n=0 := by
  rw [← (firstTiltJet η k).correct]
  apply RationalJet.iterated_zero_of_right (firstTiltJet η k).smooth
  filter_upwards [hv,self_mem_nhdsWithin] with h hh hp
  let c := (rateCoordinate k h+rateCoordinate k (-h))/2
  let F := ratePrimitive_solution η (rateCoordinate_smooth k)
  let G := ratePrimitive_solution η (contDiff_const (c := (1:ℝ)))
  have hb := (hh.congr (g := fun s ↦ rateCoordinate k s+(-c)*1) (fun s _ ↦ by dsimp [centeredCoordinate,c]; ring)).universal_boundary hp (F.add (G.scale (-c)))
  change universalBoundary η h (fun s ↦ F.value s+(-c)*G.value s)=0 at hb
  change universalBoundary η h F.value-c*universalBoundary η h G.value=0
  dsimp [universalBoundary] at hb ⊢
  linear_combination hb

end EuclideanMidpointRigidity.Endpoint

