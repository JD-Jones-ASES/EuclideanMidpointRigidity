module

public import EuclideanMidpointRigidity.LineDifference

/-! # The differential operator detected by a vanishing translation difference -/

public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.Endpoint

private theorem derivative_differenceWeight (n : ℕ) :
    iteratedDeriv (n+1) differenceWeight 0=1+(-1:ℝ)^(n+1) := by
  let A := fun s : ℝ ↦ Real.exp (1*s)
  let B := fun s : ℝ ↦ Real.exp ((-1)*s)
  have hA : ContDiff ℝ ∞ A := by dsimp [A]; fun_prop
  have hB : ContDiff ℝ ∞ B := by dsimp [B]; fun_prop
  have he : differenceWeight=(fun s ↦ 1+(A+B) s) := by funext s; simp [A,B,differenceWeight,add_assoc]
  rw [he,iteratedDeriv_const_add (by omega) 1,iteratedDeriv_add (hA.contDiffAt.of_le (by simp))
    (hB.contDiffAt.of_le (by simp))]
  simp only [A,B,iteratedDeriv_exp_const_mul,mul_zero,Real.exp_zero,mul_one,one_pow]

theorem differential_equation_of_difference {W : Set ℝ} {f : ℝ → ℝ} {p : ℝ}
    (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W) (hp : p ∈ W)
    (hzero : ∀ᶠ t in 𝓝 (0:ℝ), lineDifference t f p=0) : iteratedDeriv 3 f p=iteratedDeriv 1 f p := by
  let F := fun a : ℝ ↦ fun t ↦ f (p+t*a)
  let A := F 3-F 0
  let B := F 2-F 1
  have hs (a : ℝ) : ContDiffAt ℝ ∞ (F a) 0 := by
    have h := hf.contDiffAt (hW.mem_nhds hp)
    exact (show ContDiffAt ℝ ∞ f (p+0*a) by simpa using h).comp 0
      (contDiffAt_const.add (contDiffAt_id.mul contDiffAt_const))
  have dF (a : ℝ) (n : ℕ) : iteratedDeriv n (F a) 0=a^n*iteratedDeriv n f p := by
    simpa only [F,smul_eq_mul,zero_mul,add_zero,iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
      Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
      iteratedDeriv_spatial_line hW hf p a 0 (by simpa using hp) n
  have dA (n : ℕ) : iteratedDeriv n A 0=(3^n-0^n)*iteratedDeriv n f p := by
    rw [show A=F 3-F 0 from rfl,iteratedDeriv_sub ((hs _).of_le (by simp)) ((hs _).of_le (by simp)),dF,dF]
    ring
  have dB (n : ℕ) : iteratedDeriv n B 0=(2^n-1^n)*iteratedDeriv n f p := by
    rw [show B=F 2-F 1 from rfl,iteratedDeriv_sub ((hs _).of_le (by simp)) ((hs _).of_le (by simp)),dF,dF]
    ring
  have hA : ContDiffAt ℝ 3 A 0 := ((hs 3).sub (hs 0)).of_le (by simp)
  have hB : ContDiffAt ℝ 3 B 0 := ((hs 2).sub (hs 1)).of_le (by simp)
  have hK : ContDiff ℝ ∞ differenceWeight := by change ContDiff ℝ ∞ (fun t : ℝ ↦ 1+Real.exp t+Real.exp (-t)); fun_prop
  have hfun : (fun t ↦ lineDifference t f p)=A-differenceWeight*B := by
    funext t
    simp only [lineDifference,A,B,F,Pi.sub_apply,Pi.mul_apply,mul_zero,add_zero,mul_one,mul_comm t]
  have h0 : iteratedDeriv 3 (A-differenceWeight*B) 0=0 := by
    rw [← hfun]
    have he : (fun t ↦ lineDifference t f p)=ᶠ[𝓝 (0:ℝ)] (fun _ ↦ (0:ℝ)) := hzero
    exact (he.iteratedDeriv_eq 3).trans (by simp)
  have hKB : ContDiffAt ℝ 3 (differenceWeight*B) 0 := (hK.contDiffAt.of_le (by simp)).mul hB
  rw [iteratedDeriv_sub hA hKB,iteratedDeriv_mul (hK.contDiffAt.of_le (by simp)) hB,dA] at h0
  have d₀ : iteratedDeriv 0 differenceWeight 0=3 := by norm_num [differenceWeight]
  have d₁ := derivative_differenceWeight 0
  have d₂ := derivative_differenceWeight 1
  have d₃ := derivative_differenceWeight 2
  norm_num [Finset.sum_range_succ,Nat.choose,dB,d₀,d₁,d₂,d₃] at h0
  rw [iteratedDeriv_one]
  linarith only [h0]

end EuclideanMidpointRigidity.Endpoint

