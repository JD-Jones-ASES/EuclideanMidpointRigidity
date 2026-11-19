module

public import EuclideanMidpointRigidity.LineOperatorCalculus
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Continuation of a monic line equation by its companion matrix -/

@[expose] public section
noncomputable section
open Set Filter Metric Polynomial
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.Endpoint
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}

abbrev JetState (n : ℕ) (V : Type*) := Fin (n+1) → V

def companion (c : Fin (n+1) → ℝ) : JetState n V →L[ℝ] JetState n V :=
  ContinuousLinearMap.pi (Fin.lastCases (-(∑ j, c j • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n+1) ↦ V) j))
    (fun i : Fin n ↦ ContinuousLinearMap.proj i.succ))

def lineJet (f : ℝ → V) (s : ℝ) : JetState n V := fun i ↦ iteratedDeriv i.val f s

theorem hasDerivAt_lineJet {W : Set ℝ} {f : ℝ → V} {A : ℝ[X]} {hW : IsOpen W}
    (H : SolvesOn hW A f) (hA : A.Monic) (hdeg : A.natDegree=n+1) {s : ℝ} (hs : s ∈ W) :
    HasDerivAt (lineJet (n := n) f) ((companion (fun j : Fin (n+1) ↦ A.coeff j)) (lineJet f s)) s := by
  have hsm (m : ℕ) : ContDiffOn ℝ ∞ (iteratedDeriv m f) W := by
    induction m with
    | zero => simpa only [iteratedDeriv_zero] using H.smooth
    | succ m ih => rw [iteratedDeriv_succ]; exact ih.deriv_of_isOpen hW (by simp)
  have hd (m : ℕ) : HasDerivAt (iteratedDeriv m f) (iteratedDeriv (m+1) f s) s := by
    rw [iteratedDeriv_succ]; exact (((hsm m).contDiffAt (hW.mem_nhds hs)).differentiableAt (by simp)).hasDerivAt
  apply hasDerivAt_pi.mpr
  intro i
  induction i using Fin.lastCases with
  | cast j =>
    simpa only [companion,ContinuousLinearMap.pi_apply,Fin.lastCases_castSucc,ContinuousLinearMap.proj_apply,lineJet,Fin.val_castSucc,Fin.val_succ] using hd j.val
  | last =>
    have h := (solvesOn_iff_sum H.smooth (show A.natDegree<(n+1)+1 by omega)).mp H s hs
    have hlead : A.coeff (n+1)=1 := hdeg ▸ hA.coeff_natDegree
    rw [Finset.sum_range_succ,hlead,one_smul] at h
    have he : iteratedDeriv (n+1) f s= -(∑ j : Fin (n+1), A.coeff j • iteratedDeriv j f s) := by
      rw [Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ A.coeff k • iteratedDeriv k f s)]
      exact eq_neg_of_add_eq_zero_right h
    simpa only [companion,ContinuousLinearMap.pi_apply,Fin.lastCases_last,neg_apply,ContinuousLinearMap.sum_apply,
      smul_apply,ContinuousLinearMap.proj_apply,lineJet,Fin.val_last] using he ▸ hd n

variable [CompleteSpace V]

def companionSolution (c : Fin (n+1) → ℝ) (v : JetState n V) (s : ℝ) : V :=
  (NormedSpace.exp (s • companion c) v) 0

theorem linear_flow_eq {Y : ℝ → V} {W : Set ℝ} (hW : IsOpen W) (hc : IsPreconnected W)
    (h₀ : 0 ∈ W) (A : V →L[ℝ] V) (hY : ∀ s ∈ W, HasDerivAt Y (A (Y s)) s) {s : ℝ} (hs : s ∈ W) :
    Y s=NormedSpace.exp (s • A) (Y 0) := by
  let B := fun t : ℝ ↦ NormedSpace.exp (t • (-A))
  let F := fun t ↦ B t (Y t)
  have dF (t : ℝ) (ht : t ∈ W) : HasDerivAt F 0 t := by
    have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) t).clm_apply (hY t ht)
    convert h using 1
    change (0:V)=(B t*(-A)) (Y t)+B t (A (Y t))
    simp only [mul_apply_eq_comp,neg_apply,map_neg,neg_add_cancel]
  have H := hW.is_const_of_deriv_eq_zero hc (fun t ht ↦ (dF t ht).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ (dF t ht).deriv) hs h₀
  have e₀ : F 0=Y 0 := by simp [F,B,NormedSpace.exp_zero]
  have hmul : NormedSpace.exp (s • A)*B s=1 := by
    have hr (L : V →L[ℝ] V) : L ∈ Metric.eball 0 (NormedSpace.expSeries ℝ (V →L[ℝ] V)).radius := by
      rw [NormedSpace.expSeries_radius_eq_top,Metric.eball_top_eq_univ]; exact mem_univ _
    dsimp only [B]; rw [smul_neg,← NormedSpace.exp_add_of_commute_of_mem_ball (Commute.refl _).neg_right (hr _) (hr _),add_neg_cancel,NormedSpace.exp_zero]
  calc
    Y s = (NormedSpace.exp (s • A)*B s) (Y s) := by rw [hmul]; rfl
    _ = NormedSpace.exp (s • A) (F s) := rfl
    _ = _ := by rw [H,e₀]

theorem SolvesOn.eventually_companionSolution {W : Set ℝ} {hW : IsOpen W} {A : ℝ[X]} {f : ℝ → V} (H : SolvesOn hW A f)
    (h₀ : 0 ∈ W) (hA : A.Monic) (hdeg : A.natDegree=n+1) :
    ∀ᶠ s in 𝓝 (0:ℝ), f s=companionSolution (fun j : Fin (n+1) ↦ A.coeff j) (lineJet f 0) s := by
  obtain ⟨δ,hδ,hB⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds h₀)
  filter_upwards [ball_mem_nhds (0:ℝ) hδ] with s hs
  have eq := linear_flow_eq (Y := lineJet (n := n) f) isOpen_ball (convex_ball (0:ℝ) δ).isPreconnected (mem_ball_self hδ)
    (companion (fun j : Fin (n+1) ↦ A.coeff j)) (fun t ht ↦ hasDerivAt_lineJet H hA hdeg (hB ht)) hs
  exact congrArg (fun z : JetState n V ↦ z 0) eq

end EuclideanMidpointRigidity.Endpoint

