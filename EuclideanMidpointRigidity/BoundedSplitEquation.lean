module

public import EuclideanMidpointRigidity.BoundedTranslations
public import Mathlib.Algebra.Polynomial.Splits

/-! # A bounded entire solution of a real-split constant-coefficient ODE is constant -/

public section
noncomputable section
open Set Filter Polynomial
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.Endpoint
open LineSpace
private abbrev B := lineSpace (univ : Set ℝ) ℝ

private def shift (h : ℝ) (F : B) : B :=
  ⟨fun x ↦ F.val (x+h),F.property.1.comp (contDiff_id.add contDiff_const).contDiffOn (fun _ _ ↦ mem_univ _),by simp⟩

private theorem operator_shift (A : ℝ[X]) (F : B) (h x : ℝ) :
    ((operator isOpen_univ A) (shift h F)).val x=((operator isOpen_univ A) F).val (x+h) := by
  rw [operator_sum _ _ A (Nat.lt_succ_self _) (mem_univ x),operator_sum _ _ A (Nat.lt_succ_self _) (mem_univ (x+h))]
  apply Finset.sum_congr rfl
  intro i _
  change _ • iteratedDeriv i (fun z ↦ F.val (z+h)) x=_
  rw [iteratedDeriv_comp_add_const]

private theorem bounded_root_product (m : Multiset ℝ) {F : B} {K : ℝ} (hb : ∀ x, |F.val x|≤K)
    (ha : (operator isOpen_univ (m.map (fun r ↦ X-C r)).prod) F=0) : ∀ x y, F.val x=F.val y := by
  induction m using Multiset.induction_on generalizing F K with
  | empty =>
    have hF : F=0 := by simpa using ha
    simp [hF]
  | cons r m ih =>
    let A := (m.map (fun r ↦ X-C r)).prod
    let G := (operator isOpen_univ A) F
    have hg : ((operator isOpen_univ (X-C r)) G)=0 := by
      simpa only [Multiset.map_cons,Multiset.prod_cons,map_mul,mul_apply_eq_comp,A,G] using ha
    have hdG (x : ℝ) : HasDerivAt G.val (r*G.val x) x := by
      have e := congrArg (fun H : B ↦ H.val x) hg
      rw [map_sub,show operator isOpen_univ X=LineSpace.derivative (V := ℝ) isOpen_univ from aeval_X _,
        show operator isOpen_univ (C r)=algebraMap ℝ (Module.End ℝ B) r from aeval_C _ _] at e
      change ((LineSpace.derivative isOpen_univ) G).val x-r*G.val x=0 at e
      rw [derivative_apply _ _ (mem_univ x)] at e
      rw [← sub_eq_zero.mp e]
      exact ((G.property.1.contDiffAt (univ_mem (f := 𝓝 x))).differentiableAt (by simp)).hasDerivAt
    apply bounded_affine_translates hb
    intro h
    let a := Real.exp (r*h)
    let T : B := shift h F-a • F
    have hT (x : ℝ) : |T.val x|≤K+a*K := by
      change |F.val (x+h)-a*F.val x|≤_
      apply (abs_sub _ _).trans
      rw [abs_mul,abs_of_pos (Real.exp_pos _)]
      exact add_le_add (hb _) (mul_le_mul_of_nonneg_left (hb _) (Real.exp_pos _).le)
    have hzero : operator isOpen_univ A T=0 := by
      apply ext_on
      intro x _
      simp only [T,map_sub,map_smul,Submodule.coe_sub,Pi.sub_apply,Submodule.coe_smul_of_tower,Pi.smul_apply,
        operator_shift,smul_eq_mul]
      change G.val (x+h)-a*G.val x=0
      exact sub_eq_zero.mpr (homogeneous_scalar_translation hdG x h)
    have H := ih hT hzero
    refine ⟨a,T.val 0,Real.exp_pos _,fun x ↦ ?_⟩
    have he := H x 0
    change F.val (x+h)-a*F.val x=T.val 0 at he
    linarith

theorem SolvesOn.bounded_entire_constant {A : ℝ[X]} {f : ℝ → ℝ} (H : SolvesOn isOpen_univ A f)
    (hm : A.Monic) (hs : A.Splits) {K : ℝ} (hb : ∀ x, |f x|≤K) : ∀ x y, f x=f y := by
  let F := restrict f H.smooth
  have hF (x : ℝ) : F.val x=f x := restrict_apply _ (mem_univ x)
  have ha : (operator isOpen_univ (A.roots.map (fun r ↦ X-C r)).prod) F=0 := by
    rw [← hs.eq_prod_roots_of_monic hm]; exact H.equation
  intro x y
  exact (hF x).symm.trans ((bounded_root_product _ (fun t ↦ (hF t).symm ▸ hb t) ha x y).trans (hF y))

end EuclideanMidpointRigidity.Endpoint

