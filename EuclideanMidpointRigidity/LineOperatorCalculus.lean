module

public import EuclideanMidpointRigidity.LineOperators
public import Mathlib.Algebra.Polynomial.Degree.Support

/-! # Coefficients, restriction, and linear operations on polynomial ODEs -/

public section
noncomputable section
open Set Filter Polynomial
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.Endpoint
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {W U : Set ℝ}

namespace LineSpace

theorem operator_monomial (hW : IsOpen W) (F : lineSpace W V) (r : ℝ) (n : ℕ) {x : ℝ} (hx : x ∈ W) :
    ((operator hW (C r*X^n)) F).val x=r • iteratedDeriv n F.val x := by
  rw [map_mul,mul_apply_eq_comp]
  rw [show operator hW (C r)=(algebraMap ℝ (Module.End ℝ (lineSpace W V))) r from aeval_C _ r]
  change r • ((operator hW (X^n)) F).val x=_
  rw [operator_X_pow hW F n hx]

theorem operator_sum (hW : IsOpen W) (F : lineSpace W V) (A : ℝ[X]) {N : ℕ} (hN : A.natDegree<N) {x : ℝ} (hx : x ∈ W) :
    ((operator hW A) F).val x=∑ i ∈ Finset.range N, A.coeff i • iteratedDeriv i F.val x := by
  let e : lineSpace W V →ₗ[ℝ] V := (LinearMap.proj x).comp (lineSpace W V).subtype
  let L := (e.comp (LinearMap.applyₗ (R := ℝ) F)).comp (operator hW).toLinearMap
  have he := congrArg L (A.as_sum_range_C_mul_X_pow' hN)
  rw [map_sum] at he
  refine he.trans (Finset.sum_congr rfl (fun n _ ↦ ?_))
  exact operator_monomial hW F _ n hx

theorem iteratedDeriv_restrict (hW : IsOpen W) {f : ℝ → V} (hf : ContDiffOn ℝ ∞ f W) {x : ℝ} (hx : x ∈ W) (n : ℕ) :
    iteratedDeriv n (restrict f hf).val x=iteratedDeriv n f x := by
  have he : (restrict f hf).val =ᶠ[𝓝 x] f :=
    (show ∀ᶠ t in 𝓝 x, t ∈ W from hW.mem_nhds hx).mono fun _ ht ↦ restrict_apply hf ht
  exact he.iteratedDeriv_eq n

end LineSpace
open LineSpace

theorem solvesOn_iff_sum {hW : IsOpen W} {f : ℝ → V} {A : ℝ[X]} (hf : ContDiffOn ℝ ∞ f W) {N : ℕ} (hN : A.natDegree<N) :
    SolvesOn hW A f ↔ ∀ x ∈ W, ∑ i ∈ Finset.range N, A.coeff i • iteratedDeriv i f x=0 := by
  have he (x : ℝ) (hx : x ∈ W) := operator_sum hW (restrict f hf) A hN hx
  constructor
  · intro H x hx
    simpa only [H.equation,Submodule.coe_zero,Pi.zero_apply,iteratedDeriv_restrict hW hf hx] using (he x hx).symm
  · intro H
    refine ⟨hf,ext_on (fun x hx ↦ ?_)⟩
    rw [he x hx]
    change _=(0:V)
    simpa only [iteratedDeriv_restrict hW hf hx] using H x hx

theorem SolvesOn.mono {hW : IsOpen W} {A : ℝ[X]} {f : ℝ → V} (H : SolvesOn hW A f) (hU : IsOpen U) (hs : U ⊆ W) :
    SolvesOn hU A f := by
  apply (solvesOn_iff_sum (H.smooth.mono hs) (Nat.lt_succ_self _)).mpr
  exact fun x hx ↦ (solvesOn_iff_sum H.smooth (Nat.lt_succ_self _)).mp H x (hs hx)

theorem SolvesOn.congr {hW : IsOpen W} {A : ℝ[X]} {f g : ℝ → V} (H : SolvesOn hW A f) (he : EqOn f g W) :
    SolvesOn hW A g := by
  refine ⟨H.smooth.congr he.symm,?_⟩
  have eq : restrict g (H.smooth.congr he.symm)=restrict f H.smooth := ext_on (fun x hx ↦ by simp only [restrict_apply _ hx,he hx])
  rw [eq,H.equation]

theorem SolvesOn.add {hW : IsOpen W} {A : ℝ[X]} {f g : ℝ → V} (H : SolvesOn hW A f) (J : SolvesOn hW A g) :
    SolvesOn hW A (fun x ↦ f x+g x) := by
  refine ⟨H.smooth.add J.smooth,?_⟩
  have e : restrict (fun x ↦ f x+g x) (H.smooth.add J.smooth)=restrict f H.smooth+restrict g J.smooth := by
    apply ext_on
    intro x hx
    simp only [Submodule.coe_add,Pi.add_apply,restrict_apply _ hx]
  rw [e,map_add,H.equation,J.equation,add_zero]

theorem SolvesOn.smul {hW : IsOpen W} {A : ℝ[X]} {f : ℝ → V} (H : SolvesOn hW A f) (c : ℝ) :
    SolvesOn hW A (fun x ↦ c • f x) := by
  refine ⟨contDiffOn_const.smul H.smooth,?_⟩
  have e : restrict (fun x ↦ c • f x) (contDiffOn_const.smul H.smooth)=c • restrict f H.smooth := by
    apply ext_on
    intro x hx
    simp only [Submodule.coe_smul_of_tower,Pi.smul_apply,restrict_apply _ hx]
  rw [e,map_smul,H.equation,smul_zero]

theorem solvesOn_zero (hW : IsOpen W) (A : ℝ[X]) : SolvesOn hW A (fun _ ↦ (0:V)) := by
  refine ⟨contDiffOn_const,?_⟩
  have hz : restrict (fun _ ↦ (0:V)) (contDiffOn_const (s := W))=0 :=
    ext_on (fun x hx ↦ restrict_apply _ hx)
  rw [hz,map_zero]

theorem SolvesOn.integrate {hW : IsOpen W} {A : ℝ[X]} {f : ℝ → V} (hf : ContDiffOn ℝ ∞ f W)
    (H : SolvesOn hW A (deriv f)) : SolvesOn hW (A*X) f := by
  have he : derivative hW (restrict f hf)=restrict (deriv f) H.smooth := by
    apply ext_on
    intro x hx
    rw [derivative_apply hW _ hx,restrict_apply _ hx]
    simpa only [iteratedDeriv_one] using iteratedDeriv_restrict hW hf hx 1
  refine ⟨hf,?_⟩
  rw [map_mul,mul_apply_eq_comp]
  rw [show operator hW X=derivative (V := V) hW from aeval_X _,he,H.equation]

end EuclideanMidpointRigidity.Endpoint

