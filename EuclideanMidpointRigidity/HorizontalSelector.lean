module

public import EuclideanMidpointRigidity.HorizontalMotion

/-! # A maximizing selector whose derivative annihilates the nonresonant directions -/

@[expose] public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d

theorem Horizontal.transport_eigen {c : T} {h v : E} {a b : ℝ} (he : K c h v=b • v) :
    Horizontal.transport c h a v=((2*b+a)*(10*b-2*a)) • v := by
  simp only [transport,tenShift,doubleShift,K_add_right,K_smul_right,he,smul_add,smul_smul]
  module

structure HorizontalPatch (S : LiftedSection d) : Prop where
  maximizes : ∀ q ∈ S.domain, S.Maximizes q
  charts : ∀ q ∈ S.domain, Nonempty (OrientedEndpointChart S.field q)
  horizontal : ∀ q ∈ S.domain, ∀ l, fderiv ℝ S.axis q (Horizontal.transport (S.field q) (S.axis q) (S.a q) l)=0

theorem exists_horizontal_patch {Ω : Set E} {C : E → T} {a : ℝ} (hΩ : IsOpen Ω) (hn : Ω.Nonempty)
    (hC : ContDiffOn ℝ ∞ C Ω) (hQ : MidpointJetEquations Ω C) (hc : ∀ q ∈ Ω, Nonempty (OrientedEndpointChart C q))
    (ha : 0<a) (hamp : ∀ q ∈ Ω, amplitude (C q)=a) :
    ∃ S : LiftedSection d, S.field=C ∧ S.domain.Nonempty ∧ S.domain ⊆ Ω ∧ HorizontalPatch S := by
  classical
  let P := fun k : ℕ ↦ ∃ (U : Set E) (e : E → E), IsOpen U ∧ U.Nonempty ∧ U ⊆ Ω ∧ ContDiffOn ℝ ∞ e U ∧
    ∀ y ∈ U, (‖e y‖=1 ∧ directionProfile (e y) (C y)=a) ∧ derivativeRank e y≤k
  have hP : ∃ k, P k := by
    obtain ⟨U,e,hU,hne,hs,he,hm⟩ := smooth_maximizing_direction_on_subpatch hΩ hn hC (fun q h ↦ (hamp q h).symm ▸ ha)
    exact ⟨Module.finrank ℝ E,U,e,hU,hne,hs,he,fun y hy ↦ ⟨⟨(hm y hy).1,(hm y hy).2.trans (hamp y (hs hy))⟩,Submodule.finrank_le _⟩⟩
  let k := Nat.find hP
  obtain ⟨U,e,hU,hne,hs,he,H⟩ := Nat.find_spec hP
  have hm (q : E) (hq : q ∈ U) := (H q hq).1
  have hh (p : E) (hp : p ∈ U) (l : E) : fderiv ℝ e p (Horizontal.transport (C p) (e p) a l)=0 := by
    by_contra hbad
    obtain ⟨O,X,hO,hpO,hX,h₀,hv,hmove⟩ := Horizontal.fixed_test_motion hU (hC.mono hs) (hQ.mono hs)
      (fun q h ↦ hc q (hs h)) he ha (fun q h ↦ hamp q (hs h)) hm hp l
    let R := fun (q z : E) ↦ q ∈ U ∧ ‖z‖=1 ∧ directionProfile z (C q)=a
    obtain ⟨V,g,hV,hpV,hVU,hg,hr⟩ := selection_rank_drop (R := R) hU he hO hX hp hpO h₀ hv hbad
      (fun q hq ↦ (H q hq).2) hmove
    have hk : 0<k := Nat.zero_le _ |>.trans_lt (hr p hpV).2
    have hnew : P (k-1) := ⟨V,g,hV,⟨p,hpV⟩,hVU.trans hs,hg,fun q hq ↦ ⟨(hr q hq).1.2,Nat.le_pred_of_lt (hr q hq).2⟩⟩
    have hle : k≤k-1 := Nat.find_min' hP hnew
    omega
  have hk (q : E) (hq : q ∈ U) := critical_of_fixed_maximum ha (hamp q (hs hq)) (hm q hq).1 (hm q hq).2
  have hv (q : E) (hq : q ∈ U) : sectionValue C e q=a :=
    (directionProfile_apply (e q) (C q)).symm.trans (hm q hq).2
  have hlift (q : E) (hq : q ∈ U) : fderiv ℝ e q (e q)=liftStep (sectionValue C e q) (fderiv ℝ C q) (e q) := by
    rw [hv q hq,extremal_liftStep_zero hΩ hC hQ.quartic ha.ne' (fun x h ↦ (hamp x h).trans (abs_of_pos ha).symm)
      (hs hq) (hm q hq).1 (hk q hq)]
    have h := hh q hq (e q)
    rw [Horizontal.transport_eigen (hk q hq),map_smul] at h
    exact (smul_eq_zero.mp h).resolve_left (by apply mul_ne_zero <;> nlinarith)
  let S : LiftedSection d := ⟨U,C,e,hU,hC.mono hs,he,hQ.mono hs,fun q h ↦ (hm q h).1,
    fun q h ↦ by rw [hv q h]; exact hk q h,fun q h ↦ (hv q h).symm ▸ ha,hlift⟩
  refine ⟨S,rfl,hne,hs,⟨?_,fun q h ↦ hc q (hs h),?_⟩⟩
  · intro q hq z hz
    change ⟪K (C q) z z,z⟫_ℝ≤sectionValue C e q
    rw [hv q hq,← hamp q (hs hq),← directionProfile_apply]
    exact directionProfile_le_amplitude (by simp [mem_closedBall,dist_zero_right,hz]) _
  · intro q hq l
    change fderiv ℝ e q (Horizontal.transport (C q) (e q) (sectionValue C e q) l)=0
    rw [hv q hq]; exact hh q hq l

namespace HorizontalPatch
variable {S : LiftedSection d} (H : HorizontalPatch S)
include H

theorem annihilates_eigen {p : E} (hp : p ∈ S.domain) {v : E} {b : ℝ} (he : K (S.field p) (S.axis p) v=b • v)
    (hn : (2*b+S.a p)*(10*b-2*S.a p)≠0) : fderiv ℝ S.axis p v=0 := by
  have hh := H.horizontal p hp v
  rw [Horizontal.transport_eigen he,map_smul] at hh
  exact (smul_eq_zero.mp hh).resolve_left hn

theorem square_zero {p : E} (hp : p ∈ S.domain) (l : E) : fderiv ℝ S.axis p (fderiv ℝ S.axis p l)=0 := by
  let v := fderiv ℝ S.axis p l
  have he := (S.weighted_ruling hp H.maximizes).2.1 l
  change K ((S.a p)⁻¹ • S.field p) (S.axis p) v=(1/2:ℝ) • v at he
  rw [K_smul_coeff] at he
  have h := congrArg (fun z : E ↦ S.a p • z) he
  have ha : 0<S.a p := S.positive p hp
  simp only [smul_smul,mul_inv_cancel₀ ha.ne',one_smul] at h
  exact H.annihilates_eigen (v := v) (b := S.a p*(1/2)) hp h (by apply mul_ne_zero <;> nlinarith)

end HorizontalPatch
end EuclideanMidpointRigidity

