module

public import EuclideanMidpointRigidity.RulingAnnihilator

/-! # A real-split ordinary differential equation for the entire cubic on each ruling -/

@[expose] public section
noncomputable section
open Set Filter Polynomial
open scoped ContDiff InnerProductSpace Topology
namespace EuclideanMidpointRigidity
open Endpoint Quartic
variable {d : ℕ}
local notation "E" => Space d

def entryFunctional (x y z : E) : Cubic d →L[ℝ] ℝ :=
  (innerSL ℝ z).comp ((ContinuousLinearMap.apply ℝ E y).comp
    ((ContinuousLinearMap.apply ℝ (E →L[ℝ] E) x).comp (cubicSubspace d).subtypeL))

theorem entryFunctional_eq (x y z : E) (A : Cubic d) : entryFunctional x y z A=cubicEntry A x y z := by
  change ⟪z,K A x y⟫_ℝ=⟪K A x y,z⟫_ℝ
  exact real_inner_comm _ _

theorem cubic_zero_of_frame {ι : Type*} [Fintype ι] (B : OrthonormalBasis ι ℝ E) {A : Cubic d}
    (h : ∀ i j k, entryFunctional (B i) (B j) (B k) A=0) : A=0 := by
  have he (i : ι) : A.val (B i)=0 := operator_zero_of_entries B (fun k j ↦ h i j k)
  apply Subtype.ext
  ext x : 1
  change A.val x=0
  rw [← B.sum_repr' x,map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_smul,he]
  ext v : 1
  change ⟪B i,x⟫_ℝ • (0:E)=0
  exact smul_zero _

theorem solvesOn_of_separating {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {ι : Type*}
    {W : Set ℝ} {f : ℝ → V} {A : ℝ[X]} (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W) (L : ι → V →L[ℝ] ℝ)
    (hsep : ∀ v, (∀ i, L i v=0) → v=0) (h : ∀ i, SolvesOn hW A (L i ∘ f)) : SolvesOn hW A f := by
  apply (solvesOn_iff_sum hf (Nat.lt_succ_self _)).mpr
  intro t ht
  apply hsep
  intro i
  have h' := (solvesOn_iff_sum (h i).smooth (Nat.lt_succ_self _)).mp (h i) t ht
  have he (n : ℕ) : iteratedDeriv n (L i ∘ f) t=L i (iteratedDeriv n f t) := by
    rw [iteratedDeriv_eq_iteratedFDeriv,(L i).iteratedFDeriv_comp_left (hf.contDiffAt (hW.mem_nhds ht)) (by simp)]
    rfl
  simpa only [map_sum,map_smul,he] using h'

theorem LiftedSection.tensor_ruling_ode (S : LiftedSection d) {p : E} (hp : p ∈ S.domain)
    (hm : ∀ q ∈ S.domain, S.Maximizes q) (hc : ∀ q ∈ S.domain, Nonempty (OrientedEndpointChart S.field q)) :
    (S.rulingPolynomial p).Splits ∧ ∃ W : Set ℝ, ∃ hW : IsOpen W, 0 ∈ W ∧
      SolvesOn hW (S.rulingPolynomial p) (fun t ↦ S.field (p+t • S.axialDirection p)) := by
  obtain ⟨n,⟨F⟩⟩ := S.exists_ruling_frame hp (hm p hp)
  let ι := Unit ⊕ Fin n
  let u := S.axialDirection p
  let line := fun t : ℝ ↦ p+t • u
  obtain ⟨U,hU,h₁,hr⟩ := S.ruling_responses hp hm hc
  obtain ⟨V,hV,h₂,hj⟩ := S.line_recovery hp hm
  obtain ⟨Z,hZ,h₃,hz⟩ := S.local_normalized_line hp hm
  let W := (U ∩ V) ∩ Z
  have hW : IsOpen W := (hU.inter hV).inter hZ
  have hC : ContDiffOn ℝ ∞ (fun t ↦ S.field (line t)) W :=
    S.smooth.comp (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn (fun t ht ↦ (hz t ht.2).1)
  refine ⟨F.rulingPolynomial_splits hp,W,hW,⟨⟨h₁,h₂⟩,h₃⟩,?_⟩
  let A := S.entryDerivativePolynomial p
  let φ := fun i j k : ι ↦ lineEntry S.field p u (F.basis i) (F.basis j) (F.basis k)
  let P := fun i j k : ι ↦ tiltSource S.field p u (F.basis i) (F.basis j) (F.basis k)
  have hP (i j k : ι) (hne : j≠F.axial) : SolvesOn hW A (P i j k) := by
    have H := hr (F.basis i) (F.basis j) (F.basis k) _ _ (F.eigen j) (F.eigen k)
    exact ((H.solves_tilt hU).of_dvd (F.tilt_dvd hp hne)).mono hW (fun _ ht ↦ ht.1.1)
  have hφ (i j k : ι) : SolvesOn hW (S.rulingPolynomial p) (φ i j k) := by
    let L := entryFunctional (F.basis i) (F.basis j) (F.basis k)
    have eφ : φ i j k=L ∘ (fun t ↦ S.field (line t)) := funext fun t ↦ (entryFunctional_eq _ _ _ _).symm
    have hsm : ContDiffOn ℝ ∞ (φ i j k) W := eφ ▸ L.contDiff.comp_contDiffOn hC
    rw [← S.entryDerivativePolynomial_mul_X]
    apply SolvesOn.integrate hsm
    by_cases hav : i=F.axial ∨ j=F.axial ∨ k=F.axial
    · apply (solvesOn_zero hW A).congr
      intro t ht
      obtain ⟨hdom,hu,_⟩ := hz t ht.2
      have hder := (hasDerivAt_lineEntry S.isOpen S.smooth p u (F.basis i) (F.basis j) (F.basis k) t hdom).deriv
      change 0=deriv (lineEntry S.field p u (F.basis i) (F.basis j) (F.basis k)) t
      rw [hder]
      let J := fderiv ℝ S.field (line t)
      have hrule := (S.normalized_line_data hdom hm).2.2
      rw [hu] at hrule
      have hex : F.basis F.axial=S.a p • u := by
        rw [F.axis_eq]
        change S.axis p=S.a p • ((S.a p)⁻¹ • S.axis p)
        have ha : S.a p≠0 := (S.positive p hp).ne'
        rw [smul_smul,mul_inv_cancel₀ ha,one_smul]
      have zero (v w : E) : jetEntry J u (F.basis F.axial) v w=0 := by
        simp only [jetEntry,cubicEntry,hex,K_smul_left,show ∀ v, K (J u) u v=0 from hrule,smul_zero,inner_zero_left]
      change 0=jetEntry J u _ _ _
      rcases hav with hi|hj|hk
      · rw [hi,zero]
      · rw [jetEntry_swap₁ J u (F.basis i),hj,zero]
      · rw [jetEntry_swap₂ J u (F.basis i),jetEntry_swap₁ J u (F.basis i),hk,zero]
    · have hi : i≠F.axial := fun e ↦ hav (Or.inl e)
      have hj' : j≠F.axial := fun e ↦ hav (Or.inr (Or.inl e))
      have hk : k≠F.axial := fun e ↦ hav (Or.inr (Or.inr e))
      let a := F.value i
      let b := F.value j
      let c := F.value k
      let D := 3*(5-2*(a+b+c))
      let r := 20*a-2*b-2*c-4
      let s := 20*b-2*c-2*a-4
      let v := 20*c-2*a-2*b-4
      have hD : 0<D := by dsimp [D,a,b,c]; linarith [(F.bounds i hi).2,(F.bounds j hj').2,(F.bounds k hk).2]
      apply ((((hP i j k hj').smul r).add ((hP j k i hk).smul s)).add ((hP k i j hi).smul v)).smul (-(D⁻¹)) |>.congr
      intro t ht
      have h := hj t ht.1.2 (F.basis i) (F.basis j) (F.basis k) _ _ _ (F.eigen i) (F.eigen j) (F.eigen k)
      change D*deriv (φ i j k) t+r*P i j k t+s*P j k i t+v*P k i j t=0 at h
      change -(D⁻¹)*(r*P i j k t+s*P j k i t+v*P k i j t)=deriv (φ i j k) t
      field_simp [hD.ne']
      linarith only [h]
  let L := fun a : ι × ι × ι ↦ entryFunctional (F.basis a.1) (F.basis a.2.1) (F.basis a.2.2)
  apply solvesOn_of_separating hW hC L (fun v hv ↦ cubic_zero_of_frame F.basis (fun i j k ↦ hv (i,j,k)))
  intro i
  apply (hφ i.1 i.2.1 i.2.2).congr
  exact fun _ _ ↦ (entryFunctional_eq _ _ _ _).symm

end EuclideanMidpointRigidity

