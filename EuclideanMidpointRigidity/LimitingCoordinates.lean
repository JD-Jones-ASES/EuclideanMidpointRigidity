module

public import EuclideanMidpointRigidity.UnivariateFamilies

/-! # Equations for limits of scaled polynomial roots -/

@[expose] public section
noncomputable section
open Set Filter Polynomial
open scoped Topology
namespace EuclideanMidpointRigidity.SmoothPolynomial

/-- Regard H(t,t z) as a polynomial in t whose coefficients are polynomials in z. -/
def scaledCoordinates {R : Type*} [CommRing R] (H : Polynomial (Polynomial R)) :
    Polynomial (Polynomial R) :=
  H.eval₂ (Polynomial.mapRingHom (Polynomial.C : R →+* Polynomial R))
    (Polynomial.X * Polynomial.C Polynomial.X)

theorem eval_scaledCoordinates {R : Type*} [CommRing R] (H : Polynomial (Polynomial R))
    (φ : R →+* ℝ) (t z : ℝ) :
    (scaledCoordinates H).eval₂ (Polynomial.eval₂RingHom φ z) t =
      H.eval₂ (Polynomial.eval₂RingHom φ t) (t*z) := by
  have hc : (Polynomial.eval₂RingHom φ z).comp Polynomial.C = φ := by ext x; simp
  induction H using Polynomial.induction_on' with
  | add P Q hp hq => simpa only [scaledCoordinates,Polynomial.eval₂_add] using congrArg₂ (·+·) hp hq
  | monomial k a =>
    simp [scaledCoordinates,Polynomial.eval₂_monomial,Polynomial.eval₂_map,hc,
      Polynomial.eval₂_pow,Polynomial.eval₂_mul,Polynomial.coe_eval₂RingHom] <;> left <;> ring

theorem scaledCoordinates_has_coefficient {R : Type*} [CommRing R] {H : Polynomial (Polynomial R)}
    (hm : H.Monic) (φ : R →+* ℝ) :
    ∃ j, ((scaledCoordinates H).coeff j).map φ≠0 := by
  classical
  by_contra h
  push Not at h
  let M := H.map (Polynomial.eval₂RingHom φ (1:ℝ))
  have hM : M=0 := by
    apply Polynomial.funext
    intro z
    have hc : (scaledCoordinates H).map (Polynomial.eval₂RingHom φ z)=0 := by
      ext j
      rw [Polynomial.coeff_map,Polynomial.coeff_zero]
      change ((scaledCoordinates H).coeff j).eval₂ φ z=0
      rw [Polynomial.eval₂_eq_eval_map,h,Polynomial.eval_zero]
    have he := eval_scaledCoordinates H φ 1 z
    rw [Polynomial.eval₂_eq_eval_map,hc,Polynomial.eval_zero,one_mul] at he
    simpa [M,Polynomial.eval_map] using he.symm
  exact (hm.map (Polynomial.eval₂RingHom φ (1:ℝ))).ne_zero hM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {W : Set E}
local notation "A" => SmoothCoefficient W

/-- After shrinking the spatial open set, every convergent branch solving
H(t,t z)=0 at nonzero t has its limit in the zero set of a single
nonzero polynomial with smooth spatial coefficients. -/
theorem limiting_coordinate_polynomial {H : Polynomial (Polynomial A)} (hm : H.Monic)
    {U : Set E} (hU : IsOpen U) (hn : U.Nonempty) (hUW : U ⊆ W) :
    ∃ (V : Set E) (q : Polynomial A), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      (∀ x ∈ V, fiber q x≠0) ∧ ∀ x ∈ V, ∀ (t z : ℕ → ℝ) (w : ℝ),
        Tendsto t atTop (𝓝 0) → Tendsto z atTop (𝓝 w) → (∀ j, t j≠0) →
        (∀ j, H.eval₂ (Polynomial.eval₂RingHom (evaluateCoefficient x) (t j)) (t j*z j)=0) →
        (fiber q x).eval w=0 := by
  classical
  let P := scaledCoordinates H
  have hex : ∃ j, ∃ x ∈ U, fiber (P.coeff j) x≠0 := by
    obtain ⟨x,hx⟩ := hn
    obtain ⟨j,hj⟩ := scaledCoordinates_has_coefficient hm (evaluateCoefficient (W := W) x)
    exact ⟨j,x,hx,hj⟩
  let r := Nat.find hex
  obtain ⟨p,hp,hr⟩ := Nat.find_spec hex
  change fiber (P.coeff r) p≠0 at hr
  have low {j : ℕ} (hj : j<r) {x : E} (hx : x ∈ U) : fiber (P.coeff j) x=0 := by
    by_contra hne
    exact Nat.find_min hex hj ⟨x,hx,hne⟩
  obtain ⟨b,hb⟩ : ∃ b, (fiber (P.coeff r) p).coeff b≠0 := by
    by_contra h
    push Not at h
    apply hr
    ext j
    exact (h j).trans (Polynomial.coeff_zero j).symm
  let F := ((P.coeff r).coeff b).val
  let V := U ∩ F ⁻¹' ({0}ᶜ : Set ℝ)
  have hV : IsOpen V := (((P.coeff r).coeff b).property.continuousOn.mono hUW).isOpen_inter_preimage
    hU isClosed_singleton.isOpen_compl
  have hcoeff (x : E) : (fiber (P.coeff r) x).coeff b=F x := Polynomial.coeff_map ..
  refine ⟨V,P.coeff r,hV,⟨p,hp,by change F p≠0; simpa only [hcoeff] using hb⟩,inter_subset_left,?_,?_⟩
  · intro x hx h
    have h₀ := congrArg (fun q : Polynomial ℝ ↦ q.coeff b) h
    exact hx.2 (by change F x=0; simpa only [hcoeff,Polynomial.coeff_zero] using h₀)
  intro x hx t z w ht hz ht₀ hroot
  let Q := fun j ↦ fiber (P.coeff j) x
  let G := fun u : ℝ × ℝ ↦ ∑ j ∈ P.support, if r≤j then (Q j).eval u.2*u.1^(j-r) else 0
  have hG : Continuous G := by
    apply continuous_finsetSum
    intro j _
    by_cases h : r≤j
    · simp only [ite_eq_left h]
      exact ((Q j).continuous.comp continuous_snd).mul (continuous_fst.pow _)
    · simp only [ite_eq_right h]
      exact continuous_const
  have atzero : G (0,w)=(Q r).eval w := by
    dsimp only [G]
    rw [Finset.sum_eq_single r]
    · simp
    · intro j _ hj
      by_cases h : r≤j
      · have hpos : j-r≠0 := by omega
        simp [h,hpos]
      · simp [h]
    · intro h
      have he : P.coeff r=0 := Polynomial.notMem_support_iff.mp h
      simp [Q,fiber,he]
  have hdiv (j : ℕ) : G (t j,z j)=0 := by
    have he := (eval_scaledCoordinates H (evaluateCoefficient x) (t j) (z j)).trans (hroot j)
    have hf : (t j)^r*G (t j,z j)=P.eval₂ (Polynomial.eval₂RingHom (evaluateCoefficient x) (z j)) (t j) := by
      rw [Polynomial.eval₂_eq_sum]
      change (t j)^r*(∑ k ∈ P.support, _) = ∑ k ∈ P.support, _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      have hk : Polynomial.eval₂RingHom (evaluateCoefficient x) (z j) (P.coeff k)=(Q k).eval (z j) := by
        exact Polynomial.eval₂_eq_eval_map _
      change (t j)^r*(if r≤k then (Q k).eval (z j)*(t j)^(k-r) else 0) =
        Polynomial.eval₂RingHom (evaluateCoefficient x) (z j) (P.coeff k)*(t j)^k
      rw [hk]
      by_cases h : r≤k
      · rw [ite_eq_left h,show t j^k=t j^r*t j^(k-r) by rw [← pow_add,Nat.add_sub_of_le h]]
        ring
      · have hq : Q k=0 := low (lt_of_not_ge h) hx.1
        simp [h,hq]
    exact (mul_eq_zero.mp (hf.trans he)).resolve_left (pow_ne_zero _ (ht₀ j))
  have htend := hG.continuousAt.tendsto.comp (ht.prodMk_nhds hz)
  have hlim : Tendsto (fun j ↦ G (t j,z j)) atTop (𝓝 (G (0,w))) := htend
  have h₀ : Tendsto (fun j ↦ G (t j,z j)) atTop (𝓝 0) := by
    simpa only [hdiv] using (show Tendsto (fun _ : ℕ ↦ (0:ℝ)) atTop (𝓝 0) from tendsto_const_nhds)
  rw [← atzero]
  exact tendsto_nhds_unique hlim h₀

end EuclideanMidpointRigidity.SmoothPolynomial

