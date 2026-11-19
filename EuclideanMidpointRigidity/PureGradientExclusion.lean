module

public import EuclideanMidpointRigidity.PureHighRows
public import EuclideanMidpointRigidity.ExternalEigenbasis
public import EuclideanMidpointRigidity.AmplitudeRates
public import EuclideanMidpointRigidity.MaximumSpectrum

/-! # Exclusion of either persistent pure gradient at a lifted maximum -/

@[expose] public section
noncomputable section
open Filter
open scoped InnerProductSpace ContDiff Topology
namespace EuclideanMidpointRigidity.LiftedSection.PureAt
open Quartic
variable {d : ℕ} {S : LiftedSection d} {p : Space d} {r : PureResonance}
local notation "E" => Space d

theorem axis_normal (h : S.PureAt r p) (l : E) : ⟪S.axis p,S.pureAxisDerivative p l⟫_ℝ=0 := by
  have de := (S.smoothAxis.contDiffAt (S.isOpen.mem_nhds h.mem)).differentiableAt (by simp)
  have hn : ∀ᶠ q in 𝓝 p, ‖S.axis q‖=1 :=
    (show ∀ᶠ q in 𝓝 p, q ∈ S.domain from S.isOpen.mem_nhds h.mem).mono fun q hq ↦ S.unit q hq
  have q := stationary_inner_derivative de de (hn.mono fun q hq ↦ show ⟪S.axis q,S.axis q⟫_ℝ=1 by
    rw [real_inner_self_eq_norm_sq,hq]; norm_num) l
  rw [show ⟪fderiv ℝ S.axis p l,S.axis p⟫_ℝ=⟪S.axis p,fderiv ℝ S.axis p l⟫_ℝ from real_inner_comm _ _] at q
  rw [pureAxisDerivative,real_inner_smul_right,show ⟪S.axis p,fderiv ℝ S.axis p l⟫_ℝ=0 by linarith only [q],mul_zero]

theorem leading (h : S.PureAt r p) : r.Leading (S.cubic p) (S.pureJet p) (S.axis p) (S.gradUnit p) := by
  have hf : K (S.field p) (S.axis p) (S.gradUnit p)=(r.b*S.a p) • S.gradUnit p := h.extension.2.self_of_nhds
  have q := PureChannel.diagonal_zero (h.channel_equations hf)
  have hfe := inner_eq_zero_symm.mp h.frame.1
  obtain ⟨hg,hU⟩ := h.first_data
  refine ⟨?_,?_,?_,q,?_,?_,?_⟩
  all_goals simp only [cubicEntry,jetEntry,S.normalized_axis h.mem,h.frame.1,h.frame.2.1,hg,hU,hfe,
    one_smul,real_inner_smul_left,real_inner_self_eq_norm_sq,h.unit,S.unit p h.mem] <;> ring

theorem channel_product (h : S.PureAt r p) {w : E} {s : ℝ} (hor : ⟪S.axis p,w⟫_ℝ=0)
    (hw : K (S.field p) (S.axis p) w=(s*S.a p) • w) :
    let v := S.pureChannel p w
    v.q*⟪w,S.pureAxisDerivative p (S.gradUnit p)⟫_ℝ=v.q*v.y/(1-2*s) := by
  have hc := h.axis_coordinate hor hw (S.gradUnit p)
  rw [show ⟪S.pureAxisDerivative p (S.gradUnit p),w⟫_ℝ=⟪w,S.pureAxisDerivative p (S.gradUnit p)⟫_ℝ from
    real_inner_comm _ _] at hc
  dsimp only
  by_cases he : 1-2*s=0
  · have hs : s=1/2 := by linarith
    have heq := h.channel_equations hw
    rw [hs] at heq
    rw [PureChannel.half_zero heq,zero_mul,zero_mul,zero_div]
  · change (1-2*s)*_=(S.pureChannel p w).y at hc
    rw [← hc]
    field_simp

private theorem impossible_in_basis {ι : Type*} [Fintype ι] (h : S.PureAt r p)
    (B : OrthonormalBasis (Fin 2 ⊕ ι) ℝ E) (s : ι → ℝ)
    (hi : ∀ j, B (.inl j)=![S.axis p,S.gradUnit p] j)
    (ho : ∀ j, K (S.field p) (S.axis p) (B (.inr j))=(s j*S.a p) • B (.inr j))
    (hs : ∀ j, s j≤1/2) : False := by
  let e := S.axis p
  let f := S.gradUnit p
  let c := S.cubic p
  let J := S.pureJet p
  let w := fun j ↦ B (.inr j)
  let v := fun j ↦ S.pureChannel p (w j)
  let A := S.pureAxisDerivative p f
  let H := jetEntry J f e f f
  have e0 : B (.inl 0)=e := hi 0
  have e1 : B (.inl 1)=f := hi 1
  have hew (j : ι) : ⟪e,w j⟫_ℝ=0 := by
    rw [← e0]; exact B.orthonormal.inner_eq_zero (by simp [w])
  have hfw (j : ι) : ⟪f,w j⟫_ℝ=0 := by
    rw [← e1]; exact B.orthonormal.inner_eq_zero (by simp [w])
  have hff : ⟪f,f⟫_ℝ=1 := by rw [real_inner_self_eq_norm_sq,h.unit]; norm_num
  have L : r.Leading c J e f := h.leading
  have high := r.sum_high B h.quartic e f
  rw [Fintype.sum_sum_type,Fin.sum_univ_two,e0,e1] at high
  change r.high c J e f e+r.high c J e f f+(∑ j, r.high c J e f (w j))=0 at high
  have ext (j : ι) : r.high c J e f (w j)=r.raw (v j) := by
    apply r.outside_high
    · change ⟪K (S.cubic p) (S.axis p) (S.axis p),w j⟫_ℝ=0
      rw [S.normalized_axis h.mem,one_smul]; exact hew j
    · change ⟪K (S.cubic p) (S.axis p) (S.gradUnit p),w j⟫_ℝ=0
      rw [h.frame.2.1,real_inner_smul_left,hfw j,mul_zero]
  rw [PureResonance.core_high L] at high
  simp only [ext] at high
  have expand := B.sum_inner_mul_inner (K c f f) A
  rw [Fintype.sum_sum_type,Fin.sum_univ_two,e0,e1] at expand
  change cubicEntry c f f e*⟪e,A⟫_ℝ+cubicEntry c f f f*⟪f,A⟫_ℝ+
    (∑ j, (v j).q*⟪w j,A⟫_ℝ)=cubicEntry c f f A at expand
  have normal : ⟪e,A⟫_ℝ=0 := h.axis_normal f
  have prod (j : ι) : (v j).q*⟪w j,A⟫_ℝ=(v j).q*(v j).y/(1-2*s j) := h.channel_product (hew j) (ho j)
  simp only [L.fff,normal,mul_zero,zero_mul,zero_add,prod] at expand
  have tangent := h.diagonal_rate f
  change H=r.b*⟪f,f⟫_ℝ-cubicEntry c f f A at tangent
  rw [hff,mul_one,← expand] at tangent
  have plus : 0≤∑ j, (v j).cost r (s j) := Finset.sum_nonneg fun j _ ↦
    PureChannel.cost_nonnegative (hs j) (h.channel_equations (ho j))
  simp only [PureResonance.cost_eq,Finset.sum_add_distrib,← Finset.mul_sum] at plus
  change r.offset-r.slopeWeight*H+(∑ j, r.raw (v j))=0 at high
  rw [tangent] at high
  linarith only [high,plus,r.offset_pos]

theorem impossible (h : S.PureAt r p) (hmax : ∀ z : E, ‖z‖=1 → ⟪K (S.field p) z z,z⟫_ℝ≤S.a p) : False := by
  let V : Fin 2 → E := ![S.axis p,S.gradUnit p]
  let eig : Fin 2 → ℝ := ![1,r.b]
  let T : E →ₗ[ℝ] E := ((S.cubic p).val (S.axis p)).toLinearMap
  have hon : Orthonormal ℝ V := by
    simp [V,orthonormal_vecCons_iff,Fin.forall_fin_succ,h.unit,S.unit p h.mem,h.frame.1]
  have he (i : Fin 2) : T (V i)=eig i • V i := by
    fin_cases i
    · exact S.normalized_axis h.mem
    · exact h.frame.2.1
  obtain ⟨n,B,s,hi,ho⟩ := extend_orthonormal_eigenvectors T (K_selfAdjoint _ _) V eig hon he
  have ha : 0<S.a p := S.positive p h.mem
  have hc : S.field p=S.a p • S.cubic p := by simp [cubic,smul_smul,ha.ne']
  have hp (j : Fin n) : K (S.field p) (S.axis p) (B (.inr j))=(s j*S.a p) • B (.inr j) := by
    rw [hc,K_smul_coeff,show K (S.cubic p) (S.axis p) (B (.inr j))=_ from ho j,smul_smul,mul_comm]
  apply h.impossible_in_basis B s hi hp
  intro j
  have e₀ : B (.inl 0)=S.axis p := hi 0
  have hw : ‖B (.inr j)‖=1 := B.orthonormal.norm_eq_one _
  have hw₀ : ⟪S.axis p,B (.inr j)⟫_ℝ=0 := e₀ ▸ B.orthonormal.inner_eq_zero (by simp)
  have hb := maximizing_axis_spectral_bounds ha.le hmax (S.unit p h.mem) hw hw₀
    (show ⟪K (S.field p) (S.axis p) (S.axis p),S.axis p⟫_ℝ=S.a p from rfl)
  rw [hp,real_inner_smul_left,real_inner_self_eq_norm_sq,hw,one_pow,mul_one] at hb
  apply le_of_mul_le_mul_right (a := S.a p) _ ha
  linarith only [hb.2]

end EuclideanMidpointRigidity.LiftedSection.PureAt

