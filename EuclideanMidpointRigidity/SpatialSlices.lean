module

public import EuclideanMidpointRigidity.DilatedJets

/-! # Continuity of the spatial jets of a smooth parameter family -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.Jet
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem smooth_family_spatial_jets {U : Set (ℝ × E)} {F : ℝ × E → T} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (n : ℕ) :
    ContinuousOn (fun q : ℝ × E ↦ fieldDerivatives (fun z ↦ F (q.1,z)) q.2 n) U := by
  let L := ContinuousLinearMap.inr ℝ ℝ E
  let M : SpatialForm (ℝ × E) T n →L[ℝ] SpatialForm E T n := ContinuousMultilinearMap.compContinuousLinearMapL (fun _ ↦ L)
  have hc : ContinuousOn (fun q ↦ M (iteratedFDeriv ℝ n F q)) U :=
    M.continuous.comp_continuousOn (ContinuousOn.continuousOn_iteratedFDeriv hF hU (by simp))
  apply hc.congr
  intro q hq
  obtain ⟨g,hg,he⟩ := local_smooth_representative hU hF hq
  let b : ℝ × E := (q.1,0)
  have hi : ContinuousAt (fun z : E ↦ (q.1,z)) q.2 := continuousAt_const.prodMk continuousAt_id
  have hh : (fun z ↦ g (q.1,z)) =ᶠ[𝓝 q.2] (fun z ↦ F (q.1,z)) := he.comp_tendsto hi.tendsto
  change iteratedFDeriv ℝ n (fun z ↦ F (q.1,z)) q.2=M (iteratedFDeriv ℝ n F q)
  rw [← (hh.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds,← (he.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds]
  have hb (z : E) : b+L z=(q.1,z) := by ext <;> simp [b,L]
  have heq : (fun z ↦ g (q.1,z))=(fun x ↦ g (b+x)) ∘ L := funext fun z ↦ congrArg g (hb z).symm
  have hshift : ContDiff ℝ ∞ (fun x ↦ g (b+x)) := hg.comp (contDiff_const.add contDiff_id)
  rw [heq,L.iteratedFDeriv_comp_right hshift _ (i := n) (by simp),iteratedFDeriv_comp_add_left,hb]
  rfl

theorem continuous_realizations {Y : Type} [TopologicalSpace Y] {W : Set Y} {D : Y → Derivatives d}
    (hD : ∀ n, ContinuousOn (fun y ↦ D y n) W) (v : E) (t : Tree) : ContinuousOn (fun y ↦ t.realize (D y) v) W := by
  have hK {a : Y → T} {b c : Y → E} (ha : ContinuousOn a W) (hb : ContinuousOn b W) (hc : ContinuousOn c W) :
      ContinuousOn (fun y ↦ K (a y) (b y) (c y)) W := by
    let I : T →L[ℝ] (E →L[ℝ] E →L[ℝ] E) := (cubicSubspace d).subtypeL
    exact ((I.continuous.comp_continuousOn ha).clm_apply hb).clm_apply hc
  have hlist {n : ℕ} (f : Fin n → Y → E) (hf : ∀ i, ContinuousOn (f i) W) :
      ContinuousOn (fun y ↦ symmetricPart (D y n) (fun i ↦ f i y)) W := by
    simp only [symmetricPart_apply]
    apply (continuousOn_const (c := (Fintype.card (Equiv.Perm (Fin n)):ℝ)⁻¹)).smul
    apply continuousOn_finsetSum
    intro σ _
    apply (hD n).eval
    exact continuousOn_pi.mpr fun i ↦ hf (σ i)
  induction t with
  | direction => exact continuousOn_const
  | k a b ha hb =>
    apply hK _ ha hb
    exact hlist (n := 0) (fun i _ ↦ ([] : List E).get i) (fun i ↦ Fin.elim0 i)
  | j p a b hp ha hb =>
    apply hK _ ha hb
    apply hlist (n := 1) (fun i y ↦ [p.realize (D y) v].get i)
    intro i; fin_cases i; assumption
  | hess p q a b hp hq ha hb =>
    apply hK _ ha hb
    apply hlist (n := 2) (fun i y ↦ [p.realize (D y) v,q.realize (D y) v].get i)
    intro i; fin_cases i <;> assumption
  | third p q s a b hp hq hs ha hb =>
    apply hK _ ha hb
    apply hlist (n := 3) (fun i y ↦ [p.realize (D y) v,q.realize (D y) v,s.realize (D y) v].get i)
    intro i; fin_cases i <;> assumption
  | fourth p q s t a b hp hq hs ht ha hb =>
    apply hK _ ha hb
    apply hlist (n := 4) (fun i y ↦ [p.realize (D y) v,q.realize (D y) v,s.realize (D y) v,t.realize (D y) v].get i)
    intro i; fin_cases i <;> assumption

theorem smooth_family_spatial_value {U : Set (ℝ × E)} {F : ℝ × E → T} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (P : TimePolynomial) (v : E) : ContinuousOn (fun q : ℝ × E ↦ value P (Tree.realize (fieldDerivatives (fun z ↦ F (q.1,z)) q.2) v) 0) U := by
  induction P with
  | nil => exact continuousOn_const
  | cons m ms ih => exact ((continuousOn_const (c := (m.coeff:ℝ)*(0:ℝ)^m.power)).smul (continuous_realizations (smooth_family_spatial_jets hU hF) v m.tree)).add ih

end EuclideanMidpointRigidity.Jet

