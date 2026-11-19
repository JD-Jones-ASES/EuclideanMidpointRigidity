module

public import EuclideanMidpointRigidity.JetInterpretation
public import EuclideanMidpointRigidity.MultilinearExpansion
public import EuclideanMidpointRigidity.SmoothFieldExtension

/-! # Spatial dilation of the fourth- and sixth-order midpoint coefficients -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.Jet
variable {d : ℕ}
local notation "E" => Space d
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency false
local instance (d : ℕ) : AddMonoid (Cubic d) :=
  (cubicNormedAddCommGroup d).toAddCommGroup.toAddCommMonoid.toAddMonoid

theorem dilation_jets {U : Set E} {G F : E → Cubic d} {b z : E} {r : ℝ} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) (hp : b+r • z ∈ U) (hF : F =ᶠ[𝓝 z] (fun w ↦ G (b+r • w))) (n : ℕ) :
    fieldDerivatives F z n=r^n • fieldDerivatives G (b+r • z) n := by
  obtain ⟨g,hg,he⟩ := local_smooth_representative hU hG hp
  have hl : ContinuousAt (fun w : E ↦ b+r • w) z := by fun_prop
  have hf : F =ᶠ[𝓝 z] (fun w ↦ g (b+r • w)) :=
    hF.trans (he.symm.comp_tendsto hl.tendsto)
  have hd := (hf.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds
  have hT : ContDiff ℝ n (fun x ↦ g (b+x)) := (hg.comp (contDiff_const.add contDiff_id)).of_le (by simp)
  have hs := congrFun (iteratedFDeriv_comp_const_smul r hT) z
  rw [iteratedFDeriv_comp_add_left] at hs
  exact hd.trans (hs.trans (by rw [(he.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds]; rfl))

def Tree.spatialOrder : Tree → ℕ
  | .direction => 0
  | .k u v => u.spatialOrder+v.spatialOrder
  | .j p u v => 1+p.spatialOrder+u.spatialOrder+v.spatialOrder
  | .hess p q u v => 2+p.spatialOrder+q.spatialOrder+u.spatialOrder+v.spatialOrder
  | .third p q s u v => 3+p.spatialOrder+q.spatialOrder+s.spatialOrder+u.spatialOrder+v.spatialOrder
  | .fourth p q s t u v => 4+p.spatialOrder+q.spatialOrder+s.spatialOrder+t.spatialOrder+u.spatialOrder+v.spatialOrder

private theorem list_dilate {D' D : Derivatives d} {r : ℝ} (hd : ∀ n, D' n=r^n • D n) (xs : List E) :
    listForm D' xs=r^xs.length • listForm D xs := by
  simp only [listForm,symmetricPart_apply,hd,smul_apply,← Finset.smul_sum]
  rw [smul_comm]

private theorem slot0 (D : Derivatives d) (v : E) (s : ℝ) (xs : List E) :
    listForm D ((s • v)::xs)=s • listForm D (v::xs) :=
  listForm_middle_smul D [] xs s v

private theorem slot1 (D : Derivatives d) (x0 v : E) (s : ℝ) (xs : List E) :
    listForm D (x0::(s • v)::xs)=s • listForm D (x0::v::xs) :=
  listForm_middle_smul D [x0] xs s v

private theorem slot2 (D : Derivatives d) (x0 x1 v : E) (s : ℝ) (xs : List E) :
    listForm D (x0::x1::(s • v)::xs)=s • listForm D (x0::x1::v::xs) :=
  listForm_middle_smul D [x0,x1] xs s v

private theorem slot3 (D : Derivatives d) (x0 x1 x2 v : E) (s : ℝ) (xs : List E) :
    listForm D (x0::x1::x2::(s • v)::xs)=s • listForm D (x0::x1::x2::v::xs) :=
  listForm_middle_smul D [x0,x1,x2] xs s v

theorem Tree.realize_dilation {D' D : Derivatives d} {r : ℝ} (hd : ∀ n, D' n=r^n • D n) (h : E) (t : Tree) :
    t.realize D' h=r^t.spatialOrder • t.realize D h := by
  induction t <;> simp only [Tree.realize,Tree.spatialOrder, *, list_dilate hd,slot0,slot1,slot2,slot3,
    List.length_nil,List.length_cons,K_smul_coeff,K_smul_left,K_smul_right,smul_smul,pow_add,pow_zero,one_smul]
    <;> first | rfl | (congr 1 <;> ring)

theorem value_dilation {D' D : Derivatives d} {r : ℝ} (hd : ∀ n, D' n=r^n • D n) (h : E) (P : TimePolynomial)
    (k : ℕ) (hk : ∀ m ∈ P, m.tree.spatialOrder=k) :
    value P (Tree.realize D' h) 0=r^k • value P (Tree.realize D h) 0 := by
  induction P with
  | nil => simp [value]
  | cons m ms ih =>
    change m.value _ 0+value ms _ 0=r^k • (m.value _ 0+value ms _ 0)
    rw [ih (fun n hn ↦ hk n (List.mem_cons_of_mem _ hn)),smul_add]
    congr 1
    simp only [Term.value,Tree.realize_dilation hd h m.tree,hk m List.mem_cons_self]
    rw [smul_comm]

theorem affineSixth_spatialOrder : ∀ m ∈ affineSixth, m.tree.spatialOrder=1 := by decide
theorem higherSixth_spatialOrder : ∀ m ∈ higherSixth, m.tree.spatialOrder=3 := by decide

end EuclideanMidpointRigidity.Jet

