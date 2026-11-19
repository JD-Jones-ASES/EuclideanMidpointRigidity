module

public import EuclideanMidpointRigidity.DirectionalDerivatives
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! # Sections of the span of all derivatives of a Euclidean vector field -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d

def osculatingSpace (e : E → E) (x : E) : Submodule ℝ E :=
  Submodule.span ℝ (range fun xs : List E ↦ directions e xs x)

theorem direction_mem_osculating (e : E → E) (x : E) (xs : List E) : directions e xs x ∈ osculatingSpace e x :=
  Submodule.subset_span ⟨xs,rfl⟩

/-- The value and first derivative of the section both lie in the indicated varying space. -/
structure ParallelSection (W : Set E) (V : E → Submodule ℝ E) (f : E → E) : Prop where
  smooth : ContDiffOn ℝ ∞ f W
  value : ∀ x ∈ W, f x ∈ V x
  tangent : ∀ x ∈ W, ∀ v, fderiv ℝ f x v ∈ V x

namespace ParallelSection
variable {W U : Set (Space d)} {V : Space d → Submodule ℝ (Space d)} {f g : Space d → Space d}

theorem mono (F : ParallelSection W V f) (h : U ⊆ W) : ParallelSection U V f :=
  ⟨F.smooth.mono h,fun x hx ↦ F.value x (h hx),fun x hx ↦ F.tangent x (h hx)⟩

theorem zero : ParallelSection W V (fun _ ↦ 0) :=
  ⟨contDiffOn_const,fun x _ ↦ (V x).zero_mem,fun x _ v ↦ by simp⟩

theorem add (hW : IsOpen W) (F : ParallelSection W V f) (G : ParallelSection W V g) :
    ParallelSection W V (fun x ↦ f x+g x) := by
  refine ⟨F.smooth.add G.smooth,fun x hx ↦ (V x).add_mem (F.value x hx) (G.value x hx),?_⟩
  intro x hx v
  rw [fderiv_fun_add ((F.smooth.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp))
    ((G.smooth.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp))]
  exact (V x).add_mem (F.tangent x hx v) (G.tangent x hx v)

theorem smul (hW : IsOpen W) (F : ParallelSection W V f) {c : E → ℝ} (hc : ContDiffOn ℝ ∞ c W) :
    ParallelSection W V (fun x ↦ c x • f x) := by
  refine ⟨hc.smul F.smooth,fun x hx ↦ (V x).smul_mem _ (F.value x hx),?_⟩
  intro x hx v
  rw [fderiv_fun_smul ((hc.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp))
    ((F.smooth.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp))]
  exact (V x).add_mem ((V x).smul_mem _ (F.tangent x hx v)) ((V x).smul_mem _ (F.value x hx))

theorem sum {ι : Type*} (hW : IsOpen W) (I : Finset ι) (F : ι → E → E)
    (hf : ∀ i ∈ I, ParallelSection W V (F i)) : ParallelSection W V (fun x ↦ ∑ i ∈ I, F i x) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using (zero (W := W) (V := V))
  | insert i I hi ih =>
    simp only [Finset.sum_insert hi]
    exact add hW (hf i (Finset.mem_insert_self ..)) (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

end ParallelSection

theorem osculating_extension {W : Set E} {e : E → E} (hW : IsOpen W) (he : ContDiffOn ℝ ∞ e W)
    (p : E) {v : E} (hv : v ∈ osculatingSpace e p) :
    ∃ f : E → E, f p=v ∧ ParallelSection W (osculatingSpace e) f := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨xs,rfl⟩ := hw
    exact ⟨directions e xs,rfl,directions.smooth hW he xs,fun x _ ↦ direction_mem_osculating e x xs,
      fun x _ l ↦ direction_mem_osculating e x (l::xs)⟩
  | zero => exact ⟨_,rfl,ParallelSection.zero⟩
  | add a b _ _ ha hb =>
    obtain ⟨f,rfl,hf⟩ := ha
    obtain ⟨g,rfl,hg⟩ := hb
    exact ⟨_,rfl,ParallelSection.add hW hf hg⟩
  | smul c v _ ih =>
    obtain ⟨f,rfl,hf⟩ := ih
    exact ⟨fun x ↦ c • f x,rfl,ParallelSection.smul hW hf contDiffOn_const⟩

theorem maximum_dimension_point {W : Set E} (hW : W.Nonempty) (V : E → Submodule ℝ E) :
    ∃ p ∈ W, ∀ x ∈ W, Module.finrank ℝ (V x)≤Module.finrank ℝ (V p) := by
  classical
  obtain ⟨x,hx⟩ := hW
  let P := fun n : ℕ ↦ ∃ y ∈ W, Module.finrank ℝ (V y)=n
  have hn (y : E) : Module.finrank ℝ (V y)≤Module.finrank ℝ E := Submodule.finrank_le _
  obtain ⟨p,hp,hr⟩ := Nat.findGreatest_spec (P := P) (hn x) ⟨x,hx,rfl⟩
  exact ⟨p,hp,fun y hy ↦ hr ▸ Nat.le_findGreatest (P := P) (hn y) ⟨y,hy,rfl⟩⟩

end EuclideanMidpointRigidity

