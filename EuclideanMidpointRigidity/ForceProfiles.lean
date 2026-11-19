module

public import EuclideanMidpointRigidity.ForceExpansion
public import EuclideanMidpointRigidity.Trajectory

/-! # Identifying the signed Dirichlet forcing with the spatial Taylor force -/

@[expose] public section
noncomputable section
open Set
namespace EuclideanMidpointRigidity.Jet

variable {d : ℕ}
local notation "E" => Space d

def forceTerm (σ : ℚ) (paths : List TimePolynomial) (s : ℕ) (ds : List ℕ) : TimePolynomial :=
  let ps := (ds.take s).map fun j ↦ paths[j]?.getD []
  match ds.drop s with
  | [i,j] => scale (-σ/(s.factorial:ℚ))
      (applyProduct ps (differentiate (paths[i]?.getD [])) (differentiate (paths[j]?.getD [])))
  | _ => []

theorem forceTerm_value (σ : ℚ) (paths : List TimePolynomial) (s : ℕ) (ds : List ℕ)
    (hs : s≤4) (D : Derivatives d) (z : E) (t : ℝ) :
    let f := Tree.realize D z
    value (forceTerm σ paths s ds) f t =
      forceValue σ D (positionCoefficient paths f t) (velocityCoefficient paths f t) (s,ds) := by
  have hlen : ((ds.take s).map fun j ↦ paths[j]?.getD []).length ≤ 4 :=
    (List.length_map ..).le.trans ((List.length_take_le ..).trans hs)
  simp only [forceTerm,forceValue,tupleValue]
  generalize ds.drop s = tail
  rcases tail with _ | ⟨i,tail⟩
  · simp [value]
  rcases tail with _ | ⟨j,tail⟩
  · simp [value]
  rcases tail with _ | ⟨k,tail⟩
  · rw [value_scale, value_applyProduct _ _ _ hlen D z t]
    simp [List.map_map, Function.comp_def, velocityCoefficient]
    rfl
  · simp [value]

theorem value_flatMap {V α : Type*} [AddCommGroup V] [Module ℝ V]
    (items : List α) (g : α → TimePolynomial) (f : Tree → V) (t : ℝ) :
    value (items.flatMap g) f t = (items.map (fun a ↦ value (g a) f t)).sum := by
  simp [value,List.map_flatMap,sum_flatMap_eq]

theorem forcing_value (σ : ℚ) (paths : List TimePolynomial) (n : ℕ) (hn : n≤6)
    (D : Derivatives d) (z : E) (t : ℝ) :
    let f := Tree.realize D z
    value (forcing σ paths n) f t = degreeCoefficient (forceIndices 6 4) forceDegree
      (forceValue σ D (positionCoefficient paths f t) (velocityCoefficient paths f t)) n := by
  let f := Tree.realize D z
  change value (collect ((List.range (n-1)).flatMap fun s ↦
    (compositions n (s+2)).flatMap (forceTerm σ paths s))) f t = _
  rw [value_collect, value_flatMap, degreeCoefficient_force _ n hn]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s hs
  rw [value_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ds _
  exact forceTerm_value σ paths s ds (by have := List.mem_range.mp hs; omega) D z t

/-- Every term, including those above degree six, is a continuous time
polynomial. This gives a uniform remainder on the entire Dirichlet interval. -/
theorem continuous_forceValue (σ : ℚ) (paths : List TimePolynomial) (D : Derivatives d)
    (z : E) {a : ℕ × List ℕ} (ha : a ∈ forceIndices 6 4) :
    let f := Tree.realize D z
    Continuous (fun t ↦ forceValue σ D (positionCoefficient paths f t) (velocityCoefficient paths f t) a) := by
  rcases a with ⟨s,ds⟩
  rw [forceIndices_eq] at ha
  obtain ⟨s',hs',hds⟩ := List.mem_flatMap.mp ha
  obtain ⟨ds',_,he⟩ := List.mem_map.mp hds
  have hs : s≤4 := by
    have heq := congrArg Prod.fst he
    change s'=s at heq
    have := List.mem_range.mp hs'
    omega
  apply continuous_iff_continuousAt.mpr
  intro t
  simpa only [← forceTerm_value σ paths s ds hs D z] using
    (hasDerivAt_value (forceTerm σ paths s ds) (Tree.realize D z) t).continuousAt

end EuclideanMidpointRigidity.Jet
