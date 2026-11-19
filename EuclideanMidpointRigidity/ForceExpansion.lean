module

public import EuclideanMidpointRigidity.TaylorModel
public import EuclideanMidpointRigidity.AmplitudeSubstitution
public import EuclideanMidpointRigidity.CollectedSeries

/-! # The full Taylor force and its coefficients of degree at most six -/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity.Jet

variable {d : ℕ}
local notation "E" => Space d

/-- Keep the explicit enumeration folded when the uniform analytic bounds
are specialized. At order six its last arity alone has 46,656 terms. -/
opaque forceIndexEnumeration (m arity : ℕ) :
    {xs : List (ℕ × List ℕ) // xs =
      (List.range (arity+1)).flatMap fun s ↦ (boundedChoices m (s+2)).map (s,·)} := ⟨_,rfl⟩

def forceIndices (m arity : ℕ) : List (ℕ × List ℕ) := (forceIndexEnumeration m arity).1

theorem forceIndices_eq (m arity : ℕ) : forceIndices m arity =
    (List.range (arity+1)).flatMap fun s ↦ (boundedChoices m (s+2)).map (s,·) :=
  (forceIndexEnumeration m arity).2

def forceDegree (a : ℕ × List ℕ) := a.2.sum

def forceValue (σ : ℚ) (D : Derivatives d) (X V : ℕ → E) (a : ℕ × List ℕ) : E :=
  (-(σ:ℝ)/(a.1.factorial:ℝ)) • tupleValue D X V a.1 a.2

theorem full_force_expansion (σ : ℚ) (D : Derivatives d) (X V : ℕ → E)
    (m arity : ℕ) (ε : ℝ) :
    (-(σ:ℝ)) • K (taylorModel D arity (amplitudeSum m ε X)) (amplitudeSum m ε V)
      (amplitudeSum m ε V) =
      ((forceIndices m arity).map fun a ↦ ε^(forceDegree a) • forceValue σ D X V a).sum := by
  simp only [taylorModel, K_sum_coeff, K_smul_coeff, amplitude_box_product, List.smul_sum,
    List.map_map, Function.comp_def, forceIndices_eq, List.map_flatMap, sum_flatMap_eq,
    forceDegree, forceValue, smul_smul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

theorem compositions_eq_nil_of_lt (n k : ℕ) (hk : n<k) : compositions n k = [] := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    apply List.flatMap_eq_nil_iff.mpr
    intro i hi
    have hi' := List.mem_range.mp hi
    simp [ih (n-(i+1)) (by omega)]

theorem degreeCoefficient_force {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : ℕ × List ℕ → V) (n : ℕ) (hn : n≤6) :
    degreeCoefficient (forceIndices 6 4) forceDegree f n =
      ((List.range (n-1)).map (fun s ↦ ((compositions n (s+2)).map (fun ds ↦ f (s,ds))).sum)).sum := by
  simp only [degreeCoefficient, forceIndices_eq, forceDegree, List.filter_flatMap, List.filter_map,
    List.map_flatMap, sum_flatMap_eq, List.map_map, Function.comp_def]
  change ((List.range (4+1)).map fun s ↦
    (((boundedChoices 6 (s+2)).filter (fun ds ↦ decide (ds.sum=n))).map
      (fun ds ↦ f (s,ds))).sum).sum = _
  have hfilter (s : ℕ) := boundedChoices_filter 6 n (s+2) hn
  simp only [hfilter]
  have hr : List.range 5 = List.range (n-1) ++ (List.range (5-(n-1))).map ((n-1)+·) := by
    rw [← List.range_add, Nat.add_sub_of_le (by omega : n-1≤5)]
  rw [show 4+1=5 by decide, hr,List.map_append,List.sum_append]
  suffices (((List.range (5-(n-1))).map ((n-1)+·)).map
      (fun s ↦ ((compositions n (s+2)).map (fun ds ↦ f (s,ds))).sum)).sum=0 by rw [this,add_zero]
  apply List.sum_eq_zero
  intro a ha
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ha
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hs
  simp [compositions_eq_nil_of_lt n (n-1+i+2) (by omega)]

end EuclideanMidpointRigidity.Jet
