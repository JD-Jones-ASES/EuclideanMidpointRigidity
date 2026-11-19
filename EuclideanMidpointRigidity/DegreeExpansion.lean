module

public import EuclideanMidpointRigidity.SixthRecursion

/-! # Collecting the coefficients of a finite Taylor substitution by degree -/

@[expose] public section
namespace EuclideanMidpointRigidity.Jet

def positiveOrders (m : ℕ) := (List.range m).map (·+1)

def boundedChoices (m k : ℕ) := choices (List.replicate k (positiveOrders m))

private theorem filter_prepend_sum (ds : List (List ℕ)) (a n : ℕ) :
    ((ds.map (a::·)).filter (fun l ↦ decide (l.sum=n))) =
      if a ≤ n then (ds.filter (fun l ↦ decide (l.sum=n-a))).map (a::·) else [] := by
  rw [List.filter_map]
  by_cases h : a ≤ n
  · rw [ite_eq_left h]
    congr 1
    apply List.filter_congr
    intro x _
    change decide (a+x.sum=n) = decide (x.sum=n-a)
    by_cases hx : x.sum=n-a
    · simp [hx, Nat.add_sub_of_le h]
    · simp [hx, show ¬ a+x.sum=n by omega]
  · simp only [ite_eq_right h, Function.comp_def, List.sum_cons]
    have hx (x : List ℕ) : ¬a+x.sum=n := by omega
    simp [hx]

/-- Truncating each positive input degree at `m` preserves all compositions
whose total degree is at most `m`. The enumeration also preserves their order. -/
theorem boundedChoices_filter (m n k : ℕ) (hn : n ≤ m) :
    (boundedChoices m k).filter (fun ds ↦ decide (ds.sum=n)) = compositions n k := by
  induction k generalizing n with
  | zero =>
    by_cases h : n=0 <;> simp [boundedChoices,choices,compositions,h,eq_comm]
  | succ k ih =>
    change (((positiveOrders m).flatMap fun i ↦ (boundedChoices m k).map (i::·)).filter
      (fun ds ↦ decide (ds.sum=n))) = _
    simp only [positiveOrders, List.flatMap_map, List.filter_flatMap,
      filter_prepend_sum]
    have hr : List.range m = List.range n ++ (List.range (m-n)).map (n+·) := by
      rw [← List.range_add, Nat.add_sub_of_le hn]
    rw [hr,List.flatMap_append]
    have hexcess : ((List.range (m-n)).map (n+·)).flatMap (fun a ↦
        if a+1 ≤ n then ((boundedChoices m k).filter (fun l ↦ decide (l.sum=n-(a+1)))).map ((a+1)::·)
        else []) = [] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro x hx
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
      rw [ite_eq_right (by omega)]
    rw [hexcess,List.append_nil]
    apply List.flatMap_congr
    intro i hi
    have hlt := List.mem_range.mp hi
    rw [ite_eq_left (by omega), ih _ (by omega)]

end EuclideanMidpointRigidity.Jet
