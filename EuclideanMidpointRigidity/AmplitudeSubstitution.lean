module

public import EuclideanMidpointRigidity.JetProducts
public import EuclideanMidpointRigidity.DegreeExpansion

/-! # Substitution of finite amplitude series in the Christoffel force -/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity.Jet

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

def amplitudeSum {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (m : ℕ) (ε : ℝ) (X : ℕ → V) : V :=
  ((positiveOrders m).map (fun i ↦ ε^i • X i)).sum

def tupleValue (D : Derivatives d) (X V : ℕ → E) (s : ℕ) (ds : List ℕ) : E :=
  match ds.drop s with
  | [i,j] => K (listForm D ((ds.take s).map X)) (V i) (V j)
  | _ => 0

theorem choices_append {α : Type*} (xs ys : List (List α)) :
    choices (xs++ys) = (choices xs).flatMap (fun a ↦ (choices ys).map (a++·)) := by
  induction xs with
  | nil => simp [choices]
  | cons ss xs ih =>
    simp [choices,ih,List.flatMap_assoc,List.map_flatMap,List.flatMap_map,
      List.map_map,Function.comp_def]

private theorem boundedChoices_two_right (m s : ℕ) :
    boundedChoices m (s+2) = (boundedChoices m s).flatMap (fun pos ↦
      (positiveOrders m).flatMap fun i ↦ (positiveOrders m).map fun j ↦ pos ++ [i,j]) := by
  unfold boundedChoices
  rw [List.replicate_add, choices_append]
  simp [choices,List.replicate_succ,List.map_flatMap,← List.map_eq_flatMap,Function.comp_def]

private theorem tupleValue_append (D : Derivatives d) (X V : ℕ → E)
    (s : ℕ) (p : List ℕ) (hl : p.length=s) (i j : ℕ) :
    tupleValue D X V s (p++[i,j]) = K (listForm D (p.map X)) (V i) (V j) := by
  subst s
  simp [tupleValue]

private theorem K_sum_right {α : Type*} (c : Coeff) (x : E) (vs : List α) (Y : α → E) :
    K c x (vs.map Y).sum = (vs.map (fun v ↦ K c x (Y v))).sum := by
  induction vs with
  | nil => simp [K]
  | cons v vs ih => simp [ih]

private theorem K_sum_left {α : Type*} (c : Coeff) (x : E) (vs : List α) (Y : α → E) :
    K c (vs.map Y).sum x = (vs.map (fun v ↦ K c (Y v) x)).sum := by
  induction vs with
  | nil => simp [K]
  | cons v vs ih => simp [ih]

theorem K_sum_coeff {α : Type*} (u v : E) (as : List α) (C : α → Coeff) :
    K (as.map C).sum u v = (as.map (fun a ↦ K (C a) u v)).sum := by
  induction as with
  | nil => simp [K]
  | cons a as ih => simp [ih]

/-- The full product enumerates one index for each spatial and velocity slot. -/
theorem box_product (D : Derivatives d) (X V : ℕ → E) (m s : ℕ) :
    K (listForm D (List.replicate s ((positiveOrders m).map X).sum))
      ((positiveOrders m).map V).sum ((positiveOrders m).map V).sum =
      ((boundedChoices m (s+2)).map (tupleValue D X V s)).sum := by
  have hs := listForm_choices D (List.replicate s (positiveOrders m)) X
  simp only [List.map_replicate] at hs
  rw [hs,K_sum_coeff,boundedChoices_two_right]
  simp only [List.map_flatMap,sum_flatMap_eq,List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [K_sum_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  rw [K_sum_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro j _
  exact (tupleValue_append D X V s p
    (by simpa [boundedChoices] using length_of_mem_choices hp) i j).symm

private theorem prod_powers (p : List ℕ) (ε : ℝ) : (p.map fun i ↦ ε^i).prod = ε^p.sum := by
  induction p with
  | nil => simp
  | cons i p ih => simp [ih,pow_add]

theorem tupleValue_scaled (D : Derivatives d) (X V : ℕ → E) (s : ℕ) (ds : List ℕ) (ε : ℝ) :
    tupleValue D (fun n ↦ ε^n • X n) (fun n ↦ ε^n • V n) s ds =
      ε^ds.sum • tupleValue D X V s ds := by
  unfold tupleValue
  generalize he : ds.drop s = tail
  rcases tail with _ | ⟨i,tail⟩
  · simp
  rcases tail with _ | ⟨j,tail⟩
  · simp
  rcases tail with _ | ⟨k,tail⟩
  · have hadd : ds.sum = (ds.take s).sum+i+j := by
      have hh := congrArg List.sum (List.take_append_drop s ds)
      simp [he] at hh
      omega
    simp only [listForm_product_scalars,prod_powers,K_smul_coeff,K_smul_left,K_smul_right,
      smul_smul,hadd,pow_add,mul_assoc,mul_left_comm,mul_comm]
  · simp

theorem amplitude_box_product (D : Derivatives d) (X V : ℕ → E) (m s : ℕ) (ε : ℝ) :
    K (listForm D (List.replicate s (amplitudeSum m ε X)))
      (amplitudeSum m ε V) (amplitudeSum m ε V) =
      ((boundedChoices m (s+2)).map (fun ds ↦ ε^ds.sum • tupleValue D X V s ds)).sum := by
  unfold amplitudeSum
  rw [box_product D (fun i ↦ ε^i • X i) (fun i ↦ ε^i • V i) m s]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ds _
  exact tupleValue_scaled D X V s ds ε

end EuclideanMidpointRigidity.Jet
