module

public import EuclideanMidpointRigidity.SymmetricTaylor
public import EuclideanMidpointRigidity.SixthRecursion

/-! # Expanding a symmetric Taylor form over finite lists of summands -/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity

variable {U V α : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] (D : ∀ k, SpatialForm U V k)

omit [NormedAddCommGroup U] [NormedSpace ℝ U] in
private theorem get_cons_eq (a : U) (xs : List U) :
    (a::xs).get = Fin.cons a xs.get := by
  funext i
  exact Fin.cases rfl (fun _ ↦ rfl) i

private theorem listForm_head_add (a b : U) (xs : List U) :
    listForm D ((a+b)::xs) = listForm D (a::xs) + listForm D (b::xs) := by
  simpa only [listForm, List.length_cons, get_cons_eq] using
    (symmetricPart (D (xs.length+1))).cons_add xs.get a b

private theorem listForm_head_smul (a : U) (s : ℝ) (xs : List U) :
    listForm D ((s • a)::xs) = s • listForm D (a::xs) := by
  simpa only [listForm, List.length_cons, get_cons_eq] using
    (symmetricPart (D (xs.length+1))).cons_smul xs.get s a

private theorem listForm_middle (pre post : List U) (a : U) :
    listForm D (pre ++ a::post) = listForm D (a::(pre++post)) :=
  listForm_perm D List.perm_middle

theorem listForm_middle_add (pre post : List U) (a b : U) :
    listForm D (pre ++ (a+b)::post) =
      listForm D (pre ++ a::post) + listForm D (pre ++ b::post) := by
  simp only [listForm_middle D pre post, listForm_head_add]

theorem listForm_middle_smul (pre post : List U) (s : ℝ) (a : U) :
    listForm D (pre ++ (s • a)::post) = s • listForm D (pre ++ a::post) := by
  simp only [listForm_middle D pre post, listForm_head_smul]

private theorem listForm_middle_sum (pre post : List U) (vs : List α) (f : α → U) :
    listForm D (pre ++ (vs.map f).sum::post) =
      (vs.map (fun a ↦ listForm D (pre ++ (f a)::post))).sum := by
  induction vs with
  | nil => simpa using listForm_middle_smul D pre post 0 (0:U)
  | cons m ms ih => simp only [List.map_cons, List.sum_cons, listForm_middle_add, ih]

/-- Move one scalar out of each spatial slot. -/
theorem listForm_product_scalars (xs : List α) (s : α → ℝ) (f : α → U) :
    listForm D (xs.map fun a ↦ s a • f a) = (xs.map s).prod • listForm D (xs.map f) := by
  suffices ∀ pre : List U, listForm D (pre ++ xs.map fun a ↦ s a • f a) =
        (xs.map s).prod • listForm D (pre ++ xs.map f) by simpa using this []
  induction xs with
  | nil => intro pre; simp
  | cons a xs ih =>
    intro pre
    simp only [List.map_cons, List.prod_cons, listForm_middle_smul, mul_smul]
    simpa using congrArg (fun v : V ↦ s a • v) (ih (pre ++ [f a]))

theorem sum_flatMap_eq {γ δ : Type*} [AddMonoid δ] (l : List γ) (F : γ → List δ) :
    (l.flatMap F).sum = (l.map fun a ↦ (F a).sum).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons,ih]

/-- Independent choices of one term from each finite list give the full
multilinear expansion, with multiplicities. -/
theorem listForm_choices (xss : List (List α)) (f : α → U) :
    listForm D (xss.map fun vs ↦ (vs.map f).sum) =
      ((Jet.choices xss).map fun args ↦ listForm D (args.map f)).sum := by
  suffices ∀ pre : List U, listForm D (pre ++ xss.map fun vs ↦ (vs.map f).sum) =
      ((Jet.choices xss).map fun args ↦ listForm D (pre ++ args.map f)).sum by simpa using this []
  induction xss with
  | nil => intro pre; simp [Jet.choices]
  | cons vs ss ih =>
    intro pre
    simp only [List.map_cons, listForm_middle_sum, Jet.choices, List.map_flatMap, sum_flatMap_eq]
    apply congrArg List.sum
    apply List.map_congr_left
    intro a _
    simpa [List.map_map, Function.comp_def] using ih (pre ++ [f a])

end EuclideanMidpointRigidity
