module

public import EuclideanMidpointRigidity.JetInterpretation
public import EuclideanMidpointRigidity.MultilinearExpansion

/-! # Interpreting a product of coefficient polynomials -/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity.Jet

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

private theorem coeff_product (ps : List Term) (t : ℝ) :
    ((ps.map Term.coeff).prod:ℝ) * t^(ps.map Term.power).sum =
      (ps.map (fun a ↦ (a.coeff:ℝ)*t^a.power)).prod := by
  induction ps with
  | nil => simp
  | cons a ps ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, Rat.cast_mul, pow_add, ← ih]
    ring

private theorem productTerm_value (ps : List Term) (u v : Term) (hs : ps.length ≤ 4)
    (D : Derivatives d) (h : E) (t : ℝ) :
    let f := Tree.realize D h
    ∃ w, productTerm ps u v = some w ∧
      w.value f t = K (listForm D (ps.map (fun a ↦ a.value f t))) (u.value f t) (v.value f t) := by
  let f := Tree.realize D h
  obtain ⟨tree,ht⟩ := product_exists (ps.map Term.tree) u.tree v.tree (by simpa using hs)
  refine ⟨⟨tree,(ps.map Term.power).sum+u.power+v.power,(ps.map Term.coeff).prod*u.coeff*v.coeff⟩,
    by simp [productTerm,ht],?_⟩
  simp only [Term.value, Rat.cast_mul, pow_add]
  rw [product_realize ht D h, listForm_product_scalars (D := D)]
  simp only [K_smul_coeff, K_smul_left, K_smul_right, smul_smul, List.map_map, Function.comp_def]
  rw [← coeff_product ps t]
  congr 1
  ring

private theorem value_right (ps : List Term) (u : Term) (right : TimePolynomial)
    (hs : ps.length ≤ 4) (D : Derivatives d) (h : E) (t : ℝ) :
    let f := Tree.realize D h
    value (right.filterMap (productTerm ps u)) f t =
      K (listForm D (ps.map (fun a ↦ a.value f t))) (u.value f t) (value right f t) := by
  dsimp only
  induction right with
  | nil => simp [value,K]
  | cons v vs ih =>
    obtain ⟨w,hw,hval⟩ := productTerm_value ps u v hs D h t
    simp only [List.filterMap_cons,hw]
    change w.value _ t + value (vs.filterMap _) _ t = K _ _ (v.value _ t+value vs _ t)
    rw [hval,ih,K_add_right]

private theorem value_pair (ps : List Term) (left right : TimePolynomial)
    (hs : ps.length ≤ 4) (D : Derivatives d) (h : E) (t : ℝ) :
    let f := Tree.realize D h
    value (left.flatMap fun u ↦ right.filterMap (productTerm ps u)) f t =
      K (listForm D (ps.map (fun a ↦ a.value f t))) (value left f t) (value right f t) := by
  dsimp only
  induction left with
  | nil => simp [value,K]
  | cons u us ih =>
    simp only [List.flatMap_cons, value_append, value_right _ _ _ hs D h t, ih]
    exact (K_add_left _ _ _ _).symm

theorem length_of_mem_choices {α : Type*} {ps : List α} {vs : List (List α)}
    (hp : ps ∈ choices vs) : ps.length = vs.length := by
  induction vs generalizing ps with
  | nil => simpa [choices] using hp
  | cons ys vs ih =>
    simp only [choices, List.mem_flatMap, List.mem_map] at hp
    obtain ⟨a,_,p,hp,rfl⟩ := hp
    simp [ih hp]

theorem value_applyProduct (ps : List TimePolynomial) (left right : TimePolynomial)
    (hs : ps.length ≤ 4) (D : Derivatives d) (h : E) (t : ℝ) :
    let f := Tree.realize D h
    value (applyProduct ps left right) f t =
      K (listForm D (ps.map (fun p ↦ value p f t))) (value left f t) (value right f t) := by
  let f := Tree.realize D h
  have hsum (args : List (List Term)) (hsize : ∀ a ∈ args, a.length ≤ 4) :
      value (args.flatMap fun a ↦ left.flatMap fun u ↦ right.filterMap (productTerm a u)) f t =
      K ((args.map fun a ↦ listForm D (a.map (fun m ↦ m.value f t))).sum)
        (value left f t) (value right f t) := by
    induction args with
    | nil => simp [value,K]
    | cons a args ih =>
      simp only [List.flatMap_cons, List.map_cons, List.sum_cons, value_append, K_add_coeff]
      rw [value_pair a left right (hsize a (by simp)) D h t, ih (fun b hb ↦ hsize b (by simp [hb]))]
  dsimp only
  unfold applyProduct
  rw [hsum (choices ps) (fun a ha ↦ (length_of_mem_choices ha).trans_le hs)]
  congr 1
  exact (listForm_choices D ps (fun m ↦ m.value f t)).symm

end EuclideanMidpointRigidity.Jet
