module

public import EuclideanMidpointRigidity.CriticalAxis

/-! # Quartic rows with two repeated test directions -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity.Quartic

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

def term (c : Coeff) (J : E →L[ℝ] Coeff) (out i j k l : E) : ℝ :=
  2*⟪K c i (K (J j) k l),out⟫_ℝ+5*⟪K (J (K c i j)) k l,out⟫_ℝ-
    4*⟪K (J i) j (K c k l),out⟫_ℝ

private theorem term_diagonal (c : Coeff) (J : E →L[ℝ] Coeff) (out z : E) :
    term c J out z z z z=⟪obstruction c J z,out⟫_ℝ := by
  simp only [term,obstruction,inner_sub_left,inner_add_left,← Nat.cast_smul_eq_nsmul ℝ,real_inner_smul_left]
  norm_num

private theorem term_add₁ (c : Coeff) (J : E →L[ℝ] Coeff) (o a b j k l : E) :
    term c J o (a+b) j k l=term c J o a j k l+term c J o b j k l := by
  simp only [term,K_add_left,map_add,K_add_coeff,inner_add_left]; ring

private theorem term_add₂ (c : Coeff) (J : E →L[ℝ] Coeff) (o i a b k l : E) :
    term c J o i (a+b) k l=term c J o i a k l+term c J o i b k l := by
  simp only [term,K_add_right,K_add_left,map_add,K_add_coeff,inner_add_left]; ring

private theorem term_add₃ (c : Coeff) (J : E →L[ℝ] Coeff) (o i j a b l : E) :
    term c J o i j (a+b) l=term c J o i j a l+term c J o i j b l := by
  simp only [term,K_add_right,K_add_left,inner_add_left]; ring

private theorem term_add₄ (c : Coeff) (J : E →L[ℝ] Coeff) (o i j k a b : E) :
    term c J o i j k (a+b)=term c J o i j k a+term c J o i j k b := by
  simp only [term,K_add_right,inner_add_left]; ring

private theorem term_neg₁ (c : Coeff) (J : E →L[ℝ] Coeff) (o i j k l : E) :
    term c J o (-i) j k l= -term c J o i j k l := by
  simp only [term,K_neg_left,map_neg,K_neg_coeff,inner_neg_left]; ring

private theorem term_neg₂ (c : Coeff) (J : E →L[ℝ] Coeff) (o i j k l : E) :
    term c J o i (-j) k l= -term c J o i j k l := by
  simp only [term,K_neg_left,K_neg_right,map_neg,K_neg_coeff,inner_neg_left]; ring

private theorem term_neg₃ (c : Coeff) (J : E →L[ℝ] Coeff) (o i j k l : E) :
    term c J o i j (-k) l= -term c J o i j k l := by
  simp only [term,K_neg_left,K_neg_right,inner_neg_left]; ring

private theorem term_neg₄ (c : Coeff) (J : E →L[ℝ] Coeff) (o i j k l : E) :
    term c J o i j k (-l)= -term c J o i j k l := by
  simp only [term,K_neg_right,inner_neg_left]; ring

def row22 {V : Type*} (F : V → V → V → V → ℝ) (a b : V) :=
  F a a b b+F a b a b+F a b b a+F b a a b+F b a b a+F b b a a

def row211 {V : Type*} (F : V → V → V → V → ℝ) (a b c : V) :=
  F a a b c+F a a c b+F a b a c+F a c a b+F a b c a+F a c b a+
  F b a a c+F c a a b+F b a c a+F c a b a+F b c a a+F c b a a

theorem row22_zero {c : Coeff} {J : E →L[ℝ] Coeff} (hE : ∀ z, obstruction c J z=0) (o a b : E) :
    row22 (term c J o) a b=0 := by
  have h (w : E) : term c J o w w w w=0 := by rw [term_diagonal,hE,inner_zero_left]
  have h₁ := h (a+b)
  have h₂ := h (a+(-b))
  simp only [term_add₁,term_add₂,term_add₃,term_add₄,term_neg₁,term_neg₂,term_neg₃,term_neg₄] at h₁ h₂
  dsimp only [row22]
  linear_combination h₁/2+h₂/2-h a-h b

theorem row211_zero {c : Coeff} {J : E →L[ℝ] Coeff} (hE : ∀ z, obstruction c J z=0) (o a b w : E) :
    row211 (term c J o) a b w=0 := by
  have h₁ := row22_zero hE o a (b+w)
  have h₂ := row22_zero hE o a b
  have h₃ := row22_zero hE o a w
  simp only [row22,term_add₁,term_add₂,term_add₃,term_add₄] at h₁ h₂ h₃
  dsimp only [row211]
  linear_combination h₁-h₂-h₃

def cubicEntry (c : Coeff) (i j k : E) := ⟪K c i j,k⟫_ℝ
def jetEntry (J : E →L[ℝ] Coeff) (i j k l : E) := cubicEntry (J i) j k l

/-- The index joining the cubic and its first derivative appears exactly once. -/
def contraction {V : Type*} (T : V → V → V → ℝ) (J : V → V → V → V → ℝ)
    (r o i j k l : V) : ℝ :=
  2*T i o r*J j k l r+5*T i j r*J r k l o-4*J i j o r*T k l r

private theorem eval_spatial_sum {ι : Type*} [Fintype ι] (B : OrthonormalBasis ι ℝ E)
    (J : E →L[ℝ] Coeff) (v k l o : E) :
    jetEntry J v k l o=∑ i, ⟪v,B i⟫_ℝ*jetEntry J (B i) k l o := by
  rw [← B.sum_repr' v] at ⊢
  conv_rhs => simp only [B.sum_repr']
  have eval_sum (s : Finset ι) :
      jetEntry J (∑ i ∈ s, ⟪B i,v⟫_ℝ • B i) k l o =
      ∑ i ∈ s, ⟪B i,v⟫_ℝ*jetEntry J (B i) k l o := by
    classical
    induction s using Finset.induction_on with
    | empty => simp [jetEntry,cubicEntry,K]
    | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      simp only [jetEntry,cubicEntry,map_add,map_smul,K_add_coeff,K_smul_coeff,
        inner_add_left,real_inner_smul_left] at ih ⊢
      rw [ih]
  rw [eval_sum]
  exact Finset.sum_congr rfl (fun i _ ↦ by rw [real_inner_comm v (B i)])

theorem term_eq_sum {ι : Type*} [Fintype ι] (B : OrthonormalBasis ι ℝ E)
    (c : Coeff) (J : E →L[ℝ] Coeff) (o i j k l : E) :
    term c J o i j k l=∑ r, contraction (cubicEntry c) (jetEntry J) (B r) o i j k l := by
  have hj := eval_spatial_sum B J (K c i j) k l o
  have h₁ := B.sum_inner_mul_inner (K c i o) (K (J j) k l)
  have h₃ := B.sum_inner_mul_inner (K (J i) j o) (K c k l)
  simp only [term,contraction,jetEntry,cubicEntry,Finset.sum_sub_distrib,Finset.sum_add_distrib,
    mul_assoc,← Finset.mul_sum] at hj ⊢
  rw [K_selfAdjoint c i _ o,K_selfAdjoint (J i) j _ o,hj]
  rw [show ⟪K c i o,K (J j) k l⟫_ℝ=⟪K (J j) k l,K c i o⟫_ℝ from real_inner_comm _ _] at h₁
  rw [show ⟪K (J i) j o,K c k l⟫_ℝ=⟪K c k l,K (J i) j o⟫_ℝ from real_inner_comm _ _] at h₃
  simp_rw [show ∀ r, ⟪B r,K (J j) k l⟫_ℝ=⟪K (J j) k l,B r⟫_ℝ from fun _ ↦ real_inner_comm _ _] at h₁
  simp_rw [show ∀ r, ⟪B r,K c k l⟫_ℝ=⟪K c k l,B r⟫_ℝ from fun _ ↦ real_inner_comm _ _] at h₃
  rw [h₁,h₃]

end EuclideanMidpointRigidity.Quartic
