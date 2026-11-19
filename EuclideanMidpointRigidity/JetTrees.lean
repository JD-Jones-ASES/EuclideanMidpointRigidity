module

public import Mathlib.Tactic

/-! # Polynomial operations for the geodesic Taylor recursion

A product has two velocity inputs and up to four spatial derivative inputs.
Four spatial derivatives suffice through endpoint degree six. The two groups
are separately symmetric. A term also records a power of affine time.
-/

@[expose] public section
namespace EuclideanMidpointRigidity.Jet

inductive Tree where
  | direction
  | k (u v : Tree)
  | j (p u v : Tree)
  | hess (p q u v : Tree)
  | third (p q r u v : Tree)
  | fourth (p q r s u v : Tree)
  deriving DecidableEq, Inhabited, Repr

/-- Preorder traversal. The constructor fixes the arity of each node. -/
def Tree.code : Tree → List ℕ
  | .direction => [0]
  | .k u v => 1 :: (u.code ++ v.code)
  | .j p u v => 2 :: (p.code ++ u.code ++ v.code)
  | .hess p q u v => 3 :: (p.code ++ q.code ++ u.code ++ v.code)
  | .third p q r u v => 4 :: (p.code ++ q.code ++ r.code ++ u.code ++ v.code)
  | .fourth p q r s u v => 5 :: (p.code ++ q.code ++ r.code ++ s.code ++ u.code ++ v.code)

def lexLE : List ℕ → List ℕ → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then lexLE as bs else decide (a < b)

def insertTree (x : Tree) : List Tree → List Tree
  | [] => [x]
  | y :: ys => if lexLE x.code y.code then x :: y :: ys else y :: insertTree x ys

def branch (spatial : List Tree) (l r : Tree) : Option Tree :=
  match spatial with
  | [] => some (.k l r)
  | [a] => some (.j a l r)
  | [a,b] => some (.hess a b l r)
  | [a,b,c] => some (.third a b c l r)
  | [a,b,c,d] => some (.fourth a b c d l r)
  | _ => none

/-- Build the canonical representative under the two input symmetries. -/
def product (spatial : List Tree) (u v : Tree) : Option Tree :=
  let args := spatial.foldr insertTree []
  if lexLE u.code v.code then branch args u v else branch args v u

structure Term where
  tree : Tree
  power : ℕ
  coeff : ℚ
  deriving DecidableEq, Inhabited, Repr

abbrev TimePolynomial := List Term

def combine (m : Term) : TimePolynomial → TimePolynomial
  | [] => if m.coeff = 0 then [] else [m]
  | n :: ns =>
    if m.tree = n.tree ∧ m.power = n.power then
      if m.coeff + n.coeff = 0 then ns else {m with coeff := m.coeff+n.coeff} :: ns
    else n :: combine m ns

def collect (p : TimePolynomial) : TimePolynomial := p.foldr combine []

def scale (s : ℚ) (p : TimePolynomial) : TimePolynomial :=
  p.map (fun m ↦ {m with coeff := s*m.coeff})

def same (p q : TimePolynomial) : Bool := (collect (p ++ scale (-1) q)).isEmpty

def differentiate (p : TimePolynomial) : TimePolynomial :=
  p.filterMap fun m ↦ if m.power = 0 then none else
    some {m with power := m.power-1, coeff := m.coeff*m.power}

def atTime (p : TimePolynomial) (t : ℚ) : TimePolynomial :=
  collect (p.map (fun m ↦ {m with power := 0, coeff := m.coeff*t^m.power}))

/-- The inverse of the second time derivative with zero data at `±1`. -/
def dirichlet (p : TimePolynomial) : TimePolynomial :=
  collect (p.flatMap fun m ↦
    let k : ℕ := m.power+2
    let a := m.coeff/((k:ℚ)*(k-1))
    [⟨m.tree,k,a⟩,⟨m.tree,k%2,-a⟩])

section Evaluation
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def Term.value (m : Term) (f : Tree → V) (t : ℝ) : V :=
  ((m.coeff:ℝ)*t^m.power) • f m.tree

def value (p : TimePolynomial) (f : Tree → V) (t : ℝ) : V :=
  (p.map (fun m ↦ m.value f t)).sum

private theorem value_combine (m : Term) (p : TimePolynomial) (f : Tree → V) (t : ℝ) :
    value (combine m p) f t = m.value f t + value p f t := by
  induction p with
  | nil =>
    by_cases hm : m.coeff = 0 <;> simp [combine, value, Term.value, hm]
  | cons n ns ih =>
    by_cases ht : m.tree = n.tree ∧ m.power = n.power
    · by_cases hc : m.coeff + n.coeff = 0
      · have h' : m.coeff = -n.coeff := eq_neg_of_add_eq_zero_left hc
        simp [combine, ht, value, Term.value, h']
      · simp [combine, ht, hc, value, Term.value, add_mul, add_smul, add_assoc]
    · simp only [combine, ite_eq_right ht, value, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      abel

theorem value_collect (p : TimePolynomial) (f : Tree → V) (t : ℝ) :
    value (collect p) f t = value p f t := by
  induction p with
  | nil => rfl
  | cons m ms ih =>
    change value (combine m (collect ms)) f t = m.value f t + value ms f t
    rw [value_combine, ih]

theorem value_scale (s : ℚ) (p : TimePolynomial) (f : Tree → V) (t : ℝ) :
    value (scale s p) f t = (s:ℝ) • value p f t := by
  induction p with
  | nil => simp [scale,value]
  | cons m ms ih =>
    change ({m with coeff := s*m.coeff}:Term).value f t + value (scale s ms) f t =
      (s:ℝ) • (m.value f t + value ms f t)
    simp [Term.value, ih, smul_add, smul_smul, mul_assoc]

/-- A closed computation of coefficient equality implies equality of the
evaluations in every real vector space, for every assignment of tree values. -/
theorem same_sound {p q : TimePolynomial} (h : same p q = true) (f : Tree → V) (t : ℝ) :
    value p f t = value q f t := by
  have hc : collect (p ++ scale (-1) q) = [] := List.isEmpty_iff.mp h
  have hv := congrArg (fun s ↦ value s f t) hc
  change value (collect (p ++ scale (-1) q)) f t = 0 at hv
  rw [value_collect] at hv
  have happ (a b : TimePolynomial) : value (a++b) f t = value a f t+value b f t := by
    simp [value]
  rw [happ, value_scale] at hv
  apply sub_eq_zero.mp
  simpa [sub_eq_add_neg] using hv

end Evaluation
end EuclideanMidpointRigidity.Jet
