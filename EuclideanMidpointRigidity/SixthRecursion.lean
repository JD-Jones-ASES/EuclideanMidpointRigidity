module

public import EuclideanMidpointRigidity.JetTrees

/-! # The two signed geodesic Dirichlet recursions through degree six

The endpoints are `p ± ε h`, with affine time in `[-1,1]`. In degree `n`,
the force consists of a spatial Taylor coefficient applied to positive-order
displacements and two positive-order velocities whose degrees sum to `n`.
-/

@[expose] public section
namespace EuclideanMidpointRigidity.Jet

def compositions : ℕ → ℕ → List (List ℕ)
  | n, 0 => if n = 0 then [[]] else []
  | n, k+1 => (List.range n).flatMap fun i ↦
      (compositions (n-(i+1)) k).map ((i+1) :: ·)

def choices {α : Type*} : List (List α) → List (List α)
  | [] => [[]]
  | p :: ps => p.flatMap fun m ↦ (choices ps).map (m :: ·)

def productTerm (ps : List Term) (u v : Term) : Option Term := do
  let tree ← product (ps.map Term.tree) u.tree v.tree
  return ⟨tree,(ps.map Term.power).sum+u.power+v.power,(ps.map Term.coeff).prod*u.coeff*v.coeff⟩

def applyProduct (positions : List TimePolynomial) (left right : TimePolynomial) : TimePolynomial :=
  (choices positions).flatMap fun ps ↦
    left.flatMap fun u ↦ right.filterMap (productTerm ps u)

def forcing (σ : ℚ) (paths : List TimePolynomial) (n : ℕ) : TimePolynomial :=
  collect ((List.range (n-1)).flatMap fun s ↦
    (compositions n (s+2)).flatMap fun ds ↦
      let positions := (ds.take s).map (fun j ↦ paths[j]?.getD [])
      match ds.drop s with
      | [i,j] => scale (-σ/(s.factorial:ℚ))
          (applyProduct positions (differentiate (paths[i]?.getD [])) (differentiate (paths[j]?.getD [])))
      | _ => [])

def signedPaths (σ : ℚ) : List TimePolynomial :=
  [2,3,4,5,6].foldl (fun paths n ↦ paths ++ [dirichlet (forcing σ paths n)])
    [[],[⟨.direction,1,1⟩]]

def midpointCoefficient (n : ℕ) : TimePolynomial :=
  collect (atTime ((signedPaths 1)[n]?.getD []) 0 ++ atTime ((signedPaths (-1))[n]?.getD []) 0)

/-- Check the ODE and both endpoint values independently of the integration
formula, for every nontrivial coefficient of a single sign. -/
def boundaryEquations (σ : ℚ) : Bool :=
  let paths := signedPaths σ
  [2,3,4,5,6].all fun n ↦
    let p := paths[n]?.getD []
    same (differentiate (differentiate p)) (forcing σ paths n) &&
      same (atTime p (-1)) [] && same (atTime p 1) []

def canonical : Tree → Tree
  | .direction => .direction
  | t@(.k u v) => (product [] (canonical u) (canonical v)).getD t
  | t@(.j p u v) => (product [canonical p] (canonical u) (canonical v)).getD t
  | t@(.hess p q u v) => (product [canonical p,canonical q] (canonical u) (canonical v)).getD t
  | t@(.third p q r u v) =>
    (product [canonical p,canonical q,canonical r] (canonical u) (canonical v)).getD t
  | t@(.fourth p q r s u v) =>
    (product [canonical p,canonical q,canonical r,canonical s] (canonical u) (canonical v)).getD t

def literal (rows : List (ℚ × Tree)) : TimePolynomial :=
  rows.map fun (q,t) ↦ ⟨canonical t,0,q⟩

/-- The twenty terms with three undifferentiated products and one first
derivative. Spatial arguments of `j` are always written first. -/
def affineSixth : TimePolynomial :=
  let h := Tree.direction
  let k := Tree.k h h
  let l := Tree.k h k
  let m := Tree.k h l
  let n := Tree.k k k
  let L := Tree.k h
  let U := Tree.j h k h
  let V := Tree.j k h h
  let T := Tree.j h h h
  scale (1/180) (literal [
    (-12,L (L (L T))), (16,L (L U)), (-26,L (L V)),
    (2,L (.k k T)), (4,L (.j h l h)), (12,L (.j h k k)),
    (-18,L (.j k k h)), (-6,L (.j l h h)),
    (12,.k k (L T)), (-16,.k k U), (26,.k k V), (-12,.k l T),
    (24,.j h m h), (-8,.j h n h), (-4,.j h l k),
    (-32,.j k l h), (9,.j k k k), (12,.j l k h),
    (-22,.j m h h), (14,.j n h h)])

/-- The seven terms containing second or third spatial derivatives. -/
def higherSixth : TimePolynomial :=
  let h := Tree.direction
  let k := Tree.k h h
  let U := Tree.j h h h
  let V := Tree.hess h h h h
  let W := Tree.third h h h h h
  literal [
    (1/90,.k h W), (-1/45,.j h h V), (7/180,.j V h h),
    (-1/180,.hess h h h U), (1/60,.hess h U h h),
    (-1/45,.third h h h h k), (1/40,.third h h k h h)]

def quartic : TimePolynomial :=
  let h := Tree.direction
  let k := Tree.k h h
  let u := Tree.j h h h
  literal [(1/6,.k h u),(5/12,.j k h h),(-1/3,.j h h k)]

end EuclideanMidpointRigidity.Jet
