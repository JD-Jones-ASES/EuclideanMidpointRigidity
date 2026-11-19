module

public import EuclideanMidpointRigidity.ForceProjections

/-! # The single-index contraction in the projected vector equation -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity
open Quartic

inductive ForceAxis | negative | positive

def ForceAxis.pick {α : Type*} (i : ForceAxis) (x y : α) := match i with
  | .negative => x | .positive => y

/-- Coordinates at one basis vector. The last two entries apply the jet maps
to that basis vector and project onto the chosen output. -/
structure ForceColumn where
  x : ℝ
  dx : ℝ
  df : ℝ
  rx : ℝ
  zx : ℝ
  ro : ℝ
  zo : ℝ

def ForceColumn.cost (c : ForceColumn) (h : ℝ) : ℝ :=
  let l : ℝ := 7/13
  let v := l*(h*c.x+c.dx)
  let f := v-12*l*c.zx+(25/2)*l*c.rx
  f*c.df+(17*c.ro-19*c.zo)*v-2*(c.ro-2*c.zo)*l*(c.rx+2*c.zx)

namespace LiftedSection
variable {d : ℕ} (S : LiftedSection d)
local notation "E" => Space d

def forceColumn (p f g w : E) : ForceColumn :=
  ⟨⟪S.x p,w⟫_ℝ,⟪S.rate S.x p,w⟫_ℝ,⟪g,w⟫_ℝ,⟪S.rMap p (S.x p),w⟫_ℝ,
    ⟪S.zMap p (S.x p),w⟫_ℝ,⟪S.rMap p w,f⟫_ℝ,⟪S.zMap p w,f⟫_ℝ⟩

theorem linear_coordinates {ι : Type*} [Fintype ι] (B : OrthonormalBasis ι ℝ E) (L : E →ₗ[ℝ] E) (v f : E) :
    ⟪L v,f⟫_ℝ=∑ j, ⟪v,B j⟫_ℝ*⟪L (B j),f⟫_ℝ := by
  have h := congrArg (fun z : E ↦ ⟪L z,f⟫_ℝ) (B.sum_repr' v)
  simp only [map_sum,map_smul,sum_inner,real_inner_smul_left] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm v]

theorem force_contraction {ι : Type*} [Fintype ι] (B : OrthonormalBasis ι ℝ E) (p f g : E) :
    ⟪S.psi p,g⟫_ℝ+⟪S.forceTerm p,f⟫_ℝ=
      (∑ i, (S.forceColumn p f g (B i)).cost (S.drift p))+
      ((7/13:ℝ)^2/2)*(15*jetEntry (S.jet p) (S.x p) (S.axis p) (S.x p) f-
        11*jetEntry (S.jet p) (S.axis p) (S.x p) (S.x p) f) := by
  have hp : ⟪S.psi p,g⟫_ℝ=∑ i, ⟪S.psi p,B i⟫_ℝ*⟪g,B i⟫_ℝ := by
    rw [← B.sum_inner_mul_inner (S.psi p) g]
    exact Finset.sum_congr rfl (fun i _ ↦ by rw [real_inner_comm g])
  let X := S.theta p
  let Y := S.correction p
  let R := S.rMap p
  let Z := S.zMap p
  have h : (∑ i, (S.forceColumn p f g (B i)).cost (S.drift p))=
      (∑ i, ⟪S.psi p,B i⟫_ℝ*⟪g,B i⟫_ℝ)+17*(∑ i, ⟪X,B i⟫_ℝ*⟪R (B i),f⟫_ℝ)-
      19*(∑ i, ⟪X,B i⟫_ℝ*⟪Z (B i),f⟫_ℝ)-2*(∑ i, ⟪Y,B i⟫_ℝ*⟪R (B i),f⟫_ℝ)+
      4*(∑ i, ⟪Y,B i⟫_ℝ*⟪Z (B i),f⟫_ℝ) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [X,Y,R,Z,ForceColumn.cost,forceColumn,psi,correction,theta,axialU]
    simp only [map_smul,inner_add_left,inner_sub_left,real_inner_smul_left]
    ring
  rw [h,← hp,← linear_coordinates B R X f,← linear_coordinates B Z X f,
    ← linear_coordinates B R Y f,← linear_coordinates B Z Y f]
  simp only [X,Y,R,Z,forceTerm,inner_add_left,inner_sub_left,real_inner_smul_left,jetEntry,cubicEntry]
  ring

end LiftedSection
end EuclideanMidpointRigidity

