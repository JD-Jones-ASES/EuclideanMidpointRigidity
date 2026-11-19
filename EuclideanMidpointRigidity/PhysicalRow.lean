module

public import EuclideanMidpointRigidity.RawRegularity

/-! # Linear combinations of raw and denominator-cleared spectral rows -/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity.Spectral
open IntervalPolynomial MixedChannel Quartic

structure ChannelData (ι : Type*) where
  eigenvalue : ι → ℝ
  channel : ι → MixedChannel
  ratioSq : ℝ
  internalWeight : ℝ
  extraSource : ℝ

/-- One row in the two coordinate systems, with the source coefficient kept
alongside the quadratic form. -/
structure PhysicalRow where
  table : Row
  raw : ℝ → MixedChannel → ℝ
  coefficient : ℚ
  compatible : ∀ {v : MixedChannel} {s : ℝ}, v.Equations s → regularDenominator s≠0 →
    raw s v=table.atChannel s (v.l/regularDenominator s) (v.h/regularDenominator s)
  regularity : RawRegularity raw

namespace PhysicalRow

def residual {ι : Type*} [Fintype ι] (a : PhysicalRow) (d : ChannelData ι) : ℝ :=
  (∑ j, a.raw (d.eigenvalue j) (d.channel j))+eval a.table.internal d.ratioSq*d.internalWeight-
    eval a.table.rhs d.ratioSq-(a.coefficient:ℝ)*d.extraSource

def zero : PhysicalRow :=
  ⟨Row.zero,fun _ _ ↦ 0,0,by intros; simp [Row.zero,Row.atChannel,eval],
    ⟨fun _ ↦ rfl,by intros; fun_prop⟩⟩

def add (a b : PhysicalRow) : PhysicalRow :=
  ⟨a.table.add b.table,fun s v ↦ a.raw s v+b.raw s v,a.coefficient+b.coefficient,by
    intro v s h hd
    rw [a.compatible h hd,b.compatible h hd]
    simp only [Row.add,Row.atChannel,eval_plus]
    ring, ⟨by intro s; simp [a.regularity.null,b.regularity.null],
      fun hf hs ↦ (a.regularity.strict hf hs).add (b.regularity.strict hf hs)⟩⟩

def scale (k : ℚ) (a : PhysicalRow) : PhysicalRow :=
  ⟨a.table.scale k,fun s v ↦ (k:ℝ)*a.raw s v,k*a.coefficient,by
    intro v s h hd
    rw [a.compatible h hd]
    simp only [Row.scale,Row.atChannel,eval_scale]
    ring, ⟨by intro s; simp [a.regularity.null],
      fun hf hs ↦ continuousAt_const.mul (a.regularity.strict hf hs)⟩⟩

@[simp] theorem residual_zero {ι : Type*} [Fintype ι] (d : ChannelData ι) : zero.residual d=0 := by
  simp [residual,zero,Row.zero,eval]

@[simp] theorem residual_add {ι : Type*} [Fintype ι] (a b : PhysicalRow) (d : ChannelData ι) :
    (a.add b).residual d=a.residual d+b.residual d := by
  simp only [residual,add,Row.add,eval_plus,Finset.sum_add_distrib,Rat.cast_add]
  ring

@[simp] theorem residual_scale {ι : Type*} [Fintype ι] (k : ℚ) (a : PhysicalRow) (d : ChannelData ι) :
    (a.scale k).residual d=(k:ℝ)*a.residual d := by
  simp only [residual,scale,Row.scale,eval_scale,← Finset.mul_sum,Rat.cast_mul]
  ring

def sum (xs : List PhysicalRow) := xs.foldr add zero

theorem sum_table (xs : List PhysicalRow) : (sum xs).table=(xs.map table).foldr Row.add Row.zero := by
  induction xs with
  | nil => rfl
  | cons a xs ih => exact congrArg (a.table.add ·) ih

theorem sum_coefficient (xs : List PhysicalRow) : (sum xs).coefficient=(xs.map coefficient).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simpa only [sum,List.foldr_cons,add,List.map_cons,List.sum_cons] using congrArg (a.coefficient+·) ih

theorem sum_residual_nonpos {ι : Type*} [Fintype ι] (d : ChannelData ι) (xs : List PhysicalRow)
    (h : ∀ a ∈ xs, a.residual d≤0) : (sum xs).residual d≤0 := by
  induction xs with
  | nil => simp [sum]
  | cons a xs ih =>
    change (a.add (sum xs)).residual d≤0
    rw [residual_add]
    exact add_nonpos (h a (.head _)) (ih fun b hb ↦ h b (.tail _ hb))

def quartic (i : Fin 4) : PhysicalRow :=
  ⟨QuarticRows.table i,fun s v ↦ (QuarticRows.kind i).external s v/QuarticRows.scale i,0,QuarticRows.external_eq i,
    ⟨fun s ↦ by rw [(QuarticRows.kind i).regularity.null,zero_div],
      fun hf hs ↦ ((QuarticRows.kind i).regularity.strict hf hs).div_const _⟩⟩

def differentiated (i : Fin 3) : PhysicalRow :=
  ⟨DerivativeRows.table i,fun s v ↦ DerivativeRows.external i s v/DerivativeRows.scale i,0,DerivativeRows.external_eq i,
    ⟨fun s ↦ by rw [(DerivativeRows.regularity i).null,zero_div],
      fun hf hs ↦ ((DerivativeRows.regularity i).strict hf hs).div_const _⟩⟩

def force (i : ForceAxis) : PhysicalRow :=
  ⟨ForceRows.table i,fun s v ↦ i.external s v/ForceRows.scale i,i.pick 1 0,ForceRows.external_eq i,
    ⟨fun s ↦ by rw [i.regularity.null,zero_div],fun hf hs ↦ (i.regularity.strict hf hs).div_const _⟩⟩

def test (t : NormTest) : PhysicalRow :=
  ⟨t.row,fun _ v ↦ t.raw v,0,t.raw_eq,t.regularity⟩

def physical : List PhysicalRow := [quartic 0,quartic 1,quartic 2,quartic 3,
    differentiated 0,differentiated 1,differentiated 2,force .positive,force .negative]

theorem physical_table : physical.map table=physicalRows := by rfl

end PhysicalRow
end EuclideanMidpointRigidity.Spectral

