module

public import EuclideanMidpointRigidity.DifferentiatedCubic
public import EuclideanMidpointRigidity.CubicDerivativeMoments
public import EuclideanMidpointRigidity.QuarticSpectralRows

/-! # The three differentiated resonant rows of the spectral certificate -/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity.Spectral.DerivativeRows
open IntervalPolynomial Quartic MixedChannel LiftedSection

def combine (i : Fin 3) (z₁ zM zN z₂ source : ℝ) : ℝ :=
  let k := ResonantPlane.k
  ![zM+k*zN+k*source,z₁-(650/153)*k*zN-2*(650/153)*k*source,z₂+(159/1300)*zN-(159/1300)*source] i

def internal (i : Fin 3) (t n : ℝ) := combine i (CubicSlot.d1.internal t n) (CubicSlot.m.internal t n) (CubicSlot.n.internal t n)
  (CubicSlot.d2.internal t n) (ratioSource t n)

def external (i : Fin 3) (s : ℝ) (v : MixedChannel) := combine i (CubicSlot.d1.external s v) (CubicSlot.m.external s v) (CubicSlot.n.external s v)
  (CubicSlot.d2.external s v) 0

def scale : Fin 3 → ℝ := ![6830525/89549098,67/52,2/5]

def table (i : Fin 3) : Row := physicalRows.getD (4+i.val) Row.zero

theorem scale_pos (i : Fin 3) : 0<scale i := by fin_cases i <;> norm_num [scale]

theorem internal_eq (i : Fin 3) (t n : ℝ) :
    internal i t n/scale i=eval (table i).internal (t^2)*(t^2*n^2)-eval (table i).rhs (t^2) := by
  fin_cases i <;> norm_num [internal,scale,table,combine,CubicSlot.internal,CubicSlot.reconstruction,
    CubicSlot.framePart,Reduction.internal,ResonantPlane.k,ratioSource,physicalRows,eval,List.getD] <;> ring

private theorem regular_formula (i : Fin 3) {s : ℝ} (hd : regularDenominator s≠0) (l h : ℝ) :
    external i s (inRegular s l h)/scale i=(table i).atChannel s (l/regularDenominator s) (h/regularDenominator s) := by
  have hgap : 1-2*s≠0 := by
    intro hz
    apply hd
    have he : 2*s-1=0 := by linarith only [hz]
    simp [regularDenominator,he]
  fin_cases i <;>
    norm_num [external,combine,scale,table,Row.atChannel,eval,List.getD,physicalRows,CubicSlot.external,
      CubicSlot.reconstruction,CubicSlot.angular,Reduction.external,inRegular,ResonantPlane.k] <;>
    field_simp [hd,hgap] <;>
    simp only [regularDenominator,regular_q,regular_r1w,regular_rw1,regular_z1w,regular_r2w,regular_rw2,
      regular_z2w,regular_rot1,regular_rot2] <;> ring

theorem external_eq (i : Fin 3) {v : MixedChannel} {s : ℝ} (hv : v.Equations s) (hd : regularDenominator s≠0) :
    external i s v/scale i=(table i).atChannel s (v.l/regularDenominator s) (v.h/regularDenominator s) := by
  simpa only [inRegular_eq hv hd] using regular_formula i hd v.l v.h

theorem raw_geometric_row {d : ℕ} {S : LiftedSection d} {p : Space d} (hm : S.IsMixed p)
    {ι : Type*} [Fintype ι] (B : SpectralFrame S p ι) (i : Fin 3) :
    internal i (S.ratio p) (S.core p).n+∑ j, external i (B.value j) (S.channel p (B.w j))=0 := by
  obtain ⟨q₁,q₂,q₃⟩ := S.differentiated_relations hm
  have h₁ := CubicSlot.weighted_identity hm B .d1
  have hM := CubicSlot.weighted_identity hm B .m
  have hN := CubicSlot.weighted_identity hm B .n
  have h₂ := CubicSlot.weighted_identity hm B .d2
  dsimp only [CubicSlot.weight,CubicSlot.shape,one_mul] at h₁ hM hN h₂
  have ht : (S.core p).t=S.ratio p := rfl
  have hn : S.shape S.x S.y S.y p=(S.core p).n := rfl
  simp only [ht,one_mul] at h₁ hM hN h₂
  simp only [hn] at q₁ q₂ q₃
  rw [hM,hN] at q₁
  rw [h₁,hN] at q₂
  rw [h₂,hN] at q₃
  fin_cases i <;>
    simp [internal,external,combine,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
  · linear_combination q₁
  · linear_combination q₂
  · linear_combination q₃

theorem geometric_row {d : ℕ} {S : LiftedSection d} {p : Space d} (hm : S.IsMixed p)
    {ι : Type*} [Fintype ι] (B : SpectralFrame S p ι) (i : Fin 3) :
    let c := S.core p
    let v := fun j ↦ S.channel p (B.w j)
    (∑ j, external i (B.value j) (v j)/scale i)+eval (table i).internal (c.t^2)*(c.t^2*c.n^2)=
      eval (table i).rhs (c.t^2) := by
  have h := raw_geometric_row hm B i
  have q := congrArg (fun z : ℝ ↦ z/scale i) h
  simp only [add_div,zero_div,Finset.sum_div,internal_eq] at q
  dsimp only
  rw [show (S.core p).t=S.ratio p from rfl]
  linarith only [q]

end EuclideanMidpointRigidity.Spectral.DerivativeRows

