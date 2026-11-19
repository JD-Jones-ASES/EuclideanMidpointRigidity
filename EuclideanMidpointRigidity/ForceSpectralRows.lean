module

public import EuclideanMidpointRigidity.ForceMoments
public import EuclideanMidpointRigidity.QuarticSpectralRows

/-! # The homogeneous and inhomogeneous force rows in the certificate -/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity.Spectral.ForceRows
open IntervalPolynomial Quartic MixedChannel LiftedSection
set_option maxHeartbeats 1000000

def scale : ForceAxis → ℝ
  | .positive => 212135699951/1089633424464
  | .negative => 8673/4394

def table : ForceAxis → Row
  | .positive => physicalRows.getD 7 Row.zero
  | .negative => physicalRows.getD 8 Row.zero

theorem scale_pos (i : ForceAxis) : 0<scale i := by cases i <;> norm_num [scale]

theorem internal_eq (i : ForceAxis) (t n : ℝ) :
    i.internal t n/scale i=eval (table i).internal (t^2)*(t^2*n^2)-eval (table i).rhs (t^2) := by
  cases i <;> norm_num [scale,table,physicalRows,ForceAxis.internal,ForceAxis.pick,eval,List.getD] <;> ring

private theorem regular_formula (i : ForceAxis) {s : ℝ} (hd : regularDenominator s≠0) (l h : ℝ) :
    i.external s (inRegular s l h)/scale i=(table i).atChannel s (l/regularDenominator s) (h/regularDenominator s) := by
  have hgap : 1-2*s≠0 := by
    intro hz
    apply hd
    have he : 2*s-1=0 := by linarith only [hz]
    simp [regularDenominator,he]
  cases i <;>
    norm_num [scale,table,physicalRows,Row.atChannel,eval,List.getD,ForceAxis.external,ForceAxis.phi,
      ForceAxis.outsideColumn,ForceColumn.cost,ForceAxis.hExternal,ForceAxis.sKind,ForceAxis.pick,phiX,phiY,
      CubicSlot.external,CubicSlot.reconstruction,CubicSlot.angular,Reduction.external,inRegular] <;>
    field_simp [hd,hgap] <;>
    simp only [regularDenominator,regular_q,regular_r1w,regular_rw1,regular_z1w,regular_r2w,regular_rw2,
      regular_z2w,regular_rot1,regular_rot2] <;> ring

theorem external_eq (i : ForceAxis) {v : MixedChannel} {s : ℝ} (hv : v.Equations s) (hd : regularDenominator s≠0) :
    i.external s v/scale i=(table i).atChannel s (v.l/regularDenominator s) (v.h/regularDenominator s) := by
  simpa only [inRegular_eq hv hd] using regular_formula i hd v.l v.h

theorem geometric_row {d : ℕ} {S : LiftedSection d} {p : Space d} (hm : S.IsMixed p)
    {ι : Type*} [Fintype ι] (B : SpectralFrame S p ι) (i : ForceAxis) :
    let t := S.ratio p
    let n := (S.core p).n
    let v := fun j ↦ S.channel p (B.w j)
    (∑ j, i.external (B.value j) (v j)/scale i)+eval (table i).internal (t^2)*(t^2*n^2)=
      eval (table i).rhs (t^2)+i.source (S.a p) (S.u p)/scale i := by
  have h := i.geometric_force hm B
  have q := congrArg (fun z : ℝ ↦ z/scale i) h
  simp only [add_div,Finset.sum_div,internal_eq] at q
  dsimp only
  linarith only [q]

end EuclideanMidpointRigidity.Spectral.ForceRows

