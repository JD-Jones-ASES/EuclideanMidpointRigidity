module

public import EuclideanMidpointRigidity.CompatibilityRows
public import EuclideanMidpointRigidity.ChannelOverlap

/-! # The first four rows of the spectral certificate from the geometric quartic -/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity.Spectral.QuarticRows
open IntervalPolynomial Quartic MixedChannel

def kind : Fin 4 → Reduction := ![.c111,.c222,.c112,.c122]
def scale : Fin 4 → ℝ := ![279/26,44/25,39/61,3188/82875]
def table (i : Fin 4) : Row := physicalRows.getD i.val Row.zero

theorem scale_pos (i : Fin 4) : 0<scale i := by fin_cases i <;> norm_num [scale]

theorem internal_eq (i : Fin 4) (t n : ℝ) :
    (kind i).internal t n/scale i=eval (table i).internal (t^2)*(t^2*n^2)-eval (table i).rhs (t^2) := by
  fin_cases i <;> norm_num [kind,scale,table,physicalRows,Reduction.internal,eval,List.getD] <;> ring

private theorem regular_formula (i : Fin 4) {s : ℝ} (hd : regularDenominator s≠0) (l h : ℝ) :
    (kind i).external s (inRegular s l h)/scale i=(table i).atChannel s (l/regularDenominator s) (h/regularDenominator s) := by
  have hgap : 1-2*s≠0 := by
    intro hz
    apply hd
    have he : 2*s-1=0 := by linarith only [hz]
    simp [regularDenominator,he]
  fin_cases i <;>
    norm_num [kind,scale,table,physicalRows,Row.atChannel,eval,List.getD,Reduction.external,inRegular] <;>
    field_simp [hd,hgap] <;>
    simp only [regularDenominator,regular_q,regular_r1w,regular_rw1,regular_z1w,
      regular_r2w,regular_rw2,regular_z2w] <;> ring

theorem external_eq (i : Fin 4) {v : MixedChannel} {s : ℝ} (hv : v.Equations s) (hd : regularDenominator s≠0) :
    (kind i).external s v/scale i=(table i).atChannel s (v.l/regularDenominator s) (v.h/regularDenominator s) := by
  simpa only [inRegular_eq hv hd] using regular_formula i hd v.l v.h

theorem geometric_row {d : ℕ} {S : LiftedSection d} {p : Space d} (hm : S.IsMixed p)
    {ι : Type*} [Fintype ι] (B : LiftedSection.SpectralFrame S p ι) (i : Fin 4) :
    let c := S.core p
    let v := fun j ↦ S.channel p (B.w j)
    (∑ j, (kind i).external (B.value j) (v j)/scale i)+eval (table i).internal (c.t^2)*(c.t^2*c.n^2)=
      eval (table i).rhs (c.t^2) := by
  let c := S.core p
  have ht : c.t≠0 := (div_pos (norm_pos_iff.mpr hm.2.2) (norm_pos_iff.mpr hm.2.1)).ne'
  have h := (kind i).identity (S.normalized_entries hm) ht (geometric_quartic_moments hm B)
  have hz : (kind i).target c=0 := by fin_cases i <;> rfl
  change (kind i).internal c.t c.n+_= (kind i).target c at h
  rw [hz] at h
  have q := congrArg (fun z : ℝ ↦ z/scale i) h
  simp only [add_div,zero_div,Finset.sum_div,internal_eq] at q
  dsimp only
  change _+eval (table i).internal (c.t^2)*(c.t^2*c.n^2)=eval (table i).rhs (c.t^2)
  linarith only [q]

end EuclideanMidpointRigidity.Spectral.QuarticRows
