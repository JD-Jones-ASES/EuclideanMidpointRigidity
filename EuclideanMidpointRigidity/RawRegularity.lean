module

public import EuclideanMidpointRigidity.DerivativeSpectralRows
public import EuclideanMidpointRigidity.ForceSpectralRows
public import EuclideanMidpointRigidity.GeometricNormTests

/-! # The raw spectral rows at singular strict eigenvalues and at the null value -/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity
open Spectral Quartic

namespace MixedChannel

def zero : MixedChannel := ⟨0,0,0,0,0,0,0,0,0,0,0⟩

structure ContinuousCoordinates (f : ℝ → MixedChannel) (s : ℝ) : Prop where
  q : ContinuousAt (fun t ↦ (f t).q) s
  l : ContinuousAt (fun t ↦ (f t).l) s
  h : ContinuousAt (fun t ↦ (f t).h) s
  r1w : ContinuousAt (fun t ↦ (f t).r1w) s
  rw1 : ContinuousAt (fun t ↦ (f t).rw1) s
  z1w : ContinuousAt (fun t ↦ (f t).z1w) s
  r2w : ContinuousAt (fun t ↦ (f t).r2w) s
  rw2 : ContinuousAt (fun t ↦ (f t).rw2) s
  z2w : ContinuousAt (fun t ↦ (f t).z2w) s
  rot1 : ContinuousAt (fun t ↦ (f t).rot1) s
  rot2 : ContinuousAt (fun t ↦ (f t).rot2) s

theorem angular_continuous {s : ℝ} (hd : angularDenominator s≠0) (o p : ℝ) :
    ContinuousCoordinates (fun t ↦ inAngular t o p) s := by
  have hc : ContinuousAt angularDenominator s := by unfold angularDenominator; fun_prop
  constructor <;> dsimp only [inAngular,angular_q,angular_l,angular_h,angular_r1w,angular_rw1,angular_z1w,
    angular_r2w,angular_rw2,angular_z2w] <;> fun_prop (disch := assumption)

end MixedChannel
open MixedChannel

structure RawRegularity (F : ℝ → MixedChannel → ℝ) : Prop where
  null : ∀ s, F s MixedChannel.zero=0
  strict : ∀ {f : ℝ → MixedChannel} {s : ℝ}, ContinuousCoordinates f s → s<1/2 →
    ContinuousAt (fun t ↦ F t (f t)) s

theorem Quartic.Reduction.regularity (r : Reduction) : RawRegularity r.external := by
  constructor
  · intro s; cases r <;> simp [Reduction.external,MixedChannel.zero]
  · intro f s hf hs
    have hgap : 1-2*s≠0 := by linarith
    obtain ⟨q,l,h,a,b,c,d,e,g,o,p⟩ := hf
    cases r <;> dsimp only [Reduction.external] <;> fun_prop (disch := assumption)

theorem Quartic.CubicSlot.regularity (i : CubicSlot) : RawRegularity i.external := by
  constructor
  · intro s; simp only [CubicSlot.external,i.reconstruction.regularity.null]
    cases i <;> simp [CubicSlot.angular,MixedChannel.zero]
  · intro f s hf hs
    have h := i.reconstruction.regularity.strict hf hs
    obtain ⟨q,l,hc,a,b,c,d,e,g,o,p⟩ := hf
    unfold CubicSlot.external
    apply h.add
    cases i <;> dsimp only [CubicSlot.angular] <;> fun_prop

theorem Spectral.DerivativeRows.regularity (i : Fin 3) : RawRegularity (external i) := by
  constructor
  · intro s
    have hz (r : CubicSlot) := r.regularity.null s
    fin_cases i <;> simp [external,combine,hz]
  · intro f s hf hs
    have a := CubicSlot.d1.regularity.strict hf hs
    have b := CubicSlot.m.regularity.strict hf hs
    have c := CubicSlot.n.regularity.strict hf hs
    have d := CubicSlot.d2.regularity.strict hf hs
    fin_cases i <;> simp [external,combine] <;> fun_prop

theorem ForceAxis.regularity (i : ForceAxis) : RawRegularity i.external := by
  constructor
  · intro s
    have hn := CubicSlot.n.regularity.null s
    have hz (r : Reduction) := r.regularity.null s
    cases i <;> simp only [ForceAxis.external,hn,ForceAxis.hExternal,ForceAxis.sKind,ForceAxis.pick,hz] <;>
      simp [ForceAxis.outsideColumn,ForceAxis.pick,ForceColumn.cost,MixedChannel.zero]
  · intro f s hf hs
    have hN := CubicSlot.n.regularity.strict hf hs
    have hH := Reduction.j1xy.regularity.strict hf hs
    have h₁ := Reduction.s111.regularity.strict hf hs
    have h₂ := Reduction.s112.regularity.strict hf hs
    have gap : 1-2*s≠0 := by linarith
    obtain ⟨q,l,h,a,b,c,d,e,g,o,p⟩ := hf
    cases i <;> dsimp only [ForceAxis.external,ForceAxis.hExternal,ForceAxis.sKind,ForceAxis.pick,
      ForceAxis.outsideColumn,ForceColumn.cost] <;> fun_prop (disch := assumption)

theorem Spectral.NormTest.regularity (T : NormTest) : RawRegularity (fun _ v ↦ T.raw v) := by
  constructor
  · intro s; simp [raw,MixedChannel.zero]
  · intro f s hf _
    obtain ⟨q,l,h,_,_,_,_,_,_,_,_⟩ := hf
    dsimp only [raw]
    fun_prop

theorem LiftedSection.SpectralFrame.channel_at_half {d : ℕ} {S : LiftedSection d} {p : Space d}
    {ι : Type*} [Fintype ι] (B : S.SpectralFrame p ι) (hm : S.IsMixed p) (j : ι) (hs : B.value j=1/2) :
    S.channel p (B.w j)=MixedChannel.zero := by
  have h := B.physical_eigenvalue hm.1 j
  rw [hs] at h
  obtain ⟨_,he,hx,hy⟩ := B.transverse j
  have hc := S.null_channel hm h he hx hy
  cases hh : S.channel p (B.w j) with
  | mk q l h a b c d e g o p =>
    rw [hh] at hc
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := hc
    rfl

end EuclideanMidpointRigidity

