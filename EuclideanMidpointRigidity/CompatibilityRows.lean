module

public import EuclideanMidpointRigidity.GeometricMoments

/-! # Compatibility equations and reconstructed jets in the mixed plane

The four compatibility equations eliminate the higher jet coordinates. Six
further equations give the jet coordinates needed when differentiating the
resonant cubic and the sixth-order force. All formulas retain the external sum.
-/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity.Quartic
set_option maxHeartbeats 1500000

inductive Reduction
  | c111
  | c222
  | c112
  | c122
  | s111
  | s222
  | s112
  | j1xy
  | s122
  | j2xy

def Reduction.internal : Reduction → ℝ → ℝ → ℝ
  | .c111, t, n => 101375244140625*n^2*t^4/538769212081 + 332731546875*n^2*t^2/3728506658 + 279/26
  | .c222, t, n => -4757711*n^2*t^4/86354 + 87927*n^2*t^2/67600 + 44*t^4/25
  | .c112, t, n => 176176518984375*n^2*t^4/3866461404346 - 142588075*n^2*t^2/10535188 + 39*t^2/61
  | .c122, t, n => -6742475671750*n^2*t^4/538769212081 + 824089*n^2*t^2/143131755 + 3188*t^2/82875
  | .s111, t, n => 47308447265625*n^2*t^4/1077538424162 + 136785796875*n^2*t^2/7457013316 + 23/26
  | .s222, t, n => -683795*n^2*t^4/43177 + 7791*n^2*t^2/27040 + 2*t^4/5
  | .s112, t, n => 13620673828125*n^2*t^4/1933230702173 - 106925875*n^2*t^2/21070376 - 25*t^2/244
  | .j1xy, t, n => 27536635546875*n^2*t^4/3866461404346 - 255912125*n^2*t^2/84281504 - 85*t^2/488
  | .s122, t, n => 2722975766875*n^2*t^4/1616307636243 + 272479109*n^2*t^2/687032424 + 6176*t^2/49725
  | .j2xy, t, n => 20871466695625*n^2*t^4/6465230544972 + 168889*n^2*t^2/26424324 + 10147*t^2/99450

def Reduction.external (row : Reduction) (s : ℝ) (v : MixedChannel) : ℝ :=
  let z := (1-2*s)⁻¹
  match row with
  | .c111 => 85*v.q*v.r1w + 20*v.q*v.rw1*z - 30*v.q*v.rw1 - 32*v.q*v.z1w
  | .c222 => -90*v.h*v.r2w + 156*v.h*v.rw2*z/5 + 40*v.h*v.rw2 + 38*v.h*v.z2w
  | .c112 => 1245*v.l*v.r1w/122 - 815*v.l*v.rw1/122 - 5*v.l*v.z1w/61 + 850*v.q*v.r2w/61 - 467*v.q*v.rw2*z/122 - 623*v.q*v.rw2/122 - 649*v.q*v.z2w/61
  | .c122 => 167*v.h*v.r1w/17 - 956*v.h*v.rw1*z/1275 - 581*v.h*v.rw1/255 - 338*v.h*v.z1w/51 + 403*v.l*v.r2w/51 - 563*v.l*v.rw2/255 + 214*v.l*v.z2w/255
  | .s111 => 10*v.q*v.r1w + v.q*v.rw1*z - 4*v.q*v.rw1 - 4*v.q*v.z1w
  | .s222 => -25*v.h*v.r2w + 8*v.h*v.rw2*z + 10*v.h*v.rw2 + 10*v.h*v.z2w
  | .s112 => 475*v.l*v.r1w/122 - 235*v.l*v.rw1/122 - 95*v.l*v.z1w/61 + 275*v.q*v.r2w/122 - 75*v.q*v.rw2*z/61 - 125*v.q*v.rw2/122 - 70*v.q*v.z2w/61
  | .j1xy => 175*v.l*v.r1w/61 - 125*v.l*v.rw1/122 - 70*v.l*v.z1w/61 + 325*v.q*v.r2w/244 - 205*v.q*v.rw2*z/244 - 30*v.q*v.rw2/61 - 55*v.q*v.z2w/122
  | .s122 => 20*v.h*v.r1w/51 - 737*v.h*v.rw1*z/765 - 47*v.h*v.rw1/153 - 70*v.h*v.z1w/153 + 5*v.l*v.r2w/153 - 71*v.l*v.rw2/153 - 2*v.l*v.z2w/153
  | .j2xy => -55*v.h*v.r1w/51 - 332*v.h*v.rw1*z/765 + 131*v.h*v.rw1/306 + 65*v.h*v.z1w/153 - 665*v.l*v.r2w/306 + 263*v.l*v.rw2/306 + 133*v.l*v.z2w/153

def Reduction.target (row : Reduction) (p : CoreEntries) : ℝ :=
  match row with
  | .c111 => 0
  | .c222 => 0
  | .c112 => 0
  | .c122 => 0
  | .s111 => p.s111
  | .s222 => p.t^3*p.s222
  | .s112 => p.t^1*p.s112
  | .j1xy => p.t^1*p.j1xy
  | .s122 => p.t^2*p.s122
  | .j2xy => p.t^2*p.j2xy

def Reduction.combination {ι : Type*} (row : Reduction) (p : CoreEntries) (s : ι → ℝ) (v : ι → MixedChannel) : Moment ι :=
  let H := highMoment p v
  let D := diagMoment p s v
  match row with
  | .c111 => ((((H .oneNormal).scale (8)).add (H .oneTangent)).add ((D .j1xx).scale (20)))
  | .c222 => ((((H .twoNormal).scale (-19/2)).add (H .twoTangent)).add ((D .j2yy).scale (156/5))).scale (p.t^3)
  | .c112 => (((((H .xxyNormal).scale (109/122)).add ((H .xxyFirst).scale (-187/244))).add (H .xxySecond)).add ((D .j2xx).scale (-467/122))).scale (p.t^1)
  | .c122 => (((((H .xyyNormal).scale (41/85)).add ((H .xyySecond).scale (-89/510))).add (H .xyyFirst)).add ((D .j1yy).scale (-956/1275))).scale (p.t^2)
  | .s111 => ((H .oneNormal).add (D .j1xx))
  | .s222 => (((H .twoNormal).scale (-5/2)).add ((D .j2yy).scale (8))).scale (p.t^3)
  | .s112 => ((((H .xxyNormal).scale (55/244)).add ((H .xxyFirst).scale (-15/244))).add ((D .j2xx).scale (-75/61))).scale (p.t^1)
  | .j1xy => ((((H .xxyNormal).scale (65/488)).add ((H .xxyFirst).scale (5/244))).add ((D .j2xx).scale (-205/244))).scale (p.t^1)
  | .s122 => ((((H .xyyNormal).scale (2/51)).add ((H .xyySecond).scale (-23/306))).add ((D .j1yy).scale (-737/765))).scale (p.t^2)
  | .j2xy => ((((H .xyyNormal).scale (-11/102)).add ((H .xyySecond).scale (-1/612))).add ((D .j1yy).scale (-332/765))).scale (p.t^2)

theorem Reduction.identity {ι : Type*} [Fintype ι] (row : Reduction) {p : CoreEntries}
    {s : ι → ℝ} {v : ι → MixedChannel} (hn : p.Normalized) (ht : p.t≠0) (hm : QuarticMoments p s v) :
    row.internal p.t p.n+∑ i, row.external (s i) (v i)=row.target p := by
  have hz : (row.combination p s v).total=0 := by
    cases row <;> simp [combination,hm.high,hm.diagonal]
  have hi : (row.combination p s v).internal=row.internal p.t p.n-row.target p := by
    have hd : p.d2= -(159/1300)*p.n/p.t := (eq_div_iff ht).mpr (by linear_combination hn.d2)
    cases row <;> dsimp only [combination,highMoment,diagMoment,Moment.add,Moment.scale,HighRow.core,
      DiagonalRow.internal,internal,target] <;>
      simp only [hn.r11,hn.r12,hn.r21,hn.r22,hn.z11,hn.z12,hn.z22,hn.m,hn.d1,hd,ResonantPlane.k] <;>
      field_simp [ht] <;> ring
  have he (i : ι) : (row.combination p s v).external i=row.external (s i) (v i) := by
    cases row <;> dsimp only [combination,highMoment,diagMoment,Moment.add,Moment.scale,HighRow.outside,
      DiagonalRow.external,external,MixedChannel.unscaled] <;> simp only [div_eq_mul_inv]
    all_goals
      generalize (1-2*s i)⁻¹=z
      field_simp [ht]
      ring
  simp only [Moment.total,hi,he] at hz
  linarith only [hz]

end EuclideanMidpointRigidity.Quartic
