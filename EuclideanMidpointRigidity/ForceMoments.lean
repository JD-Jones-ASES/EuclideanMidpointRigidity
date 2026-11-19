module

public import EuclideanMidpointRigidity.ForceCoordinates
public import EuclideanMidpointRigidity.CubicDerivativeMoments

/-! # Weighted scalar moments of the two vector projections -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity.ForceAxis
open Quartic LiftedSection

def weight (i : ForceAxis) (t : ℝ) := i.pick 1 t
def phi (i : ForceAxis) := i.pick phiX phiY
def factor (i : ForceAxis) : ℝ := i.pick 2 1
def source (i : ForceAxis) (a u : ℝ) := i.pick ((7/13)*a^4/u^2) 0

def lowCost (i : ForceAxis) (P : CoreEntries) (O h : ℝ) :=
  (i.coreColumn P O 0).cost h+(i.coreColumn P O 1).cost h+(i.coreColumn P O 2).cost h

def jetH (i : ForceAxis) (P : CoreEntries) := i.pick P.j1xx (P.t*P.j1xy)
def jetS (i : ForceAxis) (P : CoreEntries) := i.pick P.s111 (P.t*P.s112)

theorem direct_eq (i : ForceAxis) (P : CoreEntries) :
    i.weight P.t*i.directJet P=(7/13:ℝ)^2/2*(15*i.jetH P-11*i.jetS P) := by
  cases i <;> dsimp only [weight,directJet,jetH,jetS,pick] <;> ring

theorem outside_cost (i : ForceAxis) {t : ℝ} (ht : t≠0) (h : ℝ) (v : MixedChannel) :
    i.weight t*(i.outsideColumn t v).cost h=(i.outsideColumn 1 v).cost 0 := by
  cases i <;> dsimp only [weight,outsideColumn,pick,ForceColumn.cost] <;> field_simp <;> ring

theorem balance {d : ℕ} {S : LiftedSection d} {p : Space d} (hm : S.IsMixed p) (i : ForceAxis) :
    let t := S.ratio p
    let n := (S.core p).n
    let f := i.field S
    i.phi*(i.factor*ratioSource t n+t^2*S.rate (S.shape S.x S.y S.y) p)+
      2*S.drift p*(i.phi*t^2*n)-i.weight t*(⟪S.psi p,S.rate f p⟫_ℝ+⟪S.forceTerm p,f p⟫_ℝ)=
      i.source (S.a p) (S.u p) := by
  obtain ⟨q₁,q₂⟩ := S.projected_equations hm
  have hr := (S.ratio_rates hm).2
  rw [← S.shape_n p] at hr
  change S.rate S.ratio p=S.ratio p*(S.core p).n*(4164755/4490408+1261750/734009*(S.ratio p)^2) at hr
  rw [hr] at q₁ q₂
  cases i <;> dsimp only [phi,factor,weight,field,source,pick,ratioSource]
  · linear_combination q₁
  · linear_combination S.ratio p*q₂

theorem cost_identity {d : ℕ} {S : LiftedSection d} {p : Space d} (hm : S.IsMixed p)
    {ι : Type*} [Fintype ι] (B : SpectralFrame S p ι) (i : ForceAxis) :
    let P := S.core p
    let f := i.field S
    i.weight P.t*(⟪S.psi p,S.rate f p⟫_ℝ+⟪S.forceTerm p,f p⟫_ℝ)=
      i.weight P.t*i.lowCost P (S.omega p) (S.drift p)+
      (∑ j, (i.outsideColumn 1 (S.channel p (B.w j))).cost 0)+
      (7/13:ℝ)^2/2*(15*i.jetH P-11*i.jetS P) := by
  let t := S.ratio p
  have ht : t≠0 := (div_pos (norm_pos_iff.mpr hm.2.2) (norm_pos_iff.mpr hm.2.1)).ne'
  have h := B.force_cost hm i
  dsimp only
  rw [h,show i.coreCost (S.core p) (S.omega p) (S.drift p)=i.lowCost (S.core p) (S.omega p) (S.drift p)+
    i.directJet (S.core p) from rfl,mul_add,mul_add,i.direct_eq]
  have he (j : ι) := i.outside_cost ht (S.drift p) (S.channel p (B.w j))
  have es : i.weight t*(∑ j, (i.outsideColumn t (S.channel p (B.w j))).cost (S.drift p))=
      ∑ j, (i.outsideColumn 1 (S.channel p (B.w j))).cost 0 := by simp only [Finset.mul_sum,he]
  change _+i.weight t*(∑ j, (i.outsideColumn t (S.channel p (B.w j))).cost (S.drift p))=_
  rw [es]
  ring

def hInternal (i : ForceAxis) (P : CoreEntries) :=
  i.pick (-1/2-P.d1*P.r11/2-(5/3)*P.m*P.r21) (Reduction.j1xy.internal P.t P.n)

def hExternal (i : ForceAxis) (s : ℝ) (v : MixedChannel) :=
  i.pick (-(v.q*v.rw1/(1-2*s))) (Reduction.j1xy.external s v)

def sKind (i : ForceAxis) := i.pick Reduction.s111 Reduction.s112

theorem h_identity {d : ℕ} {S : LiftedSection d} {p : Space d} (hm : S.IsMixed p)
    {ι : Type*} [Fintype ι] (B : SpectralFrame S p ι) (i : ForceAxis) :
    i.hInternal (S.core p)+(∑ j, i.hExternal (B.value j) (S.channel p (B.w j)))=i.jetH (S.core p) := by
  have ht : (S.core p).t≠0 := (div_pos (norm_pos_iff.mpr hm.2.2) (norm_pos_iff.mpr hm.2.1)).ne'
  cases i with
  | negative =>
    have h := (B.diagonal_equations hm).1
    dsimp only [hInternal,hExternal,jetH,pick,Finset.sum_neg_distrib]
    rw [Finset.sum_neg_distrib]
    exact (by simpa only [SpectralFrame.entries,MixedChannel.unscaled,sub_eq_add_neg] using h.symm)
  | positive =>
    simpa only [hInternal,hExternal,jetH,pick,Reduction.target,pow_one] using
      Reduction.j1xy.identity (S.normalized_entries hm) ht (geometric_quartic_moments hm B)

theorem s_identity {d : ℕ} {S : LiftedSection d} {p : Space d} (hm : S.IsMixed p)
    {ι : Type*} [Fintype ι] (B : SpectralFrame S p ι) (i : ForceAxis) :
    i.sKind.internal (S.ratio p) (S.core p).n+(∑ j, i.sKind.external (B.value j) (S.channel p (B.w j)))=
      i.jetS (S.core p) := by
  have ht : (S.core p).t≠0 := (div_pos (norm_pos_iff.mpr hm.2.2) (norm_pos_iff.mpr hm.2.1)).ne'
  have h := i.sKind.identity (S.normalized_entries hm) ht (geometric_quartic_moments hm B)
  cases i <;> simpa only [sKind,pick,Reduction.target,jetS,pow_one,show (S.core p).t=S.ratio p from rfl] using h

def internal (i : ForceAxis) (t n : ℝ) : ℝ :=
  let r := t^2
  i.pick (53555352865*r/75917082852+8673/4394+
      r*n^2*(50131355036899062500*r/1186384351771088187+375582348561851375/13111487545203216))
    (212135699951*r/1089633424464+
      r*n^2*(-365993401132435365625*r/110682681288761521446-42320730175835825/188188409472328512))

def external (i : ForceAxis) (s : ℝ) (v : MixedChannel) : ℝ :=
  i.phi*CubicSlot.n.external s v-(i.outsideColumn 1 v).cost 0-
    (15*((7/13:ℝ)^2/2))*i.hExternal s v+(11*((7/13:ℝ)^2/2))*i.sKind.external s v

theorem internal_identity (i : ForceAxis) {P : CoreEntries} (hn : P.Normalized) :
    let t := P.t
    let n := P.n
    let h := -(1261750/734009)*t^2*n
    let O := (10/7)*(P.z12+(7/26)*P.m)
    i.internal t n=i.phi*(i.factor*ratioSource t n+CubicSlot.n.internal t n)+
      2*h*(i.phi*t^2*n)-i.weight t*i.lowCost P O h-
      (15*((7/13:ℝ)^2/2))*i.hInternal P+(11*((7/13:ℝ)^2/2))*i.sKind.internal t n := by
  cases i <;> dsimp only [internal,phi,factor,weight,lowCost,coreColumn,ForceColumn.cost,
    hInternal,sKind,pick,CubicSlot.internal,CubicSlot.framePart,CubicSlot.reconstruction,Reduction.internal,
    ratioSource,phiX,phiY]
  all_goals simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,
    Function.comp_apply,Matrix.cons_val_succ,
    hn.r11,hn.r12,hn.r21,hn.r22,hn.z11,hn.z12,hn.z22,hn.d1,hn.m,ResonantPlane.k]
  all_goals ring

theorem geometric_force {d : ℕ} {S : LiftedSection d} {p : Space d} (hm : S.IsMixed p)
    {ι : Type*} [Fintype ι] (B : SpectralFrame S p ι) (i : ForceAxis) :
    i.internal (S.ratio p) (S.core p).n+(∑ j, i.external (B.value j) (S.channel p (B.w j)))=
      i.source (S.a p) (S.u p) := by
  let P := S.core p
  let t := P.t
  let v := fun j ↦ S.channel p (B.w j)
  have hc := i.cost_identity hm B
  have h := i.balance hm
  have hn := CubicSlot.weighted_identity hm B .n
  have hH := i.h_identity hm B
  have hS := i.s_identity hm B
  change _+_-i.weight t*_=i.source _ _ at h
  dsimp only [CubicSlot.shape,CubicSlot.weight] at hn
  change (S.ratio p)^2*S.rate (S.shape S.x S.y S.y) p=_ at hn
  rw [hc,hn,← hH,← hS] at h
  change i.internal P.t P.n+(∑ j, i.external (B.value j) (v j))=_
  rw [i.internal_identity (S.normalized_entries hm)]
  simp only [external,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
  rw [S.drift_eq hm] at h
  dsimp only [t,P,v,LiftedSection.omega] at *
  simp only [show (S.core p).t=S.ratio p from rfl] at *
  linear_combination h

end EuclideanMidpointRigidity.ForceAxis

