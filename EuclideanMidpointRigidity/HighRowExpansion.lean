module

public import EuclideanMidpointRigidity.ResonantEntries

/-! # Ten projected higher rows of the quartic equation

Each equation is the sum of its contribution in the three distinguished
directions and one contribution per external direction.
-/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity.Quartic
variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

inductive HighRow
  | oneNormal
  | oneTangent
  | twoNormal
  | twoTangent
  | xxyNormal
  | xxyFirst
  | xxySecond
  | xyyNormal
  | xyySecond
  | xyyFirst

def HighRow.test (r : HighRow) (c : Coeff) (J : E →L[ℝ] Coeff) (e x y w : E) : ℝ :=
  match r with
  | .oneNormal => termAt c J .threeOne w e x e e
  | .oneTangent => termAt c J .twoTwo w x e x x
  | .twoNormal => termAt c J .threeOne w e y e e
  | .twoTangent => termAt c J .twoTwo w y e y y
  | .xxyNormal => termAt c J .twoOneOne w e x e y
  | .xxyFirst => termAt c J .twoOneOne w x e x y
  | .xxySecond => termAt c J .twoTwo w y e x x
  | .xyyNormal => termAt c J .twoOneOne w e y e x
  | .xyySecond => termAt c J .twoOneOne w y e y x
  | .xyyFirst => termAt c J .twoTwo w x e y y

def HighRow.core (r : HighRow) (p : CoreEntries) : ℝ :=
  match r with
  | .oneNormal => 6*p.d1*p.r11 - 4*p.d1*p.z11 - p.j1xx + 10*p.m*p.r12 - 4*p.m*p.r21 - 4*p.m*p.z12 - p.s111 + 5/13
  | .oneTangent => 7*p.d1*p.r11 - 12*p.j1xx + 5*p.m*p.r12 + 2*p.m*p.r21 + 8*p.s111 - 61/26
  | .twoNormal => 6*p.d2*p.r22 - 4*p.d2*p.z22 + 16*p.j2yy/5 - 4*p.n*p.r12 + 10*p.n*p.r21 - 4*p.n*p.z12 + 2*p.s222/5 - 4*p.t/5
  | .twoTangent => 7*p.d2*p.r22 - 4*p.j2yy/5 + 2*p.n*p.r12 + 5*p.n*p.r21 + 19*p.s222/5 + 2*p.t/5
  | .xxyNormal => -4*p.d1*p.r12 + 10*p.d1*p.r21 - 4*p.d1*p.z12 - 24*p.j1xy/5 + 6*p.j2xx + 12*p.m*p.r11 + 6*p.m*p.r22 - 8*p.m*p.z11 - 4*p.m*p.z22 + 20*p.n*p.r12 - 8*p.n*p.r21 - 8*p.n*p.z12 - 8*p.s112/5 + 2*p.t
  | .xxyFirst => 2*p.d1*p.r12 + 4*p.d1*p.z12 - 88*p.j1xy/5 + 2*p.j2xx + 12*p.m*p.r11 + 2*p.m*p.r22 - 4*p.m*p.z11 + 4*p.m*p.z22 + 10*p.n*p.r12 + 2*p.n*p.r21 - 4*p.n*p.z12 + 52*p.s112/5 - p.t
  | .xxySecond => 5*p.d1*p.r21 - 4*p.d1*p.z12 - 46*p.j1xy/5 + 2*p.m*p.r11 + 5*p.m*p.r22 + 4*p.m*p.z11 - 4*p.m*p.z22 + 2*p.n*p.r21 + 4*p.n*p.z12 + 47*p.s112/5
  | .xyyNormal => 10*p.d2*p.r12 - 4*p.d2*p.r21 - 4*p.d2*p.z12 - 19*p.j1yy/5 + 46*p.j2xy/5 - 8*p.m*p.r12 + 20*p.m*p.r21 - 8*p.m*p.z12 + 6*p.n*p.r11 + 12*p.n*p.r22 - 4*p.n*p.z11 - 8*p.n*p.z22 - p.s122/5 - 2/13
  | .xyySecond => 2*p.d2*p.r21 + 4*p.d2*p.z12 - 74*p.j1yy/5 + 24*p.j2xy/5 + 2*p.m*p.r12 + 10*p.m*p.r21 - 4*p.m*p.z12 + 2*p.n*p.r11 + 12*p.n*p.r22 + 4*p.n*p.z11 - 4*p.n*p.z22 + 66*p.s122/5 + 54/65
  | .xyyFirst => 5*p.d2*p.r12 - 4*p.d2*p.z12 - 18*p.j2xy/5 + 2*p.m*p.r12 + 4*p.m*p.z12 + 5*p.n*p.r11 + 2*p.n*p.r22 - 4*p.n*p.z11 + 4*p.n*p.z22 + 12*p.s122/5 + 7/65

def HighRow.outside (r : HighRow) (p : OutsideEntries) : ℝ :=
  match r with
  | .oneNormal => 10*p.q*p.r1w - 4*p.q*p.rw1 - 4*p.q*p.z1w
  | .oneTangent => 5*p.q*p.r1w + 2*p.q*p.rw1
  | .twoNormal => 10*p.h*p.r2w - 4*p.h*p.rw2 - 4*p.h*p.z2w
  | .twoTangent => 5*p.h*p.r2w + 2*p.h*p.rw2
  | .xxyNormal => 20*p.l*p.r1w - 8*p.l*p.rw1 - 8*p.l*p.z1w + 10*p.q*p.r2w - 4*p.q*p.rw2 - 4*p.q*p.z2w
  | .xxyFirst => 10*p.l*p.r1w + 2*p.l*p.rw1 - 4*p.l*p.z1w + 2*p.q*p.rw2 + 4*p.q*p.z2w
  | .xxySecond => 2*p.l*p.rw1 + 4*p.l*p.z1w + 5*p.q*p.r2w - 4*p.q*p.z2w
  | .xyyNormal => 10*p.h*p.r1w - 4*p.h*p.rw1 - 4*p.h*p.z1w + 20*p.l*p.r2w - 8*p.l*p.rw2 - 8*p.l*p.z2w
  | .xyySecond => 2*p.h*p.rw1 + 4*p.h*p.z1w + 10*p.l*p.r2w + 2*p.l*p.rw2 - 4*p.l*p.z2w
  | .xyyFirst => 5*p.h*p.r1w - 4*p.h*p.z1w + 2*p.l*p.rw2 + 4*p.l*p.z2w

set_option maxHeartbeats 1200000 in
theorem HighRow.core_eq (r : HighRow) {c : Coeff} {J : E →L[ℝ] Coeff} {e x y : E} {t : ℝ}
    (hc : CoreLeading c J e x y t) :
    r.test c J e x y e+r.test c J e x y x+r.test c J e x y y=r.core (CoreEntries.ofJet c J e x y t) := by
  obtain ⟨a,b,f,g,h,i,j,k,l,m,n⟩ := hc
  cases r <;> dsimp only [test,termAt,Pattern.eval,row22,row211,row31,contraction,core,CoreEntries.ofJet]
  all_goals
    simp only [cubicEntry_swap₁,cubicEntry_swap₂,jetEntry_swap₁,jetEntry_swap₂] at *
    simp only [a,b,f,g,h,i,k,l,m,n]
    ring

set_option maxHeartbeats 1200000 in
theorem HighRow.outside_eq (r : HighRow) {c : Coeff} {J : E →L[ℝ] Coeff} {e x y w : E}
    (hc : OutsideLeading c J e x y w) :
    r.test c J e x y w=r.outside (OutsideEntries.ofJet c J e x y w) := by
  obtain ⟨a,b,f,g,h⟩ := hc
  cases r <;> dsimp only [test,termAt,Pattern.eval,row22,row211,row31,contraction,outside,OutsideEntries.ofJet]
  all_goals
    simp only [cubicEntry_swap₁,jetEntry_swap₁,jetEntry_swap₂] at *
    simp only [a,b,f]
    ring

theorem HighRow.sum_zero (r : HighRow) {S : LiftedSection d} {p : Space d} (hm : S.IsMixed p)
    {ι : Type*} [Fintype ι] (B : LiftedSection.SpectralFrame S p ι) :
    let c := S.cubic p
    let J := S.jet p
    let e := S.axis p
    let x := S.x p
    let y := S.y p
    r.core (CoreEntries.ofJet c J e x y (S.ratio p))+
      ∑ i, r.outside (OutsideEntries.ofJet c J e x y (B.w i))=0 := by
  let g := r.test (S.cubic p) (S.jet p) (S.axis p) (S.x p) (S.y p)
  have hz : ∑ i, g (B.basis i)=0 := by
    cases r <;> apply sum_termAt_eq_zero B.basis (S.normalized_obstruction hm.1)
  rw [Fintype.sum_sum_type,Fin.sum_univ_three] at hz
  simp only [B.internal,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hz
  change g (S.axis p)+g (S.x p)+g (S.y p)+(∑ i, g (B.w i))=0 at hz
  dsimp only [g] at hz
  rw [r.core_eq (core_leading S hm)] at hz
  have hw (i : ι) := r.outside_eq (outside_leading S hm (B.transverse i).2.1
    (B.transverse i).2.2.1 (B.transverse i).2.2.2)
  simpa only [hw] using hz

end EuclideanMidpointRigidity.Quartic
