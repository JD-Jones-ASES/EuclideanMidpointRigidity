module

public import EuclideanMidpointRigidity.ChannelEntries
public import EuclideanMidpointRigidity.MomentSum

/-! # The ten quartic and four diagonal equations as scalar sums -/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity.Quartic

inductive DiagonalRow | j1xx | j2xx | j1yy | j2yy

def highMoment {ι : Type*} (p : CoreEntries) (v : ι → MixedChannel) (r : HighRow) : Moment ι :=
  ⟨r.core p,fun i ↦ r.outside ((v i).unscaled p.t)⟩

def DiagonalRow.internal (r : DiagonalRow) (p : CoreEntries) : ℝ :=
  match r with
  | .j1xx => p.j1xx+1/2+p.d1*p.r11/2+5/3*p.m*p.r21
  | .j2xx => p.j2xx+p.t/2+p.d1*p.r12/2+5/3*p.m*p.r22
  | .j1yy => p.j1yy-1/5+p.n*p.r11/2+5/3*p.d2*p.r21
  | .j2yy => p.j2yy-p.t/5+p.n*p.r12/2+5/3*p.d2*p.r22

def DiagonalRow.external (r : DiagonalRow) (s : ℝ) (a : OutsideEntries) : ℝ :=
  match r with
  | .j1xx => a.q*a.rw1/(1-2*s)
  | .j2xx => a.q*a.rw2/(1-2*s)
  | .j1yy => a.h*a.rw1/(1-2*s)
  | .j2yy => a.h*a.rw2/(1-2*s)

def diagMoment {ι : Type*} (p : CoreEntries) (s : ι → ℝ) (v : ι → MixedChannel) (r : DiagonalRow) : Moment ι :=
  ⟨r.internal p,fun i ↦ r.external (s i) ((v i).unscaled p.t)⟩

structure QuarticMoments {ι : Type*} [Fintype ι] (p : CoreEntries) (s : ι → ℝ) (v : ι → MixedChannel) : Prop where
  high : ∀ r, (highMoment p v r).total=0
  diagonal : ∀ r, (diagMoment p s v r).total=0

theorem geometric_quartic_moments {d : ℕ} {S : LiftedSection d} {p : Space d} (hm : S.IsMixed p)
    {ι : Type*} [Fintype ι] (B : LiftedSection.SpectralFrame S p ι) :
    QuarticMoments (S.core p) B.value (fun i ↦ S.channel p (B.w i)) := by
  constructor
  · exact B.high_equations hm
  · obtain ⟨a,b,c,d⟩ := B.diagonal_equations hm
    intro r
    cases r <;> dsimp only [diagMoment,DiagonalRow.internal,DiagonalRow.external,Moment.total]
    · change _+(∑ i, (B.entries i).q*(B.entries i).rw1/(1-2*B.value i))=0
      linarith only [a]
    · change _+(∑ i, (B.entries i).q*(B.entries i).rw2/(1-2*B.value i))=0
      linarith only [b]
    · change _+(∑ i, (B.entries i).h*(B.entries i).rw1/(1-2*B.value i))=0
      linarith only [c]
    · change _+(∑ i, (B.entries i).h*(B.entries i).rw2/(1-2*B.value i))=0
      linarith only [d]

end EuclideanMidpointRigidity.Quartic
