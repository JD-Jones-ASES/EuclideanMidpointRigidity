module

public import EuclideanMidpointRigidity.ExponentialPrimitives
public import EuclideanMidpointRigidity.ExactScalarJets

/-! # Boundary jets for the one-, two- and three-tilt source functions -/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace EuclideanMidpointRigidity.Endpoint
open RationalJet

def QuadraticMode.evalJet (P : QuadraticMode) (x e : RationalJet) : RationalJet :=
  ((const P.a).add ((scale P.b x).add (scale P.c (x.mul x)))).mul e

private theorem evalJet_value (P : QuadraticMode) (x e : RationalJet) (q : ℚ) (h : ℝ)
    (he : e.value h=Real.exp ((q:ℝ)*x.value h)) :
    (P.evalJet x e).value h=P.value q (x.value h) := by
  dsimp [QuadraticMode.evalJet,RationalJet.mul,add,const,scale,QuadraticMode.value,QuadraticMode.eval]
  rw [he]; ring

def QuadraticMode.boundaryJet (P : QuadraticMode) (η q : ℚ) : RationalJet :=
  let plus := expTime η
  let minus := expTime (-η)
  let center := expMid η
  (((plus.sub minus).mul (P.evalJet mid (expMid q))).sub
    ((plus.sub center).mul (P.evalJet (scale (-1) time) (expTime (-q))))).sub
    ((center.sub minus).mul (P.evalJet time (expTime q)))

theorem QuadraticMode.boundaryJet_value (P : QuadraticMode) (η q : ℚ) (h : ℝ) :
    (P.boundaryJet η q).value h=boundaryValue η h (P.value q) := by
  simp only [boundaryJet,RationalJet.sub,RationalJet.mul]
  rw [evalJet_value P mid (expMid q) q h rfl,evalJet_value P time (expTime q) q h rfl,
    evalJet_value P (scale (-1) time) (expTime (-q)) q h (by simp [scale,time,expTime])]
  simp [boundaryValue,mid,chordMid,scale,time,expTime,expMid]

structure BoundaryTest (η : ℚ) where
  source : ℝ → ℝ → ℝ
  jet : RationalJet
  primitive : ∀ h, LinePrimitive (η:ℝ) (source h)
  represents : ∀ h, jet.value h=boundaryValue η h (primitive h).value

namespace BoundaryTest

def mode (η q u v : ℚ) (hη : η≠0) : BoundaryTest η where
  source _ s := ((u:ℝ)+(v:ℝ)*s)*Real.exp ((q:ℝ)*s)
  jet := (QuadraticMode.primitive η q u v).boundaryJet η q
  primitive _ := QuadraticMode.linePrimitive η q u v hη
  represents := (QuadraticMode.primitive η q u v).boundaryJet_value η q

def sub {η : ℚ} (P Q : BoundaryTest η) : BoundaryTest η where
  source h s := P.source h s+(-1)*Q.source h s
  jet := P.jet.sub Q.jet
  primitive h := (P.primitive h).add ((Q.primitive h).scale (-1))
  represents h := by
    change _=boundaryValue _ _ (fun s ↦ _+(-1)*_)
    rw [boundaryValue_add,boundaryValue_scale,← P.represents,← Q.represents]
    change _-_=_
    ring

def factor {η : ℚ} (g : RationalJet) (P : BoundaryTest η) : BoundaryTest η where
  source h s := g.value h*P.source h s
  jet := g.mul P.jet
  primitive h := (P.primitive h).scale (g.value h)
  represents h := by
    change _=boundaryValue _ _ (fun s ↦ g.value h*_)
    rw [boundaryValue_scale,← P.represents]
    rfl

/-- The shifted exponential profile multiplying an exponential velocity. -/
def tilted (η a b : ℚ) (hη : η≠0) :=
  (mode η (a+b) 1 0 hη).sub (factor (coshTime b) (mode η a 1 0 hη))

def linear (η a : ℚ) (hη : η≠0) := mode η a 0 1 hη

theorem tilted_source (η a b : ℚ) (hη : η≠0) (h s : ℝ) :
    (tilted η a b hη).source h s=Real.exp ((a:ℝ)*s)*(Real.exp ((b:ℝ)*s)-Real.cosh ((b:ℝ)*h)) := by
  simp [tilted,mode,sub,factor,coshTime_value,add_mul,Real.exp_add]
  <;> ring

theorem linear_source (η a : ℚ) (hη : η≠0) (h s : ℝ) :
    (linear η a hη).source h s=s*Real.exp ((a:ℝ)*s) := by simp [linear,mode]

theorem detect_pair {η : ℚ} (P Q : BoundaryTest η) (hη : η≠0)
    (hdet : P.jet.coeff 5*Q.jet.coeff 7-P.jet.coeff 7*Q.jet.coeff 5≠0) {a b : ℝ}
    (H : ∀ᶠ h in 𝓝[>] (0:ℝ), VanishingResponse η h (fun s ↦ a*P.source h s+b*Q.source h s)) :
    a=0 ∧ b=0 := by
  apply P.jet.independent Q.jet hdet
  filter_upwards [H,self_mem_nhdsWithin] with h hh hp
  have HB := hh.boundary (by exact_mod_cast hη) hp (((P.primitive h).scale a).add ((Q.primitive h).scale b))
  change boundaryValue _ _ (fun s ↦ a*_+b*_)=0 at HB
  rwa [boundaryValue_add,boundaryValue_scale,boundaryValue_scale,← P.represents,← Q.represents] at HB

theorem detect_single {η : ℚ} (P : BoundaryTest η) (hη : η≠0) (n : ℕ) (hn : P.jet.coeff n≠0) {a : ℝ}
    (H : ∀ᶠ h in 𝓝[>] (0:ℝ), VanishingResponse η h (fun s ↦ a*P.source h s)) : a=0 := by
  have hz : ∀ᶠ h in 𝓝[>] (0:ℝ), a*P.jet.value h+0*P.jet.value h=0 := by
    filter_upwards [H,self_mem_nhdsWithin] with h hh hp
    have HB := hh.boundary (by exact_mod_cast hη) hp ((P.primitive h).scale a)
    change boundaryValue _ _ (fun s ↦ a*_)=0 at HB
    simpa [boundaryValue_scale,← P.represents] using HB
  have hr : (P.jet.coeff n:ℝ)≠0 := by exact_mod_cast hn
  have hd := two_moments P.jet P.jet hz n
  simpa [hr] using hd

end BoundaryTest
end EuclideanMidpointRigidity.Endpoint

