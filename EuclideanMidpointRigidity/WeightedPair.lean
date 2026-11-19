module

public import Mathlib.Tactic

/-! # Positivity of the weighted trace on each strict eigenvalue pair -/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity

def traceWeight (b : ℝ) := b*(1/2-b)

structure LowPair (b c x y z : ℝ) : Prop where
  normal : (20*c-6*b)*x+(20*b-6*c)*y+(14-4*b-4*c)*z=0
  first : (b+5*c-2)*x+(2*b-4*c+3)*z=0
  second : (5*b+c-2)*y+(-4*b+2*c+3)*z=0

/-- The pair contribution multiplied by the two positive strict gaps. -/
def weightedPairNumerator (b c x y z : ℝ) :=
  (1/2-b-c)*z*((1-2*c)*x+(1-2*b)*y)-(traceWeight b+traceWeight c)*x*y

private theorem weighted_ratio (u v s t z : ℝ) (hD : 50-18*u≠0) (hH : 14-4*u-u^2≠0)
    (hM : 57*u-28≠0) (hZ : (50-18*u)*z=(26-25*u)*s)
    (hS : (50-18*u)*v*t=2*(14-4*u-u^2)*s) (hV : (57*u-28)*v^2=(14-4*u-u^2)*(3*u-2)) :
    (1/2-u)*z*((1-u)*s+v*t)-(u-u^2-v^2)/8*(s^2-t^2) =
      t^2*(3*(3-2*u)*(7-10*u)*(26-25*u)*(84-334*u+415*u^2-102*u^3)/
        (8*(57*u-28)^2*(14-4*u-u^2))) := by
  let D := 50-18*u
  let H := 14-4*u-u^2
  let M := 57*u-28
  let K := 26-25*u
  let Q := fun w : ℝ ↦ w*(1/2-u)*K/(2*H)*((1-u)*D/(2*H)+1) -
    (u-u^2-w)/8*(D^2*w/(4*H^2)-1)
  change D≠0 at hD
  change H≠0 at hH
  change M≠0 at hM
  have hz : z=K*s/D := (eq_div_iff hD).mpr (by simpa [D,K,mul_comm z] using hZ)
  have hs : s=D*v*t/(2*H) := (eq_div_iff (mul_ne_zero (by norm_num) hH)).mpr
    (by simpa only [H,D,mul_comm s] using hS.symm)
  have hv : v^2=H*(3*u-2)/M := (eq_div_iff hM).mpr (by simpa only [M,H,mul_comm (v^2)] using hV)
  calc
    _ = t^2*Q (v^2) := by rw [hz,hs]; dsimp only [Q]; field_simp; ring
    _ = _ := by
      rw [hv]
      change t^2*Q (H*(3*u-2)/M)=t^2*(3*(3-2*u)*(7-10*u)*K*
        (84-334*u+415*u^2-102*u^3)/(8*M^2*H))
      dsimp only [Q]
      field_simp [hH,hM]
      dsimp only [K,D,H,M]
      ring

theorem LowPair.weighted_pos {b c x y z : ℝ} (L : LowPair b c x y z)
    (hb : -1≤b) (hc : -1≤c) (hb' : b<1/2) (hc' : c<1/2) (hne : ¬(x=0 ∧ y=0 ∧ z=0)) :
    0<weightedPairNumerator b c x y z := by
  let u := b+c
  let v := b-c
  let s := x+y
  let t := x-y
  have hu₀ : -2≤u := by dsimp [u]; linarith
  have hu₁ : u<1 := by dsimp [u]; linarith
  have hD : 0<50-18*u := by linarith
  have hH : 0<14-4*u-u^2 := by nlinarith only [mul_nonneg (by linarith : 0≤u+5) (by linarith : 0≤1-u)]
  have r₁ : 7*u*s-13*v*t+(14-4*u)*z=0 := by dsimp [u,v,s,t]; linear_combination L.normal
  have r₂ : (3*u-2)*s-2*v*t+(6-2*u)*z=0 := by dsimp [u,v,s,t]; linear_combination L.first+L.second
  have r₃ : (3*u-2)*t-2*v*s+6*v*z=0 := by dsimp [u,v,s,t]; linear_combination L.first-L.second
  let D := 50-18*u
  let H := 14-4*u-u^2
  let M := 57*u-28
  let K := 26-25*u
  have hZ : D*z=K*s := by dsimp only [D,K]; linear_combination 13*r₂-2*r₁
  have hS : D*v*t=2*H*s := by
    dsimp only [D,H,K] at *
    linear_combination -(50-18*u)/2*r₂+(3-u)*hZ
  have hT : D*(3*u-2)*t=2*v*M*s := by
    dsimp only [D,M,K] at *
    linear_combination (50-18*u)*r₃-6*v*hZ
  have ht : t≠0 := by
    intro ht
    have hs : s=0 := (mul_eq_zero.mp (show (2*H)*s=0 by rw [← hS,ht,mul_zero])).resolve_left (by positivity)
    have hz : z=0 := (mul_eq_zero.mp (show D*z=0 by rw [hZ,hs,mul_zero])).resolve_left hD.ne'
    apply hne
    dsimp only [s,t] at hs ht
    exact ⟨by linarith,by linarith,hz⟩
  have hV : M*v^2=H*(3*u-2) := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show (D*t)*(M*v^2-H*(3*u-2))=0 by linear_combination M*v*hS-H*hT)).resolve_left
    exact mul_ne_zero hD.ne' ht
  have hM : M≠0 := by
    intro h₀
    have hz := (mul_eq_zero.mp (show H*(3*u-2)=0 by rw [← hV,h₀,zero_mul])).resolve_left hH.ne'
    dsimp only [M] at h₀
    linarith
  have hstrict : v^2<(1-u)^2 := by
    dsimp only [v,u]
    nlinarith only [mul_pos (by linarith : 0<1-2*b) (by linarith : 0<1-2*c)]
  have hu : u<7/10 := by
    by_contra! hn
    have hgap : M*(v^2-(1-u)^2)=3*u*(3-2*u)*(10*u-7) := by
      dsimp only [M,H] at hV ⊢
      linear_combination hV
    have hn₁ : M*(v^2-(1-u)^2)<0 := mul_neg_of_pos_of_neg (by dsimp [M]; linarith) (sub_neg.mpr hstrict)
    have hn₂ : 0≤3*u*(3-2*u)*(10*u-7) := mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    linarith only [hgap,hn₁,hn₂]
  have hpoly : 0<84-334*u+415*u^2-102*u^3 := by
    nlinarith only [mul_nonneg (by linarith : 0≤72-102*u) (sq_nonneg u),sq_nonneg (343*u-167)]
  have he : weightedPairNumerator b c x y z =
      (1/2-u)*z*((1-u)*s+v*t)-(u-u^2-v^2)/8*(s^2-t^2) := by
    dsimp [weightedPairNumerator,traceWeight,u,v,s,t]
    ring
  rw [he,weighted_ratio u v s t z hD.ne' hH.ne' hM hZ hS hV]
  have h₁ : 0<3-2*u := by linarith
  have h₂ : 0<7-10*u := by linarith
  have h₃ : 0<26-25*u := by linarith
  have h₄ : 0<(57*u-28)^2 := sq_pos_of_ne_zero hM
  positivity

theorem LowPair.diagonal {b x z : ℝ} (L : LowPair b b x x z) (hb : -1≤b) (hb' : b≤1/2) :
    x=0 ∧ z=0 := by
  have h : (2*b^2+4*b-7)*x=0 := by
    linear_combination (14-8*b)/4*L.first-(3-2*b)/4*L.normal
  have hn : 2*b^2+4*b-7<0 := by
    nlinarith only [mul_nonneg (by linarith : 0≤b+1) (by linarith : 0≤1/2-b),hb']
  have hx := (mul_eq_zero.mp h).resolve_left hn.ne
  have hz := L.first
  rw [hx,mul_zero,zero_add] at hz
  exact ⟨hx,(mul_eq_zero.mp hz).resolve_left (by linarith)⟩

theorem LowPair.upper {b x z : ℝ} (L : LowPair b (1/2) x 0 z) (hb : b≤1/2) :
    x=0 ∧ z=0 := by
  have h := L.second
  rw [mul_zero,zero_add] at h
  have hz := (mul_eq_zero.mp h).resolve_left (by linarith)
  have hn := L.normal
  rw [hz,mul_zero,mul_zero,add_zero,add_zero] at hn
  exact ⟨(mul_eq_zero.mp hn).resolve_left (by linarith),hz⟩

theorem LowPair.swap {b c x y z : ℝ} (L : LowPair b c x y z) : LowPair c b y x z where
  normal := by linear_combination L.normal
  first := by linear_combination L.second
  second := by linear_combination L.first

end EuclideanMidpointRigidity

