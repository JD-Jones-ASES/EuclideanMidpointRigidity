module

public import EuclideanMidpointRigidity.MovingCubic
public import EuclideanMidpointRigidity.CompatibilityRows

/-! # The four weighted cubic derivatives in internal and external coordinates -/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity.Quartic
open LiftedSection
inductive CubicSlot | d1 | m | n | d2

namespace CubicSlot

def shape {d : ℕ} (S : LiftedSection d) : CubicSlot → Space d → ℝ
  | .d1 => S.shape S.x S.x S.x
  | .m => S.shape S.x S.x S.y
  | .n => S.shape S.x S.y S.y
  | .d2 => S.shape S.y S.y S.y

def weight (t : ℝ) : CubicSlot → ℝ
  | .d1 => 1 | .m => t | .n => t^2 | .d2 => t^3

def reconstruction : CubicSlot → Reduction
  | .d1 => .s111 | .m => .s112 | .n => .s122 | .d2 => .s222

def jet (P : CoreEntries) : CubicSlot → ℝ
  | .d1 => P.s111 | .m => P.s112 | .n => P.s122 | .d2 => P.s222

def frame (P : CoreEntries) (i : CubicSlot) : ℝ :=
  let O := (10/7)*(P.z12+(7/26)*P.m)
  match i with
  | .d1 => -3*O*P.m+3*(7/26)/2
  | .m => O*(P.d1-2*P.n)
  | .n => O*(2*P.m-P.d2)-(7/26)/5
  | .d2 => 3*O*P.n

def rotation (t : ℝ) (v : MixedChannel) : CubicSlot → ℝ
  | .d1 => 3*(v.q*v.rot1)
  | .m => 2*((v.l/t)*v.rot1)+v.q*(v.rot2/t)
  | .n => (v.h/t^2)*v.rot1+2*((v.l/t)*(v.rot2/t))
  | .d2 => 3*((v.h/t^2)*(v.rot2/t))

def angular (v : MixedChannel) : CubicSlot → ℝ
  | .d1 => 3*v.q*v.rot1
  | .m => 2*v.l*v.rot1+v.q*v.rot2
  | .n => v.h*v.rot1+2*v.l*v.rot2
  | .d2 => 3*v.h*v.rot2

def framePart (t n : ℝ) (i : CubicSlot) : ℝ :=
  let m := -ResonantPlane.k*t*n
  let O := (10/7)*(-(5/28236)*(5704*m+8385*t*n)+(7/26)*m)
  match i with
  | .d1 => -3*O*m+3*(7/26)/2
  | .m => t*O*((650/153)*ResonantPlane.k*t^2*n-2*n)
  | .n => 2*t^2*O*m+(159/1300)*t*O*n-t^2*(7/26)/5
  | .d2 => 3*t^3*O*n

def internal (i : CubicSlot) (t n : ℝ) := i.reconstruction.internal t n+i.framePart t n

def external (i : CubicSlot) (s : ℝ) (v : MixedChannel) := i.reconstruction.external s v+i.angular v

theorem frame_identity (i : CubicSlot) {P : CoreEntries} (hn : P.Normalized) (ht : P.t≠0) :
    i.weight P.t*i.frame P=i.framePart P.t P.n := by
  have hd : P.d2= -(159/1300)*P.n/P.t := (eq_div_iff ht).mpr (by linear_combination hn.d2)
  cases i <;> dsimp only [weight,frame,framePart] <;> simp only [hn.z12,hn.m,hn.d1,hd] <;> field_simp <;> ring

theorem angular_identity (i : CubicSlot) {t : ℝ} (ht : t≠0) (v : MixedChannel) :
    i.weight t*i.rotation t v=i.angular v := by
  cases i <;> dsimp only [weight,rotation,angular] <;> field_simp <;> ring

theorem differential {d : ℕ} {S : LiftedSection d} {p : Space d} (hm : S.IsMixed p)
    {ι : Type*} [Fintype ι] (B : SpectralFrame S p ι) (i : CubicSlot) :
    let P := S.core p
    S.rate (i.shape S) p=i.jet P+i.frame P+∑ j, i.rotation P.t (S.channel p (B.w j)) := by
  obtain ⟨a,b,c,f⟩ := B.shape_rates hm
  dsimp only at a b c f ⊢
  have ht : (S.core p).t=S.ratio p := rfl
  cases i <;> dsimp only [shape,jet,frame,rotation]
  all_goals simp only [LiftedSection.omega,ht] at a b c f ⊢
  all_goals first | linear_combination a | linear_combination b | linear_combination c | linear_combination f

theorem weighted_identity {d : ℕ} {S : LiftedSection d} {p : Space d} (hm : S.IsMixed p)
    {ι : Type*} [Fintype ι] (B : SpectralFrame S p ι) (i : CubicSlot) :
    let P := S.core p
    i.weight P.t*S.rate (i.shape S) p=i.internal P.t P.n+∑ j, i.external (B.value j) (S.channel p (B.w j)) := by
  let P := S.core p
  let v := fun j ↦ S.channel p (B.w j)
  have ht : P.t≠0 := (div_pos (norm_pos_iff.mpr hm.2.2) (norm_pos_iff.mpr hm.2.1)).ne'
  have hn := S.normalized_entries hm
  have h := i.reconstruction.identity hn ht (geometric_quartic_moments hm B)
  have hjet : i.reconstruction.target P=i.weight P.t*i.jet P := by
    cases i <;> simp only [reconstruction,Reduction.target,weight,jet,one_mul,pow_one]
  change _+_=i.reconstruction.target P at h
  rw [hjet] at h
  change i.reconstruction.internal P.t P.n+(∑ j, i.reconstruction.external (B.value j) (v j))=i.weight P.t*i.jet P at h
  have hf : i.weight P.t*i.frame P=i.framePart P.t P.n := i.frame_identity hn ht
  have hs : i.weight P.t*(∑ j, i.rotation P.t (v j))=∑ j, i.angular (v j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ i.angular_identity ht (v j)
  change i.weight P.t*S.rate (i.shape S) p=i.internal P.t P.n+∑ j, i.external (B.value j) (v j)
  rw [i.differential hm B]
  change i.weight P.t*(i.jet P+i.frame P+∑ j, i.rotation P.t (v j))=_
  rw [mul_add,mul_add,hs,hf,← h]
  simp only [internal,external,Finset.sum_add_distrib]
  ring

end CubicSlot
end EuclideanMidpointRigidity.Quartic

