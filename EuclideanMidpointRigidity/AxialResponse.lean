module

public import EuclideanMidpointRigidity.ChordTime
public import EuclideanMidpointRigidity.EndpointCoefficients

/-! # The scalar Dirichlet response in the axial line coordinate -/

@[expose] public section
noncomputable section
open Set
namespace EuclideanMidpointRigidity.Endpoint

structure ScalarDirichlet (η h : ℝ) (f x v : ℝ → ℝ) : Prop where
  position : ∀ s ∈ Icc (-h) h, HasDerivAt x (v s) s
  velocity : ∀ s ∈ Icc (-h) h, HasDerivAt v (η*v s+f s) s
  left : x (-h)=0
  right : x h=0

theorem ScalarDirichlet.add {η h : ℝ} {f g x y v w : ℝ → ℝ}
    (H : ScalarDirichlet η h f x v) (J : ScalarDirichlet η h g y w) :
    ScalarDirichlet η h (fun s ↦ f s+g s) (fun s ↦ x s+y s) (fun s ↦ v s+w s) where
  position s hs := (H.position s hs).fun_add (J.position s hs)
  velocity s hs := by convert (H.velocity s hs).fun_add (J.velocity s hs) using 1; ring
  left := by simp [H.left,J.left]
  right := by simp [H.right,J.right]

/-- A response whose midpoint value vanishes at this chord length. -/
def VanishingResponse (η h : ℝ) (f : ℝ → ℝ) : Prop := ∃ x v, ScalarDirichlet η h f x v ∧ x (Real.log (Real.cosh h))=0

theorem scalar_response_in_line_coordinate {h b : ℝ} (hh : 0<h) {f x v : ℝ → ℝ}
    (dx : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt x (v t) t)
    (dv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt v
      ((chordSpeed h t)^2*f (chordParameter h t)-2*b*chordSpeed h t*v t) t)
    (h₀ : x 0=0) (h₁ : x 1=0) :
    ∃ X V, ScalarDirichlet (1-2*b) h f X V ∧ X (Real.log (Real.cosh h))=x (1/2) := by
  let X := x ∘ chordTime h
  let V := fun s ↦ chordTimeSpeed h s*v (chordTime h s)
  refine ⟨X,V,⟨?_,?_,?_,?_⟩,?_⟩
  · intro s hs
    simpa only [X,V,mul_comm] using (dx _ (chordTime_mem hh hs)).comp s (hasDerivAt_chordTime h s)
  · intro s hs
    let c := chordSpeed h (chordTime h s)
    let d := chordTimeSpeed h s
    let g := v (chordTime h s)
    have hcd : c*d=1 := chordSpeed_timeSpeed hh s
    have h := (hasDerivAt_chordTimeSpeed h s).fun_mul ((dv _ (chordTime_mem hh hs)).comp s (hasDerivAt_chordTime h s))
    rw [chordParameter_at_time hh] at h
    change HasDerivAt V (d*g+d*((c^2*f s-2*b*c*g)*d)) s at h
    have he : d*g+d*((c^2*f s-2*b*c*g)*d)=(1-2*b)*V s+f s := by
      change _=(1-2*b)*(d*g)+f s
      calc
        _ = (1-2*b*(c*d))*(d*g)+(c*d)^2*f s := by ring
        _ = _ := by rw [hcd]; ring
    rwa [he] at h
  · simpa only [X,Function.comp_apply,chordTime_left] using h₀
  · simpa only [X,Function.comp_apply,chordTime_right hh] using h₁
  · exact congrArg x (chordTime_midpoint hh)

end EuclideanMidpointRigidity.Endpoint

