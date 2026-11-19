module

public import EuclideanMidpointRigidity.AxialResponse

/-! # Linearity and locality of the scalar Dirichlet midpoint law -/

public section
noncomputable section
open Set
namespace EuclideanMidpointRigidity.Endpoint

theorem VanishingResponse.congr {η h : ℝ} {f g : ℝ → ℝ}
    (hf : VanishingResponse η h f) (he : EqOn f g (Icc (-h) h)) : VanishingResponse η h g := by
  obtain ⟨x,v,H,hm⟩ := hf
  exact ⟨x,v,⟨H.position,fun s hs ↦ he hs ▸ H.velocity s hs,H.left,H.right⟩,hm⟩

theorem VanishingResponse.add {η h : ℝ} {f g : ℝ → ℝ}
    (hf : VanishingResponse η h f) (hg : VanishingResponse η h g) : VanishingResponse η h (fun s ↦ f s+g s) := by
  obtain ⟨x,v,H,hm⟩ := hf
  obtain ⟨y,w,J,hn⟩ := hg
  exact ⟨_,_,H.add J,by simp only [hm,hn,add_zero]⟩

theorem VanishingResponse.smul {η h : ℝ} {f : ℝ → ℝ} (hf : VanishingResponse η h f) (r : ℝ) :
    VanishingResponse η h (fun s ↦ r*f s) := by
  obtain ⟨x,v,H,hm⟩ := hf
  refine ⟨fun s ↦ r*x s,fun s ↦ r*v s,⟨?_,?_,?_,?_⟩,?_⟩
  · exact fun s hs ↦ (H.position s hs).const_mul r
  · intro s hs
    convert (H.velocity s hs).const_mul r using 1
    ring
  · simp only [H.left,mul_zero]
  · simp only [H.right,mul_zero]
  · simp only [hm,mul_zero]

end EuclideanMidpointRigidity.Endpoint

