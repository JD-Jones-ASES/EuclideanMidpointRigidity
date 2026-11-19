module

public import EuclideanMidpointRigidity.CompanionContinuation

/-! # Smooth initial jets for a smooth family of straight lines -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.Endpoint
variable {Y V : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup V] [NormedSpace ℝ V]

def timeJet (F : Y × ℝ → V) : ℕ → Y × ℝ → V
  | 0 => F
  | n+1 => fun z ↦ fderiv ℝ (timeJet F n) z (0,1)

theorem smooth_timeJet {D : Set (Y × ℝ)} {F : Y × ℝ → V} (hD : IsOpen D) (hF : ContDiffOn ℝ ∞ F D) (n : ℕ) :
    ContDiffOn ℝ ∞ (timeJet F n) D := by
  induction n with
  | zero => exact hF
  | succ n ih => exact (ih.fderiv_of_isOpen hD (by simp)).clm_apply contDiffOn_const

theorem timeJet_eq {D : Set (Y × ℝ)} {F : Y × ℝ → V} (hD : IsOpen D) (hF : ContDiffOn ℝ ∞ F D)
    (n : ℕ) {y : Y} {t : ℝ} (hz : (y,t) ∈ D) : timeJet F n (y,t)=iteratedDeriv n (fun s ↦ F (y,s)) t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    have hd : HasDerivAt (fun s : ℝ ↦ (y,s)) (0,1) t := (hasDerivAt_const t y).prodMk (hasDerivAt_id t)
    have dh := (((smooth_timeJet hD hF n).contDiffAt (hD.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hd
    have near : ∀ᶠ s in 𝓝 t, (y,s) ∈ D := (continuous_const.prodMk continuous_id).continuousAt (hD.mem_nhds hz)
    have he : (fun s ↦ timeJet F n (y,s))=ᶠ[𝓝 t] iteratedDeriv n (fun s ↦ F (y,s)) :=
      near.mono fun s hs ↦ ih hs
    exact dh.deriv.symm.trans (he.deriv_eq.trans (by rw [iteratedDeriv_succ]))

theorem smooth_line_initial_jet {Ω : Set Y} {C : Y → V} {u : Y → Y} (hΩ : IsOpen Ω)
    (hC : ContDiffOn ℝ ∞ C Ω) (hu : ContDiffOn ℝ ∞ u Ω) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun y ↦ lineJet (n := n) (fun t ↦ C (y+t • u y)) 0) Ω := by
  let V₀ : Set (Y × ℝ) := Prod.fst ⁻¹' Ω
  let L := fun z : Y × ℝ ↦ z.1+z.2 • u z.1
  let D := V₀ ∩ L ⁻¹' Ω
  let F := C ∘ L
  have hV : IsOpen V₀ := hΩ.preimage continuous_fst
  have hL : ContDiffOn ℝ ∞ L V₀ := contDiffOn_fst.add (contDiffOn_snd.smul (hu.comp contDiffOn_fst (fun _ hx ↦ hx)))
  have hD : IsOpen D := hL.continuousOn.isOpen_inter_preimage hV hΩ
  have hF : ContDiffOn ℝ ∞ F D := hC.comp (hL.mono inter_subset_left) (fun _ hx ↦ hx.2)
  have h0 (y : Y) (hy : y ∈ Ω) : (y,(0:ℝ)) ∈ D := ⟨hy,by simpa [L] using hy⟩
  apply contDiffOn_pi.mpr
  intro i
  apply ((smooth_timeJet hD hF i.val).comp (contDiffOn_id.prodMk contDiffOn_const) h0).congr
  exact fun y hy ↦ (timeJet_eq hD hF i.val (h0 y hy)).symm

end EuclideanMidpointRigidity.Endpoint

