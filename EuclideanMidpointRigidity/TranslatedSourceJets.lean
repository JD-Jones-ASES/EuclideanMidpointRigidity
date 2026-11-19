module

public import EuclideanMidpointRigidity.TranslatedVariations
public import EuclideanMidpointRigidity.FlatForceJets

/-! # Endpoint jets of the force obtained by translating the cubic field -/

public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.SmoothEndpointFamily
variable {d : ℕ} {C : Space d → Cubic d} {σ r : ℝ} {p : Space d} (F : SmoothEndpointFamily C σ p r)
local notation "E" => Space d
local notation "H" => E × E
local notation "P" => PhaseCurve d
local notation "Q" => AccelerationCurve d
set_option backward.isDefEq.respectTransparency false

theorem source_word {Ω : Set E} (hΩ : IsOpen Ω) (hC : ContDiffOn ℝ ∞ C Ω) (b : E)
    {q : H} (hq : q ∈ F.domain) (t : UnitInterval) (hx : (F.phase q t).1 ∈ Ω) (xs : List H)
    (hz : ∀ ys : List H, ys.length<xs.length → directions (phaseCore (directional C b)) ys (F.phase q t)=0) :
    (directions (F.translatedSource b) xs q) t=
      -σ • directions (phaseCore (directional C b)) (xs.map (fun w ↦ (F.variation q w) t)) (F.phase q t) := by
  let D := directional C b
  let M := (ContinuousMap.evalCLM ℝ t : P →L[ℝ] H)
  let N := (ContinuousMap.evalCLM ℝ t : Q →L[ℝ] E)
  let X := M ∘ F.phase
  let V : Set H := Prod.fst ⁻¹' Ω
  let U := F.domain ∩ X ⁻¹' V
  let L := (-σ) • ContinuousLinearMap.id ℝ E
  have hD : ContDiffOn ℝ ∞ D Ω := directions.smooth hΩ hC [b]
  have hV : IsOpen V := hΩ.preimage continuous_fst
  have hG : ContDiffOn ℝ ∞ (phaseCore D) V := PhaseProduct.smooth hΩ hD ⟨[],none,none⟩
  have hX : ContDiffOn ℝ ∞ X F.domain := M.contDiff.comp_contDiffOn F.smooth
  have hU : IsOpen U := hX.continuousOn.isOpen_inter_preimage F.isOpen hV
  have hqU : q ∈ U := ⟨hq,hx⟩
  have hm : MapsTo X U V := fun _ h ↦ h.2
  have hXU := hX.mono (show U ⊆ F.domain from inter_subset_left)
  have dx : fderiv ℝ X q=M.comp (fderiv ℝ F.phase q) :=
    (M.hasFDerivAt.comp q ((F.smooth.contDiffAt (F.isOpen.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt).fderiv
  have hsrc : ContDiffOn ℝ ∞ (F.translatedSource b) F.domain := F.smooth_linearForce.clm_apply contDiffOn_const
  have he : (N ∘ F.translatedSource b) =ᶠ[𝓝 q] (L ∘ (phaseCore D ∘ X)) := by
    filter_upwards [hU.mem_nhds hqU] with y hy
    change fderiv ℝ (F.force : H → E) (F.phase y t) (b,0)= -σ • K (D (F.phase y t).1) (F.phase y t).2 (F.phase y t).2
    have hxy : (F.phase y t).1 ∈ Ω := hy.2
    rw [(F.forceGerm y hy.1 t).fderiv_eq,fderiv_geodesicForce_apply σ (F.phase y t) (b,0) (hC.contDiffAt (hΩ.mem_nhds hxy))]
    simp only [firstForceJet,firstProduct,D,directional,K,Prod.fst,Prod.snd,map_zero,smul_zero,add_zero]
  have hh := (directions.congr_germ he xs).eq_of_nhds
  rw [directions.linear_map F.isOpen hsrc N xs hq,directions.linear_map hU (hG.comp hXU hm) L xs hqU] at hh
  change (directions (F.translatedSource b) xs q) t= -σ • directions (phaseCore D ∘ X) xs q at hh
  rw [directions.leading_comp hU hV hXU hm hqU xs hG hz,dx] at hh
  exact hh

end EuclideanMidpointRigidity.SmoothEndpointFamily

