module

public import EuclideanMidpointRigidity.AxialCurvature
public import EuclideanMidpointRigidity.ReducedTilts
public import EuclideanMidpointRigidity.CubicPolynomial

/-! # A reflected third-variation law at each center of the maximizing ruling -/

@[expose] public section
noncomputable section
open Set Filter Metric
open scoped ContDiff InnerProductSpace Topology
namespace EuclideanMidpointRigidity.HorizontalPatch
open Endpoint
variable {d : ℕ} {S : LiftedSection d} (H : HorizontalPatch S)
local notation "E" => Space d
set_option backward.isDefEq.respectTransparency false

include H in
theorem curvature_chords {p : E} (hp : p ∈ S.domain) (a y z w : E) {b : ℝ}
    (hy : S.axisSlice p y=b • y) (hz : S.axisSlice p z=(2*b) • z) (hw : S.axisSlice p w=b • w) :
    let u := S.idempotent p
    let D := directional S.field (fderiv ℝ S.axis p a)
    let A := fun t : ℝ ↦ TiltData.atPoint D (p+t • u) u y y z w
    ∃ W : Set ℝ, IsOpen W ∧ 0 ∈ W ∧
      ThirdTiltLaws W (1-2*b) (1-2*(2*b)) A ∧
      (∀ xs : List E, ∀ v l : E, ContDiffOn ℝ ∞ (fun t : ℝ ↦ ⟪w,K (directions D xs (p+t • u)) v l⟫_ℝ) W) ∧
      (∀ x ∈ W, ∀ l : E, directions D [l] (p+x • u)=directions D [l] p) := by
  let u := S.idempotent p
  let v₀ := fderiv ℝ S.axis p a
  let D := directional S.field v₀
  let line := fun t : ℝ ↦ p+t • u
  obtain ⟨U,r,hpU,R⟩ := H.first_jet_strip hp
  let f := fun t : ℝ ↦ t*(S.a p)⁻¹
  let W := f ⁻¹' ball 0 r
  have pos (t : ℝ) : line t=position S (f t) p := by simp only [line,u,LiftedSection.idempotent,smul_smul,f,position]
  have hW : IsOpen W := isOpen_ball.preimage (continuous_id.mul continuous_const)
  have h₀ : 0 ∈ W := by simpa [W,f] using R.positive
  have maps (x : ℝ) (hx : x ∈ W) : line x ∈ S.domain := pos x ▸ R.maps p hpU _ hx
  have idemp (x : ℝ) (hx : x ∈ W) : S.idempotent (line x)=u := by
    rw [pos,LiftedSection.idempotent,R.axis _ hpU _ hx,R.amplitude _ hpU _ hx]; rfl
  have hline : ContDiff ℝ ∞ line := by dsimp [line]; fun_prop
  have hs (x s : ℝ) : line x+s • u=line (x+s) := by dsimp only [line]; rw [add_smul,add_assoc]
  refine ⟨W,hW,h₀,?_,?_,?_⟩
  · intro x hx
    obtain ⟨C⟩ := H.charts _ (maps x hx)
    have hc := S.eventually_realized_chords (maps x hx) H.maximizes C
    change ∀ᶠ h in 𝓝[>] (0:ℝ), chordEnds (line x) (S.idempotent (line x)) h ∈ C.domain ∧ _ at hc
    have he := idemp x hx
    have hB : S.axisSlice (line x)=S.axisSlice p := pos x ▸ R.slice p hpU _ hx
    change ∀ᶠ h in 𝓝[>] (0:ℝ), chordEnds (line x) (S.idempotent (line x)) h ∈ C.domain ∧
      RealizedChord S.domain S.field 1 (line x) (S.idempotent (line x)) h (S.axisSlice (line x)) C.plus ∧
      RealizedChord S.domain S.field (-1) (line x) (-(S.idempotent (line x))) h (S.axisSlice (line x)) C.minus at hc
    rw [he,hB] at hc
    filter_upwards [hc,ThirdTiltLaws.small_segments hW hx] with h ⟨hd,J,N⟩ ht
    have flat (s : ℝ) (hs' : s ∈ Icc (-h) h) : FlatAxialForce D (line x+s • u) u := by
      have hm := (ht s hs').2
      have hA : fderiv ℝ S.axis (line (x+s))=fderiv ℝ S.axis p := pos _ ▸ R.axisJet p hpU _ hm
      have h := H.flat_at_slope (maps _ hm) a
      rw [idemp _ hm,hA] at h
      rwa [hs]
    intro i j l
    have hR := C.reflected_third S.isOpen S.smooth hd J N v₀ flat hy hy hz hw
      (signedProfile _ h i false) (signedProfile _ h i true) (signedProfile _ h j false) (signedProfile _ h j true)
      (signedProfile _ h l false) (signedProfile _ h l true) (signedProfile_swap _ h i y) (signedProfile_swap _ h j y) (signedProfile_swap _ h l z)
    exact hR.congr fun s _ ↦ by dsimp only [TiltData.test]; rw [hs,hs]; rfl
  · intro xs v l
    have hD : ContDiffOn ℝ ∞ D S.domain := directions.smooth S.isOpen S.smooth [v₀]
    have h := contDiffOn_cubic_entry (directions.smooth S.isOpen hD xs) v l w
    simpa only [Function.comp_def,real_inner_comm w] using h.comp hline.contDiffOn maps
  · intro x hx l
    change directional D l (line x)=directional D l p
    rw [pos]
    exact H.constant_translated_jet R hpU hx a l

end EuclideanMidpointRigidity.HorizontalPatch

