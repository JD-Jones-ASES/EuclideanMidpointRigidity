module

public import EuclideanMidpointRigidity.PhysicalRow
public import EuclideanMidpointRigidity.SpectralCertificates

/-! # Pulling the interval certificates back to the full spectral channels -/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity.Spectral
open IntervalPolynomial MixedChannel PhysicalRow

namespace MixedCertificate

def physicalTerms (ws : List ℚ) (xs : List PhysicalRow) :=
  (ws.zip xs).map (fun (k,x) ↦ x.scale k)

def testTerms (ts : List NormTest) := ts.map (fun t ↦ (PhysicalRow.test t).scale t.weight)

def lifted (w : MixedCertificate) := PhysicalRow.sum (physicalTerms w.weights physical++testTerms w.tests)

private theorem tables (ws : List ℚ) (xs : List PhysicalRow) :
    (physicalTerms ws xs).map PhysicalRow.table=
    (ws.zip (xs.map PhysicalRow.table)).map (fun (k,x) ↦ x.scale k) := by
  induction ws generalizing xs with
  | nil => simp [physicalTerms]
  | cons k ws ih =>
    cases xs with
    | nil => simp [physicalTerms]
    | cons x xs =>
      change (x.table.scale k)::(physicalTerms ws xs).map PhysicalRow.table=(x.table.scale k)::_
      rw [ih]
      simp only [List.zip]

theorem lifted_table (w : MixedCertificate) : w.lifted.table=w.combined := by
  rw [lifted,sum_table,List.map_append,tables,physical_table]
  simp only [combined,testTerms,List.map_map,Function.comp_def,PhysicalRow.test,PhysicalRow.scale]

private theorem nine {ws : List ℚ} (hn : ws.length=9) :
    ∃ a b c d e f g h i, ws=[a,b,c,d,e,f,g,h,i] := by
  rcases ws with _|⟨a,ws⟩
  · simp at hn
  rcases ws with _|⟨b,ws⟩
  · simp at hn
  rcases ws with _|⟨c,ws⟩
  · simp at hn
  rcases ws with _|⟨d,ws⟩
  · simp at hn
  rcases ws with _|⟨e,ws⟩
  · simp at hn
  rcases ws with _|⟨f,ws⟩
  · simp at hn
  rcases ws with _|⟨g,ws⟩
  · simp at hn
  rcases ws with _|⟨h,ws⟩
  · simp at hn
  rcases ws with _|⟨i,ws⟩
  · simp at hn
  cases ws with
  | nil => exact ⟨a,b,c,d,e,f,g,h,i,rfl⟩
  | cons j js => simp at hn

private theorem test_coefficients (ts : List NormTest) : ((testTerms ts).map PhysicalRow.coefficient).sum=0 := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    change t.weight*0+_=0
    rw [mul_zero,zero_add]
    exact ih

theorem lifted_coefficient (w : MixedCertificate) (hn : w.weights.length=9) :
    w.lifted.coefficient=w.weights.getLastD 0 := by
  rw [lifted,sum_coefficient,List.map_append,List.sum_append,test_coefficients,add_zero]
  obtain ⟨a,b,c,d,e,f,g,h,i,hs⟩ := nine hn
  rw [hs]
  simp [physicalTerms,physical,List.zip,PhysicalRow.quartic,PhysicalRow.differentiated,PhysicalRow.force,
    PhysicalRow.scale,ForceAxis.pick,List.getLastD]

theorem geometric_weights {w : MixedCertificate} (hw : w.verify=true) :
    (w.weights.length=9 ∧ w.weights.getLastD 0≤0) ∧
    ∀ t ∈ w.tests, 0<t.weight ∧ 0<t.x^2+t.z^2 := by
  simp only [verify,Bool.and_eq_true] at hw
  simpa only [validWeights,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] using hw.1.1.1.1

theorem lifted_residual {ι : Type*} [Fintype ι] {w : MixedCertificate} (hw : w.verify=true) (d : ChannelData ι)
    (hphys : ∀ r ∈ physical, r.residual d=0)
    (htests : ∀ t : NormTest, 0<t.x^2+t.z^2 → (PhysicalRow.test t).residual d≤0) : w.lifted.residual d≤0 := by
  apply sum_residual_nonpos
  intro a ha
  rcases List.mem_append.mp ha with h|h
  · obtain ⟨⟨k,r⟩,hr,rfl⟩ := List.mem_map.mp h
    rw [residual_scale,hphys r (List.of_mem_zip hr).2,mul_zero]
  · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp h
    obtain ⟨hp,hn⟩ := (geometric_weights hw).2 t ht
    rw [residual_scale]
    exact mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast hp.le) (htests t hn)

theorem channel_nonnegative {w : MixedCertificate} (hw : w.verify=true) {v : MixedChannel} {s : ℝ}
    (hl : -1≤s) (hr : s≤1/2) (hv : v.Equations s) (hn : s=1/2 → v=MixedChannel.zero) :
    0≤w.lifted.raw s v := by
  simp only [verify,Bool.and_eq_true] at hw
  obtain ⟨⟨⟨⟨_,_⟩,ha⟩,hc⟩,hd⟩ := hw
  have regular {t : ℝ} (hlo : -1≤t) (hhi : t≤1/2) (ht : regularDenominator t≠0)
      (u : MixedChannel) (hu : u.Equations t) : 0≤w.lifted.raw t u := by
    rw [w.lifted.compatible hu ht,w.lifted_table]
    exact Row.channel_nonnegative ha hc hd hlo hhi _ _
  by_cases hi : s=1/2
  · rw [hn hi,w.lifted.regularity.null]
  by_cases lo : s= -1
  · subst s
    apply regular hl hr _ v hv
    norm_num [regularDenominator]
  apply nonnegative_on_channels (lt_of_le_of_ne hl (Ne.symm lo)) (lt_of_le_of_ne hr hi) hv
  · intro o p hD
    exact w.lifted.regularity.strict (angular_continuous hD o p) (lt_of_le_of_ne hr hi)
  · intro t h₁ h₂ hD u hu
    exact regular h₁.le h₂.le hD u hu

end MixedCertificate
end EuclideanMidpointRigidity.Spectral

