module

public import EuclideanMidpointRigidity.FirstTiltCoefficients

/-! # A first endpoint tilt detects every pair of real Jacobi rates -/

public section
noncomputable section
open Filter
open scoped Topology
namespace EuclideanMidpointRigidity.Endpoint
open RealJet

set_option maxRecDepth 12000
set_option maxHeartbeats 3000000

private def cubicTest (k : ℝ) := 54*k^3-149*k^2+72*k-1
private def fifthTest (k : ℝ) := -11682*k^5+42793*k^4-42424*k^3+19738*k^2-4470*k+69

local macro "compute_tilt_jet" : tactic => `(tactic|
  (norm_num [firstTiltJet,boundary,sub,atMinus,atMid,mul,halfSum,coord,forced,one,
    productCoeff,Finset.sum_range_succ,Nat.choose,coordinateCoeff,solutionCoeff,oneCoeff,atMidCoeff,cubicTest,fifthTest]
   <;> ring))

private theorem jet_five (η k : ℝ) : (firstTiltJet η k).coeff 5=10*(η+5*k-2) := by compute_tilt_jet

private theorem jet_seven (k : ℝ) : (firstTiltJet (2-5*k) k).coeff 7=14*cubicTest k := by compute_tilt_jet

private theorem jet_nine (k : ℝ) : (firstTiltJet (2-5*k) k).coeff 9=12*fifthTest k+168*(2-5*k)^2*cubicTest k := by compute_tilt_jet

theorem firstTilt_detects (η k : ℝ) :
    ¬∀ᶠ h in 𝓝[>] (0:ℝ), VanishingResponse η h (centeredCoordinate k h) := by
  intro H
  have h₅ := firstTiltJet_law η k H 5
  rw [jet_five] at h₅
  have hη : η=2-5*k := by linarith
  subst η
  have h₇ := firstTiltJet_law _ k H 7
  have h₉ := firstTiltJet_law _ k H 9
  rw [jet_seven] at h₇
  have hc : cubicTest k=0 := by linarith only [h₇]
  rw [jet_nine,hc] at h₉
  have hf : fifthTest k=0 := by linarith only [h₉]
  have h : (-(11048535463032:ℝ))=0 := by
    dsimp [cubicTest,fifthTest] at hc hf
    linear_combination (-78039597271191+428399659781328*k-993961922402791*k^2+1175180510583650*k^3-343175023259640*k^4)*hc+
      (-1291132358467+3998391608110*k-1586325223080*k^2)*hf
  norm_num at h

end EuclideanMidpointRigidity.Endpoint

