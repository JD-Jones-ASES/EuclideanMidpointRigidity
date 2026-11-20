# Euclidean midpoint rigidity

This Lean 4 development proves Nielsen–Okamura Conjecture 9.1 in every finite
dimension. Let C be a smooth symmetric cubic tensor on a connected open set
Ω in ℝᵈ. Raising its last index with the Euclidean metric gives a bilinear
product K. Write M₊ and M₋ for the time-½ midpoints of the unique short
geodesics of the two connections D + K and D − K, where D is the ordinary
Euclidean connection. Suppose that near each point of Ω the midpoints satisfy

> M₊(P, Q) + M₋(P, Q) = P + Q

for every nearby pair of endpoints P, Q. Then C is constant throughout Ω.
Conversely, for a constant tensor, reflection about the ordinary midpoint
exchanges the two geodesics after time reversal. Thus for a torsion-free
Euclidean dual pair, its two geodesic midpoints have the same arithmetic mean
as the endpoints exactly when the cubic is constant.
[Conjecture 9.1](https://arxiv.org/html/2609.07551v2#S9) · [Reflection proof](EuclideanMidpointRigidity/Reflection.lean)

## What the Lean statement says

The single theorem selected by Comparator is
`EuclideanMidpointRigidity.euclidean_midpoint_rigidity`, the implication from
midpoint invariance to constancy. The Lean field has an ambient value at
every point of ℝᵈ. Its smoothness hypothesis and its constancy conclusion
apply on Ω. Lean's `IsPreconnected Ω` includes the empty domain, where the
conclusion is vacuous. [Challenge](Challenge.lean) · [Comparator configuration](comparator.json)

For each p in Ω, the two signs share an open neighborhood of (p, p) in
endpoint-pair space. Each sign has its own radius. The geodesic must stay
inside that ball about p and its speed must stay below the same radius for
the whole time interval [0, 1]. Uniqueness among these short geodesics fixes
the two midpoints. The library constructs the local branches and proves that
different choices agree after shrinking the neighborhood. [Canonical midpoints](EuclideanMidpointRigidity/CanonicalMidpoints.lean)

## Relation to earlier work

Nielsen and Okamura derived a fourth-order obstruction and proved the conjecture
for scalar multiples of a fixed cubic, including dimension one. The earlier
PlanarMidpoint formalization established dimension two. This proof adapts its
short-geodesic construction and fourth-order expansion, then uses a sixth-order
identity and variations of actual geodesics to find a fixed subspace. Projecting
away that subspace preserves the midpoint identity, so induction applies in a
smaller dimension. Whether the fourth-order obstruction alone suffices in every
dimension is a separate question. [Paper, §9](https://arxiv.org/html/2609.07551v2#S9) · [PlanarMidpoint](https://github.com/JD-Jones-ASES/PlanarMidpoint/tree/f277b89a3b0db20872101fd61580ecced748e7c1) · [Proof guide](Proof.md)

## Build and verify

From the repository root with Elan installed, run

```sh
lake exe cache get
lake build
```

Lean and Mathlib are pinned to v4.36.0. On Linux with Bubblewrap available,
run `lake comparator`. The `sorry` in the independent Challenge marks the
statement to be compared. The Solution imports the proof in Rigidity.lean.
The configuration permits `propext`, `Classical.choice`, and `Quot.sound`.
[Solution](Solution.lean) · [Theorem proof](EuclideanMidpointRigidity/Rigidity.lean) · [GitHub preflight workflow](https://github.com/JD-Jones-ASES/EuclideanMidpointRigidity/actions/workflows/palomar-preflight.yml)

JD Jones developed this proof with GPT-6.2 Astra in OpenAI Codex, first using
mathematical prose and Python, then Lean. The project records a self-assessment
of statement fidelity and is distributed under the MIT license.
[Formalization metadata](formalization.yaml) · [License](LICENSE)
