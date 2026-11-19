# Euclidean midpoint rigidity

This repository proves Nielsen–Okamura Conjecture 9.1 in Lean. Let $C$ be a smooth symmetric cubic tensor on a connected open subset of $\mathbb R^d$. Raise its last index to obtain $K$, and let $M_+$ and $M_-$ be the time-$1/2$ geodesic midpoints of the connections $D+K$ and $D-K$. If

$$M_+(P,Q)+M_-(P,Q)=P+Q$$

for every sufficiently close pair of endpoints near each point of the domain, then $C$ is constant. The theorem holds for every finite $d$. [Original conjecture, §9](https://arxiv.org/html/2609.07551v2#S9)

## Read the proof

- [Challenge](Challenge.lean) gives the independent statement and defines the unique short geodesics used in the hypothesis.
- [Proof guide](Proof.md) describes the argument. [Rigidity.lean](EuclideanMidpointRigidity/Rigidity.lean) proves `EuclideanMidpointRigidity.euclidean_midpoint_rigidity`.
- [Solution](Solution.lean) exports the theorem for [Comparator](comparator.json).

## Build and check

From the repository root with Elan installed, run

```sh
lake exe cache get
lake build
```

Lean and Mathlib are pinned to v4.36.0. On Linux with Bubblewrap available, run `lake comparator` to compare the Challenge and Solution and replay the proof.
