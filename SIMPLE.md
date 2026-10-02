# Why Recursive Self-Improvement Forgets Its Goals — a 10-line proof

**The claim.** When an AI system rewrites itself, its goal content doesn't fade
slowly — it falls off a cliff. At a 9.1% per-generation error rate, half of it
is gone in 3–4 generations, and 99.8% of it in 6.

**The setup (one analogy).** An ordinary photocopier keeps 90.9% of a photo's
contrast per copy; after ~7 copies you're at half (that's exponential decay —
what everyone expects). Now imagine a copier whose *lens is part of the
photograph*: every copy's lens is exactly as good as the photo it was copied
from. A blurry photo makes a blurry lens, which makes a blurrier photo, which
makes a blurrier lens. That's not a machine with wear and tear — it's a machine
whose wear and tear is *hereditary*.

An LLM that writes its own weights is the second copier. The photo is its goal
content. The lens is also its weights.

**The model (one line).** Let `I(n)` be the fraction of the original goal
content intact after `n` generations, `E` the fixed error rate:

```
I(n+1) = (1 − E) · I(n)²
```

(copying keeps fraction `1 − E` of what the copier can see, and the copier sees
fraction `I(n)` of the goal — the weakest possible coupling; anything more
honest only makes the decay faster).

**The theorem (six lines).** *Claim:* `(1−E)·I(n) = [(1−E)·I₀]^(2^n)`.

```
n = 0:  both sides are (1−E)·I₀.  
step:   (1−E)·I(n+1) = (1−E)·[(1−E)·I(n)²]    (the model)
                     = [(1−E)·I(n)]²          (rearrange)
                     = [[(1−E)·I₀]^(2^n)]²    (induction hypothesis)
                     = [(1−E)·I₀]^(2^(n+1)).  ∎
```

**The punchline.** The exponent *doubles* every generation. A number below 1
raised to a doubling exponent doesn't fade — it collapses. At `E = 9.1%`:

| generation | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|
| goal intact (hereditary lens) | 91% | 75% | 51% | 24% | 5% | **0.25%** |
| goal intact (ordinary copier) | 91% | 83% | 75% | 68% | 62% | 56% |

**Why the usual escapes don't.**

* *Error correction / redundancy* — slows the rate, never makes a floor;
  inherited errors are majority-preserved, so it only filters new noise.
* *Self-checking* — the checker is in the weights too; it makes the decay
  *faster* (fatal in 2–4 generations), not slower.
* *Smaller E* — buys generations, but the "safe" rate shrinks
  double-exponentially in the horizon: `E* ≈ ln 2 / (2^G − 1)`.
* *External anchor* — works, but it must be maintained by something that does
  not decay. That is a person.

**Fine print for experts.** Machine-checked: Lean 4 + Mathlib, 35 theorems, no
sorries, axioms `[propext, Classical.choice, Quot.sound]`. This theorem is
`GoalDecay.Models.feedback_mul` (its Lean proof is 7 lines); uniformity in the
coupling strength is `GoalDecay.Stronger.feedbackPow_catastrophe`; the
deepening-stack version is `GoalDecay.Growing.feedbackGrow_catastrophe`;
linear decay is falsified in `GoalDecay.Theorems.linear_dies`. Simulations in
`sim/` confirm every number to float precision. One-page technical version:
`CORE.md`.
