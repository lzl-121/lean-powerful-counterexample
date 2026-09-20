# Lean formalization: consecutive powerful-number counterexample

This repository formalizes the classical counterexample to the statement:

> If two consecutive positive integers are powerful, must at least one be a perfect square?

The witnesses are:

- `12167 = 23^3`
- `12168 = 2^3 * 3^2 * 13^2`
- `12168 = 12167 + 1`
- both numbers lie strictly between `110^2 = 12100` and `111^2 = 12321`

Therefore, the two consecutive integers are powerful and neither is a perfect square.

## Attribution

The mathematical counterexample is classical and is credited to **Solomon W. Golomb**, not claimed as a new mathematical discovery here. This repository contributes a Lean 4 formalization of that result.

Problem-bank entry: [JSP-000301](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000301)

## Verification

The proof was checked in the **Stable Release (Lean v4.34.0 with Mathlib)** environment at [Lean Web](https://live.lean-lang.org/) with `All Messages (0)`.

To reproduce it, select **Stable Release (v4.34.0 with mathlib, cslib)** in Lean Web and paste the contents of `PowerfulCounterexample.lean` into the editor.
