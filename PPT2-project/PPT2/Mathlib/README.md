# PPT2/Mathlib — Formal infrastructure landing zone

Files here are **candidates for upstream Mathlib contribution**. They must be
self-contained: no `import PPT2.*` (except other `PPT2/Mathlib/` files),
no dependency on `Choi.lean` / `Separable.lean` / `EntanglementBreaking.lean`.

## Roadmap (iter-80+)
1. `Quaternions.lean` — SU(2) ≅ unit quaternions (S³)
2. `HaarSU2.lean` — Haar measure on SU(2) via spherical measure
3. `Twirling.lean` — ∫_G U ρ U† dU for compact unitary group
4. `WernerHolevo.lean` — twirling identity = depolarizing channel

Owner: ppt2_main A-line agent, iter-80+.
