# gaia-physics-lean

Lean 4 formalizations of theorems from **physics and quantum information**, autonomously
discovered and proved by the [`gaia-discovery`](https://github.com/SiliconEinstein/gaia-discovery)
agentic-loop system on top of [Mathlib4](https://leanprover-community.github.io/mathlib4_docs/).

Each problem in this repo satisfies all three strict criteria:

1. **`lake build` returns `rc=0`** — the Lean kernel type-checks the entire dependency tree.
2. **`#print axioms` lists only the standard three**: `propext`, `Classical.choice`, `Quot.sound`.
3. **Zero `sorry` placeholders** in the main proof tree.

Anything below that bar (partial proofs with `sorry`, axiom-padded proofs, build failures) is
**not** in this repository — those live in the `gaia-discovery` working tree as `TERMINAL.stuck`
or `TERMINAL.partial` markers awaiting a future iteration.

## Index

| Theorem | LOC | Tier | LKM claim |
|---|---|---|---|
| [A3 — Stinespring dilation](GaiaPhysicsLean/A3Stinespring/) | 900 | A | `gcn_85c00af123214e3e` |
| [A5 — No-cloning](GaiaPhysicsLean/A5Nocloning/) | 89 | A | `gcn_054b79cf1e5740d0` |
| [A7 — Kochen–Specker (CEGA 18-vector)](GaiaPhysicsLean/A7KochenSpecker/) | 218 | A | `gcn_0b8cd733edc4459d` |
| [A10 — Tsirelson CHSH bound](GaiaPhysicsLean/A10Tsirelson/) | 171 | A | `gcn_9f07543c6ff944b0` |
| [B7 — Naimark POVM dilation](GaiaPhysicsLean/B7NaimarkDilation/) | 347 | B | `gcn_b9e7abd2ad804f29` |

**Total**: 1,725 lines of formal Lean 4 covering five foundational results of quantum mechanics.

## Build

```bash
lake build                         # build all four theorems
lake build GaiaPhysicsLean.A3Stinespring.Theorem
lake build GaiaPhysicsLean.A5Nocloning.Theorem
lake build GaiaPhysicsLean.A7KochenSpecker.Theorem
lake build GaiaPhysicsLean.A10Tsirelson.Theorem
lake build GaiaPhysicsLean.B7NaimarkDilation.Theorem
```

First-time `lake build` will pull and compile Mathlib4 (≈30 minutes on cold cache).

## How these were proved

Each problem started as a one-paragraph statement extracted from Bohrium's LKM (Literature
Knowledge Manager) and was handed to a `claude` (Anthropic) main agent running the
`gaia-discovery` v3.5 loop:

1. **Decompose** the target into sub-claims (`gd inquiry`, `ranked_focus`).
2. **Dispatch** sub-agents (one per claim) with Lean LSP access (`lean_local_search`,
   `lean_leansearch`, `lean_loogle`, `lean_multi_attempt`) and an LKM literature
   client (`lkm_match`, `lkm_evidence`).
3. **Verify**: every action's evidence is type-checked by a `gd verify-server`
   that runs `lake env lean` on the submitted `.lean` file.
4. **Ingest** verdicts into the BP claim graph (`gd run-cycle`); the orchestrator
   chooses the next round from `ranked_focus`.
5. **Watchdog** monitors the agent and, on `TERMINAL.success.iter<N>.md`, runs an
   *independent* `lake build` of the primary target. If `rc ≠ 0`, the marker is
   auto-downgraded to `TERMINAL.fake_success_<ts>_lake_rc<N>.md` and the loop continues.

The per-problem BP plans are in [`plans/`](./plans/) — each is a small `plan.gaia.py`
file that authored the initial claim and target metadata.

## Relation to the gaia-discovery repo

- This repo: **terminal artifacts only** — Lean files + their BP plan, frozen at the
  point of successful build verification. Pure proof library.
- [`gaia-discovery`](https://github.com/SiliconEinstein/gaia-discovery): **the orchestrator** —
  agent prompts, watchdog, MCP server, BP ingest, verify-server. Active development.

## Lean toolchain

Same as Mathlib4 pin: `leanprover/lean4:v4.30.0-rc2`. See [`lean-toolchain`](./lean-toolchain).

## Contributing

These proofs were autonomously generated; if you spot a smell, a simpler proof, or a missing
limit / edge case, PRs welcome. Each project's `README.md` lists the proof outline so reviewers
can audit the reasoning against the Lean code directly.
