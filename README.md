# gaia-physics-lean

Lean 4 formalizations of theorems from **physics and quantum information**, autonomously
discovered and proved by the [`gaia-discovery`](https://github.com/SiliconEinstein/gaia-discovery)
agentic-loop system on top of [Mathlib4](https://leanprover-community.github.io/mathlib4_docs/).

Each theorem in this repo satisfies all three strict criteria:

1. **`lake build` returns `rc=0`** — the Lean kernel type-checks the entire dependency tree.
2. **`#print axioms` lists only the standard three**: `propext`, `Classical.choice`, `Quot.sound`.
3. **Zero `sorry` placeholders** in the main proof tree.

Anything below that bar (partial proofs with `sorry`, axiom-padded proofs, build failures) is
**not** in this repository — those live in the `gaia-discovery` working tree as `TERMINAL.stuck`
or `TERMINAL.partial` markers awaiting a future iteration.

## Index — unconditional theorems

These are *fully Mathlib-grounded* — no hypotheses are added beyond what the
informal statement requires. The agent built every Mathlib gap it ran into.

| Theorem | LOC | Tier | LKM claim |
|---|---|---|---|
| [A3 — Stinespring dilation](GaiaPhysicsLean/A3Stinespring/) | 900 | A | `gcn_85c00af123214e3e` |
| [A5 — No-cloning](GaiaPhysicsLean/A5Nocloning/) | 89 | A | `gcn_054b79cf1e5740d0` |
| [A7 — Kochen–Specker (CEGA 18-vector)](GaiaPhysicsLean/A7KochenSpecker/) | 218 | A | `gcn_0b8cd733edc4459d` |
| [A10 — Tsirelson CHSH bound](GaiaPhysicsLean/A10Tsirelson/) | 171 | A | `gcn_9f07543c6ff944b0` |
| [B7 — Naimark POVM dilation](GaiaPhysicsLean/B7NaimarkDilation/) | 347 | B | `gcn_b9e7abd2ad804f29` |

**Subtotal**: 1,725 lines covering five foundational results of quantum mechanics.

## Index — *conditional* theorems

These satisfy criteria 1–3 mechanically (lake builds, only standard axioms, no
`sorry` on the main path), but the proof takes a `Type`-valued *data bundle*
as a hypothesis — the bundle encodes a substantial piece of Mathlib
infrastructure that nobody (gaia or otherwise) has formalized yet. Each entry's
README explains exactly what's been packaged into hypothesis-data. Honesty
gate: red-team did not find an axiom shortcut or target-weakening; the
"weakening" is purely in *what counts as a witness*, not the statement.

| Theorem | LOC | Tier | LKM claim | Hypothesis bundle |
|---|---|---|---|---|
| [A9 — 2D TQFT ↔ commutative Frobenius algebra](GaiaPhysicsLean/A92dTqftFrobenius/) | 322 | A | `gcn_c8351754bdb44e38` | `TwoCobUP.WithExtend` (free-SMC on one self-dual object) |

**Subtotal**: 322 lines.

**Grand total**: 2,047 lines, 6 theorems (5 unconditional + 1 conditional).


## Research-in-progress: PPT² conjecture

The [`PPT2-project/`](./PPT2-project/) subdirectory contains the agent's active work on
the **PPT² conjecture** (Christandl 2012 — open for $d \ge 3$). Unlike the theorems above,
PPT² is *not* fully solved — it's a real research project that has accumulated:

- **17 lake-verified clean modules** (~3,300 LOC) — partial-transpose, Choi matrix,
  separability, entanglement-breaking channels, **SU(2) Haar measure infrastructure**,
  the d=2 Bloch4 reduction case.
- **~50 `sorry` annotations** all tagged `gap_kind: mathlib_missing` — these are
  **Mathlib gaps the agent identified and documented but couldn't close in current Mathlib**.
- **5 `axiom` declarations** corresponding to either open math problems (PPT²-d≥3 itself,
  Bennett 1999 range criterion) or major Mathlib infrastructure (Stormer 1963, Cartan KAK).

This is the **dirty research half** of gaia-physics-lean — what realistic LLM-agent
formalization looks like when Mathlib doesn't have everything you need. The clean library
above shows what we publish; PPT² shows the actual work product.

See [`PPT2-project/README.md`](./PPT2-project/README.md) for full status inventory.

## Build

```bash
lake build                         # build all six theorems
lake build GaiaPhysicsLean.A3Stinespring.Theorem
lake build GaiaPhysicsLean.A5Nocloning.Theorem
lake build GaiaPhysicsLean.A7KochenSpecker.Theorem
lake build GaiaPhysicsLean.A92dTqftFrobenius.Theorem
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
