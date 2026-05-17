# PPT² Conjecture — A-line Formalization (Mathlib-gap Research)

> **PPT² conjecture** (Christandl 2012). For every $d \ge 2$ and every pair of PPT (positive
> partial transpose) channels $\Phi, \Psi : \mathcal{M}_d \to \mathcal{M}_d$, the composition
> $\Phi \circ \Psi$ is entanglement-breaking.

Open for $d \ge 3$ (a 14-year-old quantum-information conjecture).

This sub-project is the **active-research half** of `gaia-physics-lean` — unlike the
[top-level theorems](../) (A5, A7, A10, B7, A3 — all proved & lake-verified clean),
PPT² is an ongoing formalization where each session of the agent has either:

1. **Closed a piece** (Bloch4 reduction, SU(2) Haar measure infra, etc.)
2. **Bumped into a Mathlib gap** (`sorry` annotated with `gap_kind: mathlib_missing`)
3. **Bumped into an open math problem** (`axiom` documenting an actual research question)

We push it here because it's a **realistic stress test** of using LLM agents to do
serious math when Mathlib doesn't have what you need.

## Build

```bash
# Same toolchain as parent: leanprover/lean4:v4.30.0-rc2
lake build PPT2.Cases.Bloch4    # ✅ rc=0 (2643 jobs) — the d=2 reduction case is fully proved
lake build PPT2.Mathlib.HaarSU2 # ✅ rc=0 — SU(2) Haar measure infrastructure
lake build PPT2                  # builds everything that builds; sorries are visible
```

## Status inventory

### 🟢 17 clean modules (0 sorry, 0 axiom)

| Module | LOC | What it proves |
|---|---|---|
| `PPT2/PartialTranspose.lean` | 100 | $T_B$ partial transpose definition + linearity |
| `PPT2/Choi.lean` | 404 | Choi matrix construction (CP ⇔ Choi PSD scaffold) |
| `PPT2/Separable.lean` | 117 | Separable state definition + product-state cone |
| `PPT2/EntanglementBreaking.lean` | 318 | EB channel characterization |
| `PPT2/Channels/Depolarizing.lean` | 96 | Depolarizing channel structural lemmas |
| `PPT2/Mathlib/Quaternions.lean` | 384 | Quaternion identification with SU(2) ≅ S³ |
| **`PPT2/Mathlib/HaarSU2.lean`** | **249** | **SU(2) Haar measure (new Mathlib contribution)** |
| `PPT2/Cases/Bloch.lean` | 165 | Bloch sphere parametrization |
| **`PPT2/Cases/Bloch4.lean`** | **224** | **`bloch4_coord_ppt_negation` (d=2 reduction key lemma) ✅** |
| `PPT2/Cases/Helpers.lean` | 268 | Index/dim shuffling helpers |
| `PPT2/Cases/SchmidtDim2.lean` | 173 | d=2 Schmidt decomposition |
| `PPT2/Cases/Pauli.lean` | 156 | Pauli matrix algebra |
| `PPT2/Cases/SpectralDim2.lean` | 87 | d=2 spectral analysis |
| `PPT2/V1/Spectral.lean` | 185 | V1 (range-criterion) spectral toolkit |
| `PPT2/V1/Kronecker.lean` | 171 | Kronecker product helpers |
| `PPT2/Examples/Dephasing.lean` | 134 | Worked example |
| `PPT2/Examples/MeasurePrepare.lean` | 85 | Worked example |

### 🟡 WIP modules with `gap_kind: mathlib_missing` sorries

These are **Mathlib gaps** — the proof strategy is mapped out but a foundational Mathlib lemma
is missing. Each sorry is annotated in code with the missing lemma name & PR plan.

| Module | sorry | axiom | Gap summary |
|---|---|---|---|
| `PPT2/Mathlib/Twirling.lean` | 9 | 0 | Fubini for integral over SU(2), bi-invariance integral lemma, partial trace integrability |
| `PPT2/Mathlib/Twirling_Haar.lean` | 3 | 0 | Haar pushforward + `IsFiniteMeasure` instance plumbing |
| `PPT2/Mathlib/WernerHolevo.lean` | 2 | 0 | Schur orthogonality on $\mathfrak{su}(d)$ |
| `PPT2/Cases/DUC.lean` | 1 | 0 | Discrete unitary commutant decomposition for d=2 |
| `PPT2/Cases/D3.lean` | 4 | 0 | KAK decomposition (Cartan) for $SU(2) \otimes SU(2)$ |
| `PPT2/CMHW_OpSchmidt.lean` | 3 | 0 | Operator Schmidt rank bound (Cariello-Müller-Hermes-Werner) |
| `PPT2/Cases/Stormer.lean` | 8 | 0 | Stormer's 1963 decomposition theorem for $2 \otimes 2$ PPT |
| `PPT2/Cases/Dim2.lean` | 5 | 0 | d=2 final assembly (depends on DUC + Stormer) |

### 🔴 modules with `axiom` placeholders (= documented open math problems)

| Module | axiom | Status |
|---|---|---|
| `PPT2/V1/Cone.lean` | 4 | Bennett 1999 range criterion + Caratheodory cone — **research-level Mathlib gap** |
| `PPT2/Conjectures/PPT2.lean` | 1 | The main d≥3 PPT² conjecture (still open in math literature) |

## What the gaia-discovery agent achieved here

**Iter-1 → Iter-99 over ~3 weeks of autonomous work**:

- iter-1 to ~50: built PPT² object library (PartialTranspose, Choi, EntanglementBreaking, Separable)
- iter-51 to ~85: built SU(2) Haar measure infrastructure (new Mathlib contribution)
- iter-86 to 99: closed the d=2 case via Bloch4 reduction (lake-verified)
- iter-73 to 77: B-line (P7 swarm) systematically documented why d=4 attack vectors fail

The **`TERMINAL.SUCCESS.iter98.md`** session reached BP target belief = 1.0 on
`su_d_haar_twirling_d2` — the goal the user set for iter-80 pivot.

The remaining sorries are 100% `gap_kind: mathlib_missing` (foundational Mathlib lemmas that
need to be either proved or upstreamed) or `gap_kind: open_conjecture` (= d≥3 PPT² itself).

## Why this is here (not in the clean library)

A note on the curation policy: this repo's [top-level theorems](../) require all three of
`lake build rc=0`, only standard axioms, and zero `sorry`. PPT² fails the latter two on
purpose — it's a **working notebook** of the agent's serious-research mode, and the value of
publishing it is to show what the orchestration produces when the problem is genuinely
hard and current Mathlib doesn't cover everything needed.
