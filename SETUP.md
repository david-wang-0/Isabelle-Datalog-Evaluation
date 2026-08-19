# Setup

What you need to build and work on this development, and the optional agent-facing Isabelle tooling.

## 1. Prerequisites

| Component | Where |
| --- | --- |
| Isabelle2025-2 | <https://isabelle.in.tum.de/> |
| AFP 2025-2 (supplies `Stratified_Datalog`) | <https://www.isa-afp.org/download/> |

Register the AFP with Isabelle once, so `Stratified_Datalog` resolves:

```sh
isabelle components -u <afp-checkout>/thys
isabelle components -l | grep afp        # confirm
```

The session also uses `HOL-Data_Structures` (`RBT_Map`), which ships with the distribution.

## 2. Build the dependency heaps

Nothing in this repository needs to be *built* to be edited, but the two imported sessions should be
prebuilt so the editor loads them instead of elaborating them from source:

```sh
isabelle build -b -j4 Stratified_Datalog HOL-Data_Structures
```

`Stratified_Datalog` pulls in a chunk of the AFP (`Labeled_Transition_Systems`, `Collections`,
`Native_Word`, `Deriving`, …); on a cold machine expect this to run for a while. It is a one-off.

Then build this session itself (it is not green yet — see `TODO.md`):

```sh
isabelle build -d . Datalog_Evaluation
```

## 3. Edit it interactively

Launch jEdit from the repository root, on the `Stratified_Datalog` heap:

```sh
isabelle jedit -d . -l Stratified_Datalog Datalog_Semantics.thy
```

Load `Stratified_Datalog`, **not** a heap for `Datalog_Evaluation` itself: the heap you load is
frozen, and everything in it stops being editable. The only other dependency,
`HOL-Data_Structures.RBT_Map`, is small enough to be elaborated from source at startup.

After editing `ROOT` (new theory, new session dependency, new document file), restart jEdit — a
running instance does not pick up `ROOT` changes. The same is true of a new `imports` entry in a
theory header.

## 4. The document (citations)

`document/root.tex` and `document/root.bib` are listed under `document_files` in `ROOT`, which is what
makes the `\<^cite>\<open>…\<close>` antiquotations in the theories resolve. To render the PDF:

```sh
isabelle build -d . -o document=pdf Datalog_Evaluation
```

A `\<^cite>` key that is not in `document/root.bib` shows up as a `Bad bibtex_entry` error in the
editor, so citations are checked, not just typeset.

## 5. Agent / MCP tooling (optional)

None of this is required to build the development; it is what an AI coding agent uses to drive
Isabelle instead of shelling out to `isabelle build`. Three backends, in decreasing interactivity:

| Tool | What it is | Source |
| --- | --- | --- |
| **I/Q** (`isabelle_iq`) | jEdit plugin that exposes the *running* editor as an MCP server on `127.0.0.1` (base port 8765, scanning upward). Same buffers and squiggles the human sees; single-writer. | `iq` component of AutoCorrode — <https://github.com/awslabs/AutoCorrode> |
| **PIDE MCP** (`isabelle_pide`) | `isabelle pide_mcp -l <SESSION> -d <dir>`: a private *headless* PIDE session over stdio. No editor, no port; use when jEdit must not be disturbed or several agents need to work in parallel (one session each). | <https://github.com/kappelmann/isabelle-pide-mcp> |
| **CLI** (`isabelle eval_at`, `isabelle desorry`) | One-shot headless queries: proof state at a line, `thm`/`term`/`find_theorems`/`sledgehammer` at a line, whole-file error sweep, bulk `sorry` replacement. Needs only a prebuilt heap — no jEdit, no MCP. ~6 s fixed cost per call, so batch verdicts only, never an edit→check loop. | `yonoteam/isa_agentic_cli_tools`, branch `2025-2` — <https://github.com/yonoteam/isa_agentic_cli_tools> |

Optional extra: the Isabelle linter (jEdit plugin + CLI) —
<https://github.com/isabelle-prover/isabelle-linter>.

Install the component-shaped ones the usual way and restart Isabelle:

```sh
isabelle components -u <checkout-dir>
```

Wiring notes:

- **I/Q** needs its stdio↔TCP proxy registered as an MCP server (`iq_bridge.py` in the AutoCorrode
  `iq` directory), and one authentication call per TCP connection — the token is regenerated on each
  jEdit restart unless `IQ_AUTH_TOKEN` is pinned in the environment. Because stdio MCP servers bind
  at agent-session start, a session that predates the running jEdit must reconnect (in Claude Code:
  `/mcp`) before its tools work.
- **PIDE MCP** should be registered *per repository*, not user-scope: a user-scope entry boots a full
  headless Isabelle in every project you open. Point its `-l` at a real prebuilt heap
  (`Stratified_Datalog` here); the default `-l HOL` re-elaborates every dependency from source.
