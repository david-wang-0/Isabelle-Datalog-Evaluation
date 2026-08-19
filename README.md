# Isabelle-Datalog-Evaluation

Isabelle/HOL supplements to the AFP `Stratified_Datalog` entry: a **reference semantics** for
positive datalog over a finite constant universe, a **fuel-free fixpoint evaluator**, and two
**refinements** of the evaluator's inner loop.

Extracted from the datalog layer of a verified PDDL grounder so that it can be developed (and
reused) on its own: nothing here mentions planning, and the only dependencies are the AFP
`Stratified_Datalog` entry and `HOL-Data_Structures`.

Build and tooling instructions are in [`SETUP.md`](SETUP.md).

## Layout

One session, `Datalog_Evaluation`, seven theories:

| Theory | Contents |
| --- | --- |
| `Datalog_Semantics` | Positivity, the relation to stratified datalog, and the universe-restricted least-model semantics (`datalog_prog.derivable`) with locales `positive_datalog`, `datalog_universe`, `positive_datalog_universe`. The specification side. |
| `Datalog_Fixpoint` | **The evaluator, code only.** `dl_step` (one immediate-consequence round) and `dl_saturate` (iterate until no new facts). No fuel/counter: the loop tests for a real fixpoint. Termination + soundness proved. |
| `Datalog_Matching` | Refinement 1: assoc-list matching (`match_atom_al`) and the fact-driven `body_join` — cost proportional to matching tuples, not to `|U|^k`. |
| `Fact_Index` | Refinement 2a: RBT fact index, coarse (predicate bucket) and fine (predicate, argument position, value). |
| `Datalog_Indexed_Join` | Refinement 2b: `body_join_idx` / `dl_step_idx` / `dl_saturate_idx` — the same join with candidate facts drawn from the index, plus the refinement chain back to `dl_step`. |
| `Tree_Decomposition` | Certificate datatype (`td_node`) and in-kernel checker (`valid_decomp`) for a tree decomposition, lifted from the grounder. **Scaffolding: nothing is proved about it** — see the health warning in the theory. |
| `Hypertree_Decomposition` | **Specification only, no definitions.** The hypertree-decomposition (Correa et al.) layer someone should implement next, on top of `Tree_Decomposition`. |

The refinement chain is

```
dl_step      (naive |U|^#vars enumeration, the specification)
  = dl_step_join   (fact-driven nested-loop join)            -- Datalog_Matching
  = dl_step_idx    (same join, index-narrowed candidates)    -- Datalog_Indexed_Join
```

as *fact sets*; `dl_saturate` / `dl_saturate_idx` are the corresponding loops.

## What is and is not proved

**Proved.** Termination of both loops; soundness (`dl_eval_sound`, `dl_eval_idx_sound`: every
returned fact is `datalog_prog.derivable`); the index does not lose facts
(`plookup_build_complete`, `alookup_build_complete`); the abstract semantics coincides with the AFP
stratified least solution (`derivable_iff_least_solution`).

**Deliberately not proved.** That the evaluator computes the *least model* (completeness). In the
intended use it is an **untrusted oracle** whose output is re-validated by a certificate checker,
so completeness buys nothing. `dl_saturate_is_fixpoint` states only the trivial thing — the loop
exits at a fixpoint of `dl_step`.

**Unproved scaffolding.** `Tree_Decomposition`'s checker: the datatype and the four conditions are
there, but no theorem relates them to join equivalence. That, and the layer above it, is the open
work — see `TODO.md`.

## Status

Builds green: no `sorry`, no `oops`.

## Building

Requires the AFP (for `Stratified_Datalog`) registered as an Isabelle component:

```bash
isabelle build -d . Datalog_Evaluation
```
