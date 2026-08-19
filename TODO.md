# TODO

The session is green: no `sorry`, no `oops`. The three former obligations (O1
`fireable_heads_join_eq`, O2 `first_bound_hit`, O3 `dl_saturate_idx_eq`) are proved.

## The task: a verified tree decomposition

This is the exercise the repository exists for. `Tree_Decomposition.thy` provides the certificate
datatype (`td_node`) and the in-kernel checker (`valid_decomp`: coverage, local cover, root cover,
running intersection) lifted from the PDDL grounder — but **nothing is proved about it**, and it is
not known whether the checker says the right thing. `Hypertree_Decomposition.thy` specifies the
surrounding work. In order:

1. **Validate the checker.** Prove `valid_trivial_decomp` (the single-bag fallback passes its own
   check; needs `local_cover_trivial`, deferred upstream). Convince yourself `ri_ok`'s top-down
   "outside" bookkeeping really is running intersection.
2. **The evaluator.** Bottom-up fold over a validated tree: per node run `body_join_idx` restricted
   to that node's atoms, semi-join with each child's projected result, project onto the variables
   needed above.
3. **The Yannakakis obligation** — the one real theorem:
   `valid_decomp … ⟹ set (decomposed_join …) = set (body_join …)` modulo projection onto the target
   variables. Running intersection is what makes projection lossless.
4. **Plumbing.** Replace `fireable_heads_idx` by its decomposition-driven variant and rerun the
   `dl_step_idx_eq` chain; `dl_saturate` and every soundness result then carry over verbatim.
   Decompose once per clause, outside the fixpoint loop.

The decomposer itself stays untrusted and unformalised: it emits a decomposition, the checker
re-validates it, and evaluation is proved correct relative to a validated decomposition.

## Smaller things

* **Selectivity in the index.** `cand_facts` keys on the *leftmost* bound argument. The upstream
  grounder considers every determined position and takes the smallest bucket (`determined_ids` +
  `shortest`), and evaluates fully-bound atoms as a single membership test (`all_bound`). Both were
  dropped in the extraction; both are proof-cheap and worth restoring.
* **Semi-naive evaluation.** `dl_step` re-derives every fact every round. Join against the *delta*
  in at least one body position. A further refinement of the same `dl_step` interface; composes
  with the index.
* **Completeness of the evaluator** (`set (dl_eval U Pl) = {f. datalog_prog.derivable (set U) (set Pl) f}`,
  under `dl_safe` + `dl_heads_covered`). Not needed for the certificate-checking use case; worth
  doing if the evaluator is ever to be trusted directly.
* **Code export smoke test.** No `export_code` in the session yet, so nothing checks that the
  `[code]` equations actually generate. Add one, plus a tiny worked example program.
