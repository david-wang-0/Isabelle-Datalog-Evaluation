theory Hypertree_Decomposition
  imports Datalog_Indexed_Join
begin

section \<open>TODO: worst-case-optimal joins via hypertree decomposition (Correa et al.)\<close>

text \<open>\<^bold>\<open>This theory is a placeholder. It contains no definitions --- only a specification of the work
  someone should do next.\<close>

  \<^bold>\<open>The problem.\<close> \<^const>\<open>body_join_idx\<close> is a left-deep nested-loop join. The index makes each
  lookup cheap, but the \<^emph>\<open>shape\<close> of the plan is fixed: body atoms are joined in the order they
  appear in the clause, and every intermediate result is materialised. For an acyclic body that is
  fine; for a cyclic one it is not. The standard witness is the triangle rule

    \<open>tri(x, y, z) :- e(x, y), e(y, z), e(z, x).\<close>

  where any nested-loop order builds an intermediate relation of size quadratic in \<open>|e|\<close> even
  though the output has only \<open>|e|\<^sup>3\<^sup>/\<^sup>2\<close> tuples (the AGM bound). Real grounding tasks hit exactly
  this: the hardest-to-ground planning domains are the ones whose action-schema bodies are cyclic
  conjunctive queries. Here the effect is that one round of \<^const>\<open>dl_step_idx\<close> can blow up on a
  single bad clause while every other clause is instant.

  \<^bold>\<open>The fix.\<close> Decompose each clause body once (offline, per program --- not per round), then
  evaluate along the decomposition:
  \<^item> treat the body atoms as a \<^emph>\<open>hypergraph\<close>: one vertex per variable, one hyperedge per body atom;
  \<^item> compute a (generalised) \<^emph>\<open>hypertree decomposition\<close> of that hypergraph
    \<^cite>\<open>"morak_et_al:LIPIcs.ICLP.2012.247"\<close>: a tree whose nodes carry
    a \<^emph>\<open>bag\<close> of variables and a set of atoms covering the bag, satisfying the running-intersection
    property;
  \<^item> evaluate bottom-up in Yannakakis style --- semi-join reduce upwards, project each bag onto the
    variables still needed above it, then join downwards. Intermediate relations are then bounded
    by the bag sizes, i.e.\ by the decomposition's \<^emph>\<open>width\<close>, rather than by the query size.

  This is the approach of Correa et al.\ to grounding \<^cite>\<open>correaGrounding\<close>:
  hypertree/tree decompositions of the action-schema (datalog rule) bodies evaluated by a
  Yannakakis-style bottom-up pass, which is what makes otherwise-ungroundable planning tasks
  groundable. It builds on the earlier use of database query-optimisation techniques for lifted
  successor generation \<^cite>\<open>correaLiftedSuccessor\<close>. The decompositions themselves come from
  an off-the-shelf decomposer (\<open>htd\<close> and friends), not from a hand-rolled heuristic.

  \<^bold>\<open>Why this fits a verified development.\<close> The decomposer is a large, heuristic, untrusted piece of
  software --- and it does not need to be trusted. Follow the same \<^emph>\<open>certificate\<close> discipline this
  repository uses for the evaluator itself: the decomposer emits a decomposition, a small in-kernel
  checker re-validates it, and the verified evaluation is proved correct \<^emph>\<open>relative to a validated
  decomposition\<close>. Nothing about the decomposer's search needs to be formalised.\<close>

subsection \<open>Suggested shape of the work\<close>

text \<open>\<^enum> \<^bold>\<open>The decomposition datatype and its checker.\<close> A tree

    \<open>datatype 'v td_node = TDNode (bag: "'v list") (node_atoms: "nat list") (children: "'v td_node list")\<close>

  where \<open>node_atoms\<close> are indices into the clause's \<^const>\<open>cls_body_atoms\<close>. A checker
  \<open>valid_decomp target avars n td\<close> should decide, by list/set operations only (so that it
  code-generates):
    \<^item> \<^emph>\<open>coverage\<close>: every atom index \<open>0 ..< n\<close> occurs exactly once in the tree (an \<open>mset\<close> equality);
    \<^item> \<^emph>\<open>local cover\<close>: every atom assigned to a node has all its variables in that node's bag;
    \<^item> \<^emph>\<open>root cover\<close>: the projection target (here the head variables plus the guard variables) is
      contained in the root bag;
    \<^item> \<^emph>\<open>running intersection\<close>: for every node, the variables of its subtree that also occur outside
      it lie in that node's bag. Checking this top-down, carrying the set of "outside" variables
      (ancestor bags, the target, and sibling subtrees), is the formulation that directly licenses
      early projection.
  Also define the \<^emph>\<open>trivial\<close> decomposition (one node, all atoms, bag = all variables) and prove it
  valid: that is the fail-safe fallback when the checker rejects the untrusted decomposer's output,
  and it degenerates to the present flat join.

\<^enum> \<^bold>\<open>The evaluator.\<close> A bottom-up fold over the validated tree: at each node run the existing
  \<^const>\<open>body_join_idx\<close> restricted to that node's atoms (bags are small, so a nested-loop join
  inside a bag is fine), semi-join with each child's projected result, then project onto the
  variables needed above. The per-node join reuses \<^theory>\<open>Datalog_Evaluation.Fact_Index\<close>
  unchanged.

\<^enum> \<^bold>\<open>The soundness bridge (the Yannakakis obligation).\<close> The one real theorem:

    \<open>valid_decomp \<dots> \<Longrightarrow> set (decomposed_join \<dots>) = set (body_join \<dots>)\<close>

  modulo projection onto the target variables --- the projected split-join computes exactly the same
  head-variable bindings as the flat join. Running intersection is what makes projection lossless: a
  variable projected away below a node can never be re-constrained above it.

\<^enum> \<^bold>\<open>Plumbing.\<close> Replace \<^const>\<open>fireable_heads_idx\<close> by its decomposition-driven variant and rerun
  the \<open>dl_step_idx_eq\<close> chain, so that \<^const>\<open>dl_saturate\<close> is untouched and every existing
  soundness result carries over verbatim. Decompose \<^emph>\<open>once per clause\<close>, outside the fixpoint loop:
  the decomposition depends only on the program, never on the current fact set.

  \<^bold>\<open>Scope note.\<close> Items 1--3 are independent of the rest of this repository and can be developed
  against a plain relational-join signature first; only item 4 touches the datalog layer.\<close>

end
