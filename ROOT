chapter AFP

session Datalog_Evaluation = HOL +
  description \<open>Semantics supplement to the AFP Stratified_Datalog entry, a fuel-free fixpoint
    evaluator for positive datalog programs, and its refinements: assoc-list matching with a
    fact-driven body join, and an RBT-indexed join. The evaluator is an untrusted oracle in the
    intended use, so it is proved sound (every derived fact is derivable) but not complete.\<close>
  options [timeout = 600]
  sessions
    "HOL-Data_Structures"
    "Stratified_Datalog"
  theories
    Datalog_Semantics
    Datalog_Fixpoint
    Datalog_Matching
    Fact_Index
    Datalog_Indexed_Join
    Tree_Decomposition
    Hypertree_Decomposition
  document_files
    "root.tex"
    "root.bib"
