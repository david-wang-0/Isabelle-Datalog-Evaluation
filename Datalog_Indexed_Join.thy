theory Datalog_Indexed_Join
  imports Fact_Index
begin

section \<open>Refinement 2b: the indexed body join and the indexed round\<close>

text \<open>The last of the three refinements of \<^const>\<open>dl_step\<close>:

  \<^enum> \<^const>\<open>dl_step\<close> (\<^theory>\<open>Datalog_Evaluation.Datalog_Fixpoint\<close>) --- enumerate \<open>|U|\<^sup>#\<^sup>v\<^sup>a\<^sup>r\<^sup>s\<close>
    substitutions per clause;
  \<^enum> \<^const>\<open>dl_step_join\<close> (\<^theory>\<open>Datalog_Evaluation.Datalog_Matching\<close>) --- fact-driven nested-loop
    join, but scanning all facts per body atom;
  \<^enum> \<open>dl_step_idx\<close> (here) --- the same join, but each atom's candidate facts come from the
    \<^theory>\<open>Datalog_Evaluation.Fact_Index\<close> RBT index, keyed on the first argument position that is
    already bound (a constant in the atom, or a variable bound by an earlier atom in the join).
    The index is built \<^emph>\<open>once\<close> per round and reused across all clauses and all join levels.

  All three compute the same fact set; the theorems below are the refinement chain. Note the
  remaining complexity gap: this is still a \<^emph>\<open>left-deep nested-loop\<close> join, so on a cyclic body
  (the classic triangle query) it is worst-case suboptimal no matter how good the index is. Closing
  that gap is what \<open>Hypertree_Decomposition\<close> is about.\<close>

subsection \<open>Choosing an index key for an atom under a partial binding\<close>

text \<open>The first argument position of the atom whose value is already determined --- either a
  constant in the atom, or a variable already bound in \<open>al\<close>. \<^const>\<open>None\<close> means the atom is
  completely free, in which case the join can only iterate the predicate bucket.\<close>

fun first_bound :: "('x \<times> 'c) list \<Rightarrow> ('x, 'c) id list \<Rightarrow> (nat \<times> 'c) option" where
  "first_bound al [] = None"
| "first_bound al (i # is') =
     (case i of
        id.Cst c \<Rightarrow> Some (0, c)
      | id.Var x \<Rightarrow> (case map_of al x of
                      Some v \<Rightarrow> Some (0, v)
                    | None \<Rightarrow> map_option (\<lambda>(j, v). (Suc j, v)) (first_bound al is')))"

text \<open>The candidate facts for an atom: the narrow per-argument bucket when a position is bound, the
  whole predicate bucket otherwise.\<close>
definition cand_facts ::
    "('p::linorder, 'c::linorder) findex \<Rightarrow> ('x \<times> 'c) list \<Rightarrow> ('p, 'x, 'c) lh
       \<Rightarrow> ('p, 'c) dl_fact list" where
  "cand_facts idx al a =
     (case first_bound al (snd a) of
        None \<Rightarrow> plookup (fx_p idx) (fst a)
      | Some (j, v) \<Rightarrow> alookup (fx_a idx) (fst a) j v)"

definition match_facts_idx ::
    "('p::linorder, 'c::linorder) findex \<Rightarrow> ('x \<times> 'c) list \<Rightarrow> ('p, 'x, 'c) lh
       \<Rightarrow> ('x \<times> 'c) list list" where
  "match_facts_idx idx al a = List.map_filter (match_atom_al al a) (cand_facts idx al a)"

fun body_join_idx ::
    "('p::linorder, 'c::linorder) findex \<Rightarrow> ('x \<times> 'c) list \<Rightarrow> ('p, 'x, 'c) lh list
       \<Rightarrow> ('x \<times> 'c) list list" where
  "body_join_idx idx al [] = [al]"
| "body_join_idx idx al (a # as') =
     concat (map (\<lambda>al'. body_join_idx idx al' as') (match_facts_idx idx al a))"

declare cand_facts_def [code] match_facts_idx_def [code] body_join_idx.simps [code]

subsection \<open>The index narrows without losing matches\<close>

text \<open>\<^bold>\<open>Sound\<close>: candidates are facts. Immediate from the two index-soundness lemmas.\<close>
lemma cand_facts_sound: "set (cand_facts (build_findex facts) al a) \<subseteq> set facts"
  unfolding cand_facts_def build_findex_def
  using plookup_build_sound[THEN subsetD] alookup_build_sound[THEN subsetD]
  by (auto split: option.splits prod.splits)

text \<open>\<^bold>\<open>The key narrowing lemma\<close>: if the atom matches a fact, then the position \<^const>\<open>first_bound\<close>
  picked is a real position of that fact and carries the value the index was keyed on. Hence
  narrowing by that key cannot drop a matching fact.

  The proof needs a generalisation: \<^const>\<open>first_bound\<close> may be evaluated at a partial assignment
  \<open>al0\<close> smaller than the one \<^const>\<open>match_ids_al\<close> threads, provided the latter extends it. That is
  what carries the induction through, since each matched argument only grows the assignment.\<close>

lemma match_id_al_mono:
  "match_id_al al i d = Some al' \<Longrightarrow> map_of al x = Some v \<Longrightarrow> map_of al' x = Some v"
  by (cases i) (auto split: option.splits if_splits)

lemma first_bound_match_gen:
  "first_bound al0 ids = Some (j, v) \<Longrightarrow> match_ids_al al ids ds = Some r \<Longrightarrow>
     (\<forall>z w. map_of al0 z = Some w \<longrightarrow> map_of al z = Some w) \<Longrightarrow> j < length ds \<and> ds ! j = v"
proof (induct ids arbitrary: al ds r j v)
  case Nil then show ?case by simp
next
  case (Cons i ids)
  from Cons.prems(2) obtain d ds' where ds: "ds = d # ds'" by (cases ds) auto
  from Cons.prems(2) ds obtain al' where mi: "match_id_al al i d = Some al'"
    and rec: "match_ids_al al' ids ds' = Some r" by (auto split: option.splits)
  have ext': "\<forall>z w. map_of al0 z = Some w \<longrightarrow> map_of al' z = Some w"
    using Cons.prems(3) match_id_al_mono[OF mi] by blast
  show ?case
  proof (cases i)
    case (Cst c)
    with Cons.prems(1) have jv: "j = 0" "v = c" by auto
    from mi Cst have "d = c" by (auto split: if_splits)
    with jv ds show ?thesis by simp
  next
    case (Var y)
    show ?thesis
    proof (cases "map_of al0 y")
      case (Some w)
      with Var Cons.prems(1) have jv: "j = 0" "v = w" by auto
      have "map_of al y = Some w" using Some Cons.prems(3) by blast
      with mi Var have "d = w" by (auto split: if_splits option.splits)
      with jv ds show ?thesis by simp
    next
      case None
      with Var Cons.prems(1) obtain j' where fb': "first_bound al0 ids = Some (j', v)"
        and jsuc: "j = Suc j'" by (auto split: option.splits prod.splits)
      from Cons.hyps[OF fb' rec ext'] show ?thesis using ds jsuc by simp
    qed
  qed
qed

lemma first_bound_hit:
  assumes "match_ids_al al ids ds = Some al'" and "first_bound al ids = Some (j, v)"
  shows "j < length ds" and "ds ! j = v"
  using first_bound_match_gen[OF assms(2) assms(1)] by simp_all

lemma cand_facts_complete:
  assumes "f \<in> set facts" and "match_atom_al al a f = Some al'"
  shows "f \<in> set (cand_facts (build_findex facts) al a)"
proof (cases "first_bound al (snd a)")
  case None
  have "fst a = fst f" using assms(2) unfolding match_atom_al_def by (auto split: if_splits)
  thus ?thesis
    unfolding cand_facts_def build_findex_def None
    using plookup_build_complete[OF assms(1)] by simp
next
  case (Some jv)
  obtain j v where jv: "jv = (j, v)" by (cases jv)
  have peq: "fst a = fst f" and m: "match_ids_al al (snd a) (snd f) = Some al'"
    using assms(2) unfolding match_atom_al_def by (auto split: if_splits)
  have jl: "j < length (snd f)" and jval: "snd f ! j = v"
    using first_bound_hit[OF m] Some jv by auto
  have "f \<in> set (alookup (build_aidx facts) (fst f) j (snd f ! j))"
    by (rule alookup_build_complete[OF assms(1) jl])
  thus ?thesis
    unfolding cand_facts_def build_findex_def Some jv
    using peq jval by simp
qed

theorem match_facts_idx_eq:
  "set (match_facts_idx (build_findex facts) al a) = set (match_facts_al al a facts)"
    (is "?L = ?R")
proof
  show "?L \<subseteq> ?R"
    unfolding match_facts_idx_def match_facts_al_def set_map_filter'
    using cand_facts_sound by blast
next
  show "?R \<subseteq> ?L"
    unfolding match_facts_idx_def match_facts_al_def set_map_filter'
    using cand_facts_complete by blast
qed

theorem body_join_idx_eq:
  "set (body_join_idx (build_findex facts) al atoms) = set (body_join al atoms facts)"
proof (induction atoms arbitrary: al)
  case Nil
  thus ?case by simp
next
  case (Cons a atoms)
  have "set (body_join_idx (build_findex facts) al (a # atoms))
          = (\<Union>al' \<in> set (match_facts_idx (build_findex facts) al a).
               set (body_join_idx (build_findex facts) al' atoms))"
    by auto
  also have "\<dots> = (\<Union>al' \<in> set (match_facts_al al a facts). set (body_join al' atoms facts))"
    by (simp add: match_facts_idx_eq Cons.IH)
  also have "\<dots> = set (body_join al (a # atoms) facts)"
    by auto
  finally show ?case .
qed

subsection \<open>The indexed round\<close>

definition fireable_heads_idx ::
  "'c::linorder list \<Rightarrow> ('p::linorder, 'c) findex \<Rightarrow> ('p, 'x, 'c) clause
     \<Rightarrow> ('p, 'c) dl_fact list" where
  "fireable_heads_idx U idx cl =
     map (\<lambda>al. subst_atom (\<lambda>x. the (map_of al x)) (the_lh cl))
       (filter (\<lambda>al. list_all (\<lambda>x. case map_of al x of Some c \<Rightarrow> c \<in> set U | None \<Rightarrow> False)
                              (cls_vars cl)
                     \<and> list_all (eval_guard_al al) (cls_guards cl))
               (body_join_idx idx [] (cls_body_atoms cl)))"

text \<open>One round, indexed. The \<open>let\<close> is load-bearing: it builds the index \<^emph>\<open>once\<close> and reuses it for
  every clause. Inlining \<^const>\<open>build_findex\<close> into the clause loop would rebuild it \<open>|Pl|\<close> times and
  give back all of the speed-up.\<close>
definition dl_step_idx ::
  "'c list \<Rightarrow> ('p::linorder, 'x, 'c::linorder) clause list \<Rightarrow> ('p, 'c) dl_fact list
     \<Rightarrow> ('p, 'c) dl_fact list" where
  "dl_step_idx U Pl facts =
     (let idx = build_findex facts
      in remdups (facts @ concat (map (\<lambda>cl. if clause_safe_exec cl
                                            then fireable_heads_idx U idx cl
                                            else fireable_heads U cl facts) Pl)))"

declare fireable_heads_idx_def [code] dl_step_idx_def [code]

lemma fireable_heads_idx_eq:
  "set (fireable_heads_idx U (build_findex facts) cl) = set (fireable_heads_join U cl facts)"
  unfolding fireable_heads_idx_def fireable_heads_join_def
  by (simp add: body_join_idx_eq)

theorem dl_step_idx_eq: "set (dl_step_idx U Pl facts) = set (dl_step U Pl facts)"
proof -
  have "set (dl_step_idx U Pl facts) = set (dl_step_join U Pl facts)"
    unfolding dl_step_idx_def dl_step_join_def Let_def
    by (auto simp: fireable_heads_idx_eq)
  thus ?thesis using dl_step_join_eq by simp
qed

subsection \<open>The indexed fixpoint loop\<close>

text \<open>The same loop as \<^const>\<open>dl_saturate\<close>, but stepping with \<^const>\<open>dl_step_idx\<close>. Termination is
  inherited: by \<open>dl_step_idx_eq\<close> the two rounds have the same fact set, so the very same
  \<^const>\<open>all_head_facts\<close> measure decreases.\<close>

function dl_saturate_idx ::
  "'c list \<Rightarrow> ('p::linorder, 'x, 'c::linorder) clause list \<Rightarrow> ('p, 'c) dl_fact list
     \<Rightarrow> ('p, 'c) dl_fact list" where
  "dl_saturate_idx U Pl facts =
     (if set (dl_step_idx U Pl facts) = set facts
      then facts
      else dl_saturate_idx U Pl (dl_step_idx U Pl facts))"
  by pat_completeness auto

termination dl_saturate_idx
proof (relation "measure (\<lambda>(U, Pl, facts). card (set (all_head_facts U Pl) - set facts))")
  show "wf (measure (\<lambda>(U, Pl, facts). card (set (all_head_facts U Pl) - set facts)))"
    by simp
next
  fix U Pl facts
  assume neq: "set (dl_step_idx U Pl facts) \<noteq> set facts"
  have eq: "set (dl_step_idx U Pl facts) = set (dl_step U Pl facts)"
    by (rule dl_step_idx_eq)
  have "card (set (all_head_facts U Pl) - set (dl_step U Pl facts))
          < card (set (all_head_facts U Pl) - set facts)"
    using neq eq by (simp add: dl_step_measure_decreases)
  thus "((U, Pl, dl_step_idx U Pl facts), (U, Pl, facts))
          \<in> measure (\<lambda>(U, Pl, facts). card (set (all_head_facts U Pl) - set facts))"
    using eq by simp
qed

declare dl_saturate_idx.simps [simp del, code]

lemma dl_saturate_idx_unfold:
  "dl_saturate_idx U Pl facts =
     (if set (dl_step_idx U Pl facts) = set facts then facts
      else dl_saturate_idx U Pl (dl_step_idx U Pl facts))"
  by (rule dl_saturate_idx.simps)

definition dl_eval_idx ::
  "'c list \<Rightarrow> ('p::linorder, 'x, 'c::linorder) clause list \<Rightarrow> ('p, 'c) dl_fact list" where
  "dl_eval_idx U Pl = dl_saturate_idx U Pl []"

declare dl_eval_idx_def [code]

text \<open>\<^bold>\<open>The end-to-end refinement.\<close> Since \<open>dl_step_idx_eq\<close> makes the two rounds agree on fact
  sets, and \<open>dl_step_cong\<close> says a round only depends on the fact set, the two loops agree on
  fact sets too --- by induction along \<open>dl_saturate_idx.induct\<close>, carrying the invariant
  \<open>set facts = set facts'\<close> between the two loop states. Obligation O3 of \<open>TODO.md\<close>.\<close>
theorem dl_saturate_idx_eq:
  assumes "set facts = set facts'"
  shows "set (dl_saturate_idx U Pl facts) = set (dl_saturate U Pl facts')"
  using assms
proof (induction U Pl facts arbitrary: facts' rule: dl_saturate_idx.induct)
  case (1 U Pl facts)
  have step_eq: "set (dl_step_idx U Pl facts) = set (dl_step U Pl facts')"
    by (simp add: dl_step_idx_eq dl_step_cong[OF "1.prems"])
  show ?case
  proof (cases "set (dl_step_idx U Pl facts) = set facts")
    case True
    hence fix': "set (dl_step U Pl facts') = set facts'" using step_eq "1.prems" by simp
    show ?thesis
      using True fix' "1.prems"
        dl_saturate_idx_unfold[of U Pl facts] dl_saturate_unfold[of U Pl facts'] by simp
  next
    case False
    hence ne': "set (dl_step U Pl facts') \<noteq> set facts'" using step_eq "1.prems" by simp
    have "set (dl_saturate_idx U Pl facts) = set (dl_saturate_idx U Pl (dl_step_idx U Pl facts))"
      using False dl_saturate_idx_unfold[of U Pl facts] by simp
    also have "\<dots> = set (dl_saturate U Pl (dl_step U Pl facts'))"
      using "1.IH"[OF False step_eq] .
    also have "\<dots> = set (dl_saturate U Pl facts')"
      using ne' dl_saturate_unfold[of U Pl facts'] by simp
    finally show ?thesis .
  qed
qed

corollary dl_eval_idx_eq: "set (dl_eval_idx U Pl) = set (dl_eval U Pl)"
  unfolding dl_eval_idx_def dl_eval_def by (rule dl_saturate_idx_eq) simp

corollary dl_eval_idx_sound:
  assumes "f \<in> set (dl_eval_idx U Pl)"
  shows "datalog_prog.derivable (set U) (set Pl) f"
  using assms dl_eval_idx_eq dl_eval_sound by blast

end
