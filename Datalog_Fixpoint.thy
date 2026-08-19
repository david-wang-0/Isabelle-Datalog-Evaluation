theory Datalog_Fixpoint
  imports Datalog_Semantics
begin

section \<open>Fixpoint evaluation of a positive datalog program\<close>

text \<open>\<^bold>\<open>This theory is the specification-level evaluator: code only.\<close> It computes the least model of
  a positive datalog program \<open>set Pl\<close> over a finite constant universe \<open>set U\<close> --- both given as
  lists --- by iterating the immediate-consequence operator \<open>dl_step\<close> \<^emph>\<open>until it stops
  producing new facts\<close>. There is no fuel/counter argument: the loop tests for a genuine fixpoint
  (\<open>set (dl_step U Pl facts) = set facts\<close>), which is what one wants both as a specification and in
  the executable path.

  Everything here is deliberately \<^emph>\<open>naive\<close>: one round re-enumerates every grounding substitution of
  every clause (\<^const>\<open>cls_substs\<close>, i.e.\ \<open>|U|\<^sup>#\<^sup>v\<^sup>a\<^sup>r\<^sup>s\<close> per clause) and re-derives every fact from
  scratch. That is unusable on real programs but it is short, obviously correct, and it is the
  \<^emph>\<open>reference\<close> that the efficient joins refine:
  \<^item> \<open>Datalog_Matching\<close> --- assoc-list matching and the fact-driven
    \<open>body_join\<close> (cost \<open>\<propto>\<close> matching tuples rather than \<open>|U|\<^sup>k\<close>);
  \<^item> \<open>Fact_Index\<close> / \<open>Datalog_Indexed_Join\<close> ---
    the RBT fact index and the indexed round \<open>dl_step_idx\<close>, proved to compute the same fact set;
  \<^item> \<open>Hypertree_Decomposition\<close> --- the (unimplemented) worst-case-optimal
    layer.

  \<^bold>\<open>What is proved here.\<close> Termination (mandatory: the recursion is not structural) and
  \<^emph>\<open>soundness\<close> --- every returned fact is \<^const>\<open>datalog_prog.derivable\<close>. \<^bold>\<open>Not\<close> proved: that the
  result really is the least model (completeness / "it is a fixpoint of the least-model operator").
  In the intended use the evaluator is an \<^emph>\<open>untrusted oracle\<close> whose output is re-validated by a
  certificate checker (the discipline of \<^cite>\<open>datalogLean\<close>), so completeness buys nothing;
  see \<open>TODO.md\<close> if it is ever wanted.\<close>

subsection \<open>One round of the immediate-consequence operator\<close>

text \<open>The heads a single clause fires from the current fact set: for every grounding substitution
  over \<open>U\<close> whose guards hold and whose positive body atoms are all present, the substituted head.\<close>
definition fireable_heads ::
  "'c list \<Rightarrow> ('p, 'x, 'c) clause \<Rightarrow> ('p, 'c) dl_fact list \<Rightarrow> ('p, 'c) dl_fact list" where
  "fireable_heads U cl facts =
     map (\<lambda>\<sigma>. subst_atom \<sigma> (the_lh cl))
       (filter (\<lambda>\<sigma>. (\<forall>g \<in> set (cls_guards cl). eval_guard \<sigma> g)
                    \<and> (\<forall>a \<in> set (cls_body_atoms cl). subst_atom \<sigma> a \<in> set facts))
               (cls_substs U cl))"

text \<open>One immediate-consequence round over the whole program: keep the current facts, add every
  clause's fireable heads.\<close>
definition dl_step ::
  "'c list \<Rightarrow> ('p, 'x, 'c) clause list \<Rightarrow> ('p, 'c) dl_fact list \<Rightarrow> ('p, 'c) dl_fact list" where
  "dl_step U Pl facts = remdups (facts @ concat (map (\<lambda>cl. fireable_heads U cl facts) Pl))"

text \<open>Every fact any clause could ever produce (the body/guard filter dropped) --- the finite upper
  bound that makes the fixpoint loop terminate.\<close>
definition all_head_facts ::
  "'c list \<Rightarrow> ('p, 'x, 'c) clause list \<Rightarrow> ('p, 'c) dl_fact list" where
  "all_head_facts U Pl =
     remdups (concat (map (\<lambda>cl. map (\<lambda>\<sigma>. subst_atom \<sigma> (the_lh cl)) (cls_substs U cl)) Pl))"

declare fireable_heads_def [code] dl_step_def [code] all_head_facts_def [code]

subsection \<open>A round only depends on the fact \<^emph>\<open>set\<close>\<close>

text \<open>Needed to relate the loop below to any refinement of \<^const>\<open>dl_step\<close> that permutes or
  re-duplicates the carried list.\<close>
lemma fireable_heads_cong:
  assumes "set facts = set facts'"
  shows "set (fireable_heads U cl facts) = set (fireable_heads U cl facts')"
  unfolding fireable_heads_def using assms by simp

lemma dl_step_cong:
  assumes "set facts = set facts'"
  shows "set (dl_step U Pl facts) = set (dl_step U Pl facts')"
  unfolding dl_step_def by (simp add: assms fireable_heads_cong[OF assms])

subsection \<open>Facts about a single round needed for termination\<close>

text \<open>One round only ever adds facts.\<close>
lemma dl_step_mono: "set facts \<subseteq> set (dl_step U Pl facts)"
  unfolding dl_step_def by auto

text \<open>The facts after one round are exactly the old ones plus every clause's fireable heads.\<close>
lemma dl_step_set:
  "set (dl_step U Pl facts) = set facts \<union> (\<Union>cl \<in> set Pl. set (fireable_heads U cl facts))"
  unfolding dl_step_def by auto

text \<open>Every head a clause can fire is one of the program's potential head-facts.\<close>
lemma fireable_heads_subset_all_head_facts:
  assumes "cl \<in> set Pl"
  shows "set (fireable_heads U cl facts) \<subseteq> set (all_head_facts U Pl)"
proof
  fix f assume "f \<in> set (fireable_heads U cl facts)"
  then obtain \<sigma> where \<sigma>: "\<sigma> \<in> set (cls_substs U cl)"
    and feq: "f = subst_atom \<sigma> (the_lh cl)"
    unfolding fireable_heads_def by auto
  have "f \<in> set (map (\<lambda>\<sigma>. subst_atom \<sigma> (the_lh cl)) (cls_substs U cl))"
    using \<sigma> feq by simp
  thus "f \<in> set (all_head_facts U Pl)"
    using assms unfolding all_head_facts_def by auto
qed

text \<open>Hence one round stays within the finite upper bound \<^const>\<open>all_head_facts\<close> (modulo the seed).\<close>
lemma dl_step_subset_all_head_facts:
  "set (dl_step U Pl facts) \<subseteq> set facts \<union> set (all_head_facts U Pl)"
proof
  fix f assume "f \<in> set (dl_step U Pl facts)"
  hence "f \<in> set facts \<or> (\<exists>cl \<in> set Pl. f \<in> set (fireable_heads U cl facts))"
    using dl_step_set by blast
  thus "f \<in> set facts \<union> set (all_head_facts U Pl)"
    using fireable_heads_subset_all_head_facts by blast
qed

subsection \<open>The fixpoint loop\<close>

text \<open>The recursion is \<^emph>\<open>not\<close> structural: each call recurses on \<^term>\<open>dl_step U Pl facts\<close>, a
  \<^emph>\<open>larger\<close> fact list. The termination measure is the number of head-facts not yet derived,
  \<^term>\<open>card (set (all_head_facts U Pl) - set facts)\<close>: \<^const>\<open>dl_step\<close> is monotone and every new
  fact lies in the finite \<^const>\<open>all_head_facts\<close>, so it strictly decreases per recursive call.\<close>

text \<open>The measure argument, hoisted out of the \<^theory_text>\<open>termination\<close> proof so that any refinement of
  \<^const>\<open>dl_step\<close> computing the same fact set can reuse it for its own loop.\<close>
lemma dl_step_measure_decreases:
  assumes neq: "set (dl_step U Pl facts) \<noteq> set facts"
  shows "card (set (all_head_facts U Pl) - set (dl_step U Pl facts))
           < card (set (all_head_facts U Pl) - set facts)"
proof -
  have mono: "set facts \<subseteq> set (dl_step U Pl facts)"
    by (rule dl_step_mono)
  have psub_sets: "set facts \<subset> set (dl_step U Pl facts)"
    using mono neq by auto
  obtain x where "x \<in> set (dl_step U Pl facts) - set facts"
    using psubset_imp_ex_mem[OF psub_sets] by blast
  hence x_in: "x \<in> set (dl_step U Pl facts)"
    and x_out: "x \<notin> set facts"
    by auto
  have x_head: "x \<in> set (all_head_facts U Pl)"
    using x_in x_out dl_step_subset_all_head_facts by blast
  have psub: "set (all_head_facts U Pl) - set (dl_step U Pl facts)
                \<subset> set (all_head_facts U Pl) - set facts"
  proof (rule psubsetI)
    show "set (all_head_facts U Pl) - set (dl_step U Pl facts)
            \<subseteq> set (all_head_facts U Pl) - set facts"
      using mono by blast
  next
    show "set (all_head_facts U Pl) - set (dl_step U Pl facts)
            \<noteq> set (all_head_facts U Pl) - set facts"
    proof
      assume eq: "set (all_head_facts U Pl) - set (dl_step U Pl facts)
                    = set (all_head_facts U Pl) - set facts"
      have "x \<in> set (all_head_facts U Pl) - set facts"
        using x_head x_out by blast
      hence "x \<in> set (all_head_facts U Pl) - set (dl_step U Pl facts)"
        using eq by simp
      thus False using x_in by blast
    qed
  qed
  have fin: "finite (set (all_head_facts U Pl) - set facts)"
    by simp
  show ?thesis
    by (rule psubset_card_mono[OF fin psub])
qed

function dl_saturate ::
  "'c list \<Rightarrow> ('p, 'x, 'c) clause list \<Rightarrow> ('p, 'c) dl_fact list \<Rightarrow> ('p, 'c) dl_fact list" where
  "dl_saturate U Pl facts =
     (if set (dl_step U Pl facts) = set facts
      then facts
      else dl_saturate U Pl (dl_step U Pl facts))"
  by pat_completeness auto

termination dl_saturate
proof (relation "measure (\<lambda>(U, Pl, facts). card (set (all_head_facts U Pl) - set facts))")
  show "wf (measure (\<lambda>(U, Pl, facts). card (set (all_head_facts U Pl) - set facts)))"
    by simp
next
  fix U Pl facts
  assume "set (dl_step U Pl facts) \<noteq> set facts"
  thus "((U, Pl, dl_step U Pl facts), (U, Pl, facts))
          \<in> measure (\<lambda>(U, Pl, facts). card (set (all_head_facts U Pl) - set facts))"
    using dl_step_measure_decreases by simp
qed

text \<open>Keep the recursive equation out of the default simp set (it would loop) and expose it as a
  one-step unfolding rule plus a code equation.\<close>
declare dl_saturate.simps [simp del, code]

lemma dl_saturate_unfold:
  "dl_saturate U Pl facts =
     (if set (dl_step U Pl facts) = set facts then facts else dl_saturate U Pl (dl_step U Pl facts))"
  by (rule dl_saturate.simps)

text \<open>The seeded entry point: saturate from no facts. (Ground clauses --- empty body --- fire in the
  first round, so no separate EDB seed is needed.)\<close>
definition dl_eval :: "'c list \<Rightarrow> ('p, 'x, 'c) clause list \<Rightarrow> ('p, 'c) dl_fact list" where
  "dl_eval U Pl = dl_saturate U Pl []"

declare dl_eval_def [code]

subsection \<open>The loop really does stop at a fixpoint (cheap)\<close>

text \<open>Immediate from the loop's own exit test; this is the only "fixpoint" statement proved here.
  It says nothing about the result being the \<^emph>\<open>least\<close> model --- see the header.\<close>
lemma dl_saturate_is_fixpoint:
  "set (dl_step U Pl (dl_saturate U Pl facts)) = set (dl_saturate U Pl facts)"
proof (induction U Pl facts rule: dl_saturate.induct)
  case (1 U Pl facts)
  show ?case
  proof (cases "set (dl_step U Pl facts) = set facts")
    case True
    thus ?thesis using dl_saturate_unfold[of U Pl facts] by simp
  next
    case False
    thus ?thesis using "1.IH" dl_saturate_unfold[of U Pl facts] by simp
  qed
qed

subsection \<open>Soundness: every returned fact is derivable\<close>

text \<open>A single round preserves derivability: each new head is the instance of a program clause over
  \<open>U\<close> whose guards hold and whose body atoms are derivable.\<close>
lemma dl_step_sound:
  assumes IH: "\<And>g. g \<in> set facts \<Longrightarrow> datalog_prog.derivable (set U) (set Pl) g"
      and f: "f \<in> set (dl_step U Pl facts)"
  shows "datalog_prog.derivable (set U) (set Pl) f"
proof -
  have "f \<in> set facts \<or> f \<in> set (concat (map (\<lambda>cl. fireable_heads U cl facts) Pl))"
    using f unfolding dl_step_def by auto
  thus ?thesis
  proof
    assume "f \<in> set facts" thus ?thesis using IH by blast
  next
    assume "f \<in> set (concat (map (\<lambda>cl. fireable_heads U cl facts) Pl))"
    then obtain cl where cl: "cl \<in> set Pl" and fcl: "f \<in> set (fireable_heads U cl facts)"
      by auto
    obtain \<sigma> where \<sigma>: "\<sigma> \<in> set (cls_substs U cl)"
      and guards: "\<forall>g \<in> set (cls_guards cl). eval_guard \<sigma> g"
      and body: "\<forall>a \<in> set (cls_body_atoms cl). subst_atom \<sigma> a \<in> set facts"
      and feq: "f = subst_atom \<sigma> (the_lh cl)"
      using fcl unfolding fireable_heads_def by auto
    have rng: "\<forall>x \<in> set (cls_vars cl). \<sigma> x \<in> set U"
      using \<sigma> by (blast intro: cls_substs_rangeD)
    have bder: "\<forall>a \<in> set (cls_body_atoms cl). datalog_prog.derivable (set U) (set Pl) (subst_atom \<sigma> a)"
      using body IH by blast
    show ?thesis
      using datalog_prog.derivable.derive[OF cl rng guards bder] feq by simp
  qed
qed

theorem dl_saturate_sound:
  assumes "\<And>g. g \<in> set facts \<Longrightarrow> datalog_prog.derivable (set U) (set Pl) g"
      and "f \<in> set (dl_saturate U Pl facts)"
  shows "datalog_prog.derivable (set U) (set Pl) f"
  using assms
proof (induction U Pl facts rule: dl_saturate.induct)
  case (1 U Pl facts)
  show ?case
  proof (cases "set (dl_step U Pl facts) = set facts")
    case True
    thus ?thesis using "1.prems" dl_saturate_unfold[of U Pl facts] by simp
  next
    case False
    have step: "datalog_prog.derivable (set U) (set Pl) g" if "g \<in> set (dl_step U Pl facts)" for g
      using "1.prems"(1) that by (blast intro: dl_step_sound)
    have "f \<in> set (dl_saturate U Pl (dl_step U Pl facts))"
      using "1.prems"(2) False dl_saturate_unfold[of U Pl facts] by simp
    thus ?thesis using "1.IH"[OF False step] by blast
  qed
qed

theorem dl_eval_sound:
  assumes "f \<in> set (dl_eval U Pl)"
  shows "datalog_prog.derivable (set U) (set Pl) f"
proof -
  have base: "datalog_prog.derivable (set U) (set Pl) g" if "g \<in> set []" for g
    using that by simp
  show ?thesis
    using dl_saturate_sound[OF base] assms unfolding dl_eval_def by blast
qed

end
