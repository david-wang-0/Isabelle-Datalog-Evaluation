theory Datalog_Semantics
  imports Stratified_Datalog.Datalog
begin

section \<open>Semantic supplement to the AFP \<open>Stratified_Datalog\<close> entry\<close>

text \<open>Two layers, both phrased over the datatypes of the AFP \<open>Stratified_Datalog\<close> entry
  \<^cite>\<open>datalogIsabelle\<close> (a program is a
  \<^typ>\<open>('p, 'x, 'c) dl_program\<close>, i.e.\ a clause \<^emph>\<open>set\<close>): first \<^emph>\<open>positive datalog\<close> and its
  relation to stratified datalog, then the \<^emph>\<open>universe-restricted\<close> reference semantics with the
  locales \<open>datalog_sem\<close>, \<open>positive_datalog\<close>, \<open>datalog_prog\<close>, \<open>datalog_universe\<close> and
  \<open>positive_datalog_universe\<close>.

  This theory is the \<^emph>\<open>specification\<close> side of the repository: the inductive
  \<open>datalog_prog.derivable\<close> defined here is what the executable fixpoint evaluator of
  \<open>Datalog_Fixpoint\<close> is proven sound against.\<close>

section \<open>Positive datalog and its relation to stratified datalog\<close>

text \<open>The \<^emph>\<open>positive\<close> fragment of the AFP clause language: programs whose clause bodies contain no
  \<^const>\<open>NegLit\<close>. This is the syntactic restriction under which the consequence operator is
  monotone, and --- as shown here --- a degenerate case of \<^emph>\<open>stratified\<close> datalog: a positive
  program is well-stratified at the trivial stratification \<open>\<lambda>_. 0\<close>, where the AFP stratum ordering
  collapses to pointwise \<open>\<subseteq>\<close>.\<close>

subsection \<open>Positivity of a program\<close>

fun is_pos_rh :: "('p, 'x, 'c) rh \<Rightarrow> bool" where
  "is_pos_rh (NegLit _ _) = False"
| "is_pos_rh _ = True"

definition dl_positive_prog :: "('p, 'x, 'c) dl_program \<Rightarrow> bool" where
  "dl_positive_prog P \<equiv> (\<forall>cl \<in> P. \<forall>rh \<in> set (the_rhs cl). is_pos_rh rh)"

lemma dl_positive_progD:
  assumes "dl_positive_prog P" and "cl \<in> P" and "rh \<in> set (the_rhs cl)"
  shows "is_pos_rh rh"
  using assms unfolding dl_positive_prog_def by blast

subsection \<open>Relation to stratified datalog\<close>

lemma rnk_pos_zero: "is_pos_rh rh \<Longrightarrow> rnk (\<lambda>_. 0) rh = 0"
  by (cases rh) auto

text \<open>At the trivial stratification the stratum ordering is plain pointwise \<open>\<subseteq>\<close>.\<close>
lemma lte_zero_iff: "(\<rho> \<sqsubseteq>(\<lambda>_. 0)\<sqsubseteq> \<rho>') \<longleftrightarrow> (\<forall>p. \<rho> p \<subseteq> \<rho>' p)"
proof
  assume "\<rho> \<sqsubseteq>(\<lambda>_. 0)\<sqsubseteq> \<rho>'"
  thus "\<forall>p. \<rho> p \<subseteq> \<rho>' p"
    unfolding lte_def lt_def by auto
next
  assume sub: "\<forall>p. \<rho> p \<subseteq> \<rho>' p"
  show "\<rho> \<sqsubseteq>(\<lambda>_. 0)\<sqsubseteq> \<rho>'"
  proof (cases "\<rho> = \<rho>'")
    case True
    thus ?thesis unfolding lte_def by simp
  next
    case False
    obtain p where "\<rho> p \<subset> \<rho>' p"
      using sub False by (metis fun_eq_iff psubsetI)
    hence "\<rho> \<sqsubset>(\<lambda>_. 0)\<sqsubset> \<rho>'"
      unfolding lt_def using sub by (auto intro!: exI[of _ p])
    thus ?thesis unfolding lte_def by simp
  qed
qed

lemma least_solution_zero_iff:
  "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl (\<lambda>_. 0) \<longleftrightarrow> \<rho> \<Turnstile>\<^sub>d\<^sub>l dl \<and> (\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l dl \<longrightarrow> (\<forall>p. \<rho> p \<subseteq> \<rho>' p))"
  unfolding least_solution_def by (metis lte_zero_iff)

subsection \<open>The positive datalog locale\<close>

locale positive_datalog =
  fixes P :: "('p, 'x, 'c) dl_program"
  assumes positive: "dl_positive_prog P"
begin

text \<open>\<^bold>\<open>Relation to stratified datalog:\<close> \<open>P\<close> is well-stratified at \<open>\<lambda>_. 0\<close>.\<close>
lemma positive_strat_wf: "strat_wf (\<lambda>_. 0) P"
  unfolding strat_wf_def
proof
  fix c assume c: "c \<in> P"
  obtain p ids rhs where ceq: "c = Cls p ids rhs" by (cases c)
  have "\<forall>rh \<in> set rhs. is_pos_rh rh"
    using dl_positive_progD[OF positive c] unfolding ceq by auto
  hence "\<forall>rh \<in> set rhs. rnk (\<lambda>_. 0) rh = 0"
    using rnk_pos_zero by blast
  thus "strat_wf_cls (\<lambda>_. 0) c"
    unfolding ceq strat_wf_cls.simps by simp
qed

lemmas stratified = positive_strat_wf

lemma least_solution_iff:
  "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t P (\<lambda>_. 0) \<longleftrightarrow> \<rho> \<Turnstile>\<^sub>d\<^sub>l P \<and> (\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l P \<longrightarrow> (\<forall>p. \<rho> p \<subseteq> \<rho>' p))"
  using least_solution_zero_iff .

end

section \<open>Universe-restricted datalog semantics\<close>

text \<open>The reference least-model semantics of a positive datalog program over a finite constant
  universe \<open>U\<close>. The \<open>datalog_sem\<close> locale fixes \<open>U\<close>; \<open>datalog_prog\<close> adds the program and owns the
  inductive derivability; \<open>datalog_universe\<close> adds the \<open>U\<close>-safety side conditions; and
  \<open>positive_datalog_universe\<close> combines that with \<open>positive_datalog\<close>, so that \<open>U\<close>-restricted
  derivability coincides with the AFP least solution. The list-based grounding
  (\<open>cls_substs\<close>) is the executable layer.\<close>

subsection \<open>Ground facts and substitutions\<close>

type_synonym ('p, 'c) dl_fact = "'p \<times> 'c list"

fun subst_id :: "('x \<Rightarrow> 'c) \<Rightarrow> ('x, 'c) id \<Rightarrow> 'c" where
  "subst_id \<sigma> (id.Var x) = \<sigma> x"
| "subst_id \<sigma> (id.Cst c) = c"

definition subst_atom :: "('x \<Rightarrow> 'c) \<Rightarrow> ('p, 'x, 'c) lh \<Rightarrow> ('p, 'c) dl_fact" where
  "subst_atom \<sigma> a = (fst a, map (subst_id \<sigma>) (snd a))"

fun rh_body_atom :: "('p, 'x, 'c) rh \<Rightarrow> ('p, 'x, 'c) lh option" where
  "rh_body_atom (PosLit p ids) = Some (p, ids)"
| "rh_body_atom _ = None"

definition cls_body_atoms :: "('p, 'x, 'c) clause \<Rightarrow> ('p, 'x, 'c) lh list" where
  "cls_body_atoms cl = List.map_filter rh_body_atom (the_rhs cl)"

fun is_dl_guard :: "('p, 'x, 'c) rh \<Rightarrow> bool" where
  "is_dl_guard (Eql _ _) = True"
| "is_dl_guard (Neql _ _) = True"
| "is_dl_guard _ = False"

definition cls_guards :: "('p, 'x, 'c) clause \<Rightarrow> ('p, 'x, 'c) rh list" where
  "cls_guards cl = filter is_dl_guard (the_rhs cl)"

fun eval_guard :: "('x \<Rightarrow> 'c) \<Rightarrow> ('p, 'x, 'c) rh \<Rightarrow> bool" where
  "eval_guard \<sigma> (Eql a b) = (subst_id \<sigma> a = subst_id \<sigma> b)"
| "eval_guard \<sigma> (Neql a b) = (subst_id \<sigma> a \<noteq> subst_id \<sigma> b)"
| "eval_guard \<sigma> _ = True"

fun id_vars_list :: "('x, 'c) id \<Rightarrow> 'x list" where
  "id_vars_list (id.Var x) = [x]"
| "id_vars_list (id.Cst _) = []"

fun rh_vars_list :: "('p, 'x, 'c) rh \<Rightarrow> 'x list" where
  "rh_vars_list (Eql a b) = id_vars_list a @ id_vars_list b"
| "rh_vars_list (Neql a b) = id_vars_list a @ id_vars_list b"
| "rh_vars_list (PosLit _ ids) = concat (map id_vars_list ids)"
| "rh_vars_list (NegLit _ ids) = concat (map id_vars_list ids)"

fun cls_vars :: "('p, 'x, 'c) clause \<Rightarrow> 'x list" where
  "cls_vars (Cls _ ids rhs) = remdups (concat (map id_vars_list ids) @ concat (map rh_vars_list rhs))"

definition subst_of :: "'x list \<Rightarrow> 'c list \<Rightarrow> 'x \<Rightarrow> 'c" where
  "subst_of vs args x = the (map_of (zip vs args) x)"

text \<open>The grounding substitutions of a clause over a finite constant universe \<open>U\<close>: one for every
  assignment of the clause's variables to constants from \<open>U\<close>. This is the \<^emph>\<open>naive\<close>
  \<open>|U|\<^sup>#\<^sup>v\<^sup>a\<^sup>r\<^sup>s\<close> enumeration --- it is the reference against which the fact-driven joins of
  \<open>Datalog_Indexed_Join\<close> are proved equivalent, and is used in the
  executable path only for the (non-datalog) \<^emph>\<open>unsafe\<close> clauses.\<close>
definition cls_substs :: "'c list \<Rightarrow> ('p, 'x, 'c) clause \<Rightarrow> ('x \<Rightarrow> 'c) list" where
  "cls_substs U cl = map (subst_of (cls_vars cl)) (List.n_lists (length (cls_vars cl)) U)"

subsection \<open>Side conditions tying \<open>P\<close>, \<open>U\<close> and the AFP semantics together\<close>

text \<open>The equivalence with the AFP semantics needs three side conditions:
\<^item> \<^bold>\<open>positivity\<close> (\<^const>\<open>dl_positive_prog\<close>): \<open>derivable\<close> silently ignores \<^const>\<open>NegLit\<close>s
  (they are neither guards nor body atoms), while the AFP semantics constrains them.
\<^item> \<^bold>\<open>safety\<close> (\<open>dl_safe\<close>): every clause variable occurs in a positive body atom. The AFP
  \<^const>\<open>solves_cls\<close> quantifies over \<^emph>\<open>all\<close> valuations \<open>'x \<Rightarrow> 'c\<close>, whereas \<open>derivable\<close> only
  instantiates variables from \<open>U\<close>; safety pins every variable to a derivable fact. It is also
  exactly the condition under which the fact-driven join is complete.
\<^item> \<^bold>\<open>head-constant coverage\<close> (\<open>dl_heads_covered\<close>): constants in clause heads lie in \<open>U\<close>.\<close>

fun id_consts_list :: "('x, 'c) id \<Rightarrow> 'c list" where
  "id_consts_list (id.Var _) = []"
| "id_consts_list (id.Cst c) = [c]"

definition dl_heads_covered :: "'c set \<Rightarrow> ('p, 'x, 'c) dl_program \<Rightarrow> bool" where
  "dl_heads_covered U P \<equiv>
     \<forall>cl \<in> P. \<forall>i \<in> set (snd (the_lh cl)). set (id_consts_list i) \<subseteq> U"

lemma dl_heads_coveredD:
  assumes "dl_heads_covered U P" and "cl \<in> P" and "i \<in> set (snd (the_lh cl))"
  shows "set (id_consts_list i) \<subseteq> U"
  using assms unfolding dl_heads_covered_def by blast

definition dl_safe :: "('p, 'x, 'c) dl_program \<Rightarrow> bool" where
  "dl_safe P \<equiv>
     \<forall>cl \<in> P. \<forall>x \<in> set (cls_vars cl).
       \<exists>a \<in> set (cls_body_atoms cl). x \<in> set (concat (map id_vars_list (snd a)))"

lemma dl_safeD:
  assumes "dl_safe P" and "cl \<in> P" and "x \<in> set (cls_vars cl)"
  shows "\<exists>a \<in> set (cls_body_atoms cl). x \<in> set (concat (map id_vars_list (snd a)))"
  using assms unfolding dl_safe_def by blast

subsection \<open>Bridging lemmas to the AFP evaluation functions\<close>

lemma subst_id_eval_id: "subst_id \<sigma> = (\<lambda>i. \<lbrakk>i\<rbrakk>\<^sub>i\<^sub>d \<sigma>)"
proof (rule ext)
  fix i show "subst_id \<sigma> i = \<lbrakk>i\<rbrakk>\<^sub>i\<^sub>d \<sigma>" by (cases i) simp_all
qed

lemma rh_body_atom_Some: "rh_body_atom rh = Some a \<longleftrightarrow> rh = PosLit (fst a) (snd a)"
  by (cases rh; cases a) auto

lemma set_map_filter': "set (List.map_filter f xs) = {y. \<exists>x \<in> set xs. f x = Some y}"
  by (induction xs) (auto simp: List.map_filter_simps split: option.splits)

lemma cls_body_atoms_iff:
  "a \<in> set (cls_body_atoms cl) \<longleftrightarrow> PosLit (fst a) (snd a) \<in> set (the_rhs cl)"
  unfolding cls_body_atoms_def set_map_filter' by (auto simp: rh_body_atom_Some)

lemma cls_vars_head_vars:
  assumes "i \<in> set (snd (the_lh cl))" and "x \<in> set (id_vars_list i)"
  shows "x \<in> set (cls_vars cl)"
  using assms by (cases cl) auto

lemma cls_vars_rhs_vars:
  assumes "rh \<in> set (the_rhs cl)" and "x \<in> set (rh_vars_list rh)"
  shows "x \<in> set (cls_vars cl)"
  using assms by (cases cl) auto

lemma distinct_cls_vars: "distinct (cls_vars cl)"
  by (cases cl) auto

lemma subst_id_agree:
  assumes "\<forall>x \<in> set (id_vars_list i). \<sigma> x = \<sigma>' x"
  shows "subst_id \<sigma> i = subst_id \<sigma>' i"
  using assms by (cases i) simp_all

lemma subst_atom_agree:
  assumes "\<forall>i \<in> set (snd a). \<forall>x \<in> set (id_vars_list i). \<sigma> x = \<sigma>' x"
  shows "subst_atom \<sigma> a = subst_atom \<sigma>' a"
proof -
  have "map (subst_id \<sigma>) (snd a) = map (subst_id \<sigma>') (snd a)"
    using assms by (intro map_cong[OF refl] subst_id_agree) auto
  thus ?thesis unfolding subst_atom_def by simp
qed

lemma eval_guard_agree:
  assumes "\<forall>x \<in> set (rh_vars_list g). \<sigma> x = \<sigma>' x"
  shows "eval_guard \<sigma> g = eval_guard \<sigma>' g"
proof (cases g)
  case (Eql a b)
  hence "subst_id \<sigma> a = subst_id \<sigma>' a" and "subst_id \<sigma> b = subst_id \<sigma>' b"
    using assms by (auto intro!: subst_id_agree)
  thus ?thesis using Eql by simp
next
  case (Neql a b)
  hence "subst_id \<sigma> a = subst_id \<sigma>' a" and "subst_id \<sigma> b = subst_id \<sigma>' b"
    using assms by (auto intro!: subst_id_agree)
  thus ?thesis using Neql by simp
qed simp_all

text \<open>Agreement on the clause variables transfers head, body-atom and guard instances.\<close>

lemma subst_atom_head_cong:
  assumes "\<forall>x \<in> set (cls_vars cl). \<sigma>' x = \<sigma> x"
  shows "subst_atom \<sigma>' (the_lh cl) = subst_atom \<sigma> (the_lh cl)"
  using assms by (intro subst_atom_agree) (auto dest: cls_vars_head_vars)

lemma subst_atom_body_cong:
  assumes "\<forall>x \<in> set (cls_vars cl). \<sigma>' x = \<sigma> x" and "a \<in> set (cls_body_atoms cl)"
  shows "subst_atom \<sigma>' a = subst_atom \<sigma> a"
proof (intro subst_atom_agree ballI)
  fix i x assume i: "i \<in> set (snd a)" and xi: "x \<in> set (id_vars_list i)"
  have "PosLit (fst a) (snd a) \<in> set (the_rhs cl)"
    using assms(2) cls_body_atoms_iff by blast
  moreover
  have "x \<in> set (rh_vars_list (PosLit (fst a) (snd a)))"
    using i xi by auto
  ultimately
  have "x \<in> set (cls_vars cl)" by (rule cls_vars_rhs_vars)
  thus "\<sigma>' x = \<sigma> x" using assms(1) by blast
qed

lemma eval_guard_cls_cong:
  assumes "\<forall>x \<in> set (cls_vars cl). \<sigma>' x = \<sigma> x" and "g \<in> set (cls_guards cl)"
  shows "eval_guard \<sigma>' g = eval_guard \<sigma> g"
proof (intro eval_guard_agree ballI)
  fix x assume x: "x \<in> set (rh_vars_list g)"
  have "g \<in> set (the_rhs cl)" using assms(2) by (auto simp: cls_guards_def)
  hence "x \<in> set (cls_vars cl)" using x by (rule cls_vars_rhs_vars)
  thus "\<sigma>' x = \<sigma> x" using assms(1) by blast
qed

subsection \<open>Membership in the tabulated grounding\<close>

lemma cls_substs_iff:
  "\<sigma> \<in> set (cls_substs U cl) \<longleftrightarrow>
     (\<exists>cs. \<sigma> = subst_of (cls_vars cl) cs
           \<and> length cs = length (cls_vars cl) \<and> set cs \<subseteq> set U)"
  unfolding cls_substs_def set_map set_n_lists by auto

lemma subst_of_map: "x \<in> set vs \<Longrightarrow> subst_of vs (map f vs) x = f x"
  unfolding subst_of_def map_of_zip_map by simp

lemma subst_of_in_set:
  assumes "length cs = length vs" and "x \<in> set vs"
  shows "subst_of vs cs x \<in> set cs"
proof -
  obtain c where "map_of (zip vs cs) x = Some c"
    using assms by (metis map_of_zip_is_Some)
  thus ?thesis
    unfolding subst_of_def using map_of_SomeD set_zip_rightD by fastforce
qed

lemma cls_substs_rangeD:
  assumes "\<sigma> \<in> set (cls_substs U cl)" and "x \<in> set (cls_vars cl)"
  shows "\<sigma> x \<in> set U"
  using assms subst_of_in_set unfolding cls_substs_iff by fastforce

text \<open>Any \<open>U\<close>-valued substitution agrees on the clause variables with a tabulated one --- the
  bridge from an abstract \<open>\<exists>\<sigma>\<close>/\<open>\<forall>\<sigma>\<close> to the enumerated list.\<close>
lemma cls_substs_tabulate:
  assumes "\<forall>x \<in> set (cls_vars cl). \<sigma> x \<in> set U"
  obtains \<sigma>' where "\<sigma>' \<in> set (cls_substs U cl)"
    and "\<forall>x \<in> set (cls_vars cl). \<sigma>' x = \<sigma> x"
proof -
  let ?\<sigma>' = "subst_of (cls_vars cl) (map \<sigma> (cls_vars cl))"
  have "?\<sigma>' \<in> set (cls_substs U cl)"
    unfolding cls_substs_iff
    using assms by (auto simp: image_subset_iff intro!: exI[where x = "map \<sigma> (cls_vars cl)"])
  moreover
  have "\<forall>x \<in> set (cls_vars cl). ?\<sigma>' x = \<sigma> x"
    by (simp add: subst_of_map)
  ultimately
  show ?thesis using that by blast
qed

subsection \<open>The universe-restricted datalog locale\<close>

text \<open>A fixed (abstract) finite constant universe \<open>U\<close>, as a \<^emph>\<open>set\<close>. The executable evaluator
  instantiates it with \<open>set U_list\<close>.\<close>

locale datalog_sem =
  fixes U :: "'c set"

text \<open>The assumption-free program locale, owning the inductive derivability: a fact is derivable
  iff it is the head of a ground clause instance (each variable assigned a constant from \<open>U\<close>) whose
  guards hold and whose body atoms are derivable. Bodyless clauses are the base case. Because the
  locale carries no assumptions, the exported \<open>derivable.induct\<close> / \<open>derivable.derive\<close> rules carry no
  side conditions and can be used by the (assumption-free) executable evaluator.\<close>

locale datalog_prog = datalog_sem U for U :: "'c set" +
  fixes P :: "('p, 'x, 'c) dl_program"
begin

inductive derivable :: "('p, 'c) dl_fact \<Rightarrow> bool" where
  derive: "\<lbrakk> cl \<in> P; \<forall>x \<in> set (cls_vars cl). \<sigma> x \<in> U;
             \<forall>g \<in> set (cls_guards cl). eval_guard \<sigma> g;
             \<forall>a \<in> set (cls_body_atoms cl). derivable (subst_atom \<sigma> a) \<rbrakk>
           \<Longrightarrow> derivable (subst_atom \<sigma> (the_lh cl))"

end

text \<open>\<^emph>\<open>Datalog universe\<close>: \<^locale>\<open>datalog_prog\<close> plus the side conditions that \<open>P\<close> is \<^emph>\<open>safe\<close> and
  \<^emph>\<open>head-covered\<close>. No positivity is assumed, so this isolates the facts that follow from the
  universe side conditions alone.\<close>

locale datalog_universe = datalog_prog U P
  for U :: "'c set" and P :: "('p, 'x, 'c) dl_program" +
  assumes safe:    "dl_safe P"
      and covered: "dl_heads_covered U P"
begin

text \<open>Derivable facts mention only universe constants.\<close>
lemma derivable_consts: "derivable f \<Longrightarrow> set (snd f) \<subseteq> U"
proof (induction rule: derivable.induct)
  case (derive cl \<sigma>)
  have "subst_id \<sigma> i \<in> U" if i: "i \<in> set (snd (the_lh cl))" for i
  proof (cases i)
    case (Var x)
    hence "x \<in> set (cls_vars cl)"
      using i cls_vars_head_vars by fastforce
    hence "\<sigma> x \<in> U" using derive.hyps(2) by blast
    thus ?thesis using Var by simp
  next
    case (Cst c)
    thus ?thesis
      using dl_heads_coveredD[OF covered derive.hyps(1) i] by fastforce
  qed
  thus ?case unfolding subst_atom_def by auto
qed

text \<open>\<^bold>\<open>Safety pins variables to the universe\<close>: if every body atom of a clause has a derivable
  instance under \<open>\<sigma>\<close>, then \<open>\<sigma>\<close> maps every clause variable into \<open>U\<close>.\<close>
lemma subst_cond_of_body_derivable:
  assumes cl: "cl \<in> P"
    and bd: "\<And>a. a \<in> set (cls_body_atoms cl) \<Longrightarrow> derivable (subst_atom \<sigma> a)"
    and x: "x \<in> set (cls_vars cl)"
  shows "\<sigma> x \<in> U"
proof -
  obtain a where a: "a \<in> set (cls_body_atoms cl)"
    and xa: "x \<in> set (concat (map id_vars_list (snd a)))"
    using dl_safeD[OF safe cl x] by blast
  obtain i where i: "i \<in> set (snd a)" and xi: "x \<in> set (id_vars_list i)"
    using xa by auto
  have i_eq: "i = id.Var x" using xi by (cases i) auto
  have "set (snd (subst_atom \<sigma> a)) \<subseteq> U"
    using derivable_consts[OF bd[OF a]] by simp
  moreover
  have "\<sigma> x \<in> set (snd (subst_atom \<sigma> a))"
    using i i_eq unfolding subst_atom_def by force
  ultimately
  show "\<sigma> x \<in> U" by blast
qed

text \<open>\<^bold>\<open>Completeness core\<close>: the derivable facts form an AFP solution of \<open>P\<close>.\<close>
lemma derivable_solves: "(\<lambda>q. {r. derivable (q, r)}) \<Turnstile>\<^sub>d\<^sub>l P"
    (is "?D \<Turnstile>\<^sub>d\<^sub>l _")
  unfolding solves_program_def solves_cls_def
proof (intro ballI allI)
  fix cl \<sigma>
  assume cl: "cl \<in> P"
  obtain q ids rhs where cl_eq: "cl = Cls q ids rhs" by (cases cl)
  have main: "\<lbrakk>(q, ids)\<rbrakk>\<^sub>l\<^sub>h ?D \<sigma>" if body: "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s ?D \<sigma>"
  proof -
    have body_der: "derivable (subst_atom \<sigma> a)" if a: "a \<in> set (cls_body_atoms cl)" for a
    proof -
      have "PosLit (fst a) (snd a) \<in> set rhs"
        using a cls_body_atoms_iff[of a cl] cl_eq by simp
      hence "\<lbrakk>\<^bold>+ (fst a) (snd a)\<rbrakk>\<^sub>r\<^sub>h ?D \<sigma>" using body by fastforce
      thus ?thesis by (simp add: subst_atom_def subst_id_eval_id)
    qed
    have body': "\<forall>a \<in> set (cls_body_atoms cl). derivable (subst_atom \<sigma> a)"
      using body_der by blast
    have subst_cond: "\<forall>x \<in> set (cls_vars cl). \<sigma> x \<in> U"
      using subst_cond_of_body_derivable[OF cl] body_der by blast
    have guards: "\<forall>g \<in> set (cls_guards cl). eval_guard \<sigma> g"
    proof
      fix g assume g: "g \<in> set (cls_guards cl)"
      hence g_rhs: "g \<in> set rhs" using cl_eq unfolding cls_guards_def by simp
      show "eval_guard \<sigma> g"
      proof (cases g)
        case (Eql a b)
        thus ?thesis using body g_rhs by (fastforce simp: subst_id_eval_id)
      next
        case (Neql a b)
        thus ?thesis using body g_rhs by (fastforce simp: subst_id_eval_id)
      qed simp_all
    qed
    have "derivable (subst_atom \<sigma> (the_lh cl))"
      using derivable.derive[OF cl subst_cond guards body'] by blast
    thus ?thesis
      using cl_eq by (simp add: subst_atom_def subst_id_eval_id)
  qed
  thus "\<lbrakk>cl\<rbrakk>\<^sub>c\<^sub>l\<^sub>s ?D \<sigma>"
    unfolding cl_eq meaning_cls.simps by blast
qed

end

subsection \<open>Positive datalog over a universe (the combined locale)\<close>

locale positive_datalog_universe = datalog_universe U P + positive_datalog P
  for U :: "'c set" and P :: "('p, 'x, 'c) dl_program"
begin

text \<open>\<^bold>\<open>Soundness\<close>: every derivable fact is in every AFP solution of \<open>P\<close>.\<close>
lemma derivable_in_solution:
  assumes sol: "\<rho> \<Turnstile>\<^sub>d\<^sub>l P" and der: "derivable f"
  shows "snd f \<in> \<rho> (fst f)"
  using der
proof (induction rule: derivable.induct)
  case (derive cl \<sigma>)
  obtain q ids rhs where cl_eq: "cl = Cls q ids rhs" by (cases cl)
  have "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>" if rh: "rh \<in> set rhs" for rh
  proof (cases rh)
    case (Eql a b)
    hence "rh \<in> set (cls_guards cl)"
      using rh cl_eq unfolding cls_guards_def by simp
    hence "eval_guard \<sigma> rh" using derive.hyps(3) by blast
    thus ?thesis using Eql by (simp add: subst_id_eval_id)
  next
    case (Neql a b)
    hence "rh \<in> set (cls_guards cl)"
      using rh cl_eq unfolding cls_guards_def by simp
    hence "eval_guard \<sigma> rh" using derive.hyps(3) by blast
    thus ?thesis using Neql by (simp add: subst_id_eval_id)
  next
    case (PosLit p' ids')
    hence "(p', ids') \<in> set (cls_body_atoms cl)"
      using rh cl_eq cls_body_atoms_iff by fastforce
    hence "snd (subst_atom \<sigma> (p', ids')) \<in> \<rho> (fst (subst_atom \<sigma> (p', ids')))"
      using derive.IH by blast
    thus ?thesis
      using PosLit by (simp add: subst_atom_def subst_id_eval_id)
  next
    case (NegLit p' ids')
    hence False
      using dl_positive_progD[OF positive derive.hyps(1)] rh cl_eq by fastforce
    thus ?thesis ..
  qed
  hence rhs_sat: "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>" by simp
  have "\<lbrakk>cl\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>"
    using sol derive.hyps(1) unfolding solves_program_def solves_cls_def by blast
  hence "\<lbrakk>(q, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
    using rhs_sat unfolding cl_eq meaning_cls.simps by blast
  thus ?case using cl_eq by (simp add: subst_atom_def subst_id_eval_id)
qed

text \<open>\<^bold>\<open>The equivalence\<close>: \<open>derivable\<close> coincides with the (rank-0) least solution of \<open>P\<close>.\<close>
lemma derivable_iff_least_solution:
  assumes lst: "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t P (\<lambda>_. 0)"
  shows "derivable (p, r) \<longleftrightarrow> r \<in> \<rho> p"
proof
  assume "derivable (p, r)"
  moreover
  have "\<rho> \<Turnstile>\<^sub>d\<^sub>l P"
    using lst unfolding least_solution_def by blast
  ultimately
  show "r \<in> \<rho> p"
    using derivable_in_solution by fastforce
next
  assume r: "r \<in> \<rho> p"
  have D_sol: "(\<lambda>q. {r. derivable (q, r)}) \<Turnstile>\<^sub>d\<^sub>l P"
    using derivable_solves .
  hence "lte \<rho> (\<lambda>_. 0) (\<lambda>q. {r. derivable (q, r)})"
    using lst unfolding least_solution_def by blast
  hence "\<rho> p \<subseteq> {r. derivable (p, r)}"
    unfolding lte_def lt_def by auto
  thus "derivable (p, r)" using r by blast
qed

end

end
