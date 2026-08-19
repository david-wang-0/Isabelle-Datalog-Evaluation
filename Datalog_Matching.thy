theory Datalog_Matching
  imports Datalog_Fixpoint
begin

section \<open>Refinement 1: assoc-list matching and the fact-driven body join\<close>

text \<open>The first refinement away from the naive \<^const>\<open>cls_substs\<close> enumeration of
  \<^theory>\<open>Datalog_Evaluation.Datalog_Fixpoint\<close>. Instead of generating all \<open>|U|\<^sup>#\<^sup>v\<^sup>a\<^sup>r\<^sup>s\<close> substitutions
  and testing each body atom against the fact set, we go \<^emph>\<open>fact-driven\<close>: match the body atoms
  against the facts one after another, threading the bindings discovered so far as an association
  list. Its cost is proportional to the number of \<^emph>\<open>matching\<close> tuples, not to \<open>|U|\<^sup>k\<close>.

  No \<^typ>\<open>'x \<Rightarrow> 'c\<close> function is built or applied on the executable path --- only \<^const>\<open>map_of\<close>
  look-ups; the function \<open>\<lambda>x. the (map_of al x)\<close> appears exclusively inside proofs, as the witness
  relating an assoc list back to the abstract \<open>\<sigma>\<close>.

  \<^bold>\<open>This layer is still index-free\<close>: \<open>match_facts_al\<close> scans the whole fact list for each
  atom. \<open>Datalog_Indexed_Join\<close> replaces that scan by an RBT index
  look-up.\<close>

subsection \<open>Reading a substitution off a fact, positionally\<close>

fun match_id_al :: "('x \<times> 'c) list \<Rightarrow> ('x, 'c) id \<Rightarrow> 'c \<Rightarrow> ('x \<times> 'c) list option" where
  "match_id_al al (id.Cst c) d = (if c = d then Some al else None)"
| "match_id_al al (id.Var x) d =
     (case map_of al x of Some c \<Rightarrow> (if c = d then Some al else None) | None \<Rightarrow> Some ((x, d) # al))"

fun match_ids_al :: "('x \<times> 'c) list \<Rightarrow> ('x, 'c) id list \<Rightarrow> 'c list \<Rightarrow> ('x \<times> 'c) list option" where
  "match_ids_al al [] [] = Some al"
| "match_ids_al al (i # is') (d # ds) =
     (case match_id_al al i d of Some al' \<Rightarrow> match_ids_al al' is' ds | None \<Rightarrow> None)"
| "match_ids_al al _ _ = None"

definition match_atom_al ::
    "('x \<times> 'c) list \<Rightarrow> ('p, 'x, 'c) lh \<Rightarrow> ('p, 'c) dl_fact \<Rightarrow> ('x \<times> 'c) list option" where
  "match_atom_al al a f = (if fst a = fst f then match_ids_al al (snd a) (snd f) else None)"

fun subst_id_al :: "('x \<times> 'c) list \<Rightarrow> ('x, 'c) id \<Rightarrow> 'c" where
  "subst_id_al al (id.Cst c) = c"
| "subst_id_al al (id.Var x) = the (map_of al x)"

fun eval_guard_al :: "('x \<times> 'c) list \<Rightarrow> ('p, 'x, 'c) rh \<Rightarrow> bool" where
  "eval_guard_al al (Eql a b) = (subst_id_al al a = subst_id_al al b)"
| "eval_guard_al al (Neql a b) = (subst_id_al al a \<noteq> subst_id_al al b)"
| "eval_guard_al al _ = True"

subsection \<open>The body join\<close>

definition match_facts_al ::
    "('x \<times> 'c) list \<Rightarrow> ('p, 'x, 'c) lh \<Rightarrow> ('p, 'c) dl_fact list \<Rightarrow> ('x \<times> 'c) list list" where
  "match_facts_al al a facts = List.map_filter (match_atom_al al a) facts"

text \<open>The join itself: a left-deep nested loop over the body atoms, each level extending the
  bindings of the level above. Every branch that survives to the empty atom list is one solution of
  the body.\<close>
fun body_join ::
    "('x \<times> 'c) list \<Rightarrow> ('p, 'x, 'c) lh list \<Rightarrow> ('p, 'c) dl_fact list \<Rightarrow> ('x \<times> 'c) list list" where
  "body_join al [] facts = [al]"
| "body_join al (a # as') facts =
     concat (map (\<lambda>al'. body_join al' as' facts) (match_facts_al al a facts))"

text \<open>A clause is \<^emph>\<open>safe\<close> (executable form of \<^const>\<open>dl_safe\<close>) when every variable occurs in a
  positive body atom. Exactly for safe clauses is the join \<^emph>\<open>complete\<close>: it binds every variable, so
  no separate enumeration over \<open>U\<close> is needed. Unsafe clauses --- outside datalog proper --- must
  fall back to \<^const>\<open>cls_substs\<close>.\<close>
definition clause_safe_exec :: "('p, 'x, 'c) clause \<Rightarrow> bool" where
  "clause_safe_exec cl =
     list_all (\<lambda>x. list_ex (\<lambda>a. x \<in> set (concat (map id_vars_list (snd a)))) (cls_body_atoms cl))
              (cls_vars cl)"

lemma clause_safe_exec_iff:
  "clause_safe_exec cl \<longleftrightarrow>
     (\<forall>x \<in> set (cls_vars cl).
        \<exists>a \<in> set (cls_body_atoms cl). x \<in> set (concat (map id_vars_list (snd a))))"
  unfolding clause_safe_exec_def by (simp add: list_all_iff list_ex_iff)

declare match_facts_al_def [code] body_join.simps [code] clause_safe_exec_def [code]

subsection \<open>The assoc-list evaluators coincide with the \<open>\<sigma>\<close>-function ones\<close>

lemma subst_id_al_eq: "subst_id_al al i = subst_id (\<lambda>x. the (map_of al x)) i"
  by (cases i) auto

lemma eval_guard_al_eq: "eval_guard_al al g = eval_guard (\<lambda>x. the (map_of al x)) g"
  by (cases g) (auto simp: subst_id_al_eq)

subsection \<open>Soundness of matching: a match reproduces the fact\<close>

text \<open>Matching only ever \<^emph>\<open>extends\<close> the bindings (\<^const>\<open>map_of\<close>-monotone), and a matched id/atom
  is reproduced by the resulting bindings.\<close>

lemma match_id_al_mono:
  "match_id_al al i d = Some al' \<Longrightarrow> map_of al \<subseteq>\<^sub>m map_of al'"
  by (cases i) (auto simp: map_le_def split: option.splits if_splits)

lemma match_id_al_correct:
  "match_id_al al i d = Some al'
     \<Longrightarrow> subst_id (\<lambda>x. the (map_of al' x)) i = d \<and> (\<forall>x. i = id.Var x \<longrightarrow> map_of al' x \<noteq> None)"
  by (cases i) (auto split: option.splits if_splits)

lemma match_ids_al_spec:
  "match_ids_al al ids ds = Some al'
     \<Longrightarrow> map_of al \<subseteq>\<^sub>m map_of al'
       \<and> (\<forall>x \<in> set (concat (map id_vars_list ids)). map_of al' x \<noteq> None)
       \<and> map (subst_id (\<lambda>x. the (map_of al' x))) ids = ds"
proof (induction al ids ds arbitrary: al' rule: match_ids_al.induct)
  case (2 al i is' d ds)
  obtain al2 where a2: "match_id_al al i d = Some al2"
    and rest: "match_ids_al al2 is' ds = Some al'"
    using "2.prems" by (auto split: option.splits)
  have le2: "map_of al2 \<subseteq>\<^sub>m map_of al'"
    and bndT: "\<forall>x \<in> set (concat (map id_vars_list is')). map_of al' x \<noteq> None"
    and repT: "map (subst_id (\<lambda>x. the (map_of al' x))) is' = ds"
    using "2.IH"[OF a2 rest] by auto
  have le: "map_of al \<subseteq>\<^sub>m map_of al'"
    using match_id_al_mono[OF a2] le2 by (rule map_le_trans)
  have drep2: "subst_id (\<lambda>x. the (map_of al2 x)) i = d"
    and bnd2: "\<forall>x. i = id.Var x \<longrightarrow> map_of al2 x \<noteq> None"
    using match_id_al_correct[OF a2] by auto
  have agree_i: "the (map_of al' x) = the (map_of al2 x)" if "x \<in> set (id_vars_list i)" for x
    using that bnd2 le2 by (cases i) (auto simp: map_le_def dom_def)
  have headbnd: "\<forall>x \<in> set (id_vars_list i). map_of al' x \<noteq> None"
    using bnd2 le2 by (cases i) (auto simp: map_le_def dom_def)
  have drep: "subst_id (\<lambda>x. the (map_of al' x)) i = d"
    using drep2 agree_i by (cases i) auto
  have bnd: "\<forall>x \<in> set (concat (map id_vars_list (i # is'))). map_of al' x \<noteq> None"
    using headbnd bndT by auto
  show ?case using le drep repT bnd by simp
qed (auto simp: map_le_def)

lemma match_atom_al_spec:
  "match_atom_al al a f = Some al'
     \<Longrightarrow> map_of al \<subseteq>\<^sub>m map_of al'
       \<and> (\<forall>x \<in> set (concat (map id_vars_list (snd a))). map_of al' x \<noteq> None)
       \<and> subst_atom (\<lambda>x. the (map_of al' x)) a = f"
  using match_ids_al_spec[of al "snd a" "snd f"]
  by (auto simp: match_atom_al_def subst_atom_def split: if_splits)

text \<open>The join only extends the bindings it is seeded with.\<close>
lemma body_join_extends:
  assumes "al \<in> set (body_join al0 atoms facts)"
  shows "map_of al0 \<subseteq>\<^sub>m map_of al"
  using assms
proof (induction atoms arbitrary: al0)
  case Nil
  thus ?case by simp
next
  case (Cons a atoms)
  obtain al1 where al1: "al1 \<in> set (match_facts_al al0 a facts)"
    and alin: "al \<in> set (body_join al1 atoms facts)"
    using Cons.prems by auto
  obtain f where m: "match_atom_al al0 a f = Some al1"
    using al1 by (auto simp: match_facts_al_def set_map_filter')
  have "map_of al0 \<subseteq>\<^sub>m map_of al1" using match_atom_al_spec[OF m] by simp
  thus ?case using Cons.IH[OF alin] by (rule map_le_trans)
qed

text \<open>Hence: every assoc list the join returns instantiates all body atoms into the facts.\<close>
lemma body_join_sound:
  assumes "al \<in> set (body_join al0 atoms facts)"
  shows "\<forall>a \<in> set atoms. subst_atom (\<lambda>x. the (map_of al x)) a \<in> set facts"
  using assms
proof (induction atoms arbitrary: al0)
  case Nil
  thus ?case by simp
next
  case (Cons a atoms)
  obtain al1 where al1: "al1 \<in> set (match_facts_al al0 a facts)"
    and alin: "al \<in> set (body_join al1 atoms facts)"
    using Cons.prems by auto
  obtain f where f: "f \<in> set facts" and m: "match_atom_al al0 a f = Some al1"
    using al1 by (auto simp: match_facts_al_def set_map_filter')
  have rest: "\<forall>a' \<in> set atoms. subst_atom (\<lambda>x. the (map_of al x)) a' \<in> set facts"
    using Cons.IH[OF alin] .
  have bnd: "\<forall>x \<in> set (concat (map id_vars_list (snd a))). map_of al1 x \<noteq> None"
    and rep: "subst_atom (\<lambda>x. the (map_of al1 x)) a = f"
    using match_atom_al_spec[OF m] by auto
  have le: "map_of al1 \<subseteq>\<^sub>m map_of al"
    using body_join_extends[OF alin] .
  have "subst_atom (\<lambda>x. the (map_of al x)) a = subst_atom (\<lambda>x. the (map_of al1 x)) a"
  proof (intro subst_atom_agree ballI)
    fix i x assume i: "i \<in> set (snd a)" and x: "x \<in> set (id_vars_list i)"
    have "x \<in> set (concat (map id_vars_list (snd a)))" using i x by auto
    hence "map_of al1 x \<noteq> None" using bnd by blast
    hence "map_of al x = map_of al1 x" using le by (auto simp: map_le_def dom_def)
    thus "the (map_of al x) = the (map_of al1 x)" by simp
  qed
  hence "subst_atom (\<lambda>x. the (map_of al x)) a = f" using rep by simp
  thus ?case using f rest by simp
qed

subsection \<open>Completeness of matching: every consistent \<open>\<sigma>\<close> is found\<close>

lemma match_id_al_complete:
  assumes "\<forall>x d. map_of al x = Some d \<longrightarrow> \<sigma> x = d"
  shows "\<exists>al'. match_id_al al i (subst_id \<sigma> i) = Some al'
             \<and> (\<forall>x d. map_of al x = Some d \<longrightarrow> map_of al' x = Some d)
             \<and> (\<forall>x d. map_of al' x = Some d \<longrightarrow> \<sigma> x = d)
             \<and> (\<forall>x \<in> set (id_vars_list i). map_of al' x = Some (\<sigma> x))"
proof (cases i)
  case (Cst c)
  thus ?thesis using assms by (intro exI[where x = al]) auto
next
  case (Var x)
  show ?thesis
  proof (cases "map_of al x")
    case None
    thus ?thesis using Var assms by (intro exI[where x = "(x, \<sigma> x) # al"]) auto
  next
    case (Some d)
    hence "\<sigma> x = d" using assms by blast
    thus ?thesis using Var Some assms by (intro exI[where x = al]) auto
  qed
qed

lemma match_ids_al_complete:
  assumes "\<forall>x d. map_of al x = Some d \<longrightarrow> \<sigma> x = d"
  shows "\<exists>al'. match_ids_al al ids (map (subst_id \<sigma>) ids) = Some al'
             \<and> (\<forall>x d. map_of al x = Some d \<longrightarrow> map_of al' x = Some d)
             \<and> (\<forall>x d. map_of al' x = Some d \<longrightarrow> \<sigma> x = d)
             \<and> (\<forall>x \<in> set (concat (map id_vars_list ids)). map_of al' x = Some (\<sigma> x))"
  using assms
proof (induction ids arbitrary: al)
  case Nil
  thus ?case by auto
next
  case (Cons i ids)
  obtain al1 where
    m1: "match_id_al al i (subst_id \<sigma> i) = Some al1"
    and ext1: "\<forall>x d. map_of al x = Some d \<longrightarrow> map_of al1 x = Some d"
    and cons1: "\<forall>x d. map_of al1 x = Some d \<longrightarrow> \<sigma> x = d"
    and bind1: "\<forall>x \<in> set (id_vars_list i). map_of al1 x = Some (\<sigma> x)"
    using match_id_al_complete[OF Cons.prems, of i] by blast
  obtain al' where
    m': "match_ids_al al1 ids (map (subst_id \<sigma>) ids) = Some al'"
    and ext': "\<forall>x d. map_of al1 x = Some d \<longrightarrow> map_of al' x = Some d"
    and cons': "\<forall>x d. map_of al' x = Some d \<longrightarrow> \<sigma> x = d"
    and bind': "\<forall>x \<in> set (concat (map id_vars_list ids)). map_of al' x = Some (\<sigma> x)"
    using Cons.IH[OF cons1] by blast
  have bindi: "\<forall>x \<in> set (id_vars_list i). map_of al' x = Some (\<sigma> x)" using bind1 ext' by blast
  show ?case
  proof (intro exI[where x = al'] conjI)
    show "match_ids_al al (i # ids) (map (subst_id \<sigma>) (i # ids)) = Some al'" using m1 m' by simp
    show "\<forall>x d. map_of al x = Some d \<longrightarrow> map_of al' x = Some d" using ext1 ext' by blast
    show "\<forall>x d. map_of al' x = Some d \<longrightarrow> \<sigma> x = d" using cons' .
    show "\<forall>x \<in> set (concat (map id_vars_list (i # ids))). map_of al' x = Some (\<sigma> x)"
      using bindi bind' by auto
  qed
qed

lemma match_atom_al_complete:
  assumes "\<forall>x d. map_of al x = Some d \<longrightarrow> \<sigma> x = d"
  shows "\<exists>al'. match_atom_al al a (subst_atom \<sigma> a) = Some al'
             \<and> (\<forall>x d. map_of al x = Some d \<longrightarrow> map_of al' x = Some d)
             \<and> (\<forall>x d. map_of al' x = Some d \<longrightarrow> \<sigma> x = d)
             \<and> (\<forall>x \<in> set (concat (map id_vars_list (snd a))). map_of al' x = Some (\<sigma> x))"
  using match_ids_al_complete[OF assms, of "snd a"]
  by (simp add: match_atom_al_def subst_atom_def)

text \<open>\<^bold>\<open>Join completeness\<close>: every \<open>\<sigma>\<close> that maps the body into the facts is captured by some branch,
  and that branch binds every body variable to \<open>\<sigma>\<close>'s value.\<close>
lemma body_join_complete:
  assumes "\<forall>a \<in> set atoms. subst_atom \<sigma> a \<in> set facts"
    and "\<forall>x d. map_of al0 x = Some d \<longrightarrow> \<sigma> x = d"
  shows "\<exists>al \<in> set (body_join al0 atoms facts).
           (\<forall>x d. map_of al0 x = Some d \<longrightarrow> map_of al x = Some d)
           \<and> (\<forall>x d. map_of al x = Some d \<longrightarrow> \<sigma> x = d)
           \<and> (\<forall>a \<in> set atoms. \<forall>x \<in> set (concat (map id_vars_list (snd a))). map_of al x = Some (\<sigma> x))"
  using assms
proof (induction atoms arbitrary: al0)
  case Nil
  thus ?case by auto
next
  case (Cons a atoms)
  have fa: "subst_atom \<sigma> a \<in> set facts" using Cons.prems(1) by simp
  obtain al1 where m1: "match_atom_al al0 a (subst_atom \<sigma> a) = Some al1"
    and ext1: "\<forall>x d. map_of al0 x = Some d \<longrightarrow> map_of al1 x = Some d"
    and cons1: "\<forall>x d. map_of al1 x = Some d \<longrightarrow> \<sigma> x = d"
    and bind1: "\<forall>x \<in> set (concat (map id_vars_list (snd a))). map_of al1 x = Some (\<sigma> x)"
    using match_atom_al_complete[OF Cons.prems(2), of a] by blast
  have al1in: "al1 \<in> set (match_facts_al al0 a facts)"
    using m1 fa by (force simp: match_facts_al_def List.map_filter_def)
  have rest_facts: "\<forall>a \<in> set atoms. subst_atom \<sigma> a \<in> set facts" using Cons.prems(1) by simp
  obtain al where
    alin: "al \<in> set (body_join al1 atoms facts)"
    and ext': "\<forall>x d. map_of al1 x = Some d \<longrightarrow> map_of al x = Some d"
    and cons': "\<forall>x d. map_of al x = Some d \<longrightarrow> \<sigma> x = d"
    and bind': "\<forall>a \<in> set atoms. \<forall>x \<in> set (concat (map id_vars_list (snd a))). map_of al x = Some (\<sigma> x)"
    using Cons.IH[OF rest_facts cons1] by blast
  have binda: "\<forall>x \<in> set (concat (map id_vars_list (snd a))). map_of al x = Some (\<sigma> x)"
    using bind1 ext' by blast
  show ?case
  proof (intro bexI[where x = al] conjI)
    show "\<forall>x d. map_of al0 x = Some d \<longrightarrow> map_of al x = Some d" using ext1 ext' by blast
    show "\<forall>x d. map_of al x = Some d \<longrightarrow> \<sigma> x = d" using cons' .
    show "\<forall>a' \<in> set (a # atoms). \<forall>x \<in> set (concat (map id_vars_list (snd a'))).
            map_of al x = Some (\<sigma> x)"
      using binda bind' by auto
    show "al \<in> set (body_join al0 (a # atoms) facts)" using alin al1in by auto
  qed
qed

subsection \<open>Refinement 1 of one round: the join-based \<open>dl_step\<close>\<close>

text \<open>The fireable heads of a \<^emph>\<open>safe\<close> clause, computed by the join: enumerate the body solutions,
  keep those whose bindings stay inside \<open>U\<close> and satisfy the guards, and read off the head. For an
  unsafe clause fall back to the naive \<^const>\<open>fireable_heads\<close>, so the refinement is unconditional.\<close>

definition fireable_heads_join ::
  "'c list \<Rightarrow> ('p, 'x, 'c) clause \<Rightarrow> ('p, 'c) dl_fact list \<Rightarrow> ('p, 'c) dl_fact list" where
  "fireable_heads_join U cl facts =
     map (\<lambda>al. subst_atom (\<lambda>x. the (map_of al x)) (the_lh cl))
       (filter (\<lambda>al. list_all (\<lambda>x. case map_of al x of Some c \<Rightarrow> c \<in> set U | None \<Rightarrow> False)
                              (cls_vars cl)
                     \<and> list_all (eval_guard_al al) (cls_guards cl))
               (body_join [] (cls_body_atoms cl) facts))"

definition dl_step_join ::
  "'c list \<Rightarrow> ('p, 'x, 'c) clause list \<Rightarrow> ('p, 'c) dl_fact list \<Rightarrow> ('p, 'c) dl_fact list" where
  "dl_step_join U Pl facts =
     remdups (facts @ concat (map (\<lambda>cl. if clause_safe_exec cl
                                        then fireable_heads_join U cl facts
                                        else fireable_heads U cl facts) Pl))"

declare fireable_heads_join_def [code] dl_step_join_def [code]

text \<open>\<^bold>\<open>The refinement theorem.\<close> Both directions are available from the lemmas above:
  \<^item> \<open>\<subseteq>\<close> (soundness) from \<open>body_join_sound\<close> --- a join branch instantiates the body into the
    facts, its \<open>U\<close>-range and guard filters reproduce the two \<^const>\<open>fireable_heads\<close> conditions, and
    \<open>cls_substs_tabulate\<close> turns \<open>\<lambda>x. the (map_of al x)\<close> into a tabulated substitution
    (the head instance is unchanged by \<open>subst_atom_head_cong\<close>);
  \<^item> \<open>\<supseteq>\<close> (completeness) from \<open>body_join_complete\<close> --- for a firing \<open>\<sigma>\<close> pick the branch it
    induces; safety (\<open>clause_safe_exec_iff\<close>) says every clause variable occurs in a body atom,
    hence is bound by that branch to \<open>\<sigma>\<close>'s value, so head, guards and range checks all agree.

  It is the same argument as the two directions of \<open>clause_ok_iff\<close> in the certificate development
  this repository was extracted from.\<close>
lemma fireable_heads_join_eq:
  assumes safe: "clause_safe_exec cl"
  shows "set (fireable_heads_join U cl facts) = set (fireable_heads U cl facts)"
proof (intro equalityI subsetI)
  fix h assume "h \<in> set (fireable_heads_join U cl facts)"
  then obtain al where
    alin: "al \<in> set (body_join [] (cls_body_atoms cl) facts)"
    and rng: "list_all (\<lambda>x. case map_of al x of Some c \<Rightarrow> c \<in> set U | None \<Rightarrow> False) (cls_vars cl)"
    and grd: "list_all (eval_guard_al al) (cls_guards cl)"
    and h: "h = subst_atom (\<lambda>x. the (map_of al x)) (the_lh cl)"
    unfolding fireable_heads_join_def by auto
  have rngU: "\<forall>x \<in> set (cls_vars cl). the (map_of al x) \<in> set U"
    using rng by (auto simp: list_all_iff split: option.splits)
  obtain \<sigma>' where \<sigma>': "\<sigma>' \<in> set (cls_substs U cl)"
    and agree: "\<forall>x \<in> set (cls_vars cl). \<sigma>' x = the (map_of al x)"
    using cls_substs_tabulate[OF rngU] by blast
  have body: "\<forall>a \<in> set (cls_body_atoms cl). subst_atom \<sigma>' a \<in> set facts"
    using body_join_sound[OF alin] subst_atom_body_cong[OF agree] by simp
  have guards: "\<forall>g \<in> set (cls_guards cl). eval_guard \<sigma>' g"
    using grd by (simp add: list_all_iff eval_guard_al_eq eval_guard_cls_cong[OF agree])
  have "h = subst_atom \<sigma>' (the_lh cl)" using h subst_atom_head_cong[OF agree] by simp
  thus "h \<in> set (fireable_heads U cl facts)"
    unfolding fireable_heads_def using \<sigma>' body guards by auto
next
  fix h assume "h \<in> set (fireable_heads U cl facts)"
  then obtain \<sigma> where \<sigma>: "\<sigma> \<in> set (cls_substs U cl)"
    and guards: "\<forall>g \<in> set (cls_guards cl). eval_guard \<sigma> g"
    and body: "\<forall>a \<in> set (cls_body_atoms cl). subst_atom \<sigma> a \<in> set facts"
    and h: "h = subst_atom \<sigma> (the_lh cl)"
    unfolding fireable_heads_def by auto
  obtain al where
    alin: "al \<in> set (body_join [] (cls_body_atoms cl) facts)"
    and bind: "\<forall>a \<in> set (cls_body_atoms cl).
                 \<forall>x \<in> set (concat (map id_vars_list (snd a))). map_of al x = Some (\<sigma> x)"
    using body_join_complete[OF body, of "[]"] by auto
  \<comment> \<open>Safety is what makes the join bind \<^emph>\<open>every\<close> clause variable, not just the body ones.\<close>
  have bound: "map_of al x = Some (\<sigma> x)" if x: "x \<in> set (cls_vars cl)" for x
  proof -
    obtain a where "a \<in> set (cls_body_atoms cl)"
      and "x \<in> set (concat (map id_vars_list (snd a)))"
      using safe x unfolding clause_safe_exec_iff by blast
    thus ?thesis using bind by blast
  qed
  have agree: "\<forall>x \<in> set (cls_vars cl). (\<lambda>x. the (map_of al x)) x = \<sigma> x"
    using bound by simp
  have rng: "list_all (\<lambda>x. case map_of al x of Some c \<Rightarrow> c \<in> set U | None \<Rightarrow> False) (cls_vars cl)"
    using bound cls_substs_rangeD[OF \<sigma>] by (simp add: list_all_iff)
  have grd: "list_all (eval_guard_al al) (cls_guards cl)"
    using guards by (simp add: list_all_iff eval_guard_al_eq eval_guard_cls_cong[OF agree])
  have "h = subst_atom (\<lambda>x. the (map_of al x)) (the_lh cl)"
    using h subst_atom_head_cong[OF agree] by simp
  thus "h \<in> set (fireable_heads_join U cl facts)"
    unfolding fireable_heads_join_def using alin rng grd by auto
qed

theorem dl_step_join_eq:
  "set (dl_step_join U Pl facts) = set (dl_step U Pl facts)"
  unfolding dl_step_join_def dl_step_def
  by (auto simp: fireable_heads_join_eq)

end
