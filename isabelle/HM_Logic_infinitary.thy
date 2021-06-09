(*<*)
theory HM_Logic_infinitary
  imports 
    Strong_Bisimilarity
begin
(*>*)

chapter \<open>Infinitary Hennessy-Milner Logic\<close>
text \<open>\label{chap:HML_infinitary}\<close>

text \<open>We will show that a modal characterisation of strong bisimilarity is possible without any assumptions about the cardinality of derivative sets \<open>Der(p, \<alpha>)\<close>, using infinitary HML (with conjunction of arbitrary cardinality). Instead of formalising formulas under a conjunction as a countable set,%
\footnote{Note that it is not possible to define a dataype with a constructor depending on a set of the type itself, i.e.\@ \<open>HML_conj \<open>('a)HML_formula set\<close>\<close> would not yield a valid data type. Dunno y tho.}
we use an index set of arbitrary type \<open>I :: 'x set\<close> and a mapping \<open>F :: 'x \<Rightarrow> ('a, 'x)HML_formula\<close> so that each element of \<open>I\<close> is mapped to a formula. This closely resembles the semantics of $\bigwedge_{i \in I} \varphi_i$. Since the mapping is total, we cannot use the empty conjunction as a base for the type. Instead of using partial mappings \<open>F :: 'x \<Rightarrow> ('a, 'x)HML_formula option\<close>, I included a constructor \<open>HML_true\<close> and implicitly assume that \<open>F\<close> maps to \<open>HML_true\<close> for all objects of type \<open>'x\<close> that are not elements of \<open>I\<close>.\<close>

datatype ('a, 'x)HML_formula =
  HML_true 
| HML_conj \<open>'x set\<close> \<open>'x \<Rightarrow> ('a, 'x)HML_formula\<close> 
| HML_neg \<open>('a, 'x)HML_formula\<close> 
| HML_poss \<open>'a\<close> \<open>('a, 'x)HML_formula\<close> 


subsubsection \<open>Satisfaction Relation\<close>

text \<open>Data types cannot be used with arbitrary parameter types \<open>'x\<close> in concrete contexts; so when using our data type in the \<open>context lts\<close>, we use the type of processes \<open>'s\<close> as the type for conjunction index sets. Since this suffices to proof the modal characterisation, we can conclude that it suffices for the cardinality of conjunction to be equal to the cardinality of the set of processes $\Proc$. As we can deduce from the part of the proof where formula conjunction is used, a weaker requirement would be to allow for conjunction of cardinality equal to $\displaystyle\max_{\substack{p\in\Proc \\ \alpha\in\Act}} |\text{Der}(p, \alpha)|$.

The remainder of this section follows the same structure as \cref{sec:HML}. The explanations from there mostly apply here as well.\<close>

context lts begin

function satisfies :: \<open>'s \<Rightarrow> ('a, 's) HML_formula \<Rightarrow> bool\<close> 
  (\<open>_ \<Turnstile> _\<close> [50, 50] 50)
  where
    \<open>(p \<Turnstile> HML_true) = True\<close> 
  | \<open>(p \<Turnstile> HML_conj I F) = (\<forall> i \<in> I. p \<Turnstile> (F i))\<close> 
  | \<open>(p \<Turnstile> HML_neg \<phi>) = (\<not> p \<Turnstile> \<phi>)\<close> 
  | \<open>(p \<Turnstile> HML_poss \<alpha> \<phi>) = (\<exists> p'. p \<longmapsto>\<alpha> p' \<and> p' \<Turnstile> \<phi>)\<close>
  using HML_formula.exhaust by (auto, blast)

inductive_set HML_wf_rel :: \<open>('s \<times> ('a, 's) HML_formula) rel\<close> 
  where
    \<open>\<phi> = F i \<and> i \<in> I \<Longrightarrow> ((p, \<phi>), (p, HML_conj I F)) \<in> HML_wf_rel\<close> 
  | \<open>((p, \<phi>), (p, HML_neg \<phi>)) \<in> HML_wf_rel\<close> 
  | \<open>((p, \<phi>), (p', HML_poss \<alpha> \<phi>)) \<in> HML_wf_rel\<close>

lemma HML_wf_rel_is_wf: \<open>wf HML_wf_rel\<close> 
  unfolding wf_def
proof (rule allI, rule impI, rule allI)
  fix P::\<open>'s \<times> ('a, 's) HML_formula \<Rightarrow> bool\<close> and t::\<open>'s \<times> ('a, 's) HML_formula\<close>
  obtain p \<phi> where \<open>t = (p, \<phi>)\<close> by force
  assume \<open>\<forall>x. (\<forall>y. (y, x) \<in> HML_wf_rel \<longrightarrow> P y) \<longrightarrow> P x\<close>
  hence \<open>P (p, \<phi>)\<close>
    apply (induct \<phi> arbitrary: p)
    apply (metis HML_formula.ctr_transfer(1) HML_formula.distinct(3) HML_formula.distinct(5) HML_formula.rel_distinct(2) HML_wf_relp.cases HML_wf_relp_HML_wf_rel_eq surj_pair)
    apply (smt (verit) HML_formula.distinct(10) HML_formula.distinct(7) HML_formula.inject(1) HML_wf_rel_def UNIV_I case_prodE' image_eqI lts.HML_wf_rel.cases mem_Collect_eq split_conv)
    apply (smt (verit, ccfv_threshold) HML_formula.distinct(11) HML_formula.distinct(7) HML_formula.inject(2) case_prodI2 case_prod_curry lts.HML_wf_rel.cases lts.HML_wf_rel_def)
    apply (smt (verit, del_insts) HML_formula.distinct(3,5,9,11)  HML_formula.inject(3) HML_wf_rel.cases case_prodD case_prodE' lts.HML_wf_rel_def mem_Collect_eq)
    done
  thus \<open>P t\<close> using \<open>t = (p, \<phi>)\<close> by simp
qed

termination\<^marker>\<open>tag (proof) visible\<close> satisfies using HML_wf_rel_is_wf 
  by (standard, (simp add: HML_wf_rel.intros)+)


subsubsection \<open>Modal Characterisation of Strong Bisimilarity\<close>

definition HML_equivalent :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close>
  where \<open>HML_equivalent p q 
    \<equiv> (\<forall> \<phi>::('a, 's) HML_formula. (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))\<close>

lemma distinguishing_formula:
  assumes \<open>\<not> HML_equivalent p q\<close>
  shows \<open>\<exists> \<phi>. p \<Turnstile> \<phi> \<and> \<not> q \<Turnstile> \<phi>\<close>
proof -
  from assms obtain \<phi> where \<open>p \<Turnstile> \<phi> \<and> \<not> q \<Turnstile> \<phi> \<or> q \<Turnstile> \<phi> \<and> \<not> p \<Turnstile> \<phi>\<close>
    using HML_equivalent_def assms by blast
  thus ?thesis proof (elim disjE, auto)
    assume \<open>q \<Turnstile> \<phi>\<close> and \<open>\<not> p \<Turnstile> \<phi>\<close>
    from \<open>q \<Turnstile> \<phi>\<close> have \<open>\<not> q \<Turnstile> HML_neg \<phi>\<close> by simp
    moreover from \<open>\<not> p \<Turnstile> \<phi>\<close> have \<open>p \<Turnstile> HML_neg \<phi>\<close> by simp
    ultimately show \<open>\<exists> \<phi>. p \<Turnstile> \<phi> \<and> \<not> q \<Turnstile> \<phi>\<close> by blast
  qed
qed

lemma HML_equivalent_symm:
  assumes \<open>HML_equivalent p q\<close>
  shows \<open>HML_equivalent q p\<close>
  using HML_equivalent_def assms by presburger

lemma\<^marker>\<open>tag (proof) visible\<close> strong_bisimilarity_implies_HML_equivalent:
  assumes \<open>p \<leftrightarrow> q\<close> \<open>p \<Turnstile> \<phi>\<close>
  shows \<open>q \<Turnstile> \<phi>\<close>
  using assms
proof (induct \<phi> arbitrary: p q)
  case HML_true
  then show ?case 
    by force
next
  case (HML_conj X F)
  then show ?case 
    by force
next
  case (HML_neg \<phi>)
  then show ?case
    using satisfies.simps(3) strongly_bisimilar_symm by blast
next
  case (HML_poss \<alpha> \<phi>)
  then show ?case
    by (meson satisfies.simps(4) strongly_bisimilar_step(1))
qed


lemma\<^marker>\<open>tag (proof) visible\<close> HML_equivalence_is_SB:
  shows \<open>SB HML_equivalent\<close>
proof -
  {
    fix p q p' \<alpha>
    assume \<open>HML_equivalent p q\<close> \<open>p \<longmapsto>\<alpha> p'\<close>
    assume \<open>\<forall> q' \<in> Der(q, \<alpha>). \<not> HML_equivalent p' q'\<close>
    
    hence "exists_\<phi>\<^bsub>q'\<^esub>": \<open>\<forall>q' \<in> Der(q, \<alpha>). \<exists>\<phi>. p' \<Turnstile> \<phi> \<and> \<not> q' \<Turnstile> \<phi>\<close>
      using distinguishing_formula by blast

    let ?I = \<open>Der(q, \<alpha>)\<close>
    let ?F = \<open>(\<lambda> q'. SOME \<phi>. p' \<Turnstile> \<phi> \<and> \<not> q' \<Turnstile> \<phi>)\<close>
    let ?\<phi> = \<open>HML_conj ?I ?F\<close>
    
    from "exists_\<phi>\<^bsub>q'\<^esub>" have \<open>p' \<Turnstile> ?\<phi>\<close>
      by (smt (z3) satisfies.simps(2) someI_ex)
    hence \<open>p \<Turnstile> HML_poss \<alpha> ?\<phi>\<close> using \<open>p \<longmapsto>\<alpha> p'\<close>
      by auto

    from "exists_\<phi>\<^bsub>q'\<^esub>" have \<open>\<forall>q' \<in> Der(q, \<alpha>). \<not> q' \<Turnstile> ?\<phi>\<close>
      by (smt (z3) satisfies.simps(2) someI_ex)
    hence \<open>\<not> q \<Turnstile> HML_poss \<alpha> ?\<phi>\<close>
      by simp
  
    from \<open>p \<Turnstile> HML_poss \<alpha> ?\<phi>\<close> \<open>\<not> q \<Turnstile> HML_poss \<alpha> ?\<phi>\<close> have False 
      using \<open>HML_equivalent p q\<close> 
      unfolding HML_equivalent_def by blast
  }

  thus \<open>SB HML_equivalent\<close> unfolding SB_def 
    using HML_equivalent_symm by blast
qed

  
theorem\<^marker>\<open>tag (proof) visible\<close> modal_characterisation_of_strong_bisimilarity: 
  shows \<open>p \<leftrightarrow> q  \<Longleftrightarrow>  (\<forall> \<phi>. p \<Turnstile> \<phi> \<longleftrightarrow> q \<Turnstile> \<phi>)\<close>
proof
  show \<open>p \<leftrightarrow> q \<Longrightarrow> \<forall>\<phi>. (p \<Turnstile> \<phi>) = (q \<Turnstile> \<phi>)\<close>
    using strong_bisimilarity_implies_HML_equivalent 
      strongly_bisimilar_symm 
    by blast
next
  show \<open>\<forall>\<phi>. (p \<Turnstile> \<phi>) = (q \<Turnstile> \<phi>) \<Longrightarrow> p \<leftrightarrow> q\<close> 
    using HML_equivalence_is_SB HML_equivalent_def 
      strongly_bisimilar_def 
    by blast
qed

end \<comment> \<open>of \<open>context lts\<close>\<close>
(*<*)
end \<comment> \<open>of \<open>theory\<close>\<close>
(*>*)