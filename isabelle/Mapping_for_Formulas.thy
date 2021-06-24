(*<*)
theory Mapping_for_Formulas
  imports
    Mapping_for_Transition_Systems
    HM_Logic
    HM_Logic_with_TimeOuts
begin
(*>*)

section \<open>A Mapping for Formulas\<close>
text \<open>\label{sec:mapping_formulas}\<close>

text \<open>We will now introduce a mapping $\sigma(\cdot)$ that maps formulas of \HMLt{} to formulas of HML, in the context of the process mapping from \cref{sec:mapping_lts}, such that $\vartheta(p)$ satisfies $\sigma(\varphi)$ iff $p$ satisfies $\varphi$.

Again, we have $\mathbb{T} = (\Proc, \Act, \rightarrow)$ and $\mathbb{T}_\vartheta = (\Proc_\vartheta, \Act_\vartheta, \rightarrow_\vartheta)$ as defined in \cref{sec:mapping_lts}, with $A = \Act \!\setminus\! \{\tau, t\}$, and we assume that $t_\varepsilon \notin \Act$ and $\forall X \subseteq A.\; \varepsilon_X \notin \Act$.

Let $\sigma : (\text{\HMLt{} formulas}) \longrightarrow (\text{HML formulas})$ be recursively defined by
\begin{align*}
    \sigma(\textstyle\bigwedge_{i \in I} \varphi_i) =\;& \textstyle\bigwedge_{i \in I} \sigma(\varphi_i) &\\
    \sigma(\neg\varphi) =\;& \neg\,\sigma(\varphi)\\
    \sigma(\langle\tau\rangle\varphi) =\;& \langle\tau\rangle\,\sigma(\varphi)\\
    \sigma(\langle\alpha\rangle\varphi) =\;& 
        \langle\alpha\rangle\,\sigma(\varphi)\;\vee\\
        &\langle\varepsilon_A\rangle\langle\alpha\rangle\,\sigma(\varphi)\;\vee\\ 
        &\langle{}t_\varepsilon\rangle\langle\varepsilon_A\rangle\langle\alpha\rangle\,\sigma(\varphi) && \text{if $\alpha \in A$}\\
    \sigma(\langle\alpha\rangle\varphi) =\;& f\!\!f && \text{if $\alpha \notin A \cup \{\tau\}$}\\
    \sigma(\langle{}X\rangle\varphi) =\;&
        \langle\varepsilon_X\rangle\langle{}t\rangle\,\sigma(\varphi)\;\vee\\
        &\langle{}t_\varepsilon\rangle\langle\varepsilon_X\rangle\langle{}t\rangle\,\sigma(\varphi) && \text{if $X \subseteq A$} \\
    \sigma(\langle{}X\rangle\varphi) =\;& f\!\!f && \text{if $X \not\subseteq A$}
\end{align*}

This mapping simply expresses the time-out semantics given by the satisfaction relations of \HMLt{} (\cref{sec:HMLt}) in terms of ordinary HML evaluated on our mapped LTS $\mathbb{T}_\vartheta$. The disjunctive clauses compensate for the additional environment transitions ($\varepsilon$-actions) that are not present in $\mathbb{T}$.
\pagebreak\<close>


subsection \<open>Isabelle\<close>

text \<open>The implementation of the mapping in Isabelle is rather straightforward, although some details might not be obvious: 

\<open>cimage (\<lambda> \<phi>. \<sigma>(\<phi>)) \<Phi>\<close> is the image of the countable set \<open>\<Phi>\<close> under the function \<open>\<lambda> \<phi>. \<sigma>(\<phi>)\<close>, so it corresponds to $\{ \sigma(\varphi) \mid \varphi \in \Phi \}$ for countable $\Phi$.

\<open>\<alpha> \<noteq> \<tau> \<and> \<alpha> \<noteq> t \<and> \<alpha> \<noteq> t_\<epsilon> \<and> (\<forall> X. \<alpha> \<noteq> \<epsilon>[X])\<close> corresponds to $\alpha \in A$ with our assumption about there being no $\varepsilon$-actions in $\Act$. Similarly, \linebreak \<open>\<alpha> = t \<or> \<alpha> = t_\<epsilon> \<or> \<alpha> = \<epsilon>[X]\<close> corresponds to $\alpha \notin A \cup \{\tau\}$.\<close>

context lts_timeout_mappable begin

function HMt_mapping :: \<open>('a)HMLt_formula \<Rightarrow> ('a)HML_formula\<close> 
  (\<open>\<sigma>'(_')\<close>)
  where
    \<open>\<sigma>(HMLt_conj \<Phi>) = HML_conj (cimage (\<lambda> \<phi>. \<sigma>(\<phi>)) \<Phi>)\<close>
  | \<open>\<sigma>(HMLt_neg \<phi>) = HML_neg \<sigma>(\<phi>)\<close>
  | \<open>\<alpha> = \<tau> \<Longrightarrow>
      \<sigma>(HMLt_poss \<alpha> \<phi>) = HML_poss \<alpha> \<sigma>(\<phi>)\<close>
  | \<open>\<alpha> \<noteq> \<tau> \<and> \<alpha> \<noteq> t \<and> \<alpha> \<noteq> t_\<epsilon> \<and> (\<forall> X. \<alpha> \<noteq> \<epsilon>[X]) \<Longrightarrow>
      \<sigma>(HMLt_poss \<alpha> \<phi>) = HML_disj (acset {
        HML_poss \<alpha> \<sigma>(\<phi>),
        HML_poss \<epsilon>[visible_actions] (HML_poss \<alpha> \<sigma>(\<phi>)),
        HML_poss t_\<epsilon> (HML_poss \<epsilon>[visible_actions] (HML_poss \<alpha> \<sigma>(\<phi>)))
      })\<close>
  | \<open>\<alpha> = t \<or> \<alpha> = t_\<epsilon> \<or> \<alpha> = \<epsilon>[X] \<Longrightarrow>
      \<sigma>(HMLt_poss \<alpha> \<phi>) = HML_false\<close>
  | \<open>X \<subseteq> visible_actions \<Longrightarrow>
      \<sigma>(HMLt_time X \<phi>) = HML_disj (acset {
        HML_poss \<epsilon>[X] (HML_poss t \<sigma>(\<phi>)),
        HML_poss t_\<epsilon> (HML_poss \<epsilon>[X] (HML_poss t \<sigma>(\<phi>)))
      })\<close>
  | \<open>\<not> X \<subseteq> visible_actions \<Longrightarrow>
      \<sigma>(HMLt_time X \<phi>) = HML_false\<close>  
  by (metis HMLt_formula.exhaust, auto+, (simp add: distinctness_special_actions(1,2))+, metis distinctness_special_actions(4))

text \<open>Again, we show that the function terminates using a well-founded relation.\<close>

inductive_set sigma_wf_rel :: \<open>(('a)HMLt_formula) rel\<close> 
  where
    \<open>\<phi> \<in>\<^sub>c \<Phi> \<Longrightarrow> (\<phi>, HMLt_conj \<Phi>) \<in> sigma_wf_rel\<close> 
  | \<open>(\<phi>, HMLt_neg \<phi>) \<in> sigma_wf_rel\<close> 
  | \<open>(\<phi>, HMLt_poss \<alpha> \<phi>) \<in> sigma_wf_rel\<close> 
  | \<open>(\<phi>, HMLt_time X \<phi>) \<in> sigma_wf_rel\<close>

(*<*)
lemma\<^marker>\<open>tag (proof) unimportant\<close> sigma_wf_rel_is_wf: \<open>wf sigma_wf_rel\<close> 
  unfolding wf_def
proof (rule allI, rule impI, rule allI)
  fix P::\<open>('a)HMLt_formula \<Rightarrow> bool\<close> and t::\<open>('a)HMLt_formula\<close>
  assume \<open>\<forall>x. (\<forall>y. (y, x) \<in> sigma_wf_rel \<longrightarrow> P y) \<longrightarrow> P x\<close>
  thus \<open>P t\<close>
    apply (induction t)
    apply (metis HMLt_formula.distinct(1,3,5) HMLt_formula.inject(1) sigma_wf_rel.cases cin.rep_eq)
    apply (metis HMLt_formula.distinct(2,8,10) HMLt_formula.inject(2) sigma_wf_rel.cases)
    apply (metis HMLt_formula.distinct(3,7,11) HMLt_formula.inject(3) sigma_wf_rel.cases)
    apply (metis HMLt_formula.distinct(5,9,11) HMLt_formula.inject(4) sigma_wf_rel.cases)
    done
qed
(*>*)


termination HMt_mapping using sigma_wf_rel_is_wf by (standard, (simp add: cin.rep_eq sigma_wf_rel.intros)+)

end \<comment> \<open>of \<open>context lts_timeout_mappable\<close>\<close>
(*<*)
end \<comment> \<open>of \<open>theory\<close>\<close>
(*>*)