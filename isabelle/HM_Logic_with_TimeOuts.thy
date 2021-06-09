(*<*)
theory HM_Logic_with_TimeOuts
  imports 
    Reactive_Bisimilarity
    "HOL-Library.Countable_Set_Type"
begin
(*>*)

section \<open>Hennessy-Milner Logic with Time-Outs\<close>
text \<open>\label{sec:HMLt}\<close>

text \<open>In @{cite \<open>Section 3\<close> rbs}, van~Glabbeek extends Hennessy-Milner logic by a family of new modal operators $\langle X \rangle \varphi$, for $X \subseteq A$, as well as additional satisfaction relations $\vDash_X$ for each $X \subseteq A$. Intuitively, $p \vDash \langle X \rangle \varphi$ means that $p$ is idle when placed in an environment~$X$ \emph{and} $p$ can perform a $t$-transition into a state that satisfies $\varphi$; $p \vDash_X \varphi$ means that $p$ satisfies $\varphi$ in environments~$X$.

I call this extension \emph{Hennessy-Milner Logic with Time-Outs} (\HMLt{}) and $\langle X \rangle$ for $X \subseteq A$ the \emph{time-out--possibility operators} (to be distinguished from the ordinary possibility operators $\langle \alpha \rangle$ for $\alpha \in \Act$).

The precise semantics are given by the following inductive definition of the satisfaction relation @{cite \<open>Section 3\<close> rbs} (notation slightly adapted):

\begin{tabular}{l l l}
    $p \vDash \bigwedge_{i \in I} \varphi_i$ 
    & \text{if} 
    & $\forall i \in I.\; p \vDash \varphi_i$ \\
    
    $p \vDash \neg\varphi$
    & \text{if} 
    & $p \not\vDash \varphi$ \\
    
    $p \vDash \langle \alpha \rangle \varphi$ \quad with $\alpha \in A \cup \{\tau\}$
    & \text{if} 
    & $\exists p'.\; p \xrightarrow{\alpha} p' \wedge p' \vDash \varphi$ \\
    
    $p \vDash \langle X \rangle \varphi$ \quad with $X \subseteq A$
    & \text{if} 
    & $\mathcal{I}(p) \cap (X \cup \{\tau\}) = \emptyset \wedge \exists p'.\; p \xrightarrow{t} p' \wedge p' \vDash_X \varphi$ \\[1em]
    
    
    $p \vDash_X \bigwedge_{i \in I} \varphi_i$ 
    & \text{if} 
    & $\forall i \in I.\; p \vDash_X \varphi_i$ \\
    
    $p \vDash_X \neg\varphi$
    & \text{if} 
    & $p \not\vDash_X \varphi$ \\
    
    $p \vDash_X \langle a \rangle \varphi$ \quad with $a \in A$
    & \text{if} 
    & $a \in X \wedge \exists p'.\; p \xrightarrow{a} p' \wedge p' \vDash \varphi$ \\
    
    $p \vDash_X \langle \tau \rangle \varphi$
    & \text{if} 
    & $\exists p'.\; p \xrightarrow{\tau} p' \wedge p' \vDash_X \varphi$ \\[0.5em]
    
    
    $p \vDash_X \varphi$
    & \text{if} 
    & $\mathcal{I}(p) \cap (X \cup \{\tau\}) = \emptyset \wedge p \vDash \varphi$
\end{tabular}\<close>

text \<open>The same intuitions regarding triggered and stable environments as for the definition of strong reactive bisimulations in \cref{sec:strong_bisimilarity} hold. $\vDash$ expresses that a property holds in triggered environments and $\vDash_X$ that a property holds in environments~$X$. The last clause expresses the possibility of stable environments timing out into triggered environments.

Van~Glabbeek then also proves that \HMLt{} characterises strong reactive/$X$-bisimilarity, i.e.\@ that 
$p \leftrightarrow_r q \iff (\forall \varphi .\; p \vDash \varphi \longleftrightarrow q \vDash \varphi)$ and 
$p \leftrightarrow_r^X q \iff (\forall \varphi .\; p \vDash_X \varphi \longleftrightarrow q \vDash_X \varphi)$,
where $\varphi$ are formulas of \HMLt{}.
A replication of the proof of this characterisation, however, is not part of this thesis.\<close>


subsection \<open>Isabelle\<close>

text \<open>The following formalisation is analogous to the one in \cref{sec:HML}.\<close>

datatype ('a)HMLt_formula =
  HMLt_conj \<open>('a)HMLt_formula cset\<close> \<comment> \<open>$\bigwedge \Phi$\<close> 
| HMLt_neg \<open>('a)HMLt_formula\<close> \<comment> \<open>$\neg\varphi$\<close> 
| HMLt_poss \<open>'a\<close> \<open>('a)HMLt_formula\<close> \<comment> \<open>$\langle\alpha\rangle\varphi$\<close> 
| HMLt_time \<open>'a set\<close> \<open>('a)HMLt_formula\<close> \<comment> \<open>$\langle X \rangle\varphi$\<close>

(*<*)
notation\<^marker>\<open>tag unimportant\<close> cin (\<open>_ \<in>\<^sub>c _\<close> [100, 100] 100)
(*>*)

text \<open>In order to formalise the semantics, I combined both the usual satisfaction relation $\vDash$ and the environment satisfaction relations $\vDash_X$ into one predicate, which is formalised by the function \<open>HMLt_sat\<close> below, where \<open>p \<TTurnstile>?[None] \<phi>\<close> corresponds to $p \vDash \varphi$ and \<open>p \<TTurnstile>?[Some X] \<phi>\<close> corresponds to $p \vDash_X \varphi$. 

Note that, in Isabelle code, I use the symbol \<open>\<TTurnstile>\<close> for all satisfaction relations in the context of \HMLt{}, whereas I use \<open>\<Turnstile>\<close> for satisfaction relations in the context of ordinary HML. 
This notational nuance will be important when we examine the relationship between the satisfaction relations of \HMLt{} and HML in the context of the reduction in \cref{sec:reduction_satisfaction}.

The first four clauses of my formalisation, then, are clearly direct translations of the clauses for the satisfaction relation $\vDash$ quoted above. To see that the next four clauses do, in fact, correspond to the five clauses for $\vDash_X$ above is less straightforward. 

First, each of the four clauses requires that \<open>X\<close> is a subset of the visible actions; in the original definition, the satisfaction relations $\vDash_X$ are only defined for those $X$ to begin with.

Next, the clause for \<open>p \<TTurnstile>?[Some X] (HMLt_poss \<alpha> \<phi>)\<close> combines the original clauses for $p \vDash_X \langle a \rangle \varphi$ and $p \vDash_X \langle \tau \rangle \varphi$. 

Lastly and most importantly, the last clause of the original definition, stating that $p \vDash_X \varphi$ if $p$ is idle in environments~$X$ and $p \vDash \varphi$, is added disjunctively to the cases \<open>p \<TTurnstile>?[Some X] (HMLt_poss \<alpha> \<phi>)\<close> and \<open>p \<TTurnstile>?[Some X] (HMLt_time Y \<phi>)\<close>; the latter case is not part of the original definition and can only be true by virtue of the last clause of the original definition, wherefore this is the only way for the last clause of the function definition below to be true. 

I will show below that this is sufficient to assure that my satisfaction function satisfies the last clause of the original definition, i.e.\@ that it does not need to be added disjunctively to the cases \<open>p \<TTurnstile>?[Some X] (HMLt_conj \<Phi>)\<close> and \<open>p \<TTurnstile>?[Some X] (HMLt_neg \<phi>)\<close>.\<close>

context lts_timeout begin

function HMLt_sat :: \<open>'s \<Rightarrow> 'a set option \<Rightarrow> ('a)HMLt_formula \<Rightarrow> bool\<close> 
  (\<open>_ \<TTurnstile>?[_] _\<close> [50, 50, 50] 50)
  where
    \<open>(p \<TTurnstile>?[None] (HMLt_conj \<Phi>)) = 
      (\<forall> \<phi>. \<phi> \<in>\<^sub>c \<Phi> \<longrightarrow> p \<TTurnstile>?[None] \<phi>)\<close> 
  | \<open>(p \<TTurnstile>?[None] (HMLt_neg \<phi>)) = 
      (\<not> p \<TTurnstile>?[None] \<phi>)\<close> 
  | \<open>(p \<TTurnstile>?[None] (HMLt_poss \<alpha> \<phi>)) = 
      ((\<alpha> \<in> visible_actions \<union> {\<tau>}) \<and> 
        (\<exists> p'. p \<longmapsto>\<alpha> p' \<and> p' \<TTurnstile>?[None] \<phi>))\<close> 
  | \<open>(p \<TTurnstile>?[None] (HMLt_time X \<phi>)) = 
      ((X \<subseteq> visible_actions) \<and> (idle p X) \<and> 
        (\<exists> p'. p \<longmapsto>t p' \<and> p' \<TTurnstile>?[Some X] \<phi>))\<close> 
  
  | \<open>(p \<TTurnstile>?[Some X] (HMLt_conj \<Phi>)) = (X \<subseteq> visible_actions \<and>
      (\<forall> \<phi>. \<phi> \<in>\<^sub>c \<Phi> \<longrightarrow> p \<TTurnstile>?[Some X] \<phi>))\<close> 
  | \<open>(p \<TTurnstile>?[Some X] (HMLt_neg \<phi>)) = (X \<subseteq> visible_actions \<and>
      (\<not> p \<TTurnstile>?[Some X] \<phi>))\<close> 
  | \<open>(p \<TTurnstile>?[Some X] (HMLt_poss \<alpha> \<phi>)) = (X \<subseteq> visible_actions \<and>
      (((\<alpha> \<in> X) \<and> (\<exists> p'. p \<longmapsto>\<alpha> p' \<and> p' \<TTurnstile>?[None] \<phi>)) \<or> 
        ((\<alpha> = \<tau>) \<and> (\<exists> p'. p \<longmapsto>\<tau> p' \<and> p' \<TTurnstile>?[Some X] \<phi>)) \<or> 
        ((idle p X) \<and> (p \<TTurnstile>?[None] (HMLt_poss \<alpha> \<phi>)))))\<close> 
  | \<open>(p \<TTurnstile>?[Some X] (HMLt_time Y \<phi>)) = (X \<subseteq> visible_actions \<and>
      ((idle p X) \<and> (p \<TTurnstile>?[None] (HMLt_time Y \<phi>))))\<close>
  using HMLt_formula.exhaust
  by (metis (no_types, hide_lams) not_Some_eq prod_cases3, fast+)

text \<open>The well-founded relation used for the termination proof of the satisfaction function is considerably more difficult due to the last line of the definition containing the same formula on both sides of the implication (as opposed to the other lines of the definition, where the premises only contain subformulas of the formula in the conclusion). This required me to define two relations, prove their well-foundedness separately, and then prove that their union is well-founded using the theorem @{thm wf_union_compatible} (where \<open>O\<close> is relation composition). Further details have been excluded from the thesis document.\<close>


(* These lemmas are not important for the thesis document. *)
(*<*)
inductive_set\<^marker>\<open>tag unimportant\<close> HMLt_wf_rel_1 :: \<open>('s \<times> 'a set option \<times> ('a)HMLt_formula) rel\<close> where
  \<open>\<phi> \<in>\<^sub>c \<Phi> \<Longrightarrow> ((p, XoN, \<phi>), (p', XoN', HMLt_conj \<Phi>)) \<in> HMLt_wf_rel_1\<close> |
  \<open>((p, XoN, \<phi>), (p', XoN', HMLt_neg \<phi>)) \<in> HMLt_wf_rel_1\<close> |
  \<open>((p, XoN, \<phi>), (p', XoN', HMLt_poss \<alpha> \<phi>)) \<in> HMLt_wf_rel_1\<close> |
  \<open>((p, XoN, \<phi>), (p', XoN', HMLt_time X \<phi>)) \<in> HMLt_wf_rel_1\<close>

lemma\<^marker>\<open>tag (proof) unimportant\<close> HMLt_wf_rel_1_is_wf: \<open>wf HMLt_wf_rel_1\<close> 
  unfolding wf_def
proof (rule allI, rule impI, rule allI)
  fix P::\<open>'s \<times> 'a set option \<times> ('a)HMLt_formula \<Rightarrow> bool\<close> and t::\<open>'s \<times> 'a set option \<times> ('a)HMLt_formula\<close>
  obtain p XoN \<phi> where \<open>t = (p, XoN, \<phi>)\<close>
    using prod_cases3 by blast
  assume \<open>\<forall>x. (\<forall>y. (y, x) \<in> HMLt_wf_rel_1 \<longrightarrow> P y) \<longrightarrow> P x\<close>
  hence \<open>P (p, XoN, \<phi>)\<close>
    apply (induct \<phi> arbitrary: p XoN)
    apply (smt (verit) HMLt_wf_rel_1_def case_prodD case_prodE' mem_Collect_eq HMLt_formula.distinct(1,3,5) HMLt_formula.inject(1) HMLt_wf_rel_1p.simps HMLt_wf_rel_1p_HMLt_wf_rel_1_eq cin.rep_eq prod_cases3)
    apply (smt (verit) HMLt_wf_rel_1_def case_prodD case_prodE' mem_Collect_eq HMLt_formula.distinct(1,7,9) HMLt_formula.inject(2) HMLt_wf_rel_1.simps surj_pair)
    apply (smt (verit) HMLt_wf_rel_1_def case_prodD case_prodE' mem_Collect_eq HMLt_formula.distinct(3,7,11) HMLt_formula.inject(3) HMLt_wf_rel_1.simps surj_pair)
    apply (smt (verit, del_insts) HMLt_formula.distinct(5,9,12) HMLt_formula.inject(4) HMLt_wf_rel_1.simps HMLt_wf_rel_1_def case_prodD case_prodE' mem_Collect_eq)
    done

  thus \<open>P t\<close> using \<open>t = (p, XoN, \<phi>)\<close> by simp
qed

inductive_set\<^marker>\<open>tag unimportant\<close> HMLt_wf_rel_2 :: \<open>('s \<times> 'a set option \<times> ('a)HMLt_formula) rel\<close> where
  \<open>((p, None, \<phi>), (p, Some X, \<phi>)) \<in> HMLt_wf_rel_2\<close>

lemma\<^marker>\<open>tag (proof) unimportant\<close> HMLt_wf_rel_2_is_wf: \<open>wf HMLt_wf_rel_2\<close> 
  by (simp add: HMLt_wf_rel_2.simps wf_def)

abbreviation\<^marker>\<open>tag unimportant\<close> HMLt_wf_rel where \<open>HMLt_wf_rel \<equiv> (HMLt_wf_rel_1 \<union> HMLt_wf_rel_2)\<close>

lemma\<^marker>\<open>tag (proof) unimportant\<close> HMLt_wf_rel_is_wf: \<open>wf HMLt_wf_rel\<close>
proof (rule wf_union_compatible[OF HMLt_wf_rel_1_is_wf HMLt_wf_rel_2_is_wf], standard)
  fix tup
  assume \<open>tup \<in> HMLt_wf_rel_1 O HMLt_wf_rel_2\<close>
  then obtain a c where \<open>(a, c) = tup\<close> \<open>(a, c) \<in> HMLt_wf_rel_1 O HMLt_wf_rel_2\<close> by blast
  with relcomp.simps obtain b where \<open>(a, b) \<in> HMLt_wf_rel_1\<close> \<open>(b, c) \<in> HMLt_wf_rel_2\<close> by blast

  from \<open>(b, c) \<in> HMLt_wf_rel_2\<close> obtain p X \<phi> where \<open>b = (p, None, \<phi>)\<close> \<open>c = (p, Some X, \<phi>)\<close>
    by (metis HMLt_wf_rel_2.cases surj_pair)

  have \<open>(a, (p, None, \<phi>)) \<in> HMLt_wf_rel_1\<close> using \<open>(a, b) \<in> HMLt_wf_rel_1\<close> \<open>b = (p, None, \<phi>)\<close> by simp

  have \<open>(a, (p, Some X, \<phi>)) \<in> HMLt_wf_rel_1\<close> 
    using \<open>(a, (p, None, \<phi>)) \<in> HMLt_wf_rel_1\<close>
  proof (induct a)
    case (fields p' XoN \<phi>')
    then show ?case
      by (induct \<phi>' arbitrary: p' XoN, (simp add: HMLt_wf_rel_1.simps)+)
  qed
  thus \<open>tup \<in> HMLt_wf_rel_1\<close>
    using \<open>(a, c) = tup\<close> \<open>c = (p, Some X, \<phi>)\<close> by fastforce
qed
(*>*)

termination HMLt_sat using HMLt_wf_rel_is_wf by (standard, (simp add: HMLt_wf_rel_1.intros HMLt_wf_rel_2.intros)+)

text \<open>We can now introduce the more readable notation (more closely corresponding to the notation in @{cite rbs}) through abbreviations.\<close>

abbreviation HMLt_sat_triggered :: \<open>'s\<Rightarrow>('a)HMLt_formula \<Rightarrow> bool\<close> 
  ("_ \<TTurnstile> _" [50, 50] 50)
  where \<open>p \<TTurnstile> \<phi> \<equiv> p \<TTurnstile>?[None] \<phi>\<close>
abbreviation HMLt_sat_stable :: \<open>'s\<Rightarrow>'a set\<Rightarrow>('a)HMLt_formula \<Rightarrow> bool\<close>
  ("_ \<TTurnstile>[_] _" [70, 70, 70] 80)
  where \<open>p \<TTurnstile>[X] \<phi> \<equiv> p \<TTurnstile>?[Some X] \<phi>\<close>

text \<open>Lastly, we show (by induction over \<open>\<phi>\<close>) that the function \<open>HMLt_sat\<close> does indeed satisfy the last clause of the original definition.\<close>


(* These lemma is not important for the thesis document. *)
(*<*)
lemma\<^marker>\<open>tag (proof) unimportant\<close> idle_sat_lemma:
  assumes 
    \<open>idle p X\<close>
    \<open>X \<subseteq> visible_actions\<close>
  shows 
    \<open>(p \<TTurnstile> \<phi>) = (p \<TTurnstile>[X] \<phi>)\<close>
proof (induct \<phi>)
  case (HMLt_conj \<Phi>)
  then show ?case 
    by (meson assms(2) cin.rep_eq HMLt_sat.simps(1,5))
next
  case (HMLt_neg \<phi>)
  then show ?case
    by (simp add: assms(2))
next
  case (HMLt_poss \<alpha> \<phi>)
  show ?case 
  proof
    assume \<open>p \<TTurnstile> HMLt_poss \<alpha> \<phi>\<close>
    with assms show \<open>p \<TTurnstile>[X] HMLt_poss \<alpha> \<phi>\<close> using HMLt_sat.simps(7) by blast
  next
    assume \<open>p \<TTurnstile>[X] HMLt_poss \<alpha> \<phi>\<close>
    hence \<open>\<alpha> \<in> X \<and> (\<exists>p'. p \<longmapsto>\<alpha> p' \<and> p' \<TTurnstile> \<phi>) \<or> \<alpha> = \<tau> \<and> (\<exists>p'. p \<longmapsto>\<tau> p' \<and> p' \<TTurnstile>[X] \<phi>) \<or> idle p X \<and> p \<TTurnstile> HMLt_poss \<alpha> \<phi>\<close>
      using HMLt_sat.simps(7) by simp+
    thus \<open>p \<TTurnstile> HMLt_poss \<alpha> \<phi>\<close> using \<open>idle p X\<close>
      by (meson UnCI assms(2) idle_no_derivatives singletonI)
  qed
next
  case (HMLt_time Y \<phi>)
  then show ?case using HMLt_sat.simps(8) assms by blast
qed
(*>*)

proposition
  assumes 
    \<open>X \<subseteq> visible_actions\<close>
    \<open>idle p X\<close>
    \<open>p \<TTurnstile> \<phi>\<close>
  shows 
    \<open>p \<TTurnstile>[X] \<phi>\<close>
  using idle_sat_lemma[OF assms(2,1)] assms(3) ..

text \<open>As the last clause of van Glabbeek definition is the main difference to the function definition of \<open>HMLt_sat\<close>, this proposition gives confidence that the original definition and the function definition correspond.\<close>

end \<comment> \<open>of \<open>context lts_timeout\<close>\<close>
(*<*)
end \<comment> \<open>of \<open>theory\<close>
(*>*)\<close>