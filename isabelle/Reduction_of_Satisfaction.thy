(*<*)
theory Reduction_of_Satisfaction
  imports
    Mapping_for_Formulas
begin
(*>*)

section \<open>Reduction of Formula Satisfaction\<close>
text \<open>\label{sec:reduction_satisfaction}\<close>

text \<open>We will show that, for a process $p$ of an \LTSt{} and a formula $\varphi$ of \HMLt{}, we have $p \vDash \varphi \iff \vartheta(p) \vDash \sigma(\varphi)$ and $p \vDash_X \varphi \iff \vartheta_X(p) \vDash \sigma(\varphi)$. The proof is rather straightforward: we use induction over \HMLt{} formulas and show that, for each case, the semantics given by van~Glabbeek's satisfaction relations and those given by the mappings $\sigma$ and $\vartheta$/$\vartheta_X$ coincide. Due to the relative complexity of the mapping and the satisfaction relations, the proof is quite tedious, however.
\vspace{-.3cm}\<close>


subsection \<open>Isabelle\<close>

text \<open>\vspace{-.4cm}
Similarly to the formalisations in \cref{sec:reduction_bisimilarity}, we begin by interpreting our transition mapping \<open>tran_theta\<close> as an \<open>lts\<close> and reassigning notation appropriately (we only care about HML formula satisfaction for $\mathbb{T}_\vartheta$, not $\mathbb{T}$).\<close>

context lts_timeout_mappable begin

interpretation lts_theta: lts tran_theta .
no_notation local.HML_sat ("_ \<Turnstile> _" [50, 50] 50)
notation lts_theta.HML_sat ("_ \<Turnstile> _" [50, 50] 50)

text \<open>We show \<open>p \<TTurnstile>?[XoN] \<phi>  \<Longleftrightarrow>  \<theta>?[XoN](p) \<Turnstile> \<sigma>(\<phi>)\<close> by induction over \<open>\<phi>\<close>. By using those terms for formula satisfaction and process mappings that handle both triggered and stable environments, we can handle both situations simultaneously, which is required due to the interdependence of $\vDash$ and $\vDash_X$. However, this requires us to consider four cases (each combination of \<open>\<TTurnstile>?[XoN\<^sub>1]\<close> and \<open>\<theta>?[XoN\<^sub>2]\<close> for \<open>XoN\<^sub>1, XoN\<^sub>2 \<in> {None, Some X}\<close>%
\footnote{Once again, we only consider cases where \<open>X \<subseteq> visible_actions\<close>.}%
) per inductive case for \<open>\<phi>\<close>. Together with the many disjunctive clauses in the mapping, a large number of cases needs to be considered, leading to a proof spanning roughly 350 lines of Isabelle code.\<close>

(* These lemmas are not important for the thesis document. *)
(*<*)
lemma\<^marker>\<open>tag (proof) unimportant\<close> sat_poss_alpha_not_special:
  assumes 
    \<open>no_special_action \<alpha>\<close>
    \<open>P \<Turnstile> \<phi>'\<close>
    \<open>\<phi>' \<in> {HML_poss \<alpha> \<sigma>(\<phi>), 
          HML_poss (\<epsilon>[visible_actions]) (HML_poss \<alpha> \<sigma>(\<phi>)),
          HML_poss t_\<epsilon> (HML_poss (\<epsilon>[visible_actions]) (HML_poss \<alpha> \<sigma>(\<phi>)))}\<close> (is \<open>\<phi>' \<in> ?disj\<close>)
  shows
    \<open>P \<Turnstile> \<sigma>(HMLt_poss \<alpha> \<phi>)\<close>
proof -
  from assms(3) have \<open>cin \<phi>' (acset ?disj)\<close> 
    by (simp add: cin.abs_eq eq_onp_same_args)
  with assms(2) have \<open>P \<Turnstile> (HML_disj (acset ?disj))\<close> using HML_sat_disj by auto
  with HMt_mapping.simps(4)[OF assms(1)] show ?thesis by simp
qed

lemma\<^marker>\<open>tag (proof) unimportant\<close> sat_time_forward:
  assumes 
    \<open>X \<subseteq> visible_actions\<close>
    \<open>P \<Turnstile> \<phi>'\<close>
    \<open>\<phi>' \<in> {HML_poss (\<epsilon>[X]) (HML_poss t \<sigma>(\<phi>)),
          HML_poss t_\<epsilon> (HML_poss (\<epsilon>[X]) (HML_poss t \<sigma>(\<phi>)))}\<close> (is \<open>\<phi>' \<in> ?disj\<close>)
  shows
    \<open>P \<Turnstile> \<sigma>(HMLt_time X \<phi>)\<close>
proof -
  from assms(3) have \<open>cin \<phi>' (acset ?disj)\<close> 
    by (simp add: cin.abs_eq eq_onp_same_args)
  with assms(2) have \<open>P \<Turnstile> (HML_disj (acset ?disj))\<close> using HML_sat_disj by auto
  with HMt_mapping.simps(6)[OF assms(1)] show ?thesis by simp
qed

lemma\<^marker>\<open>tag (proof) unimportant\<close> sat_time_backward:
  assumes 
    \<open>\<theta>?[XoN](p) \<Turnstile> \<sigma>(HMLt_time Y \<phi>)\<close>
  shows 
    \<open>Y \<subseteq> visible_actions \<and> (\<theta>?[XoN](p) \<Turnstile> HML_poss (\<epsilon>[Y]) (HML_poss t \<sigma>(\<phi>)) \<or>
    \<theta>?[XoN](p) \<Turnstile> HML_poss t_\<epsilon> (HML_poss (\<epsilon>[Y]) (HML_poss t \<sigma>(\<phi>))))\<close>
proof -
  have \<open>Y \<subseteq> visible_actions\<close>
  proof (rule ccontr)
    assume \<open>\<not> Y \<subseteq> visible_actions\<close>
    with assms have \<open>\<theta>?[XoN](p) \<Turnstile> HML_false\<close> by simp
    thus False using lts_theta.HML_sat_false by fast
  qed
  let ?disj = \<open>{HML_poss (\<epsilon>[Y]) (HML_poss t \<sigma>(\<phi>)), 
    HML_poss t_\<epsilon> (HML_poss (\<epsilon>[Y]) (HML_poss t \<sigma>(\<phi>)))}\<close>
  from assms have \<open>\<theta>?[XoN](p) \<Turnstile> HML_disj (acset ?disj)\<close> 
    using HMt_mapping.simps(6)[OF \<open>Y \<subseteq> visible_actions\<close>] by simp
  then obtain \<phi>' where \<open>cin \<phi>' (acset ?disj)\<close> \<open>\<theta>?[XoN](p) \<Turnstile> \<phi>'\<close> 
    using lts_theta.HML_sat_disj by blast
  from \<open>cin \<phi>' (acset ?disj)\<close> have \<open>\<phi>' \<in> ?disj\<close>
    by (simp add: cin.abs_eq eq_onp_same_args)
  with \<open>\<theta>?[XoN](p) \<Turnstile> \<phi>'\<close> \<open>Y \<subseteq> visible_actions\<close> show ?thesis
    by fastforce
qed

lemma\<^marker>\<open>tag (proof) unimportant\<close> triggered_env_cannot_timeout: 
  \<open>\<And> \<phi>. \<not> \<theta>(p) \<Turnstile> HML_poss t_\<epsilon> \<phi>\<close> using generation_triggered_transitions
  using distinctness_special_actions(2,6) by force

lemma\<^marker>\<open>tag (proof) unimportant\<close> stable_env_cannot_stabilise: 
  \<open>\<And> \<phi>. \<not> \<theta>[X](p) \<Turnstile> HML_poss (\<epsilon>[Y]) \<phi>\<close>
  using generation_stable_transitions distinctness_special_actions(6) 
    no_epsilon_in_tran(1) lts_theta.HML_sat.simps(3) by meson
(*>*)

lemma HMLt_sat_iff_HML_sat:
  assumes \<open>XoN = None \<or> (XoN = (Some X) \<and> X \<subseteq> visible_actions)\<close>
  shows \<open>p \<TTurnstile>?[XoN] \<phi>  \<Longleftrightarrow>  \<theta>?[XoN](p) \<Turnstile> \<sigma>(\<phi>)\<close>
  using assms
proof (induct \<phi> arbitrary: p XoN X)
  case (HMLt_conj \<Phi>)
  from HMLt_conj.prems show ?case 
  proof safe
    assume \<open>p \<TTurnstile> HMLt_conj \<Phi>\<close>
    hence \<open>\<forall>\<phi>. \<phi> \<in>\<^sub>c \<Phi> \<longrightarrow> p \<TTurnstile> \<phi>\<close> by simp
    with HMLt_conj.hyps have \<open>\<forall>\<phi>. \<phi> \<in>\<^sub>c \<Phi> \<longrightarrow> \<theta>(p) \<Turnstile> \<sigma>(\<phi>)\<close> by (simp add: cin.rep_eq)
    thus \<open>\<theta>(p) \<Turnstile> \<sigma>(HMLt_conj \<Phi>)\<close> by fastforce
  next
    assume \<open>\<theta>(p) \<Turnstile> \<sigma>(HMLt_conj \<Phi>)\<close>
    hence \<open>\<theta>(p) \<Turnstile> HML_conj (cimage (\<lambda> \<phi>. \<sigma>(\<phi>)) \<Phi>)\<close> by simp
    hence \<open>\<forall>\<phi>. cin \<phi> (cimage (\<lambda> \<phi>. \<sigma>(\<phi>)) \<Phi>) \<longrightarrow> \<theta>(p) \<Turnstile> \<phi>\<close> by simp
    hence \<open>\<forall>\<phi>. \<phi> \<in>\<^sub>c \<Phi> \<longrightarrow> \<theta>(p) \<Turnstile> \<sigma>(\<phi>)\<close> by blast
    with HMLt_conj.hyps have \<open>\<forall>\<phi>. \<phi> \<in>\<^sub>c \<Phi> \<longrightarrow> p \<TTurnstile> \<phi>\<close> by (simp add: cin.rep_eq)
    thus \<open>p \<TTurnstile> HMLt_conj \<Phi>\<close> by fastforce
  next
    fix X
    assume \<open>X \<subseteq> visible_actions\<close>
    assume \<open>p \<TTurnstile>[X] HMLt_conj \<Phi>\<close>
    hence \<open>(\<forall>\<phi>. \<phi> \<in>\<^sub>c \<Phi> \<longrightarrow> p \<TTurnstile>[X] \<phi>)\<close> by simp
    with HMLt_conj.hyps \<open>X \<subseteq> visible_actions\<close> have \<open>\<forall>\<phi>. \<phi> \<in>\<^sub>c \<Phi> \<longrightarrow> \<theta>[X](p) \<Turnstile> \<sigma>(\<phi>)\<close> 
      by (simp add: cin.rep_eq)
    thus \<open>\<theta>[X](p) \<Turnstile> (\<sigma>(HMLt_conj \<Phi>))\<close> by auto
  next
    fix X
    assume \<open>X \<subseteq> visible_actions\<close>
    assume \<open>\<theta>[X](p) \<Turnstile> \<sigma>(HMLt_conj \<Phi>)\<close>
    hence \<open>\<theta>[X](p) \<Turnstile> HML_conj (cimage (\<lambda> \<phi>. \<sigma>(\<phi>)) \<Phi>)\<close> by simp
    hence \<open>\<forall>\<phi>. cin \<phi> (cimage (\<lambda> \<phi>. \<sigma>(\<phi>)) \<Phi>) \<longrightarrow> \<theta>[X](p) \<Turnstile> \<phi>\<close> by simp
    hence \<open>\<forall>\<phi>. \<phi> \<in>\<^sub>c \<Phi> \<longrightarrow> \<theta>[X](p) \<Turnstile> \<sigma>(\<phi>)\<close> by blast
    with HMLt_conj.hyps \<open>X \<subseteq> visible_actions\<close> have \<open>\<forall>\<phi>. \<phi> \<in>\<^sub>c \<Phi> \<longrightarrow> p \<TTurnstile>[X] \<phi>\<close> by (simp add: cin.rep_eq)
    with \<open>X \<subseteq> visible_actions\<close> show \<open>p \<TTurnstile>[X] HMLt_conj \<Phi>\<close> by simp
  qed
next
  case (HMLt_neg \<phi>)
  thus ?case by auto
next
  case (HMLt_poss \<alpha> \<phi>)
  from HMLt_poss.prems show ?case
  proof safe
    assume \<open>p \<TTurnstile> HMLt_poss \<alpha> \<phi>\<close>
    hence \<open>\<exists> p'. p \<longmapsto>\<alpha> p' \<and> p' \<TTurnstile> \<phi>\<close> \<open>\<alpha> = \<tau> \<or> \<alpha> \<in> visible_actions\<close> by auto
    then obtain p' where \<open>p \<longmapsto>\<alpha> p' \<and> p' \<TTurnstile> \<phi>\<close> by blast
    with HMLt_poss.hyps have \<open>\<theta>(p') \<Turnstile> \<sigma>(\<phi>)\<close> by blast

    from \<open>\<alpha> = \<tau> \<or> \<alpha> \<in> visible_actions\<close> 
    show \<open>\<theta>(p) \<Turnstile> \<sigma>(HMLt_poss \<alpha> \<phi>)\<close>
    proof safe
      assume \<open>\<alpha> = \<tau>\<close>
      with \<open>p \<longmapsto>\<alpha> p' \<and> p' \<TTurnstile> \<phi>\<close> have \<open>\<theta>(p) \<longmapsto>\<^sup>\<theta>\<tau> \<theta>(p')\<close> using triggered_tau by simp
      with \<open>\<theta>(p') \<Turnstile> \<sigma>(\<phi>)\<close> have \<open>\<theta>(p) \<Turnstile> HML_poss \<tau> \<sigma>(\<phi>)\<close> by auto
      thus \<open>\<theta>(p) \<Turnstile> \<sigma>(HMLt_poss \<tau> \<phi>)\<close> by simp
    next
      assume \<open>\<alpha> \<in> visible_actions\<close>
      hence \<open>\<alpha> \<noteq> \<tau> \<and> \<alpha> \<noteq> t \<and> \<alpha> \<noteq> t_\<epsilon> \<and> (\<forall> X. \<alpha> \<noteq> \<epsilon>[X])\<close> 
        using no_epsilon_in_tran visible_actions_def by auto
      have \<open>\<theta>(p) \<longmapsto>\<^sup>\<theta>\<epsilon>[visible_actions] \<theta>[visible_actions](p)\<close> using env_stabilise by auto
      moreover from \<open>\<alpha> \<in> visible_actions\<close> \<open>p \<longmapsto>\<alpha> p' \<and> p' \<TTurnstile> \<phi>\<close> 
      have \<open>\<theta>[visible_actions](p) \<longmapsto>\<^sup>\<theta>\<alpha> \<theta>(p')\<close> using tran_visible by auto
      moreover note \<open>\<theta>(p') \<Turnstile> \<sigma>(\<phi>)\<close> 
      ultimately have \<open>\<theta>(p) \<Turnstile> HML_poss (\<epsilon>[visible_actions]) (HML_poss \<alpha> \<sigma>(\<phi>))\<close> by auto
      with  \<open>\<alpha> \<noteq> \<tau> \<and> \<alpha> \<noteq> t \<and> \<alpha> \<noteq> t_\<epsilon> \<and> (\<forall> X. \<alpha> \<noteq> \<epsilon>[X])\<close> show \<open>\<theta>(p) \<Turnstile> \<sigma>(HMLt_poss \<alpha> \<phi>)\<close>
        using sat_poss_alpha_not_special visible_actions_def by blast
    qed
  next
    assume \<open>\<theta>(p) \<Turnstile> \<sigma>(HMLt_poss \<alpha> \<phi>)\<close>
    have \<open>\<alpha> = \<tau> \<Longrightarrow> p \<TTurnstile> HMLt_poss \<alpha> \<phi>\<close> proof -
      assume \<open>\<alpha> = \<tau>\<close>
      with \<open>\<theta>(p) \<Turnstile> \<sigma>(HMLt_poss \<alpha> \<phi>)\<close> have \<open>\<theta>(p) \<Turnstile> HML_poss \<tau> \<sigma>(\<phi>)\<close> by simp
      then obtain p' where \<open>\<theta>(p) \<longmapsto>\<^sup>\<theta>\<tau> \<theta>(p')\<close> \<open>p \<longmapsto>\<tau> p'\<close>  \<open>\<theta>(p') \<Turnstile> \<sigma>(\<phi>)\<close>
        using generation_triggered_tau lts_theta.HML_sat.simps(3) by blast
      from HMLt_poss.hyps \<open>\<theta>(p') \<Turnstile> \<sigma>(\<phi>)\<close> have \<open>p' \<TTurnstile> \<phi>\<close> by auto
      with \<open>p \<longmapsto>\<tau> p'\<close> \<open>\<alpha> = \<tau>\<close> show \<open>p \<TTurnstile> HMLt_poss \<alpha> \<phi>\<close> by auto
    qed
    moreover have \<open>\<alpha> = t \<or> \<alpha> = t_\<epsilon> \<or> (\<exists> X. \<alpha> = \<epsilon>[X]) \<Longrightarrow> p \<TTurnstile> HMLt_poss \<alpha> \<phi>\<close> proof -
      assume \<open>\<alpha> = t \<or> \<alpha> = t_\<epsilon> \<or> (\<exists> X. \<alpha> = \<epsilon>[X])\<close>
      with \<open>\<theta>(p) \<Turnstile> \<sigma>(HMLt_poss \<alpha> \<phi>)\<close> have \<open>\<theta>(p) \<Turnstile> HML_false\<close> using HMt_mapping.simps(5) by metis 
      with lts_theta.HML_sat_false have False by simp
      thus \<open>p \<TTurnstile> HMLt_poss \<alpha> \<phi>\<close> by simp
    qed
    moreover have \<open>no_special_action \<alpha> \<Longrightarrow> p \<TTurnstile> HMLt_poss \<alpha> \<phi>\<close> proof -
      let ?disj = \<open>{HML_poss \<alpha> \<sigma>(\<phi>), 
                  HML_poss (\<epsilon>[visible_actions]) (HML_poss \<alpha> \<sigma>(\<phi>)),
                  HML_poss t_\<epsilon> (HML_poss (\<epsilon>[visible_actions]) (HML_poss \<alpha> \<sigma>(\<phi>)))}\<close>
      have \<open>countable ?disj\<close> by auto
      assume \<open>\<alpha> \<noteq> \<tau> \<and> \<alpha> \<noteq> t \<and> \<alpha> \<noteq> t_\<epsilon> \<and> (\<forall> X. \<alpha> \<noteq> \<epsilon>[X])\<close>
      with \<open>\<theta>(p) \<Turnstile> \<sigma>(HMLt_poss \<alpha> \<phi>)\<close> have \<open>\<theta>(p) \<Turnstile> HML_disj (acset ?disj)\<close> by simp
      hence \<open>\<exists> \<phi>' \<in> ?disj. \<theta>(p) \<Turnstile> \<phi>'\<close> using lts_theta.HML_sat_disj \<open>countable ?disj\<close>
        by (smt (z3) cin.abs_eq eq_onp_same_args)
      thus \<open>p \<TTurnstile> HMLt_poss \<alpha> \<phi>\<close> proof safe
        assume \<open>\<theta>(p) \<Turnstile> HML_poss \<alpha> \<sigma>(\<phi>)\<close>
        then obtain P' where \<open>\<theta>(p) \<longmapsto>\<^sup>\<theta>\<alpha> P'\<close> by auto
        hence \<open>\<alpha> = \<tau> \<or> (\<exists> X. \<alpha> = \<epsilon>[X])\<close> using generation_triggered_transitions by blast
        with \<open>\<alpha> \<noteq> \<tau> \<and> \<alpha> \<noteq> t \<and> \<alpha> \<noteq> t_\<epsilon> \<and> (\<forall> X. \<alpha> \<noteq> \<epsilon>[X])\<close> have False by auto
        thus \<open>p \<TTurnstile> HMLt_poss \<alpha> \<phi>\<close> by simp
      next
        assume \<open>\<theta>(p) \<Turnstile> HML_poss (\<epsilon>[visible_actions]) (HML_poss \<alpha> \<sigma>(\<phi>))\<close>
        hence \<open>\<theta>[visible_actions](p) \<Turnstile> HML_poss \<alpha> \<sigma>(\<phi>)\<close>
          using generation_env_stabilise injectivity_theta(2) lts_theta.HML_sat.simps(3) by blast
        then obtain P' where \<open>\<theta>[visible_actions](p) \<longmapsto>\<^sup>\<theta>\<alpha> P'\<close> \<open>P' \<Turnstile> \<sigma>(\<phi>)\<close> by auto
        with \<open>\<alpha> \<noteq> \<tau> \<and> \<alpha> \<noteq> t \<and> \<alpha> \<noteq> t_\<epsilon> \<and> (\<forall> X. \<alpha> \<noteq> \<epsilon>[X])\<close> have \<open>\<alpha> \<in> visible_actions\<close>
          using generation_stable_transitions by blast
        with \<open>\<theta>[visible_actions](p) \<longmapsto>\<^sup>\<theta>\<alpha> P'\<close>
        obtain p' where \<open>P' = \<theta>(p')\<close> \<open>p \<longmapsto>\<alpha> p'\<close> using generation_tran_visible by blast
        from \<open>P' \<Turnstile> \<sigma>(\<phi>)\<close> \<open>P' = \<theta>(p')\<close> have \<open>p' \<TTurnstile> \<phi>\<close> using HMLt_poss.hyps by blast

        with \<open>p \<longmapsto>\<alpha> p'\<close> \<open>\<alpha> \<in> visible_actions\<close> show \<open>p \<TTurnstile> HMLt_poss \<alpha> \<phi>\<close> by auto
      next
        assume \<open>\<theta>(p) \<Turnstile> HML_poss t_\<epsilon> (HML_poss (\<epsilon>[visible_actions]) (HML_poss \<alpha> \<sigma>(\<phi>)))\<close>
        then obtain P' where \<open>\<theta>(p) \<longmapsto>\<^sup>\<theta>t_\<epsilon> P'\<close> by auto
        hence False using generation_triggered_transitions distinctness_special_actions by blast
        thus \<open>p \<TTurnstile> HMLt_poss \<alpha> \<phi>\<close> by simp
      qed
    qed
    ultimately show \<open>p \<TTurnstile> HMLt_poss \<alpha> \<phi>\<close> by blast
  next
    assume \<open>X \<subseteq> visible_actions\<close>
    assume \<open>p \<TTurnstile>[X] HMLt_poss \<alpha> \<phi>\<close>
    hence \<open>\<alpha> \<in> X \<and> (\<exists>p'. p \<longmapsto>\<alpha> p' \<and> p' \<TTurnstile> \<phi>) 
      \<or> \<alpha> = \<tau> \<and> (\<exists>p'. p \<longmapsto>\<tau>  p' \<and> p' \<TTurnstile>[X] \<phi>) 
      \<or> idle p X \<and> p \<TTurnstile> HMLt_poss \<alpha> \<phi>\<close> 
      by simp
    thus \<open>\<theta>[X](p) \<Turnstile> \<sigma>(HMLt_poss \<alpha> \<phi>)\<close>
    proof (elim disjE)
      assume \<open>\<alpha> \<in> X \<and> (\<exists>p'. p \<longmapsto>\<alpha> p' \<and> p' \<TTurnstile> \<phi>)\<close>
      hence \<open>\<alpha> \<in> X\<close> \<open>\<exists>p'. p \<longmapsto>\<alpha> p' \<and> p' \<TTurnstile> \<phi>\<close> by auto

      from \<open>\<alpha> \<in> X\<close> \<open>X \<subseteq> visible_actions\<close> have \<open>\<alpha> \<noteq> \<tau> \<and> \<alpha> \<noteq> t \<and> \<alpha> \<noteq> t_\<epsilon> \<and> (\<forall>X. \<alpha> \<noteq> \<epsilon>[X])\<close>
        using no_epsilon_in_tran visible_actions_def by auto

      from \<open>\<exists>p'. p \<longmapsto>\<alpha> p' \<and> p' \<TTurnstile> \<phi>\<close> obtain p' where \<open>p \<longmapsto>\<alpha> p'\<close> \<open>p' \<TTurnstile> \<phi>\<close> by blast
      with \<open>\<alpha> \<in> X\<close> \<open>X \<subseteq> visible_actions\<close> have \<open>\<theta>[X](p) \<longmapsto>\<^sup>\<theta>\<alpha> \<theta>(p')\<close> using tran_visible by auto
      moreover from \<open>p' \<TTurnstile> \<phi>\<close> have \<open>\<theta>(p') \<Turnstile> \<sigma>(\<phi>)\<close> using HMLt_poss.hyps by auto
      ultimately have \<open>\<theta>[X](p) \<Turnstile> HML_poss \<alpha> \<sigma>(\<phi>)\<close> by auto
      thus \<open>\<theta>[X](p) \<Turnstile> \<sigma>(HMLt_poss \<alpha> \<phi>)\<close> using \<open>\<alpha> \<noteq> \<tau> \<and> \<alpha> \<noteq> t \<and> \<alpha> \<noteq> t_\<epsilon> \<and> (\<forall>X. \<alpha> \<noteq> \<epsilon>[X])\<close>
        by (metis insertCI sat_poss_alpha_not_special)
    next
      assume \<open>\<alpha> = \<tau> \<and> (\<exists>p'. p \<longmapsto>\<tau>  p' \<and> p' \<TTurnstile>[X] \<phi>)\<close>
      hence \<open>\<alpha> = \<tau>\<close> \<open>\<exists>p'. p \<longmapsto>\<tau>  p' \<and> p' \<TTurnstile>[X] \<phi>\<close> by auto
      then obtain p' where \<open>p \<longmapsto>\<tau>  p'\<close> \<open>p' \<TTurnstile>[X] \<phi>\<close> by blast
      with \<open>X \<subseteq> visible_actions\<close> have \<open>\<theta>[X](p) \<longmapsto>\<^sup>\<theta>\<tau> \<theta>[X](p')\<close> using stable_tau by auto
      moreover from \<open>p' \<TTurnstile>[X] \<phi>\<close> \<open>X \<subseteq> visible_actions\<close> have \<open>\<theta>[X](p') \<Turnstile> \<sigma>(\<phi>)\<close> using HMLt_poss.hyps by auto
      ultimately have \<open>\<theta>[X](p) \<Turnstile> HML_poss \<tau> \<sigma>(\<phi>)\<close> by auto
      thus \<open>\<theta>[X](p) \<Turnstile> \<sigma>(HMLt_poss \<alpha> \<phi>)\<close> using \<open>\<alpha> = \<tau>\<close> HMt_mapping.simps(3) by auto
    next
      assume \<open>idle p X \<and> p \<TTurnstile> HMLt_poss \<alpha> \<phi>\<close>
      hence \<open>idle p X\<close> \<open>p \<TTurnstile> HMLt_poss \<alpha> \<phi>\<close> by blast+

      from \<open>idle p X\<close> \<open>X \<subseteq> visible_actions\<close> have \<open>\<theta>[X](p) \<longmapsto>\<^sup>\<theta>t_\<epsilon> \<theta>(p)\<close>
        using env_timeout by simp
      have \<open>\<theta>(p) \<longmapsto>\<^sup>\<theta>\<epsilon>[visible_actions] \<theta>[visible_actions](p)\<close>
        using env_stabilise by simp

      from \<open>p \<TTurnstile> HMLt_poss \<alpha> \<phi>\<close> have \<open>\<alpha> \<in> visible_actions \<or> \<alpha> = \<tau>\<close> \<open>\<exists>p'. p \<longmapsto>\<alpha> p' \<and> p' \<TTurnstile> \<phi>\<close>
        by auto
      from \<open>\<exists>p'. p \<longmapsto>\<alpha> p' \<and> p' \<TTurnstile> \<phi>\<close> obtain p' where \<open>p \<longmapsto>\<alpha> p'\<close> \<open>p' \<TTurnstile> \<phi>\<close> by blast
      from \<open>\<alpha> \<in> visible_actions \<or> \<alpha> = \<tau>\<close> \<open>idle p X\<close> \<open>p \<longmapsto>\<alpha> p'\<close> have \<open>\<alpha> \<in> visible_actions\<close> 
        using initial_actions_def by auto
      from \<open>\<alpha> \<in> visible_actions\<close>
      have \<open>\<alpha> \<noteq> \<tau> \<and> \<alpha> \<noteq> t \<and> \<alpha> \<noteq> t_\<epsilon> \<and> (\<forall>X. \<alpha> \<noteq> \<epsilon>[X])\<close>
        using no_epsilon_in_tran visible_actions_def by auto

      from \<open>p \<longmapsto>\<alpha> p'\<close> \<open>\<alpha> \<in> visible_actions\<close> have \<open>\<theta>[visible_actions](p) \<longmapsto>\<^sup>\<theta>\<alpha> \<theta>(p')\<close> using tran_visible by auto
      moreover from \<open>p' \<TTurnstile> \<phi>\<close> have \<open>\<theta>(p') \<Turnstile> \<sigma>(\<phi>)\<close> using HMLt_poss.hyps by auto
      ultimately have \<open>\<theta>[visible_actions](p) \<Turnstile> HML_poss \<alpha> \<sigma>(\<phi>)\<close> by auto

      with \<open>\<theta>(p) \<longmapsto>\<^sup>\<theta>\<epsilon>[visible_actions] \<theta>[visible_actions](p)\<close>
      have \<open>\<theta>(p) \<Turnstile> HML_poss (\<epsilon>[visible_actions]) (HML_poss \<alpha> \<sigma>(\<phi>))\<close> by auto

      with \<open>\<theta>[X](p) \<longmapsto>\<^sup>\<theta>t_\<epsilon> \<theta>(p)\<close>
      have \<open>\<theta>[X](p) \<Turnstile> HML_poss t_\<epsilon> (HML_poss (\<epsilon>[visible_actions]) (HML_poss \<alpha> \<sigma>(\<phi>)))\<close> by auto

      thus \<open>\<theta>[X](p) \<Turnstile> \<sigma>(HMLt_poss \<alpha> \<phi>)\<close> using \<open>\<alpha> \<noteq> \<tau> \<and> \<alpha> \<noteq> t \<and> \<alpha> \<noteq> t_\<epsilon> \<and> (\<forall>X. \<alpha> \<noteq> \<epsilon>[X])\<close>
        by (metis insertCI sat_poss_alpha_not_special)
    qed
  next
    assume \<open>X \<subseteq> visible_actions\<close>
    assume prem: \<open>\<theta>[X](p) \<Turnstile> \<sigma>(HMLt_poss \<alpha> \<phi>)\<close>

    have \<open>\<alpha> = \<tau> \<Longrightarrow> p \<TTurnstile>[X] HMLt_poss \<alpha> \<phi>\<close> proof -
      assume \<open>\<alpha> = \<tau>\<close>
      with prem have \<open>\<theta>[X](p) \<Turnstile> HML_poss \<tau> \<sigma>(\<phi>)\<close> by auto
      hence \<open>\<exists> P'. \<theta>[X](p) \<longmapsto>\<^sup>\<theta>\<tau> P' \<and> P' \<Turnstile> \<sigma>(\<phi>)\<close> by auto
      then obtain p' where \<open>p \<longmapsto>\<tau> p'\<close> \<open>\<theta>[X](p') \<Turnstile> \<sigma>(\<phi>)\<close>
        using generation_stable_tau by blast
      from \<open>\<theta>[X](p') \<Turnstile> \<sigma>(\<phi>)\<close> have \<open>p' \<TTurnstile>[X] \<phi>\<close> 
        using HMLt_poss.hyps \<open>X \<subseteq> visible_actions\<close> by blast
      with \<open>p \<longmapsto>\<tau> p'\<close> \<open>\<alpha> = \<tau>\<close> \<open>X \<subseteq> visible_actions\<close> show \<open>p \<TTurnstile>[X] HMLt_poss \<alpha> \<phi>\<close> by auto
    qed
    moreover have \<open>\<alpha> = t \<or> \<alpha> = t_\<epsilon> \<or> (\<exists> X. \<alpha> = \<epsilon>[X]) \<Longrightarrow> p \<TTurnstile>[X] HMLt_poss \<alpha> \<phi>\<close> proof -
      assume \<open>\<alpha> = t \<or> \<alpha> = t_\<epsilon> \<or> (\<exists> X. \<alpha> = \<epsilon>[X])\<close>
      with prem have \<open>\<theta>[X](p) \<Turnstile> HML_false\<close> using HMt_mapping.simps(5) by metis
      with lts_theta.HML_sat_false have False by simp
      thus \<open>p \<TTurnstile>[X] HMLt_poss \<alpha> \<phi>\<close> by simp
    qed
    moreover have \<open>\<alpha> \<noteq> \<tau> \<and> \<alpha> \<noteq> t \<and> \<alpha> \<noteq> t_\<epsilon> \<and> (\<forall>X. \<alpha> \<noteq> \<epsilon>[X]) \<Longrightarrow> p \<TTurnstile>[X] HMLt_poss \<alpha> \<phi>\<close> proof -
      let ?disj = \<open>{HML_poss \<alpha> \<sigma>(\<phi>), 
        HML_poss (\<epsilon>[visible_actions]) (HML_poss \<alpha> \<sigma>(\<phi>)),
        HML_poss t_\<epsilon> (HML_poss (\<epsilon>[visible_actions]) (HML_poss \<alpha> \<sigma>(\<phi>)))}\<close>
      have \<open>countable ?disj\<close> by auto
      assume \<alpha>_not_special: \<open>\<alpha> \<noteq> \<tau> \<and> \<alpha> \<noteq> t \<and> \<alpha> \<noteq> t_\<epsilon> \<and> (\<forall>X. \<alpha> \<noteq> \<epsilon>[X])\<close>
      with prem have \<open>\<theta>[X](p) \<Turnstile> HML_disj (acset ?disj)\<close> using HMt_mapping.simps(5) by auto
      hence \<open>\<exists> \<phi>' \<in> ?disj. \<theta>[X](p) \<Turnstile> \<phi>'\<close> using lts_theta.HML_sat_disj \<open>countable ?disj\<close>
        by (smt (z3) cin.abs_eq eq_onp_same_args)
      thus \<open>p \<TTurnstile>[X] HMLt_poss \<alpha> \<phi>\<close> proof (safe)
        assume \<open>\<theta>[X](p) \<Turnstile> HML_poss \<alpha> \<sigma>(\<phi>)\<close>
        then obtain P' where \<open>\<theta>[X](p) \<longmapsto>\<^sup>\<theta>\<alpha> P'\<close> \<open>P' \<Turnstile> \<sigma>(\<phi>)\<close> by auto
        hence \<open>\<alpha> \<in> X\<close> using generation_stable_transitions \<alpha>_not_special by blast
        with \<open>X \<subseteq> visible_actions\<close> \<open>\<theta>[X](p) \<longmapsto>\<^sup>\<theta>\<alpha> P'\<close> obtain p' where \<open>P' = \<theta>(p')\<close> \<open>p \<longmapsto>\<alpha> p'\<close>
          using generation_tran_visible by blast
        
        from \<open>P' \<Turnstile> \<sigma>(\<phi>)\<close> \<open>P' = \<theta>(p')\<close> have \<open>p' \<TTurnstile> \<phi>\<close>
          using HMLt_poss.hyps by auto

        from \<open>\<alpha> \<in> X\<close> \<open>p \<longmapsto>\<alpha> p'\<close> \<open>p' \<TTurnstile> \<phi>\<close> show \<open>p \<TTurnstile>[X] HMLt_poss \<alpha> \<phi>\<close>
          using \<open>X \<subseteq> visible_actions\<close> by auto
      next
        assume \<open>\<theta>[X](p) \<Turnstile> HML_poss (\<epsilon>[visible_actions]) (HML_poss \<alpha> \<sigma>(\<phi>))\<close>
        then obtain P' where \<open>\<theta>[X](p) \<longmapsto>\<^sup>\<theta>\<epsilon>[visible_actions] P'\<close> by auto
        with generation_env_stabilise injectivity_theta(1) have False by metis
        thus \<open>p \<TTurnstile>[X] HMLt_poss \<alpha> \<phi>\<close> by simp
      next
        assume \<open>\<theta>[X](p) \<Turnstile> HML_poss t_\<epsilon> (HML_poss (\<epsilon>[visible_actions]) (HML_poss \<alpha> \<sigma>(\<phi>)))\<close>
        hence \<open>\<theta>(p) \<Turnstile> HML_poss (\<epsilon>[visible_actions]) (HML_poss \<alpha> \<sigma>(\<phi>))\<close> \<open>idle p X\<close>
          using generation_env_timeout by auto
        hence \<open>\<theta>[visible_actions](p) \<Turnstile> HML_poss \<alpha> \<sigma>(\<phi>)\<close>
          using generation_env_stabilise by (metis injectivity_theta(2) lts_theta.HML_sat.simps(3))
        then obtain P' where \<open>\<theta>[visible_actions](p) \<longmapsto>\<^sup>\<theta>\<alpha> P'\<close> \<open>P' \<Turnstile> \<sigma>(\<phi>)\<close> by auto
        with \<alpha>_not_special have \<open>\<alpha> \<in> visible_actions\<close> using generation_stable_transitions by blast
        with \<open>\<theta>[visible_actions](p) \<longmapsto>\<^sup>\<theta>\<alpha> P'\<close> obtain p' where \<open>P' = \<theta>(p')\<close> \<open>p \<longmapsto>\<alpha> p'\<close>
          using generation_tran_visible by blast

        from \<open>P' = \<theta>(p')\<close> \<open>P' \<Turnstile> \<sigma>(\<phi>)\<close> have \<open>p' \<TTurnstile> \<phi>\<close>
          using HMLt_poss.hyps by auto
        with \<open>p \<longmapsto>\<alpha> p'\<close> have \<open>p \<TTurnstile> HMLt_poss \<alpha> \<phi>\<close> using \<open>\<alpha> \<in> visible_actions\<close> by auto
        with \<open>idle p X\<close> \<open>X \<subseteq> visible_actions\<close> show \<open>p \<TTurnstile>[X] HMLt_poss \<alpha> \<phi>\<close> by auto
      qed
    qed
    ultimately show \<open>p \<TTurnstile>[X] HMLt_poss \<alpha> \<phi>\<close> by blast
  qed
next
  case (HMLt_time Y \<phi>)

  {
    assume \<open>\<theta>(p) \<Turnstile> \<sigma>(HMLt_time Y \<phi>)\<close>
    hence \<open>\<theta>(p) \<Turnstile> HML_poss (\<epsilon>[Y]) (HML_poss t \<sigma>(\<phi>))\<close> \<open>Y \<subseteq> visible_actions\<close> 
      using sat_time_backward triggered_env_cannot_timeout by blast+
    hence \<open>\<theta>[Y](p) \<Turnstile> HML_poss t \<sigma>(\<phi>)\<close>
      using generation_env_stabilise injectivity_theta(2) lts_theta.HML_sat.simps(3) by blast
    then obtain P' where \<open>\<theta>[Y](p) \<longmapsto>\<^sup>\<theta>t P'\<close> \<open>P' \<Turnstile> \<sigma>(\<phi>)\<close> by (simp, blast)
    from \<open>\<theta>[Y](p) \<longmapsto>\<^sup>\<theta>t P'\<close> obtain p' where \<open>P' = \<theta>[Y](p')\<close> \<open>idle p Y\<close> \<open>p \<longmapsto>t  p'\<close> 
      using generation_sys_timeout by blast
    moreover from \<open>P' = \<theta>[Y](p')\<close> \<open>P' \<Turnstile> \<sigma>(\<phi>)\<close> have \<open>p' \<TTurnstile>[Y] \<phi>\<close> 
      using HMLt_time.hyps \<open>Y \<subseteq> visible_actions\<close> by blast
    ultimately have \<open>p \<TTurnstile> HMLt_time Y \<phi>\<close> using \<open>Y \<subseteq> visible_actions\<close> by auto
  }
  note case2 = this

  from HMLt_time.prems show ?case
  proof safe
    assume \<open>p \<TTurnstile> HMLt_time Y \<phi>\<close>
    hence \<open>Y \<subseteq> visible_actions\<close> \<open>idle p Y\<close> \<open>\<exists>p'. p \<longmapsto>t  p' \<and> p' \<TTurnstile>[Y] \<phi>\<close> by auto
    then obtain p' where \<open>p \<longmapsto>t  p'\<close> \<open>p' \<TTurnstile>[Y] \<phi>\<close> by blast
    from \<open>p' \<TTurnstile>[Y] \<phi>\<close> have \<open>\<theta>[Y](p') \<Turnstile> \<sigma>(\<phi>)\<close> using HMLt_time.hyps \<open>Y \<subseteq> visible_actions\<close> by simp
    moreover have \<open>\<theta>[Y](p) \<longmapsto>\<^sup>\<theta>t \<theta>[Y](p')\<close> 
      using sys_timeout[OF \<open>Y \<subseteq> visible_actions\<close> \<open>idle p Y\<close> \<open>p \<longmapsto>t  p'\<close>] .
    ultimately have \<open>\<theta>[Y](p) \<Turnstile> HML_poss t \<sigma>(\<phi>)\<close> by auto

    moreover have \<open>\<theta>(p) \<longmapsto>\<^sup>\<theta>\<epsilon>[Y] \<theta>[Y](p)\<close> using env_stabilise[OF \<open>Y \<subseteq> visible_actions\<close>] .
    ultimately have \<open>\<theta>(p) \<Turnstile> HML_poss (\<epsilon>[Y]) (HML_poss t \<sigma>(\<phi>))\<close> by auto

    thus \<open>\<theta>(p) \<Turnstile> \<sigma>(HMLt_time Y \<phi>)\<close> using sat_time_forward[OF \<open>Y \<subseteq> visible_actions\<close>] by blast
  next
    show \<open>\<theta>(p) \<Turnstile> \<sigma>(HMLt_time Y \<phi>) \<Longrightarrow> p \<TTurnstile> HMLt_time Y \<phi>\<close> using case2 .
  next
    assume \<open>X \<subseteq> visible_actions\<close>
    assume \<open>p \<TTurnstile>[X] HMLt_time Y \<phi>\<close>

    hence \<open>idle p X\<close> \<open>p \<TTurnstile> HMLt_time Y \<phi>\<close> by simp+
    from \<open>p \<TTurnstile> HMLt_time Y \<phi>\<close> have \<open>Y \<subseteq> visible_actions\<close> \<open>idle p Y\<close> \<open>\<exists>p'. p \<longmapsto>t p' \<and> p' \<TTurnstile>[Y] \<phi>\<close>
      by auto
    then obtain p' where \<open>p \<longmapsto>t p'\<close> \<open>p' \<TTurnstile>[Y] \<phi>\<close> by blast

    have \<open>\<theta>[X](p) \<longmapsto>\<^sup>\<theta>t_\<epsilon> \<theta>(p)\<close> using env_timeout[OF \<open>X \<subseteq> visible_actions\<close> \<open>idle p X\<close>] .
    have \<open>\<theta>(p) \<longmapsto>\<^sup>\<theta>\<epsilon>[Y] \<theta>[Y](p)\<close> using env_stabilise[OF \<open>Y \<subseteq> visible_actions\<close>] .

    from \<open>p' \<TTurnstile>[Y] \<phi>\<close> have \<open>\<theta>[Y](p') \<Turnstile> \<sigma>(\<phi>)\<close> using HMLt_time.hyps \<open>Y \<subseteq> visible_actions\<close> by simp
    moreover from \<open>p \<longmapsto>t p'\<close> \<open>idle p Y\<close> have \<open>\<theta>[Y](p) \<longmapsto>\<^sup>\<theta>t \<theta>[Y](p')\<close> 
      using sys_timeout[OF \<open>Y \<subseteq> visible_actions\<close>] by simp
    ultimately have \<open>\<theta>[Y](p) \<Turnstile> HML_poss t \<sigma>(\<phi>)\<close> by auto
    with \<open>\<theta>(p) \<longmapsto>\<^sup>\<theta>\<epsilon>[Y] \<theta>[Y](p)\<close> have \<open>\<theta>(p) \<Turnstile> HML_poss (\<epsilon>[Y]) (HML_poss t \<sigma>(\<phi>))\<close> by auto
    with \<open>\<theta>[X](p) \<longmapsto>\<^sup>\<theta>t_\<epsilon> \<theta>(p)\<close> have \<open>\<theta>[X](p) \<Turnstile> HML_poss (t_\<epsilon>) (HML_poss (\<epsilon>[Y]) (HML_poss t \<sigma>(\<phi>)))\<close> by auto

    thus \<open>\<theta>[X](p) \<Turnstile> \<sigma>(HMLt_time Y \<phi>)\<close> using sat_time_forward[OF \<open>Y \<subseteq> visible_actions\<close>] by blast
  next
    assume \<open>X \<subseteq> visible_actions\<close>
    assume \<open>\<theta>[X](p) \<Turnstile> \<sigma>(HMLt_time Y \<phi>)\<close>
    hence \<open>\<theta>[X](p) \<Turnstile> HML_poss t_\<epsilon> (HML_poss (\<epsilon>[Y]) (HML_poss t \<sigma>(\<phi>)))\<close> \<open>Y \<subseteq> visible_actions\<close> 
      using sat_time_backward stable_env_cannot_stabilise by blast+
    hence \<open>\<theta>(p) \<Turnstile> HML_poss (\<epsilon>[Y]) (HML_poss t \<sigma>(\<phi>))\<close> \<open>idle p X\<close> 
      using generation_env_timeout by force+
    hence \<open>\<theta>(p) \<Turnstile> \<sigma>(HMLt_time Y \<phi>)\<close> using sat_time_forward[OF \<open>Y \<subseteq> visible_actions\<close>] by blast
    from case2[OF this] have \<open>p \<TTurnstile> HMLt_time Y \<phi>\<close> .

    thus \<open>p \<TTurnstile>[X] HMLt_time Y \<phi>\<close> using \<open>X \<subseteq> visible_actions\<close> \<open>idle p X\<close> by auto
  qed
qed

text \<open>Theorems using nicer notation are immediate consequences of this lemma.\<close>

theorem\<^marker>\<open>tag (proof) visible\<close> HMLt_sat_triggered_iff_triggered_env_HML_sat:
  shows \<open>p \<TTurnstile> \<phi>  \<Longleftrightarrow>  \<theta>(p) \<Turnstile> \<sigma>(\<phi>)\<close> 
  using HMLt_sat_iff_HML_sat by blast
theorem\<^marker>\<open>tag (proof) visible\<close> HMLt_sat_stable_iff_stable_env_HML_sat:
  assumes \<open>X \<subseteq> visible_actions\<close>
  shows \<open>p \<TTurnstile>[X] \<phi>  \<Longleftrightarrow>  \<theta>[X](p) \<Turnstile> \<sigma>(\<phi>)\<close> 
  using HMLt_sat_iff_HML_sat assms by blast

end \<comment> \<open>of \<open>context lts_timeout_mappable\<close>\<close>
(*<*)
end \<comment> \<open>of \<open>theory\<close>\<close>
(*>*)