(*<*)
theory Reduction_of_Bisimilarity
  imports
  Mapping_for_Transition_Systems
  Reactive_Bisimilarity
  Strong_Bisimilarity
begin
(*>*)

section \<open>Reduction of Bisimilarity\<close>
text \<open>\label{sec:reduction_bisimilarity}\<close>

text \<open>The main result of this section will be that two processes $p$ and $q$ of an \LTSt{} $\mathbb{T}$ are strongly reactive bisimilar (strongly $X$-bisimilar) iff the corresponding processes $\vartheta(p)$ and $\vartheta(q)$ ($\vartheta_X(p)$ and $\vartheta_X(q)$) of $\mathbb{T}_\vartheta$ are strongly bisimilar. 

We show the $\Longrightarrow$-direction first. For an SRB $\mathcal{R}$, let
$$\mathcal{S} = \{ (\vartheta(p), \vartheta(q)) \mid (p, q) \in R \} \cup \{ (\vartheta_X(p), \vartheta_X(q)) \mid (p, X, q) \in R \}.$$
We can prove that $\mathcal{S}$ is an SB, by showing that the mapping satiesfies all clauses of the definition of SBs, using the fact that $\mathcal{R}$ is an SRB as well as the rules and generation lemmas for $\rightarrow_\vartheta$. Hence, the existence of an SRB $\mathcal{R}$ with $(p, q) \in R$ implies the existence of an SB $\mathcal{S}$ with $(\vartheta(p), \vartheta(q)) \in \mathcal{S}$ (and similarly for $\vartheta_X$), so strong reactive/$X$-bisimilarity in $\mathbb{T}$ implies strong bisimilarity in $\mathbb{T}_\vartheta$.

Next, we show the $\Longleftarrow$-direction. Let
$$\mathcal{R} = \{ (p, q) \mid \vartheta(p) \leftrightarrow \vartheta(q) \} \cup \{ (p, X, q) \mid \vartheta_X(p) \leftrightarrow \vartheta_X(q) \}.$$
We can prove that $\mathcal{R}$ is an SRB, again, by showing that all clauses of the definition are satisfied. Hence, strong bisimilarity of $\vartheta(p)$ and $\vartheta(q)$ implies the existence of an SRB $\mathcal{R}$ with $(p, q) \in \mathcal{R}$ (and similarly for $\vartheta_X$), so strong bisimilarity in $\mathbb{T}_\vartheta$ implies strong reactive/$X$-bisimilarity in $\mathbb{T}$.

Thus, we have that strong reactive/$X$-bisimilarity in $\mathbb{T}$ corresponds to strong bisimilarity in $\mathbb{T}_\vartheta$.\<close>


subsection \<open>Isabelle\<close>

text \<open>We begin by \emph{interpreting} our transition mapping \<open>tran_theta\<close> as an \<open>lts\<close> and call it \<open>lts_theta\<close>. Therefore, we are handling two separate LTSs: the \LTSt{} $\mathbb{T}$ given by the local \<open>context lts_timeout_mappable\<close>, and the LTS $\mathbb{T}_\vartheta$ given by the \<open>interpretation lts_theta\<close>.
When referring to definitions involving the transition relation of \<open>lts_theta\<close>, we have to prefix them, e.g.\@ \<open>lts_theta.SB\<close> for the definition of strong bisimulations using \<open>\<longmapsto>\<^sup>\<theta>\<close> instead of \<open>\<longmapsto>\<close>.

By default, \<open>interpretation\<close>s do not import special notation, so we reassign strong bisimilarity notation \<open>\<leftrightarrow>\<close> to \<open>lts_theta\<close>, since we do not care about strong bisimilarity in $\mathbb{T}$.\<close>

context lts_timeout_mappable begin

interpretation lts_theta: lts tran_theta .
no_notation local.strongly_bisimilar (\<open>_ \<leftrightarrow> _\<close> [70, 70] 70)
notation lts_theta.strongly_bisimilar (\<open>_ \<leftrightarrow> _\<close> [70, 70] 70)


text \<open>We can now formalise the proof as described above.\<close>

subsubsection \<open>If \dots{} (\boldmath{$\Longrightarrow$})\<close>

definition SRB_mapping \<comment> \<open>$\mathcal{S}$\<close> 
  :: \<open>('s\<Rightarrow>'a set option\<Rightarrow>'s \<Rightarrow> bool) \<Rightarrow> ('ss\<Rightarrow>'ss \<Rightarrow> bool)\<close>
  where \<open>SRB_mapping R P Q \<equiv> 
    (\<exists> p q. P = \<theta>(p) \<and> Q = \<theta>(q) \<and> R p None q) \<or>
    (\<exists> p q X. P = \<theta>[X](p) \<and> Q = \<theta>[X](q) \<and> R p (Some X) q)\<close>

lemma SRB_mapping_is_SB:
  assumes \<open>SRB R\<close>
  shows \<open>lts_theta.SB (SRB_mapping R)\<close>
    (is \<open>lts_theta.SB ?S\<close>)
proof -
  {
    fix P Q P' a
    assume
      \<open>?S P Q\<close>
      \<open>P \<longmapsto>\<^sup>\<theta>a P'\<close>
    have \<open>\<exists>Q'. ?S P' Q' \<and> Q \<longmapsto>\<^sup>\<theta>a Q'\<close>
      using \<open>?S P Q\<close> unfolding SRB_mapping_def
    proof (elim disjE)
      assume \<open>\<exists>p q. P = \<theta>(p) \<and> Q = \<theta>(q) \<and> R p None q\<close>
      then obtain p q where \<open>P = \<theta>(p)\<close> \<open>Q = \<theta>(q)\<close> \<open>R p None q\<close> by blast
      from \<open>P = \<theta>(p)\<close> \<open>P \<longmapsto>\<^sup>\<theta>a P'\<close> have
        \<open>(\<exists>X. a = \<epsilon>[X] \<and> P' = \<theta>[X](p) \<and> X \<subseteq> visible_actions) \<or> a = \<tau> \<and> (\<exists>p'. p \<longmapsto>\<tau>  p')\<close>
        using generation_triggered_transitions by blast
      thus \<open>\<exists>Q'. ((\<exists>p q. P' = \<theta>(p) \<and> Q' = \<theta>(q) \<and> R p None q) 
        \<or> (\<exists>p q X. P' = \<theta>[X](p) \<and> Q' = \<theta>[X](q) \<and> R p (Some X) q)) \<and> Q \<longmapsto>\<^sup>\<theta>a Q'\<close>
      proof (auto, goal_cases)
        case (1 X)
        from \<open>X \<subseteq> visible_actions\<close> \<open>Q = \<theta>(q)\<close> have \<open>Q \<longmapsto>\<^sup>\<theta>\<epsilon>[X] \<theta>[X](q)\<close> 
        using env_stabilise by force
    
        have \<open>R p (Some X) q\<close> using SRB_ruleformat(4)[OF assms(1) \<open>R p None q\<close> \<open>X \<subseteq> visible_actions\<close>] .
    
        from \<open>P' = \<theta>[X](p)\<close> \<open>Q \<longmapsto>\<^sup>\<theta>\<epsilon>[X] \<theta>[X](q)\<close> \<open>R p (Some X) q\<close> \<open>a = \<epsilon>[X]\<close>
        show ?case by blast
      next
        case (2 p')
        have \<open>\<exists>q'. q \<longmapsto>\<tau>  q' \<and> R p' None q'\<close> using SRB_ruleformat(3)[OF assms(1) \<open>R p None q\<close> 2(2)] .
        with \<open>P = \<theta>(p)\<close> \<open>Q = \<theta>(q)\<close> \<open>R p None q\<close> show ?case
          by (metis "2"(1) assms(1) \<open>P \<longmapsto>\<^sup>\<theta>a P'\<close> generation_triggered_tau SRB_ruleformat(3) triggered_tau)
      qed
    
    next
    
      assume \<open>\<exists>p q X. P = \<theta>[X](p) \<and> Q = \<theta>[X](q) \<and> R p (Some X) q\<close>
      then obtain p q X where \<open>P = \<theta>[X](p)\<close> \<open>Q = \<theta>[X](q)\<close> \<open>R p (Some X) q\<close> by fast
      hence \<open>X \<subseteq> visible_actions\<close> using SRB_ruleformat(1)[OF assms(1)] by blast
      
      from \<open>P \<longmapsto>\<^sup>\<theta>a P'\<close> \<open>P = \<theta>[X](p)\<close> have \<open>a = t_\<epsilon> \<or> (\<exists> p'. p \<longmapsto>a p')\<close>
        using generation_stable_transitions by blast
    
      hence \<open>a = t_\<epsilon> \<or> a = \<tau> \<or> a = t \<or> a \<in> visible_actions\<close> using visible_actions_def by fast
      thus \<open>\<exists>Q'. ((\<exists>p q. P' = \<theta>(p) \<and> Q' = \<theta>(q) \<and> R p None q) \<or> (\<exists>p q X. P' = \<theta>[X](p) \<and> Q' = \<theta>[X](q) \<and> R p (Some X) q)) \<and> Q \<longmapsto>\<^sup>\<theta>a Q'\<close>
      proof (elim disjE)
        assume \<open>a = t_\<epsilon>\<close>
        with \<open>P \<longmapsto>\<^sup>\<theta>a P'\<close> \<open>P = \<theta>[X](p)\<close> have \<open>P' = \<theta>(p)\<close> \<open>idle p X\<close> using generation_env_timeout by fast+
        with \<open>R p (Some X) q\<close> have \<open>idle q X\<close>
          using assms GSRB_preserves_idleness SRB_is_GSRB by blast
        with \<open>Q = \<theta>[X](q)\<close> \<open>X \<subseteq> visible_actions\<close> have \<open>Q \<longmapsto>\<^sup>\<theta>t_\<epsilon> \<theta>(q)\<close> using env_timeout by simp
        from \<open>R p (Some X) q\<close> \<open>idle p X\<close> have \<open>R p None q\<close> using SRB_ruleformat(7)[OF assms(1)] by simp
        with \<open>P' = \<theta>(p)\<close> \<open>Q \<longmapsto>\<^sup>\<theta>t_\<epsilon> \<theta>(q)\<close> \<open>a = t_\<epsilon>\<close> show ?thesis by blast
      next
        assume \<open>a = \<tau>\<close>
        with \<open>P \<longmapsto>\<^sup>\<theta>a P'\<close> \<open>P = \<theta>[X](p)\<close> obtain p' where \<open>P' = \<theta>[X](p')\<close> \<open>p \<longmapsto>\<tau> p'\<close>
          using generation_stable_tau by blast
        with \<open>R p (Some X) q\<close> obtain q' where \<open>q \<longmapsto>\<tau> q'\<close> \<open>R p' (Some X) q'\<close>
          using SRB_ruleformat(6)[OF assms(1)] by blast
        with \<open>Q = \<theta>[X](q)\<close> \<open>X \<subseteq> visible_actions\<close> have \<open>Q \<longmapsto>\<^sup>\<theta>\<tau> \<theta>[X](q')\<close> 
          using stable_tau by blast
        with \<open>P' = \<theta>[X](p')\<close> \<open>R p' (Some X) q'\<close> \<open>a = \<tau>\<close> show ?thesis by blast
      next
        assume \<open>a = t\<close>
        with \<open>P \<longmapsto>\<^sup>\<theta>a P'\<close> \<open>P = \<theta>[X](p)\<close> obtain p' where \<open>P' = \<theta>[X](p')\<close> \<open>idle p X\<close> \<open> p \<longmapsto>t p'\<close>
          using generation_sys_timeout by blast
        with \<open>R p (Some X) q\<close> obtain q' where \<open>q \<longmapsto>t q'\<close> \<open>R p' (Some X) q'\<close>
          using SRB_ruleformat(8)[OF assms(1)] by blast
        from \<open>idle p X\<close> \<open>R p (Some X) q\<close> have \<open>idle q X\<close>
          using assms GSRB_preserves_idleness SRB_is_GSRB by blast
        from \<open>q \<longmapsto>t q'\<close> \<open>Q = \<theta>[X](q)\<close> \<open>X \<subseteq> visible_actions\<close> \<open>idle q X\<close> have \<open>Q \<longmapsto>\<^sup>\<theta>t \<theta>[X](q')\<close> 
          using sys_timeout by blast
        with \<open>P' = \<theta>[X](p')\<close> \<open>R p' (Some X) q'\<close> \<open>a = t\<close> show ?thesis by blast
      next
        thm SRB_ruleformat
        assume \<open>a \<in> visible_actions\<close>
        with \<open>P \<longmapsto>\<^sup>\<theta>a P'\<close> \<open>P = \<theta>[X](p)\<close> obtain p' where \<open>a \<in> X\<close> \<open>P' = \<theta>(p')\<close> \<open>p \<longmapsto>a p'\<close> 
          using generation_tran_visible by blast
        with \<open>R p (Some X) q\<close> obtain q' where \<open>q \<longmapsto>a q'\<close> \<open>R p' None q'\<close>
          using SRB_ruleformat(5)[OF assms(1)] by blast
        with \<open>Q = \<theta>[X](q)\<close> \<open>X \<subseteq> visible_actions\<close> \<open>a \<in> X\<close> have \<open>Q \<longmapsto>\<^sup>\<theta>a \<theta>(q')\<close>
          using tran_visible by blast
        with \<open>P' = \<theta>(p')\<close> \<open>R p' None q'\<close> show ?thesis by blast
      qed
    qed
  }
  note SB_property_half = this

  have SRB_mapping_symmetry: 
    \<open>\<And> P Q. SRB R \<and> ?S P Q \<Longrightarrow> ?S Q P\<close>
    using assms SRB_mapping_def SRB_ruleformat(2) by (smt (verit, best))

  show \<open>lts_theta.SB ?S\<close> unfolding lts_theta.SB_def
    using assms SB_property_half SRB_mapping_symmetry by blast
qed

lemma srby_implies_sby:
  assumes \<open>p \<leftrightarrow>\<^sub>r q\<close> 
  shows \<open>\<theta>(p) \<leftrightarrow> \<theta>(q)\<close>
  using assms
  by (metis SRB_mapping_def SRB_mapping_is_SB lts_theta.strongly_bisimilar_def strongly_reactive_bisimilar_def)

lemma sxby_implies_sby:
  assumes \<open>p \<leftrightarrow>\<^sub>r\<^sup>X q\<close> 
  shows \<open>\<theta>[X](p) \<leftrightarrow> \<theta>[X](q)\<close>
  using assms
  by (metis SRB_mapping_def SRB_mapping_is_SB strongly_X_bisimilar_def lts_theta.strongly_bisimilar_def)


subsubsection \<open>\dots{} and only if (\boldmath{$\Longleftarrow$})\<close>

definition strong_bisimilarity_mapping \<comment> \<open>$\mathcal{R}$\<close>
  :: \<open>'s\<Rightarrow>'a set option\<Rightarrow>'s \<Rightarrow> bool\<close>
  where \<open>(strong_bisimilarity_mapping) p XoN q 
    \<equiv> (XoN = None \<and> (\<theta>(p)) \<leftrightarrow> (\<theta>(q))) \<or>
    (\<exists> X. XoN = Some X \<and> X \<subseteq> visible_actions \<and> (\<theta>[X](p)) \<leftrightarrow> (\<theta>[X](q)))\<close>

lemma strong_bisimilarity_mapping_is_SRB:
  shows \<open>SRB strong_bisimilarity_mapping\<close>
    (is \<open>SRB ?R\<close>)
  unfolding SRB_def
proof (safe)
  fix p XoN q
  assume \<open>?R p XoN q\<close>
  thus \<open>?R q XoN p\<close> using lts_theta.strongly_bisimilar_symm unfolding strong_bisimilarity_mapping_def by blast
next
  fix p X q x
  assume \<open>?R p (Some X) q\<close> \<open>x \<in> X\<close>
  thus \<open>x \<in> visible_actions\<close> unfolding strong_bisimilarity_mapping_def by auto
next
  fix p q p'
  assume \<open>?R p None q\<close> \<open>p \<longmapsto>\<tau> p'\<close>

  from \<open>?R p None q\<close> have \<open>(\<theta>(p)) \<leftrightarrow> (\<theta>(q))\<close> 
    unfolding strong_bisimilarity_mapping_def by auto
  from \<open>p \<longmapsto>\<tau> p'\<close> have \<open>\<theta>(p) \<longmapsto>\<^sup>\<theta>\<tau> \<theta>(p')\<close>
    using triggered_tau by blast
  with \<open>\<theta>(p) \<leftrightarrow> \<theta>(q)\<close> obtain Q' where \<open>\<theta>(q) \<longmapsto>\<^sup>\<theta>\<tau> Q'\<close> \<open>\<theta>(p') \<leftrightarrow> Q'\<close>
    using lts_theta.strongly_bisimilar_step by blast
  then obtain q' where \<open>Q' = \<theta>(q') \<and> q \<longmapsto>\<tau> q'\<close>
    using generation_triggered_tau by blast
  with \<open>\<theta>(p') \<leftrightarrow> Q'\<close> have \<open>\<exists> q'. q \<longmapsto>\<tau> q' \<and> \<theta>(p') \<leftrightarrow> \<theta>(q')\<close> by fast
  with \<open>p \<longmapsto>\<tau> p'\<close> show \<open>\<exists>q'. q \<longmapsto>\<tau>  q' \<and> ?R p' None q'\<close> 
    using strong_bisimilarity_mapping_def by auto
next
  fix p q X
  assume \<open>?R p None q\<close> \<open>X \<subseteq> visible_actions\<close>
  from \<open>?R p None q\<close> have \<open>\<theta>(p) \<leftrightarrow> \<theta>(q)\<close> using strong_bisimilarity_mapping_def by simp
  have \<open>\<theta>(p) \<longmapsto>\<^sup>\<theta>\<epsilon>[X] \<theta>[X](p)\<close> using env_stabilise[OF \<open>X \<subseteq> visible_actions\<close>] .
  with \<open>\<theta>(p) \<leftrightarrow> \<theta>(q)\<close> obtain Q' where \<open>\<theta>(q) \<longmapsto>\<^sup>\<theta>\<epsilon>[X] Q'\<close> \<open>\<theta>[X](p) \<leftrightarrow> Q'\<close> 
    using lts_theta.strongly_bisimilar_step(1) by blast
  from \<open>\<theta>(q) \<longmapsto>\<^sup>\<theta>\<epsilon>[X] Q'\<close> have \<open>Q' = \<theta>[X](q)\<close>
    using generation_env_stabilise injectivity_theta(2) by blast
  with \<open>\<theta>[X](p) \<leftrightarrow> Q'\<close> have \<open>\<theta>[X](p) \<leftrightarrow> \<theta>[X](q)\<close> by simp
  thus \<open>?R p (Some X) q\<close> using strong_bisimilarity_mapping_def \<open>X \<subseteq> visible_actions\<close> by simp
next
  fix p X q p' a
  assume \<open>?R p (Some X) q\<close> \<open>p \<longmapsto>a p'\<close> \<open>a \<in> X\<close>
  hence \<open>\<theta>[X](p) \<leftrightarrow> \<theta>[X](q)\<close> \<open>X \<subseteq> visible_actions\<close> using strong_bisimilarity_mapping_def by blast+
  from \<open>p \<longmapsto>a p'\<close> \<open>X \<subseteq> visible_actions\<close> \<open>a \<in> X\<close> have \<open>\<theta>[X](p) \<longmapsto>\<^sup>\<theta>a \<theta>(p')\<close> 
    using tran_visible by blast
  with \<open>\<theta>[X](p) \<leftrightarrow> \<theta>[X](q)\<close> have \<open>\<exists> Q'. \<theta>[X](q) \<longmapsto>\<^sup>\<theta>a Q' \<and> \<theta>(p') \<leftrightarrow> Q'\<close>
    using lts_theta.strongly_bisimilar_step(1) by blast
  then obtain Q' where \<open>\<theta>[X](q) \<longmapsto>\<^sup>\<theta>a Q'\<close> \<open>\<theta>(p') \<leftrightarrow> Q'\<close> by blast
  hence \<open>\<exists> q'. Q' = \<theta>(q') \<and> q \<longmapsto>a q'\<close> using generation_tran_visible \<open>a \<in> X\<close> \<open>X \<subseteq> visible_actions\<close> by blast
  with \<open>\<theta>(p') \<leftrightarrow> Q'\<close> show \<open>\<exists>q'. q \<longmapsto>a q' \<and> ?R p' None q'\<close> using strong_bisimilarity_mapping_def by blast
next
  fix p X q p'
  assume \<open>?R p (Some X) q\<close> \<open>p \<longmapsto>\<tau>  p'\<close>
  hence \<open>\<theta>[X](p) \<leftrightarrow> \<theta>[X](q)\<close> \<open>X \<subseteq> visible_actions\<close> using strong_bisimilarity_mapping_def by blast+
  from \<open>p \<longmapsto>\<tau>  p'\<close> \<open>X \<subseteq> visible_actions\<close> have \<open>\<theta>[X](p) \<longmapsto>\<^sup>\<theta>\<tau> \<theta>[X](p')\<close> 
    using stable_tau by blast
  with \<open>\<theta>[X](p) \<leftrightarrow> \<theta>[X](q)\<close> have \<open>\<exists> Q'. \<theta>[X](q) \<longmapsto>\<^sup>\<theta>\<tau> Q' \<and> \<theta>[X](p') \<leftrightarrow> Q'\<close>
    using lts_theta.strongly_bisimilar_step(1) by blast
  then obtain Q' where \<open>\<theta>[X](q) \<longmapsto>\<^sup>\<theta>\<tau> Q'\<close> \<open>\<theta>[X](p') \<leftrightarrow> Q'\<close> by blast
  hence \<open>\<exists> q'. Q' = \<theta>[X](q') \<and> q \<longmapsto>\<tau>  q'\<close> using generation_stable_tau \<open>X \<subseteq> visible_actions\<close> by blast
  with \<open>\<theta>[X](p') \<leftrightarrow> Q'\<close> show \<open>\<exists>q'. q \<longmapsto>\<tau>  q' \<and> ?R p' (Some X) q'\<close> 
    using strong_bisimilarity_mapping_def \<open>X \<subseteq> visible_actions\<close> by blast
next
  fix p X q
  assume \<open>?R p (Some X) q\<close> \<open>idle p X\<close>
  hence \<open>\<theta>[X](p) \<leftrightarrow> \<theta>[X](q)\<close> \<open>X \<subseteq> visible_actions\<close> using strong_bisimilarity_mapping_def by blast+
  from \<open>X \<subseteq> visible_actions\<close> \<open>idle p X\<close> have \<open>\<theta>[X](p) \<longmapsto>\<^sup>\<theta>t_\<epsilon> \<theta>(p)\<close> 
    using env_timeout by blast
  with \<open>\<theta>[X](p) \<leftrightarrow> \<theta>[X](q)\<close> have \<open>\<exists> Q'. \<theta>[X](q) \<longmapsto>\<^sup>\<theta>t_\<epsilon> Q' \<and> \<theta>(p) \<leftrightarrow> Q'\<close>
    using lts_theta.strongly_bisimilar_step(1) by blast
  then obtain Q' where \<open>\<theta>[X](q) \<longmapsto>\<^sup>\<theta>t_\<epsilon> Q'\<close> \<open>\<theta>(p) \<leftrightarrow> Q'\<close> by blast
  have \<open>Q' = \<theta>(q)\<close> using generation_env_timeout[OF \<open>\<theta>[X](q) \<longmapsto>\<^sup>\<theta>t_\<epsilon> Q'\<close>] ..
  with \<open>\<theta>(p) \<leftrightarrow> Q'\<close> show \<open>?R p None q\<close> using strong_bisimilarity_mapping_def by auto
next
  fix p X q p'
  assume \<open>?R p (Some X) q\<close> \<open>idle p X\<close> \<open>p \<longmapsto>t  p'\<close>
  hence \<open>\<theta>[X](p) \<leftrightarrow> \<theta>[X](q)\<close> \<open>X \<subseteq> visible_actions\<close> using strong_bisimilarity_mapping_def by blast+
  from \<open>p \<longmapsto>t  p'\<close> \<open>X \<subseteq> visible_actions\<close> \<open>idle p X\<close> have \<open>\<theta>[X](p) \<longmapsto>\<^sup>\<theta>t \<theta>[X](p')\<close> 
    using sys_timeout by blast
  with \<open>\<theta>[X](p) \<leftrightarrow> \<theta>[X](q)\<close> have \<open>\<exists> Q'. \<theta>[X](q) \<longmapsto>\<^sup>\<theta>t Q' \<and> \<theta>[X](p') \<leftrightarrow> Q'\<close>
    using lts_theta.strongly_bisimilar_step(1) by blast
  then obtain Q' where \<open>\<theta>[X](q) \<longmapsto>\<^sup>\<theta>t Q'\<close> \<open>\<theta>[X](p') \<leftrightarrow> Q'\<close> by blast
  hence \<open>\<exists> q'. Q' = \<theta>[X](q') \<and> q \<longmapsto>t  q' \<and> idle q X\<close> using generation_sys_timeout \<open>X \<subseteq> visible_actions\<close> by blast
  with \<open>\<theta>[X](p') \<leftrightarrow> Q'\<close> show \<open>\<exists>q'. q \<longmapsto>t  q' \<and> ?R p' (Some X) q'\<close> 
    using strong_bisimilarity_mapping_def \<open>X \<subseteq> visible_actions\<close> by blast
qed

lemma sby_implies_srby:
  assumes \<open>\<theta>(p) \<leftrightarrow> \<theta>(q)\<close> 
  shows \<open>p \<leftrightarrow>\<^sub>r q\<close>
  using assms strong_bisimilarity_mapping_is_SRB
  using strong_bisimilarity_mapping_def strongly_reactive_bisimilar_def by auto

lemma sby_implies_sxby:
  assumes \<open>\<theta>[X](p) \<leftrightarrow> \<theta>[X](q)\<close> \<open>X \<subseteq> visible_actions\<close>
  shows \<open>p \<leftrightarrow>\<^sub>r\<^sup>X q\<close> using assms strong_bisimilarity_mapping_is_SRB
  using strong_bisimilarity_mapping_def strongly_X_bisimilar_def by auto

text \<open>We need to include the assumption \<open>X \<subseteq> visible_actions\<close>, since for \<open>\<not> X \<subseteq> visible_actions\<close>, \<open>\<theta>[X](p)\<close> and \<open>\<theta>[X](q)\<close> might be identical (since we do not require injectivity for that subset of the domain), so \<open>\<theta>[X](p) \<leftrightarrow> \<theta>[X](q)\<close> would be true, whereas \<open>p \<leftrightarrow>\<^sub>r\<^sup>X q\<close> would be false (since \<open>X \<subseteq> visible_actions\<close> is part of the definition of SRBs).\<close>


subsubsection \<open>Iff (\boldmath{$\Longleftrightarrow$})\<close>

theorem\<^marker>\<open>tag (proof) visible\<close> strongly_reactive_bisimilar_iff_theta_strongly_bisimilar:
  shows \<open>p \<leftrightarrow>\<^sub>r q  \<Longleftrightarrow>  \<theta>(p) \<leftrightarrow> \<theta>(q)\<close>
  using sby_implies_srby srby_implies_sby by fast

theorem\<^marker>\<open>tag (proof) visible\<close> strongly_X_bisimilar_iff_theta_X_strongly_bisimilar:
  assumes \<open>X \<subseteq> visible_actions\<close>
  shows \<open>p \<leftrightarrow>\<^sub>r\<^sup>X q  \<Longleftrightarrow>  \<theta>[X](p) \<leftrightarrow> \<theta>[X](q)\<close>
  using sxby_implies_sby sby_implies_sxby assms by fast


end \<comment> \<open>of \<open>context lts_timeout_mappable\<close>\<close>
(*<*)
end \<comment> \<open>of \<open>theory\<close>\<close>
(*>*)