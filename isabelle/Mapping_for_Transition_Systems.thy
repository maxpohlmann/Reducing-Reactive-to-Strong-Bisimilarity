(*<*)
theory Mapping_for_Transition_Systems
  imports
    Labelled_Transition_Systems_with_TimeOuts
begin
(*>*)

section \<open>A Mapping for Transition Systems\<close>
text \<open>\label{sec:mapping_lts}\<close>

text \<open>Let $\mathbb{T} = (\Proc, \Act, \rightarrow)$ be an \LTSt{}. Let $A = \Act \!\setminus\! \{\tau, t\}$.

In reference to van~Glabbeek's $\theta_X$-operators, I introduce a family of operators $\vartheta_X$ with similar but not identical semantics. Additionally, I introduce the operator $\vartheta$ that places a process in an indeterminate environment.

Furthermore, I introduce a family of special actions $\varepsilon_X$ for $X \subseteq A$ that represent a triggered environment stabilising into an environment~$X$, as well as a special action $t_\varepsilon$ that represents a time-out of the environment.

We assume that $t_\varepsilon \notin \Act$ and $\forall X \subseteq A.\; \varepsilon_X \notin \Act$. 

Then we define $\mathbb{T}_\vartheta = (\Proc_\vartheta, \Act_\vartheta, \rightarrow_\vartheta)$ with
\begin{align*}
    \Proc_\vartheta &= \{ \vartheta(p) \mid p \in \Proc \} \cup \{ \vartheta_X(p) \mid p \in \Proc \wedge X \subseteq A \}, \\
    \Act_\vartheta &= \Act \cup \{t_\varepsilon\} \cup \{ \varepsilon_X \mid X \subseteq A \},
\end{align*}
and $\rightarrow_\vartheta$ defined by the following rules:

$$
(1)\,\frac{}{\vartheta(p) \xrightarrow{\varepsilon_X}_\vartheta \vartheta_X(p)} \; X \subseteq A
\qquad
(2)\,\frac{p \xrightarrow{\tau} p'}{\vartheta(p) \xrightarrow{\tau}_\vartheta \vartheta(p')}
$$
\\[-5pt]
$$
(3)\,\frac{p \not\xrightarrow{\alpha} \text{ for all } \alpha \in X \cup \{\tau\}}
{\vartheta_X(p) \xrightarrow{t_\varepsilon}_\vartheta \vartheta(p)}
$$
\\[-5pt]
$$
(4)\,\frac{p \xrightarrow{a} p'}{\vartheta_X(p) \xrightarrow{a}_\vartheta \vartheta(p')} \; a \in X
\qquad
(5)\,\frac{p \xrightarrow{\tau} p'}{\vartheta_X(p) \xrightarrow{\tau}_\vartheta \vartheta_X(p')}
$$
\\[-5pt]
$$
(6)\,\frac{p \not\xrightarrow{\alpha} \text{ for all } \alpha \in X \cup \{\tau\} \quad p \xrightarrow{t} p'}
{\vartheta_X(p) \xrightarrow{t}_\vartheta \vartheta_X(p')}
$$\\

These rules are motivated by the intuitions developed in \cref{sec:reactive_bisimilarity}:

\begin{enumerate}[nosep]
    \item indeterminate environments can stabilise into arbitrary stable \linebreak environments~$X$ for $X \subseteq A$,
    \item $\tau$-transitions can be performed regardless of the environment,
    \item if the underlying system is idle, the environment may time-out and turn into an indeterminate/triggered environment,
    \item facilitated visible transitions can be performed and can trigger a change in the environment,
    \item $\tau$-transitions cannot be observed by the environment and hence cannot trigger a change,
    \item if the underlying system is idle and has a $t$-transition, the transition may be performed and is not observable by the environment.
\end{enumerate}

\example{%
The \LTSt{} on the left (with $\Act = \{a,\tau,t\}$) gets mapped to the LTS on the right. States that have no incoming or outgoing transitions other than $\varepsilon_X$ or $t_\varepsilon$ are omitted. Note how $\vartheta(p_4)$ is not reachable from $\vartheta(p)$.

\phantomsection
\label{fig:mapping_example}
\scalebox{.9}{\vbox{\lts{
    \node[state]    (P)                             {$p$};
    \node[state]    (Q) [below left of=P]           {$p_1$};
    \node[state]    (R) [below right of=P]          {$p_2$};
    \node[state]    (S) [below left of=R]           {$p_3$};
    \node[state]    (T) [below right of=R]          {$p_4$};
    
    \path   (P) edge node[above left]               {$a$}               (Q)
                edge node[above right]              {$t$}               (R)
            (R) edge node[above left]               {$\tau$}            (S)
                edge node[above right]              {$a$}               (T);


    \node[state]    (Pt) [right of=P, xshift=4.5cm] {$\vartheta(p)$};
    \node[state]    (Pa) [below left of=Pt]         {$\vartheta_{\{a\}}(p)$};
    \node[state]    (Pe) [below right of=Pt]        {$\vartheta_\emptyset(p)$};
    \node[state]    (Rt) [right of=Pe]              {$\vartheta(p_2)$};
    \node[state]    (Qt) [below of=Pa]              {$\vartheta(p_1)$};
    \node[state]    (Re) [below of=Pe]              {$\vartheta_\emptyset(p_2)$};
    \node[state]    (Se) [below of=Re]              {$\vartheta_\emptyset(p_3)$};
    \node[state]    (Ra) [below of=Rt,xshift=1.8cm] {$\vartheta_{\{a\}}(p_2)$};
    \node[state]    (Tt) [right of=Ra,xshift=.7cm]  {$\vartheta(p_4)$};
    \node[state]    (Sa) [below of=Ra]              {$\vartheta_{\{a\}}(p_3)$};
    \node[state]    (St) [right of=Se,yshift=-2cm]  {$\vartheta(p_3)$};
    
    \path   (Pt)    edge node[above left]           {$\varepsilon_{\{a\}}$}     (Pa)
            (Pt)    edge node[left]                 {$\varepsilon_\emptyset$}   (Pe)
            (Pe)    edge[bend right] node[right]    {$t_\varepsilon$}           (Pt)
            (Pa)    edge node[left]                 {$a$}                       (Qt)
            (Pe)    edge node[left]                 {$t$}                       (Re)
            (Re)    edge node[left]                 {$\tau$}                    (Se)
            (Rt)    edge node[right]                {$\varepsilon_{\{a\}}$}     (Ra)
            (Rt)    edge node[left]                 {$\varepsilon_\emptyset$}   (Re)
            (Ra)    edge node[above]                {$a$}                       (Tt)
            (Ra)    edge node[left]                 {$\tau$}                    (Sa)
            (Se)    edge node[above]                {$t_\varepsilon$}           (St)
            (St)    edge[bend left] node[left]      {$\varepsilon_\emptyset$}   (Se)
            (Sa)    edge node[above]                {$t_\varepsilon$}           (St)
            (St)    edge[bend right] node[right]    {$\varepsilon_{\{a\}}$}   (Sa)
            (Rt)    edge node[right]                {$\tau$}                    (St);
            
    \coordinate [below of=Qt,yshift=10pt] (Qc);
    \coordinate [below of=Tt,yshift=10pt] (Tc);
            
    \draw [dotted,->,shorten >= 7pt] (Qt) to[bend right] node[left] {$\varepsilon_{\dots}$} (Qc);
    \draw [dotted,->,shorten <= 7pt] (Qc) to[bend right] node[right] {$t_\varepsilon$} (Qt);
    \draw [dotted,->,shorten >= 7pt] (Tt) to[bend right] node[left] {$\varepsilon_{\dots}$} (Tc);
    \draw [dotted,->,shorten <= 7pt] (Tc) to[bend right] node[right] {$t_\varepsilon$} (Tt);
}}}}
\vspace{-1cm}\<close>


subsection \<open>Isabelle\<close>

subsubsection \<open>Formalising \boldmath{$\Proc_\vartheta$} and \boldmath{$\Act_\vartheta$}\<close>

text \<open>We specify another locale based on \<open>lts_timeout\<close>, where the aforementioned special actions and operators are considered; we call it \<open>lts_timeout_mappable\<close>. 
Since $\Proc \cap \Proc_\vartheta = \emptyset$, we introduce a new type variable \<open>'ss\<close> for $\Proc_\vartheta$, but use \<open>'a\<close> for both $\Act$ and $\Act_\vartheta$.
We formalise the family of special actions $\varepsilon_X$ as a mapping \<open>\<epsilon>[_] :: 'a set \<Rightarrow> 'a\<close>, and the environment operators $\vartheta$/$\vartheta_X$ as a single mapping \<open>\<theta>?[_](_) :: 'a set option \<Rightarrow> 's \<Rightarrow> 'ss\<close>.

As for \<open>lts_timeout\<close> in \cref{sec:LTSt}, we require that all special actions are distinct, formalised by the first set of assumptions \<open>distinctness_special_actions\<close>.

As an operator, the term $\vartheta_X(p)$ simply refers to the state $p$ in an environment~$X$; when understood as a mapping, we have to be more careful, since \<open>\<theta>?[Some X](p)\<close> is now itself a state. Specifically, we have to assume that \<open>\<theta>?[_](_)\<close> is injective (when restricted to domains where \<open>X \<subseteq> visible_actions\<close>, because $\vartheta_X$ is only defined for those $X \subseteq A$). Otherwise, we might have \<open>\<theta>?[None](p) = \<theta>?[None](q)\<close> for \<open>p \<noteq> q\<close>, which is problematic if e.g.\@ \<open>p\<close> has a \<open>\<tau>\<close>-transition, but \<open>q\<close> does not.
Hence, the (restricted) injectivity of \<open>\<theta>?[_](_)\<close> is formalised as the set of assumptions \<open>injectivity_theta\<close>.

The same is required for the mapping \<open>\<epsilon>[_]\<close>, as formalised in the last clause of the set of assumptions \<open>distinctness_special_actions\<close> (the (restricted) injectivity of \<open>\<epsilon>[_]\<close> is part of the requirement that all special actions must be distinct). Again, we only require injectivity for the mapping restricted to the domain \<open>visible_actions\<close>. If we required that \<open>\<epsilon>[_] :: 'a set \<Rightarrow> 'a\<close> were injective over its entire domain \<open>'a set\<close>, we would run into problems, since such a function cannot exist by Cantor's theorem.

That such mappings exist is intuitively clear, whence there were no ambiguities when defining them as operators in the prosaic/mathematical section above. Formalising these mappings in HOL, however, is not so straight\-forward: as operators, we assume that they are only defined for certain parameters; in HOL, every mapping must be total. For now, we simply assume that such total functions that formalise these operators exist. Doing this significantly improves the readability of following sections, since we must only consider the relevant properties of the mappings given by the assumptions. In \cref{chap:example_instantiation}, I give examples for these mappings and show that, together with these, any \<open>lts_timeout\<close> can be interpreted as an \<open>lts_timeout_mappable\<close>, i.e.\@ every \LTSt{} $\mathbb{T}$ can be mapped to an LTS $\mathbb{T}_\vartheta$.

Lastly, we formalise our requirements $t_\varepsilon \notin \Act$ and $\forall X \subseteq A.\; \varepsilon_X \notin \Act$ as the last set of assumptions \<open>no_epsilon_in_tran\<close>. Technically, these assumptions only state that the $\varepsilon$-actions do not label any transition of $\mathbb{T}$. However, we can assume that 
$\Act = \{ \alpha \mid \exists p, p'.\; p \xrightarrow{\alpha} p' \}$, 
since actions that do not label any transitions are not relevant to the behaviour of an LTS.\<close>

locale lts_timeout_mappable = lts_timeout tran \<tau> t 
  for tran :: "'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool" 
      ("_ \<longmapsto>_ _" [70, 70, 70] 80) 
    and \<tau> :: 'a 
    and t :: 'a +
  fixes t_\<epsilon> :: 'a 
    and stabilise :: \<open>'a set \<Rightarrow> 'a\<close> 
      (\<open>\<epsilon>[_]\<close>) 
    and in_env :: \<open>'a set option \<Rightarrow> 's \<Rightarrow> 'ss\<close> 
      (\<open>\<theta>?[_]'(_')\<close>)
  assumes
    distinctness_special_actions:
    \<open>\<tau> \<noteq> t\<close> \<open>\<tau> \<noteq> t_\<epsilon>\<close> \<open>t \<noteq> t_\<epsilon>\<close>
    \<open>\<epsilon>[X] \<noteq> \<tau>\<close> \<open>\<epsilon>[X] \<noteq> t\<close> \<open>\<epsilon>[X] \<noteq> t_\<epsilon>\<close> 
    \<open>X \<subseteq> visible_actions \<Longrightarrow> \<epsilon>[X] = \<epsilon>[Y] \<Longrightarrow> X = Y\<close>
    and
    
    injectivity_theta:
    \<open>\<theta>?[None](p) \<noteq> \<theta>?[Some X](q)\<close>
    \<open>(\<theta>?[None](p) = \<theta>?[None](q)) \<longrightarrow> p = q\<close>
    \<open>X \<subseteq> visible_actions \<Longrightarrow> 
      (\<theta>?[Some X](p) = \<theta>?[Some Y](q)) \<longrightarrow> X = Y \<and> p = q\<close>
    and

    no_epsilon_in_tran:
    \<open>\<not> p \<longmapsto>\<epsilon>[X] q\<close>
    \<open>\<not> p \<longmapsto>t_\<epsilon> q\<close>
begin

text \<open>We can now define abbreviations with notations that correspond more closely to our operators defined above.\<close>

abbreviation triggered_env :: \<open>'s \<Rightarrow> 'ss\<close> 
  (\<open>\<theta>'(_')\<close>)
  where \<open>\<theta>(p) \<equiv> \<theta>?[None](p)\<close>
abbreviation stable_env :: \<open>'a set \<Rightarrow> 's \<Rightarrow> 'ss\<close> 
  (\<open>\<theta>[_]'(_')\<close>)
  where \<open>\<theta>[X](p) \<equiv> \<theta>?[Some X](p)\<close>

(* This abbreviation and this lemma are not important for the thesis document. *)
(*<*)
abbreviation\<^marker>\<open>tag unimportant\<close> no_special_action :: \<open>'a \<Rightarrow> bool\<close>
  where \<open>no_special_action \<alpha> 
    \<equiv> \<alpha> \<noteq> \<tau> \<and> \<alpha> \<noteq> t \<and> \<alpha> \<noteq> t_\<epsilon> \<and> (\<forall> X. \<alpha> \<noteq> \<epsilon>[X])\<close>

lemma\<^marker>\<open>tag (proof) unimportant\<close> special_actions_invisible:
  assumes \<open>X \<subseteq> visible_actions\<close> \<open>\<alpha> \<in> X\<close>
  shows \<open>no_special_action \<alpha>\<close>
  using assms(1) assms(2) no_epsilon_in_tran(1) no_epsilon_in_tran(2) visible_actions_def by auto
(*>*)

subsubsection \<open>Formalising \boldmath{$\rightarrow_\vartheta$}\<close>
text \<open>We formalise the transition relation of our mapping, given above by the structural operational rules, as a function \<open>tran_theta\<close>.% 
\footnote{We use the notation \<open>_ \<longmapsto>\<^sup>\<theta>_ _\<close> instead of the more obvious \<open>_ \<longmapsto>\<^sub>\<theta>_ _\<close> simply because of better readability.}

We use the \<open>inductive\<close> command, because this allows us to define separate clauses (as opposed to the \<open>definition\<close> command). Technically speaking, however, this inductive definition only has base cases, since none of the premises involves \<open>\<longmapsto>\<^sup>\<theta>\<close>.

It should be easy to see that the clauses below correspond directly to the rules above. Like in previous sections, we have to take extra care to handle the requirement \<open>X \<subseteq> visible_actions\<close>.\<close>

inductive tran_theta :: \<open>'ss \<Rightarrow> 'a \<Rightarrow> 'ss \<Rightarrow> bool\<close> 
  (\<open>_ \<longmapsto>\<^sup>\<theta>_ _\<close> [70, 70, 70] 70)
  where 
    env_stabilise: \<open>X \<subseteq> visible_actions \<Longrightarrow> 
      \<theta>(p) \<longmapsto>\<^sup>\<theta>\<epsilon>[X] \<theta>[X](p)\<close>
  | triggered_tau:
      \<open>p \<longmapsto>\<tau> q \<Longrightarrow> \<theta>(p) \<longmapsto>\<^sup>\<theta>\<tau> \<theta>(q)\<close>
  | env_timeout: \<open>X \<subseteq> visible_actions \<Longrightarrow> 
      idle p X \<Longrightarrow> \<theta>[X](p) \<longmapsto>\<^sup>\<theta>t_\<epsilon> \<theta>(p)\<close>
  | tran_visible: \<open>X \<subseteq> visible_actions \<Longrightarrow> 
      a \<in> X \<Longrightarrow> p \<longmapsto>a q \<Longrightarrow> \<theta>[X](p) \<longmapsto>\<^sup>\<theta>a \<theta>(q)\<close>
  | stable_tau: \<open>X \<subseteq> visible_actions \<Longrightarrow> 
      p \<longmapsto>\<tau> q \<Longrightarrow> \<theta>[X](p) \<longmapsto>\<^sup>\<theta>\<tau> \<theta>[X](q)\<close>
  | sys_timeout: \<open>X \<subseteq> visible_actions \<Longrightarrow> 
      idle p X \<Longrightarrow> p \<longmapsto>t q \<Longrightarrow> \<theta>[X](p) \<longmapsto>\<^sup>\<theta>t \<theta>[X](q)\<close>

text \<open>\pagebreak\<close>
subsubsection \<open>Generation Lemmas\<close>

text \<open>Lastly, we derive a set of generation lemmas, i.e.\@ lemmas that allow us to reason backwards: if we know \<open>P \<longmapsto>\<^sup>\<theta>\<alpha> P'\<close> and some other information about \<open>P\<close> and/or \<open>\<alpha>\<close>, we can deduce some information about the other variables as well as the transitions of the original \LTSt{}.\<close>

lemma generation_triggered_transitions:
  assumes \<open>\<theta>(p) \<longmapsto>\<^sup>\<theta>\<alpha> P'\<close>
  shows \<open>(\<exists>X. \<alpha> = \<epsilon>[X] \<and> P' = \<theta>[X](p) \<and> X \<subseteq> visible_actions) 
    \<or> (\<alpha> = \<tau> \<and> (\<exists>p'. p \<longmapsto>\<tau> p'))\<close>
  using iffD1[OF tran_theta.simps assms]
  by (smt (z3) injectivity_theta(1,2))

lemma generation_stable_transitions:
  assumes \<open>\<theta>[X](p) \<longmapsto>\<^sup>\<theta>\<alpha> P'\<close>
  shows \<open>\<alpha> = t_\<epsilon> \<or> (\<exists> p'. p \<longmapsto>\<alpha> p' \<and> (\<alpha> \<in> X \<or> \<alpha> = \<tau> \<or> \<alpha> = t))\<close>
  using iffD1[OF tran_theta.simps assms]
  by (smt injectivity_theta(1,3) lts_timeout_mappable_axioms)
  
lemma generation_env_stabilise:
  assumes \<open>P \<longmapsto>\<^sup>\<theta>\<epsilon>[X] P'\<close>
  shows \<open>\<exists> p. P = \<theta>(p) \<and> P' = \<theta>[X](p)\<close> 
  using iffD1[OF tran_theta.simps assms(1)] 
  by (smt (z3) distinctness_special_actions(6) distinctness_special_actions(7) no_epsilon_in_tran(1))

lemma generation_triggered_tau:
  assumes \<open>\<theta>(p) \<longmapsto>\<^sup>\<theta>\<tau> P'\<close>
  shows \<open>\<exists> p'. P' = \<theta>(p') \<and> p \<longmapsto>\<tau> p'\<close>
  using iffD1[OF tran_theta.simps assms]
  using distinctness_special_actions(4) injectivity_theta(1) injectivity_theta(2) by blast
  
lemma generation_env_timeout:
  assumes \<open>\<theta>[X](p) \<longmapsto>\<^sup>\<theta>t_\<epsilon> P'\<close>
  shows \<open>P' = \<theta>(p) \<and> idle p X\<close>
  using iffD1[OF tran_theta.simps assms] distinctness_special_actions
  by (smt injectivity_theta(3) insertCI no_epsilon_in_tran(2))+

lemma generation_tran_visible:
  assumes \<open>\<theta>[X](p) \<longmapsto>\<^sup>\<theta>a P'\<close> \<open>a \<in> visible_actions\<close>
  shows \<open>a \<in> X \<and> (\<exists> p'. P' = \<theta>(p') \<and> p \<longmapsto>a p')\<close>
  using iffD1[OF tran_theta.simps assms(1)]
proof (elim disjE, goal_cases)
  case 1
  then show ?case by (metis injectivity_theta(1))
next
  case 2
  then obtain p' where \<open>\<theta>[X](p) = \<theta>(p')\<close> by blast
  hence False using injectivity_theta(1) by metis
  thus ?case by simp
next
  case 3
  then show ?case using assms(2) no_epsilon_in_tran(2) visible_actions_def by auto
next
  case 4
  hence \<open>X \<subseteq> visible_actions\<close> by (metis injectivity_theta(3))
  with 4 show ?case using injectivity_theta(3) by blast
next
  case 5
  hence False using visible_actions_def assms(2) by simp
  thus ?case by simp
next
  case 6
  hence False using visible_actions_def assms(2) by simp
  thus ?case by simp
qed

lemma generation_stable_tau:
  assumes \<open>\<theta>[X](p) \<longmapsto>\<^sup>\<theta>\<tau> P'\<close>
  shows \<open>\<exists> p'. P' = \<theta>[X](p') \<and> p \<longmapsto>\<tau> p'\<close>
  using iffD1[OF tran_theta.simps assms]
proof (elim disjE, goal_cases)
  case 1
  hence False using distinctness_special_actions by blast
  thus ?case by simp
next
  case 2
  then obtain p' where \<open>\<theta>[X](p) = \<theta>(p')\<close> by blast
  hence False using injectivity_theta(1) by metis
  thus ?case by simp
next
  case 3
  hence False using distinctness_special_actions by blast
  thus ?case by simp
next
  case 4
  then show ?case using visible_actions_def by fastforce
next
  case 5
  hence \<open>X \<subseteq> visible_actions\<close> by (metis injectivity_theta(3))
  with 5 show ?case using injectivity_theta(3) by blast
next
  case 6
  hence False using lts_timeout_axioms lts_timeout_def by force
  thus ?case by simp
qed

lemma generation_sys_timeout:
  assumes \<open>\<theta>[X](p) \<longmapsto>\<^sup>\<theta>t P'\<close>
  shows \<open>\<exists> p'. P' = \<theta>[X](p') \<and> idle p X \<and> p \<longmapsto>t p'\<close>
  using iffD1[OF tran_theta.simps assms]
proof (elim disjE, goal_cases)
  case 1
  hence False using distinctness_special_actions by blast
  thus ?case ..
next
  case 2
  then obtain p' where \<open>\<theta>[X](p) = \<theta>(p')\<close> by blast
  hence False using injectivity_theta(1) by metis
  thus ?case ..
next
  case 3
  hence False using distinctness_special_actions by blast
  thus ?case ..
next
  case 4
  then show ?case using visible_actions_def by auto
next
  case 5
  hence False using lts_timeout_axioms lts_timeout_def by force
  thus ?case ..
next
  case 6
  hence \<open>X \<subseteq> visible_actions\<close> by (metis injectivity_theta(3))
  with 6 show ?case using injectivity_theta(3) by blast
qed

end \<comment> \<open>of \<open>locale lts_timeout_mappable\<close>\<close>
(*<*)
end \<comment> \<open>of \<open>theory\<close>\<close>
(*>*)