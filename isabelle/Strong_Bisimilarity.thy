(*<*)
theory Strong_Bisimilarity
  imports Labelled_Transition_Systems
begin
(*>*)

section \<open>Strong Bisimilarity\<close>
text \<open>\label{sec:strong_bisimilarity}\<close>

text \<open>As discussed in the previous section, LTSs can describe the behaviour of reactive systems, and this behaviour is observable by the environment (in terms of the transitions performed by the system). This begets a notion of behavioural equivalence, where two processes are said to be behaviourally equivalent if they exhibit the same (observable) behaviour @{cite resyst}.

Bisimilarity (or \emph{strong bisimilarity}, to be precise) is the \enquote{\emph{finest extensional behavioural equivalence} \textelp{} on processes} @{cite introBC}, an extensional property being one that treats the system in question as a black box, i.e.\@ the specific state space of the system remains hidden and performed transitions are only observable in terms of their action-label. This distinguishes bisimilarity from stronger graph equivalences like \emph{graph isomorphism}, where the (intensional) identity of processes (graph nodes) is relevant @{cite advBC_origins}.

\example{%
The processes $p$ and $q$ are strongly bisimilar (written $p \leftrightarrow q$, following @{cite rbs}), as both can always perform exactly two a-transitions and no further transitions afterwards. There is no isomorphism between the left and right subgraphs, as they have a different number of nodes.

\lts{
    \node[state]    (p0)                            {$p$};
    \node[state]    (p1) [below left of=p0]         {$p_1$};
    \node[state]    (p2) [below of=p1]              {$p_2$};
    \node[state]    (p3) [below right of=p0]        {$p_3$};
    \node[state]    (p4) [below of=p3]              {$p_4$};
    \node[state]    (q0) [right of=p0,xshift=2cm]   {$q$};
    \node[state]    (q1) [below of=q0]              {$q_1$};
    \node[state]    (q2) [below of=q1]              {$q_2$};
    
    \path   (p0) edge node[above left]  {$a$}   (p1)
                 edge node              {$a$}   (p3)
            (p1) edge node[left]        {$a$}   (p2)
            (p3) edge node[left]        {$a$}   (p4)
            (q0) edge node              {$a$}   (q1)
            (q1) edge node              {$a$}   (q2);
}}

\pagebreak
It is important to note that not only transitions that are performable, but also those that are not, are relevant.

\example{%
The processes $p$ and $q$ are not strongly bisimilar, as $p$ can perform an $a$-transition into a subsequent state, where it can perform no further transitions, whereas $q$ can always perform two $a$-transitions in sequence.

\lts{
    \node[state]    (p0)                            {$p$};
    \node[state]    (p1) [below left of=p0]         {$p_1$};
    \node[state]    (p2) [below of=p1]              {$p_2$};
    \node[state]    (p3) [below right of=p0]        {$p_3$};
    \node[state]    (q0) [right of=p0,xshift=2cm]   {$q$};
    \node[state]    (q1) [below of=q0]              {$q_1$};
    \node[state]    (q2) [below of=q1]              {$q_2$};
    
    \path   (p0) edge node[above left]  {$a$}   (p1)
                 edge node              {$a$}   (p3)
            (p1) edge node[left]        {$a$}   (p2)
            (q0) edge node              {$a$}   (q1)
            (q1) edge node              {$a$}   (q2);
}}

Strong bisimilarity is the \emph{finest} extensional behavioural equivalence, because all actions are thought of as observable. An example of a coarser equivalence is \emph{weak bisimilarity}, which treats the aforementioned hidden action $\tau$ as unobservable. However, weak bisimilarity is of no further relevance for this thesis and the interested reader is referred to @{cite \<open>Chapter 3.4\<close> resyst}.

The notion of strong bisimilarity can be formalised through \emph{strong bisimulation} (SB) relations, introduced originally by David Park in @{cite park81}. A binary relation $\mathcal{R}$ over the set of processes $\Proc$ is an SB iff for all $(p,q) \in \mathcal{R}$:
\begin{align*}
&\forall p' \in \Proc,\; \alpha \in \Act .\; p \xrightarrow{\alpha} p' \longrightarrow
\exists q' \in \Proc .\; q \xrightarrow{\alpha} q' \wedge (p',q') \in \mathcal{R}, \text{ and}\\
&\forall q' \in \Proc,\; \alpha \in \Act .\; q \xrightarrow{\alpha} q' \longrightarrow
\exists p' \in \Proc .\; p \xrightarrow{\alpha} p' \wedge (p',q') \in \mathcal{R}.
\end{align*}\<close>


subsection \<open>Isabelle\<close>

text \<open>Strong bisimulations are straightforward to formalise in Isabelle, using the curried function definition approach discussed in \cref{chap:isabelle}.\<close>

context lts begin

\<comment> \<open>strong bisimulation\<close>
definition SB :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where \<open>SB R \<equiv> \<forall> p q. R p q \<longrightarrow> 
    (\<forall> p' \<alpha>. p \<longmapsto>\<alpha> p' \<longrightarrow> (\<exists> q'. (q \<longmapsto>\<alpha> q') \<and> R p' q')) \<and>
    (\<forall> q' \<alpha>. q \<longmapsto>\<alpha> q' \<longrightarrow> (\<exists> p'. (p \<longmapsto>\<alpha> p') \<and> R p' q'))\<close>

text \<open>\pagebreak
Two processes $p$ and $q$ are then strongly bisimilar iff there is an SB that contains the pair $(p, q)$.\<close>

definition strongly_bisimilar :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> 
  (\<open>_ \<leftrightarrow> _\<close> [70, 70] 70)
  where \<open>p \<leftrightarrow> q \<equiv> \<exists> R. SB R \<and> R p q\<close>

text \<open>The following corollaries are immediate consequences of these definitions.\<close>

corollary strongly_bisimilar_step:
  assumes 
    \<open>strongly_bisimilar p q\<close>
  shows
    \<open>p \<longmapsto>a p' \<Longrightarrow> (\<exists> q'. (q \<longmapsto>a q') \<and> p' \<leftrightarrow> q')\<close>
    \<open>q \<longmapsto>a q' \<Longrightarrow> (\<exists> p'. (p \<longmapsto>a p') \<and> p' \<leftrightarrow> q')\<close>
  using assms SB_def strongly_bisimilar_def by (smt (verit))+
  
corollary strongly_bisimilar_symm:
  assumes \<open>p \<leftrightarrow> q\<close> 
  shows \<open>q \<leftrightarrow> p\<close> 
  using assms unfolding strongly_bisimilar_def
proof
  fix R
  assume \<open>SB R \<and> R p q\<close>
  let ?R' = \<open>\<lambda> a b. R b a\<close>
  have \<open>SB ?R' \<and> ?R' q p\<close> using SB_def \<open>SB R \<and> R p q\<close> by presburger
  thus \<open>\<exists>R. SB R \<and> R q p\<close> by auto
qed

end \<comment> \<open>context lts\<close>
(*<*)
end \<comment> \<open>of theory\<close>
(*?>*)