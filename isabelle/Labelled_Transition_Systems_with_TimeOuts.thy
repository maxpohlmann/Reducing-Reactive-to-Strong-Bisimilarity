(*<*)
theory Labelled_Transition_Systems_with_TimeOuts
  imports Labelled_Transition_Systems
begin
(*>*)

section \<open>Labelled Transition Systems with Time-Outs\<close>
text \<open>\label{sec:LTSt}\<close>

text \<open>In addition to the hidden action $\tau$, labelled transition systems with time-outs (\LTSt{}) @{cite vanglabbeek2021failure} include the \emph{time-out action} $t$ as another special action; $t$-transitions can only be performed when no other (non--time-out) transition is allowed in a given environment. The rationale is that, in this model, all transitions that are facilitated by or independent of the environment happen instantaneously, and only when no such transition is possible, time elapses and the system is idle.
However, since the passage of time is not quantified here, the system does not \emph{have} to take a time-out transition in such a case; instead, the environment can spontaneously change its set of allowed actions (corresponding to a time-out on the part of the environment). Thus, the resolution of an idling period is non-deterministic.

In most works on LTSs, the actions which the environment allows in any given state are usually not modelled explicitly; an (often implicit) requirement for any property of the system is that it should hold for arbitrary (and arbitrarily changing) environments. The introduction of time-outs necessitates an explicit consideration of the environment, as the possibility of a transition does not only depend on whether its action is currently allowed, but potentially on the set of all actions currently allowed by the environment. This is why, in previous sections, I have put unusual emphasis on the actions that are allowed or blocked by the system's environment in a given moment. Henceforth, I will refer to \enquote{environments allowing exactly the actions in $X$} simply as \enquote{environments~$X$}.

\example{%
The process $p$ can perform an $a$-transition in environments allowing the action $a$ and a $t$-transition in environments blocking $a$. On the other hand, the process $q$ cannot perform a $t$-transition in any environment, since the $\tau$-transition will always be performed immediately.

\lts{
    \node[state]    (p0)                            {$p$};
    \node[state]    (p1) [below left of=p0]         {$p_1$};
    \node[state]    (p2) [below right of=p0]        {$p_2$};
    \node[state]    (q0) [right of=p0,xshift=3cm]   {$q$};
    \node[state]    (q1) [below left of=q0]         {$q_1$};
    \node[state]    (q2) [below right of=q0]        {$q_2$};
    
    \path   (p0) edge node[above left]  {$a$}   (p1)
                 edge node              {$t$}   (p2)
            (q0) edge node[above left]  {$\tau$}(q1)
                 edge node              {$t$}   (q2);
}}

Furthermore, since $t$-transitions (as well as $\tau$-transitions) are hidden, they cannot trigger a change of the environment, so some states may only ever be entered in certain environments.

\example{%
The process $p$ can perform a $t$-transition only in environments disallowing $a$. Therefore, the subsequent state $p_2$ must be entered in such an environment. The $\tau$-transition is now the only possible transition and will be performed immediately.

\lts{
    \node[state]    (p0)                            {$p$};
    \node[state]    (p1) [below left of=p0]         {$p_1$};
    \node[state]    (p2) [below right of=p0]        {$p_2$};
    \node[state]    (p3) [below left of=p2]         {$p_3$};
    \node[state]    (p4) [below right of=p2]        {$p_4$};
    
    \path   (p0) edge node[above left]  {$a$}   (p1)
                 edge node              {$t$}   (p2)
            (p2) edge node[above left]  {$\tau$}   (p3)
                 edge node              {$a$}(p4);
}}

On the other hand, transitions with labels other than $\tau$ and $t$ require an interaction with the environment, and therefore \emph{are} detectable and can trigger a change in the allowed actions of the environment.

\example{%
Only in environments disallowing $a$, $p$ can make a $t$-transition to $p_2$. However (if $b$ is allowed), the performance of the $b$-transition into $p_3$ may trigger a change of the environment, so it is possible that $p_3$ could perform its $a$-transition.

\lts{
    \node[state]    (p0)                            {$p$};
    \node[state]    (p1) [below left of=p0]         {$p_1$};
    \node[state]    (p2) [below right of=p0]        {$p_2$};
    \node[state]    (p3) [below of=p2]              {$p_3$};
    \node[state]    (p4) [below left of=p3]         {$p_4$};
    \node[state]    (p5) [below right of=p3]        {$p_5$};
    
    \path   (p0) edge node[above left]  {$a$}   (p1)
                 edge node              {$t$}   (p2)
            (p2) edge node              {$b$}   (p3)
            (p3) edge node[above left]  {$\tau$}   (p4)
                 edge node              {$a$}(p5);
}}

These semantics of \LTSt{}s induce a novel notion of behavioural equivalence, which will be investigated in the next section. For the remainder of this section, we shall formalise \LTSt{}s, along with some useful concepts.\<close>

subsubsection \<open>Note on Metavariable usage\<close>

text \<open>If not referenced directly by $\vartheta(p)$ or $\vartheta_X(p)$, arbitrary states of an \LTSt{} range over $P, Q, P', Q', \dots$, where $P$ and $P'$ are used for states connected by some transition (i.e.\@ $P \xrightarrow{\alpha}_\vartheta P'$), whereas $P$ and $Q$ are used for states possibly related by some equivalence (e.g.\@ $P \leftrightarrow_r Q$), as will be discussed in the next section.\<close>

subsubsection \<open>Practical Example\<close>

text \<open>As in \cref{sec:LTS}, we shall consider a real-world machine that may be modelled as an \LTSt{}. Let us imagine that our simple vending machine ejects the coin if no snack has been selected after a certain amount of time. We can attempt to model the machine with this extended behaviour as an LTS, where the coin ejection requires no interaction and is therefore also modelled as a $\tau$-transition.

\lts{
    \node[state]    (p0) {$p$};
    \node[state]    (p1) [below of=p0] {$p_1$};
    \node[state]    (p2) [below left of=p1,xshift=-10pt] {$p_2$};
    \node[state]    (p3) [below of=p1] {$p_3$};
    \node[state]    (p4) [below right of=p1,xshift=10pt] {$p_4$};
    
    \path   (p0) edge node[right] {coin} (p1)
            (p1) edge node[above left] {choc} (p2)
                 edge node[right] {nuts} (p3)
                 edge node[above right] {crisps} (p4);
                 
    \draw (p2) to[out=150, in=180, looseness=1, edge node={node [left] {$\tau$}}] (p0);
    \draw (p4) to[out=30, in=-30, looseness=1, edge node={node [right] {$\tau$}}] (p0);
    \draw (p3) to[out=-20, in=0, looseness=2.5, edge node={node [right] {$\tau$}}] (p0);
    \draw (p1) to[out=150, in=230, looseness=.8, edge node={node [left] {$\tau$}}] (p0);
}

However, this LTS also models a machine that randomly ejects coins right after insertion.%
\footnote{A behaviour that seems to be implemented by the train ticket machines in Berlin.}
In order to distinguish these behaviours, we need \LTSt{} semantics.

\lts{
    \node[state]    (p0) {$p$};
    \node[state]    (p1) [below of=p0] {$p_1$};
    \node[state]    (p11) [below left of=p0,xshift=-10pt] {$p_1'$};
    \node[state]    (p2) [below left of=p1,xshift=-10pt] {$p_2$};
    \node[state]    (p3) [below of=p1] {$p_3$};
    \node[state]    (p4) [below right of=p1,xshift=10pt] {$p_4$};
    
    \path   (p0) edge node[right] {coin} (p1)
            (p1) edge node[above left] {choc} (p2)
                 edge node[right] {nuts} (p3)
                 edge node[above right] {crisps} (p4)
            (p1) edge node[above] {$t$} (p11)
            (p11) edge node[left] {$\tau$} (p0);
                 
    \draw (p2) to[out=150, in=180, looseness=2, edge node={node [left] {$\tau$}}] (p0);
    \draw (p4) to[out=30, in=-30, looseness=1, edge node={node [right] {$\tau$}}] (p0);
    \draw (p3) to[out=-20, in=0, looseness=2.5, edge node={node [right] {$\tau$}}] (p0);
}\<close>


subsection \<open>Isabelle\<close>

text \<open>We extend LTSs with hidden actions (\<open>lts_tau\<close>) by the special action \<open>t\<close>. We have to explicitly require (/assume) that \<open>\<tau> \<noteq> t\<close>; when instantiating the locale \<open>lts_timeout\<close> and specifying a concrete type for the type variable \<open>'a\<close>, this assumption must be (proved to be) satisfied.\<close>

locale lts_timeout = lts_tau tran \<tau> 
  for tran :: "'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool" 
    ("_ \<longmapsto>_ _" [70, 70, 70] 80)
    and \<tau> :: "'a" +
  fixes t :: "'a"
  assumes tau_not_t: \<open>\<tau> \<noteq> t\<close>
begin

text \<open>We define the set of (relevant) visible actions (usually denoted by $A \subseteq \Act$) as the set of all actions that are not hidden and that are labels of some transition in the given LTS.\<close>

definition visible_actions :: \<open>'a set\<close>
  where \<open>visible_actions 
    \<equiv> {a. (a \<noteq> \<tau>) \<and> (a \<noteq> t) \<and> (\<exists> p p'. p \<longmapsto>a p')}\<close>

text \<open>The formalisations in upcoming sections will often involve the type \<open>'a set option\<close>, which has values of the form \<open>None\<close> and \<open>Some X\<close> for some \<open>X :: 'a set\<close>. We will usually use the metavariable \<open>XoN\<close> (for \enquote{\<open>X\<close> or \<open>None\<close>}). The following abbreviation will be useful in these situations.\<close>

abbreviation some_visible_subset :: \<open>'a set option \<Rightarrow> bool\<close>
  where \<open>some_visible_subset XoN 
    \<equiv> \<exists> X. XoN = Some X \<and> X \<subseteq> visible_actions\<close>

text \<open>The initial actions of a process ($\mathcal{I}(p)$ in @{cite rbs}) are the actions for which the process has a transition it can perform immediately (if facilitated by the environment), i.e.\@ it is not a $t$-transition.\<close>

definition initial_actions :: \<open>'s \<Rightarrow> 'a set\<close>
  where \<open>initial_actions(p) 
    \<equiv> {\<alpha>. (\<alpha> \<in> visible_actions \<or> \<alpha> = \<tau>) \<and> (\<exists> p'. p \<longmapsto>\<alpha> p')}\<close>

text \<open>In @{cite rbs}, the term $\mathcal{I}(p) \cap (X \cup \{\tau\}) = \emptyset$ is used a lot, which states that there are no immediate transitions the process $p$ can perform (i.e.\@ it is idle) in environments~$X$.\<close>

abbreviation idle :: \<open>'s \<Rightarrow> 'a set \<Rightarrow> bool\<close>
  where \<open>idle p X \<equiv> initial_actions(p) \<inter> (X\<union>{\<tau>}) = \<emptyset>\<close>

text \<open>The following corollary is an immediate consequence of this definition.\<close>

corollary idle_no_derivatives:
  assumes 
    \<open>idle p X\<close> 
    \<open>X \<subseteq> visible_actions\<close>
    \<open>\<alpha> \<in> X\<union>{\<tau>}\<close>
  shows
    \<open>\<nexists> p'. p \<longmapsto>\<alpha> p'\<close>
proof (rule ccontr, auto)
  fix p'
  assume \<open>p \<longmapsto>\<alpha> p'\<close>
  with assms(2,3) have \<open>\<alpha> \<in> initial_actions(p)\<close>
    unfolding initial_actions_def by auto
  with assms(3) have \<open>\<not> idle p X\<close> by blast 
  with assms(1) show False by simp
qed

end \<comment> \<open>of \<open>locale lts_timeout\<close>\<close>
(*<*)
end \<comment> \<open>of \<open>theory\<close>\<close>
(*>*)