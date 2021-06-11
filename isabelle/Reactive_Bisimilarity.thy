(*<*)
theory Reactive_Bisimilarity
imports 
  Labelled_Transition_Systems_with_TimeOuts
begin
(*>*)

section \<open>Reactive Bisimilarity\<close>
text \<open>\label{sec:reactive_bisimilarity}\<close>

text \<open>In the examples of the previous section, we saw that there are \LTSt{}s with transitions that can never be performed or that can only be performed in certain environments. The behavioural equivalence implied hereby is defined in @{cite rbs} as \emph{strong reactive bisimilarity}.

\example{%
The processes $p$ and $q$ are behaviourally equivalent for \LTSt{} semantics, i.e.\@ strongly reactive bisimilar.

\lts{
    \node[state]    (p0)                            {$p$};
    \node[state]    (p1) [below left of=p0]         {$p_1$};
    \node[state]    (p2) [below right of=p0]        {$p_2$};
    \node[state]    (p3) [below left of=p2]         {$p_3$};
    \node[state]    (p4) [below right of=p2]        {$p_4$};
    
    \path   (p0) edge node[above left]  {$a$}   (p1)
                 edge node              {$t$}   (p2)
            (p2) edge node[above left]  {$\tau$}(p3)
                 edge node              {$a$}   (p4);
                 
    \node[state]    (q0) [right of=p0,xshift=5cm]   {$q$};
    \node[state]    (q1) [below left of=q0]         {$q_1$};
    \node[state]    (q2) [below right of=q0]        {$q_2$};
    \node[state]    (q3) [below left of=q2]         {$q_3$};
    
    \path   (q0) edge node[above left]  {$a$}   (q1)
                 edge node              {$t$}   (q2)
            (q2) edge node[above left]  {$\tau$}(q3);
}}\<close>

subsubsection \<open>Strong Reactive Bisimulations\<close>
text \<open>Van~Glabbeek introduces several characterisations of this equivalence, beginning with \emph{strong reactive bisimulation} (SRB) relations. These differ from strong bisimulations in that the relations contain not only pairs of processes $(p,q)$, but additionally triples consisting of two processes and a set of actions $(p,X,q)$. The following definition of SRB relations is quoted, with minor adaptations, from @{cite \<open>Definition 1\<close> rbs}:

A \emph{strong reactive bisimulation} is a symmetric relation 
$$\mathcal{R} \subseteq (\Proc \times \mathcal{P}(A) \times \Proc) \cup (\Proc \times \Proc)$$
(meaning that $(p,X,q)\!\in\!\mathcal{R}\!\iff\!(q,X,p)\!\in\!\mathcal{R}$ and
$(p,q)\!\in\!\mathcal{R}\!\iff\!(q,p)\!\in\!\mathcal{R}$),\\
such that,
\newpage
for all $(p,q) \in \mathcal{R}$:
\begin{enumerate}
    \item if $p \xrightarrow{\tau} p'$, then $\exists q'$ such that $q \xrightarrow{\tau} q'$ and $(p',q') \in \mathcal{R}$,
    \item $(p,X,q) \in \mathcal{R}$ for all $X \subseteq A$,
\end{enumerate}
and for all $(p,X,q) \in \mathcal{R}$:
\begin{enumerate}
    \setcounter{enumi}{2}
    \item if $p \xrightarrow{a} p'$ with $a \in X$, then $\exists q'$ such that $q \xrightarrow{a} q'$ and $(p',q') \in \mathcal{R}$,
    \item if $p \xrightarrow{\tau} p'$, then $\exists q'$ such that $q \xrightarrow{\tau} q'$ and $(p',X,q') \in \mathcal{R}$,
    \item if $\mathcal{I}(p) \cap (X \cup \{\tau\}) = \emptyset$, then $(p,q) \in \mathcal{R}$, and
    \item if $\mathcal{I}(p) \cap (X \cup \{\tau\}) = \emptyset$ and $p \xrightarrow{t} p'$, then $\exists q'$ such that $q \xrightarrow{t} q'$ and $(p',X,q') \in \mathcal{R}$.
\end{enumerate}

We can derive the following intuitions: an environment can either be stable, allowing a specific set of actions, or indeterminate. Indeterminate environments cannot facilitate any transitions, but they can stabilise into arbitrary stable environments. This is expressed by clause 2. Hence, $X$-bisimilarity is behavioural equivalence in stable environments~$X$, and reactive bisimilarity is behavioural equivalence in indeterminate environments (and thus in arbitrary stable environments).

Since only stable environments can facilitate transitions, there are no clauses involving visible action transitions for $(p,q) \in \mathcal{R}$. However, $\tau$-transitions can be performed regardless of the environment, hence clause 1.

At this point, it is important to discuss what exactly it means for an action to be visible or hidden in this context: as we saw in the last section, the environment cannot react (change its set of allowed actions) when the system performs a $\tau$- or a $t$-transition, since these are hidden actions. However, since we are talking about a \emph{strong} bisimilarity (as opposed to e.g.\@ weak bisimilarity), the performance of $\tau$- or $t$-transitions is still relevant when examining and comparing the behavior of systems.

With that, we can look more closely at the remaining clauses:
in clause 3, given $(p,X,q) \in \mathcal{R}$, for $p \xrightarrow{a} p'$ with $a \in X$, we require for the \enquote{mirroring} state $q'$ that $(p',q') \in \mathcal{R}$, because $a$ is a visible action and the transition can thus trigger a change of the environment;%
\footnote{This is why van~Glabbeek talks about \emph{triggered} environments rather than indeterminate ones. I will use both terms interchangeably.}
on the other hand, in clause 4, for $p \xrightarrow{\tau} p'$, and in clause 6, for $p \xrightarrow{t} p'$, we require $(p',X,q') \in \mathcal{R}$, because these actions are hidden and cannot trigger a change of the environment.

Lastly, clause 5 formalises the possibility of the environment timing out (i.e.\@ turning into an indeterminate environment) instead of the system.

These intuitions also form the basis for the process mapping which will be presented in \cref{sec:mapping_lts}.\<close>


subsubsection \<open>Strong Reactive/$X$-Bisimilarity\<close>
text \<open>Two processes $p$ and $q$ are \emph{strongly reactive bisimilar} ($p \leftrightarrow_r q$) iff there is an SRB containing $(p,q)$, and \emph{strongly $X$-bisimilar} ($p \leftrightarrow_r^X q$), i.e.\@ \enquote{equivalent} in environments~$X$, when there is an SRB containing $(p,X,q)$.\<close>


subsubsection \<open>Generalised Strong Reactive Bisimulations\<close>
text \<open>Another characterisation of reactive bisimilarity uses \emph{generalised strong reactive bisimulation} (GSRB) relations, defined over the same set as SRBs, but with different clauses @{cite \<open>Definition 3\<close> rbs}. It is proved that both characterisations do, in fact, characterise the same equivalence. More details will be discussed in the formalisation below.\<close>


subsection \<open>Isabelle\<close>

text \<open>I first formalise both SRB and GSRB relations (as well as strong reactive bisimilarity, defined by the existence of an SRB, as above), and then replicate the proof of their correspondence.\<close>


subsubsection \<open>Strong Reactive Bisimulations\<close>

text \<open>SRB relations are defined over the set
$$(\Proc \times \mathscr{P}(A) \times \Proc) \cup (\Proc \times \Proc).$$

As can be easily seen, this set it isomorphic to
$$(\Proc \times (\mathscr{P}(A) \cup \{\bot\}) \times \Proc),$$
which is a subset of
$$(\Proc \times (\mathscr{P}(\Act) \cup \{\bot\}) \times \Proc).$$ 

This last set can now be easily formalised in terms of a type, where we formalise
$\mathscr{P}(\Act) \cup \{\bot\}$
as \<open>'a set option\<close>.

The fact that SRBs are defined using the power set of visible actions ($A$), whereas our type uses all actions ($\Act$ / \<open>'a\<close>), is handled by the first line of the definition below. The second line formalises that symmetry is required by definition. All other lines are direct formalisations of the clauses of the original definition.
\pagebreak\<close>

context lts_timeout begin

\<comment> \<open>strong reactive bisimulation @{cite \<open>Definition 1\<close> rbs}\<close>
definition SRB :: \<open>('s \<Rightarrow> 'a set option \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where \<open>SRB R \<equiv>
  (\<forall> p X q. R p (Some X) q  \<longrightarrow>  X \<subseteq> visible_actions) \<and>
  (\<forall> p XoN q. R p XoN q  \<longrightarrow>  R q XoN p) \<and>

  (\<forall> p q. R p None q \<longrightarrow>
    (\<forall> p'. p \<longmapsto>\<tau> p'  \<longrightarrow>  (\<exists> q'. (q \<longmapsto>\<tau> q') \<and> R p' None q')) \<and>
    (\<forall> X \<subseteq> visible_actions. (R p (Some X) q))) \<and>

  (\<forall> p X q. R p (Some X) q \<longrightarrow>
    (\<forall> p' a. p \<longmapsto>a p' \<and> a \<in> X  \<longrightarrow>  (\<exists> q'. (q \<longmapsto>a q') \<and> 
      R p' None q')) \<and>
    (\<forall> p'. p \<longmapsto>\<tau> p'  \<longrightarrow>  (\<exists> q'. (q \<longmapsto>\<tau> q') \<and> R p' (Some X) q')) \<and>
    (idle p X  \<longrightarrow>  R p None q) \<and>
    (\<forall> p'. idle p X \<and> (p \<longmapsto>t p')  \<longrightarrow>  (\<exists> q'. q \<longmapsto>t q' \<and> 
      R p' (Some X) q')))\<close>

(* This lemma simply translates the definition above into simple implications that are easy-to-use in proofs. It is not relevant for the thesis document. *)
(*<*)
lemma\<^marker>\<open>tag (proof) unimportant\<close> SRB_ruleformat:
  assumes \<open>SRB R\<close>
  shows 
    \<open>R p (Some X) q \<Longrightarrow> X \<subseteq> visible_actions\<close>
    \<open>R p XoN q \<Longrightarrow> R q XoN p\<close>
    \<open>R p None q \<Longrightarrow> p \<longmapsto>\<tau> p' \<Longrightarrow> \<exists> q'. (q \<longmapsto>\<tau> q') \<and> R p' None q'\<close>
    \<open>R p None q \<Longrightarrow> X \<subseteq> visible_actions \<Longrightarrow> R p (Some X) q\<close>
    \<open>R p (Some X) q \<Longrightarrow> p \<longmapsto>a p' \<Longrightarrow> a \<in> X \<Longrightarrow> \<exists> q'. (q \<longmapsto>a q') \<and> R p' None q'\<close>
    \<open>R p (Some X) q \<Longrightarrow> p \<longmapsto>\<tau> p' \<Longrightarrow> \<exists> q'. (q \<longmapsto>\<tau> q') \<and> R p' (Some X) q'\<close>
    \<open>R p (Some X) q \<Longrightarrow> idle p X \<Longrightarrow> R p None q\<close>
    \<open>R p (Some X) q \<Longrightarrow> idle p X \<Longrightarrow> p \<longmapsto>t p' \<Longrightarrow> \<exists> q'. q \<longmapsto>t q' \<and> R p' (Some X) q'\<close>
  using assms unfolding SRB_def by metis+
(*>*)

subsubsection \<open>Strong Reactive/$X$-Bisimilarity\<close>

text \<open>Van~Glabbeek differentiates between strong reactive bisimilarity ($(p,q) \in \mathcal{R}$ for an SRB $\mathcal{R}$) and strong $X$-bisimilarity ($(p,X,q) \in \mathcal{R}$ for an SRB $\mathcal{R}$).\<close>

definition strongly_reactive_bisimilar :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> 
  (\<open>_ \<leftrightarrow>\<^sub>r _\<close> [70, 70] 70)
  where \<open>p \<leftrightarrow>\<^sub>r q \<equiv> \<exists> R. SRB R \<and> R p None q\<close>

definition strongly_X_bisimilar :: \<open>'s \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> bool\<close> 
  (\<open>_ \<leftrightarrow>\<^sub>r\<^sup>_ _\<close> [70, 70, 70] 70)
  where \<open>p \<leftrightarrow>\<^sub>r\<^sup>X q \<equiv> \<exists> R. SRB R \<and> R p (Some X) q\<close>

text \<open>For the upcoming proofs, it is useful to combine both reactive and $X$-bisimilarity into a single relation.\<close>

definition strongly_reactive_or_X_bisimilar 
  :: \<open>'s \<Rightarrow> 'a set option \<Rightarrow> 's \<Rightarrow> bool\<close>
  where \<open>strongly_reactive_or_X_bisimilar p XoN q 
    \<equiv> \<exists> R. SRB R \<and> R p XoN q\<close>

text \<open>Obviously, then, these relations coincide accordingly.\<close>

corollary \<open>p \<leftrightarrow>\<^sub>r q \<Longleftrightarrow> strongly_reactive_or_X_bisimilar p None q\<close>
  using strongly_reactive_bisimilar_def strongly_reactive_or_X_bisimilar_def by force
corollary \<open>p \<leftrightarrow>\<^sub>r\<^sup>X q \<Longleftrightarrow> strongly_reactive_or_X_bisimilar p (Some X) q\<close>
  using strongly_X_bisimilar_def strongly_reactive_or_X_bisimilar_def by force

                                                                
subsubsection \<open>Generalised Strong Reactive Bisimulations\<close>

text \<open>Since GSRBs are defined over the same set as SRBs, the same considerations concerning the type and the clauses of the definition as above hold.\<close>

\<comment> \<open>generalised strong reactive bisimulation @{cite \<open>Definition 3\<close> rbs}\<close>
definition GSRB :: \<open>('s \<Rightarrow> 'a set option \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where \<open>GSRB R \<equiv>
    (\<forall> p X q. R p (Some X) q  \<longrightarrow>  X \<subseteq> visible_actions) \<and>
    (\<forall> p XoN q. R p XoN q  \<longrightarrow>  R q XoN p) \<and>

    (\<forall> p q. R p None q \<longrightarrow>
      (\<forall> p' a. p \<longmapsto>a p' \<and> a \<in> visible_actions \<union> {\<tau>}  \<longrightarrow>
        (\<exists> q'. q \<longmapsto>a q' \<and> R p' None q')) \<and>
      (\<forall> X p'. idle p X \<and> X \<subseteq> visible_actions \<and> p \<longmapsto>t p'  \<longrightarrow>  
        (\<exists> q'. q \<longmapsto>t q' \<and> R p' (Some X) q'))) \<and>
    
    (\<forall> p Y q. R p (Some Y) q \<longrightarrow>
      (\<forall> p' a. a \<in> visible_actions \<and> p \<longmapsto>a p' \<and> (a\<in>Y \<or> idle p Y) \<longrightarrow>
        (\<exists> q'. q \<longmapsto>a q' \<and> R p' None q')) \<and>
      (\<forall> p'. p \<longmapsto>\<tau> p'  \<longrightarrow>  
        (\<exists> q'. q \<longmapsto>\<tau> q' \<and> R p' (Some Y) q')) \<and>
      (\<forall> p' X. idle p (X\<union>Y) \<and> X \<subseteq> visible_actions \<and> p \<longmapsto>t p'  \<longrightarrow>  
        (\<exists> q'. q \<longmapsto>t q' \<and> R p' (Some X) q')))\<close>

(* This lemma is not important for the thesis document. *)
(*<*)
lemma\<^marker>\<open>tag (proof) unimportant\<close> GSRB_ruleformat:
  assumes \<open>GSRB R\<close>
  shows
    \<open>R p (Some X) q \<Longrightarrow> X \<subseteq> visible_actions\<close>
    \<open>R p XoN q \<Longrightarrow> R q XoN p\<close>
    \<open>R p None q \<Longrightarrow> p \<longmapsto>a p' \<Longrightarrow> a \<in> visible_actions \<union> {\<tau>} \<Longrightarrow> \<exists> q'. q \<longmapsto>a q' \<and> R p' None q'\<close>
    \<open>R p None q \<Longrightarrow> idle p X \<Longrightarrow> X \<subseteq> visible_actions \<Longrightarrow> p \<longmapsto>t p' \<Longrightarrow> \<exists> q'. q \<longmapsto>t q' \<and> R p' (Some X) q'\<close>
    \<open>R p (Some Y) q \<Longrightarrow> a \<in> visible_actions \<Longrightarrow> p \<longmapsto>a p' \<Longrightarrow> a \<in> Y \<or> idle p Y \<Longrightarrow> \<exists> q'. q \<longmapsto>a q' \<and> R p' None q'\<close>
    \<open>R p (Some Y) q \<Longrightarrow> p \<longmapsto>\<tau> p' \<Longrightarrow> \<exists> q'. q \<longmapsto>\<tau> q' \<and> R p' (Some Y) q'\<close>
    \<open>R p (Some Y) q \<Longrightarrow> idle p (X\<union>Y) \<Longrightarrow> X \<subseteq> visible_actions \<Longrightarrow> p \<longmapsto>t p' \<Longrightarrow> \<exists> q'. q \<longmapsto>t q' \<and> R p' (Some X) q'\<close>
  using assms unfolding GSRB_def by metis+
(*>*)


subsubsection \<open>GSRBs characterise strong reactive/$X$-bisimilarity\<close>

text \<open>@{cite \<open>Proposition 4\<close> rbs} reads (notation adapted): \enquote{$p \leftrightarrow_r q$ iff there exists a GSRB $\mathcal{R}$ with $(p,q) \in \mathcal{R}$. Likewise, $p \leftrightarrow_r^X q$ iff there exists a GSRB $\mathcal{R}$ with $(p,X,q) \in \mathcal{R}$.} We shall now replicate the proof of this proposition. First, we prove that each SRB is a GSRB (by showing that each SRB satisfies all clauses of the definition of GSRBs).\<close>

lemma SRB_is_GSRB:
  assumes \<open>SRB R\<close>
  shows \<open>GSRB R\<close>
  unfolding GSRB_def
proof (safe)
  fix p XoN q
  assume \<open>R p XoN q\<close>
  thus \<open>R q XoN p\<close> 
    using SRB_ruleformat[OF assms] by blast
next
  fix p X q x
  assume \<open>R p (Some X) q\<close> and \<open>x \<in> X\<close>
  thus \<open>x \<in> visible_actions\<close> 
    using SRB_ruleformat[OF assms] by blast
next
  fix p q p' a
  assume \<open>R p None q\<close> and \<open>p \<longmapsto>a p'\<close> and \<open>a \<in> visible_actions\<close>
  thus \<open>\<exists>q'. q \<longmapsto>a q' \<and> R p' None q'\<close>
    using SRB_ruleformat(4, 5)[OF assms, where ?X = \<open>{a}\<close>] by blast
next
  fix p q p' a
  assume \<open>R p None q\<close> and \<open>p \<longmapsto>\<tau>  p'\<close>
  thus \<open>\<exists>q'. q \<longmapsto>\<tau>  q' \<and> R p' None q'\<close>
    using SRB_ruleformat(3)[OF assms] by blast
next
  fix p q X p'
  assume \<open>R p None q\<close> and \<open>idle p X\<close> and \<open>X \<subseteq> visible_actions\<close> and \<open>p \<longmapsto>t p'\<close>
  thus \<open>\<exists>q'. q \<longmapsto>t  q' \<and> R p' (Some X) q'\<close>
    using SRB_ruleformat(4, 8)[OF assms] by blast
next
  fix p Y q p' a
  assume \<open>R p (Some Y) q\<close> and \<open>p \<longmapsto>a p'\<close> and \<open>a \<in> Y\<close>
  thus \<open>\<exists>q'. q \<longmapsto>a q' \<and> R p' None q'\<close>
    using SRB_ruleformat(5)[OF assms] by blast
next
  fix p Y q p' a
  assume \<open>R p (Some Y) q\<close> \<open>a \<in> visible_actions\<close> \<open>p \<longmapsto>a p'\<close>  \<open>idle p Y\<close>
  hence \<open>R p None q\<close> using SRB_ruleformat(7)[OF assms] by simp
  hence \<open>R p (Some {a}) q\<close> using SRB_ruleformat(4)[OF assms] \<open>a \<in> visible_actions\<close> by simp
  thus \<open>\<exists>q'. q \<longmapsto>a q' \<and> R p' None q'\<close> using SRB_ruleformat(5)[OF assms] \<open>p \<longmapsto>a p'\<close> by blast
next
  fix p Y q p'
  assume \<open>R p (Some Y) q\<close> and \<open>p \<longmapsto>\<tau> p'\<close>
  thus \<open>\<exists>q'. q \<longmapsto>\<tau>  q' \<and> R p' (Some Y) q'\<close>
    using SRB_ruleformat(6)[OF assms] by blast
next
  fix p Y q p' X
  assume \<open>R p (Some Y) q\<close> \<open>idle p (X \<union> Y)\<close> \<open>X \<subseteq> visible_actions\<close> \<open>p \<longmapsto>t p'\<close>
  from \<open>idle p (X \<union> Y)\<close> have \<open>idle p Y\<close> and \<open>idle p X\<close>
    by (simp add: Int_Un_distrib)+
  from \<open>R p (Some Y) q\<close> \<open>idle p Y\<close> have \<open>R p None q\<close>
    using SRB_ruleformat(7)[OF assms] by blast
  with \<open>X \<subseteq> visible_actions\<close> have \<open>R p (Some X) q\<close> 
    using SRB_ruleformat(4)[OF assms] by blast
  with \<open>idle p X\<close> \<open>p \<longmapsto>t p'\<close> show \<open>\<exists>q'. q \<longmapsto>t  q' \<and> R p' (Some X) q'\<close>
    using SRB_ruleformat(8)[OF assms] by blast
qed

text \<open>Then, we show that each GSRB can be extended to yield an SRB. First, we define this extension. Generally, GSRBs can be smaller than SRBs when proving reactive bisimilarity of processes, because they require triples $(p,X,q)$ only after encountering $t$-transitions, whereas SRBs require these triples for all processes and all environments. These triples (and also some process pairs $(p,q)$ related to environment time-outs, also omitted in GSRBs) are re-added by this extension.
\pagebreak\<close>

definition GSRB_extension 
  :: \<open>('s\<Rightarrow>'a set option\<Rightarrow>'s \<Rightarrow> bool)\<Rightarrow>('s\<Rightarrow>'a set option\<Rightarrow>'s \<Rightarrow> bool)\<close>
  where \<open>(GSRB_extension R) p XoN q \<equiv>
    (R p XoN q)
    \<or> (some_visible_subset XoN \<and> R p None q)
    \<or> ((XoN = None \<or> some_visible_subset XoN) 
      \<and> (\<exists> Y. R p (Some Y) q \<and> idle p Y))\<close>

text \<open>Now we show that this extension does, in fact, yield an SRB (again, by showing that all clauses of the definition of SRBs are satisfied).\<close>

(* This lemma is required for the next proof, but it is not important for the outline document. *)
(*<*)
lemma\<^marker>\<open>tag (proof) unimportant\<close> GSRB_preserves_idleness:
  assumes 
    \<open>GSRB R\<close>
    \<open>R p (Some X) q\<close>
    \<open>idle p X\<close>
  shows 
    \<open>idle q X\<close>
proof (rule ccontr)
  assume \<open>\<not> idle q X\<close>
  hence \<open>initial_actions q \<inter> (X \<union> {\<tau>}) \<noteq> \<emptyset>\<close> by blast
  hence \<open>\<exists> a. a \<in> initial_actions q \<and> a \<in> X \<union> {\<tau>}\<close> by blast
  then obtain \<alpha> where \<open>\<alpha> \<in> initial_actions q\<close> \<open>\<alpha> \<in> X \<union> {\<tau>}\<close> by blast
  then obtain q' where \<open>q \<longmapsto>\<alpha> q'\<close> using initial_actions_def by blast

  from assms have \<open>R q (Some X) p\<close> 
    by (simp add: GSRB_def)

  from \<open>q \<longmapsto>\<alpha> q'\<close> \<open>\<alpha> \<in> X \<union> {\<tau>}\<close> have \<open>\<exists>p'. p \<longmapsto>\<alpha> p'\<close>
  proof (safe)
    assume \<open>\<alpha> \<in> X\<close> \<open>q \<longmapsto>\<alpha> q'\<close>
    from GSRB_ruleformat(1) assms(1,2) have \<open>X \<subseteq> visible_actions\<close> .
    with \<open>R q (Some X) p\<close> \<open>\<alpha> \<in> X\<close> \<open>q \<longmapsto>\<alpha> q'\<close> show \<open>\<exists>p'. p \<longmapsto>\<alpha> p'\<close> 
      using GSRB_ruleformat(5)[OF assms(1)] by blast
  next
    assume \<open>q \<longmapsto>\<tau>  q'\<close>
    with \<open>R q (Some X) p\<close> show \<open>\<exists>p'. p \<longmapsto>\<tau>  p'\<close>
      using GSRB_ruleformat(6)[OF assms(1)] by blast
  qed

  with \<open>\<alpha> \<in> initial_actions q\<close> have \<open>\<alpha> \<in> initial_actions p\<close> using initial_actions_def by auto
  with \<open>\<alpha> \<in> X \<union> {\<tau>}\<close> have \<open>\<not> idle p X\<close> by auto
  with assms show False by simp
qed
(*>*)

lemma GSRB_extension_is_SRB:
  assumes
    \<open>GSRB R\<close>
  shows
    \<open>SRB (GSRB_extension R)\<close> (is \<open>SRB ?R_ext\<close>)
  unfolding SRB_def
proof (safe)
  fix p XoN q
  assume \<open>?R_ext p XoN q\<close>
  thus \<open>?R_ext q XoN p\<close> 
    unfolding GSRB_extension_def
  proof (elim disjE, goal_cases)
    case 1
    hence \<open>R q XoN p\<close>
      using assms GSRB_def by auto
    thus ?case by simp
  next
    case 2
    hence \<open>some_visible_subset XoN \<and> R q None p\<close>
      using assms GSRB_def by auto
    thus ?case by simp
  next
    case 3
    then obtain Y where \<open>R p (Some Y) q\<close> \<open>idle p Y\<close> by auto
    hence \<open>R q (Some Y) p\<close>
      using assms GSRB_def by auto
    have \<open>idle q Y\<close>
      using GSRB_preserves_idleness[OF assms] \<open>R p (Some Y) q\<close> \<open>idle p Y\<close> .
    from 3 \<open>R q (Some Y) p\<close> \<open>idle q Y\<close> show ?case by blast
  qed
next
  fix p X q x
  assume \<open>?R_ext p (Some X) q\<close> \<open>x \<in> X\<close>
  thus \<open>x \<in> visible_actions\<close> 
    unfolding GSRB_extension_def
  proof (elim disjE, goal_cases)
    case 1
    thus ?case using GSRB_ruleformat(1)[OF assms] by blast
  next
    case 2
    thus ?case by auto
  next
    case 3
    thus ?case by auto
  qed
next
  fix p q p'
  assume \<open>?R_ext p None q\<close> \<open>p \<longmapsto>\<tau> p'\<close>
  thus \<open>\<exists>q'. q \<longmapsto>\<tau>  q' \<and> ?R_ext p' None q'\<close> 
    unfolding GSRB_extension_def
  proof (elim disjE, goal_cases)
    case 1
    then obtain q' where \<open>q \<longmapsto>\<tau> q'\<close> \<open>R p' None q'\<close>
      using GSRB_ruleformat(3)[OF assms] lts_timeout_axioms by fastforce
    thus ?case by auto
  next
    case 2
    hence False by auto
    thus ?case by simp
  next
    thm GSRB_ruleformat(5)[OF assms, where ?a=\<tau>]
    case 3
    hence \<open>\<exists>q'. q \<longmapsto>\<tau>  q' \<and> R p' None q'\<close>
      using initial_actions_def by fastforce
    thus ?case by auto
  qed
next
  fix p q X
  assume \<open>?R_ext p None q\<close> \<open>X \<subseteq> visible_actions\<close>
  thus \<open>?R_ext p (Some X) q\<close> 
    unfolding GSRB_extension_def
  proof (elim disjE, goal_cases)
    case 1
    thus ?case by auto
  next
    case 2
    hence False by auto
    thus ?case by simp
  next
    case 3
    hence \<open>some_visible_subset (Some X)\<close> by simp
    with 3 show ?case by simp
  qed
next
  fix p X q p' a
  assume \<open>?R_ext p (Some X) q\<close> \<open>p \<longmapsto>a p'\<close> \<open>a \<in> X\<close>
  thus \<open>\<exists>q'. q \<longmapsto>a q' \<and> ?R_ext p' None q'\<close> 
    unfolding GSRB_extension_def
  proof (elim disjE, goal_cases)
    case 1
    thus ?case 
      using GSRB_ruleformat(1,5)[OF assms] by blast
  next
    case 2
    thus ?case 
      using GSRB_ruleformat(3)[OF assms] by blast
  next
    case 3
    then obtain Y where \<open>R p (Some Y) q\<close> \<open>idle p Y\<close> by blast
    with 3 have \<open>a \<in> visible_actions\<close>
      using GSRB_ruleformat(2)[OF assms] by blast
    from 3 \<open>idle p Y\<close> show ?case 
      using GSRB_ruleformat(5)[OF assms \<open>R p (Some Y) q\<close> \<open>a \<in> visible_actions\<close>] by metis
  qed
next
  fix p X q p'
  assume \<open>?R_ext p (Some X) q\<close> \<open>p \<longmapsto>\<tau> p'\<close>
  thus \<open>\<exists>q'. q \<longmapsto>\<tau>  q' \<and> ?R_ext p' (Some X) q'\<close> 
    unfolding GSRB_extension_def
  proof (elim disjE, goal_cases)
    case 1
    thus ?case 
      using GSRB_ruleformat(6)[OF assms] by meson
  next
    case 2
    thus ?case 
      using GSRB_ruleformat(3)[OF assms] by blast
  next
    case 3
    then obtain Y where \<open>idle p Y\<close> by blast
    with 3(1) have False 
      using initial_actions_def by auto
    thus ?case by simp
  qed
next
  fix p X q
  assume \<open>?R_ext p (Some X) q\<close> \<open>idle p X\<close>
  thus \<open>?R_ext p None q\<close> 
    unfolding GSRB_extension_def by auto
next
  fix p X q p'
  assume \<open>?R_ext p (Some X) q\<close> \<open>idle p X\<close> \<open>p \<longmapsto>t p'\<close>
  thus \<open>\<exists>q'. q \<longmapsto>t  q' \<and> ?R_ext p' (Some X) q'\<close> 
    unfolding GSRB_extension_def
  proof (elim disjE, goal_cases)
    case 1
    from 1(1) have \<open>idle p (X \<union> X)\<close> by simp
    from GSRB_ruleformat(1)[OF assms 1(3)] have \<open>X \<subseteq> visible_actions\<close> .
    from GSRB_ruleformat(7)[OF assms 1(3) \<open>idle p (X \<union> X)\<close> \<open>X \<subseteq> visible_actions\<close> 1(2)]
    show ?case by auto
  next
    case 2
    thus ?case
      using GSRB_ruleformat(4)[OF assms]
      by (metis option.inject)
  next
    case 3
    then obtain Y where \<open>R p (Some Y) q\<close> \<open>idle p Y\<close> by blast
    from \<open>idle p X\<close> \<open>idle p Y\<close> have \<open>idle p (X \<union> Y)\<close>
      by (smt bot_eq_sup_iff inf_sup_distrib1)
    from 3(3) have \<open>X \<subseteq> visible_actions\<close> by blast
    from GSRB_ruleformat(7)[OF assms \<open>R p (Some Y) q\<close> \<open>idle p (X \<union> Y)\<close> \<open>X \<subseteq> visible_actions\<close> 3(2)]
    show ?case by auto
  qed
qed

text \<open>Finally, we can conclude the following:\<close>

lemma GSRB_whenever_SRB:
  shows \<open>(\<exists> R. GSRB R \<and> R p XoN q)  \<Longleftrightarrow>  (\<exists> R. SRB R \<and> R p XoN q)\<close>
  by (metis GSRB_extension_def GSRB_extension_is_SRB SRB_is_GSRB)

text \<open>This, now, directly implies that GSRBs do charactarise strong reactive/$X$-bisimilarity.\<close>

proposition\<^marker>\<open>tag (proof) visible\<close> GSRBs_characterise_strong_reactive_bisimilarity:
  \<open>p \<leftrightarrow>\<^sub>r q \<Longleftrightarrow> (\<exists> R. GSRB R \<and> R p None q)\<close>
  using GSRB_whenever_SRB strongly_reactive_bisimilar_def by blast

proposition\<^marker>\<open>tag (proof) visible\<close> GSRBs_characterise_strong_X_bisimilarity:
  \<open>p \<leftrightarrow>\<^sub>r\<^sup>X q \<Longleftrightarrow> (\<exists> R. GSRB R \<and> R p (Some X) q)\<close>
  using GSRB_whenever_SRB strongly_X_bisimilar_def by blast

end \<comment> \<open>of \<open>context lts_timeout\<close>\<close>


text \<open>As a little meta-comment, I would like to point out that van~Glabbeek's proof spans a total of five lines (\enquote{Clearly, \textelp{}}, \enquote{It is straightforward to check \textelp{}}), whereas the Isabelle proof takes up around 250 lines of code. This just goes to show that for things which are clear and straightforward for humans, it might require quite some effort to \enquote{explain} them to a computer.
\pagebreak\<close>

(*<*)
end \<comment> \<open>of \<open>theory\<close>\<close>
(*>*)