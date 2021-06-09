(*<*)
theory HM_Logic
  imports 
    Strong_Bisimilarity
    "HOL-Library.Countable_Set_Type"
begin
(*>*)

section \<open>Hennessy-Milner Logic\<close>
text \<open>\label{sec:HML}\<close>

text \<open>In their seminal paper @{cite hm85}, Matthew Hennessy and Robin Milner present a modal-logical characterisation of strong bisimilarity (although they do not call it that), by process properties: \enquote{two processes are equivalent if and only if they enjoy the same set of properties.} These properties are expressed as terms of a modal-logical language, consisting merely of (finite) conjunction, negation, and a family of modal possibility operators. This language is known today as Hennessy-Milner logic (HML), with formulas $\varphi$ defined by the following grammar (where $\alpha$ ranges over the set of actions $\Act$):
$$\varphi ::= t\!t \mid \varphi_1 \;\wedge\; \varphi_2 \mid \neg\varphi \mid \langle\alpha\rangle\varphi$$

The semantics (on LTS processes) is given as follows: all processes satisfy $t\!t$, $\varphi_1 \;\wedge\; \varphi_2$ is satisfied if both $\varphi_1$ and $\varphi_2$ are satisfied, $\neg\varphi$ is satisfied if $\varphi$ is not satisfied, and $\langle\alpha\rangle\varphi$ is satisfied by a process if it is possible to do an $\alpha$-transition into a process that satisfies $\varphi$.

@{cite hm85} also contains the proof that this modal-logical characterisation of strong bisimilarity coincides with a characterisation that is effectively the same as the one we saw in \cref{sec:strong_bisimilarity} using strong bisimulations. Although they use different terminology, their result can be summarised as follows: for image-finite LTSs, two processes are strongly bisimilar iff they satisfy the same set of HML formulas. We call this the \emph{modal characterisation} of strong bisimilarity.

Let the \emph{cardinality of conjunction} be the maximally allowed cardinality of sets of formulas conjoined under a conjunction term (for a given variant of HML). For the simple variant above, conjunction has finite cardinality. By allowing for conjunction of arbitrary cardinality (infinitary HML), the modal characterisation of strong bisimilarity can be proved for arbitrary LTSs. This is done in \cref{chap:HML_infinitary}.

In this section, however, conjunction is constrained to be of countable cardinality, as this turned out to be significantly easier to deal with in the upcoming proofs. The modal characterisation of strong bisimilarity, then, works for LTSs that are image-countable, as we shall see below.

Formulas $\varphi$ are given by the following grammar, where $I$ ranges over all subsets of the natural numbers $\mathbb{N}$:
$$\varphi ::= \textstyle\bigwedge_{i \in I} \varphi_i \mid \neg\varphi \mid \langle\alpha\rangle\varphi$$

The semantics of HML formulas on LTSs are as above, with the alteration that a process satisfies $\bigwedge_{i \in I} \varphi_i$ iff it satisfies $\varphi_i$ for all $i \in I$.

Additional operators can be added as \enquote{syntactic sugar} as follows:
\begin{align*}
    t\!t &\equiv \textstyle\bigwedge_{i \in \emptyset} \varphi_i \\
    f\!\!f &\equiv \neg t\!t \\
    \textstyle\bigvee_{i \in I} \varphi_i &\equiv \neg \textstyle\bigwedge_{i \in I} \neg\varphi_i
\end{align*}\<close>


subsection \<open>Isabelle\<close>

subsubsection \<open>Syntax\<close>

text \<open>By definition of countability, all countable sets of formulas can be given by $\{\varphi_i\}_{i \in I} =: \Phi$ for some $I \subseteq \mathbb{N}$ (then $\bigwedge_{i \in I} \varphi_i$ corresponds to $\bigwedge \Phi$). Therefore, the following data type (parameterised by the type of actions \<open>'a\<close>) formalises the definition of HML formulas above (\<open>cset\<close> is the type constructor for countable sets; \<open>acset\<close> and \<open>rcset\<close> are the type morphisms between the types \<open>set\<close> and \<open>cset\<close>; more details below).

I abstained from assigning the constructors a more readable symbolic notation because of the ambiguities and name clashes that would ensue in upcoming sections. The symbolic notations after the constructors below are just code comments.\<close>

datatype ('a)HML_formula =
  HML_conj  \<open>('a)HML_formula cset\<close> \<comment> \<open>$\bigwedge \Phi$\<close> 
| HML_neg   \<open>('a)HML_formula\<close> \<comment> \<open>$\neg\varphi$\<close> 
| HML_poss  \<open>'a\<close> \<open>('a)HML_formula\<close> \<comment> \<open>$\langle\alpha\rangle\varphi$\<close>

text \<open>The following abbreviations introduce useful constants as syntactic sugar.\<close>

abbreviation HML_true :: \<open>('a)HML_formula\<close> \<comment> \<open>$t\!t$\<close>
  where \<open>HML_true \<equiv> HML_conj (acset \<emptyset>)\<close>
abbreviation HML_false :: \<open>('a)HML_formula\<close> \<comment> \<open>$f\!\!f$\<close>
  where \<open>HML_false \<equiv> HML_neg HML_true\<close>
abbreviation HML_disj :: \<open>('a)HML_formula cset \<Rightarrow> ('a)HML_formula\<close> \<comment> \<open>$\bigvee \Phi$\<close>
  where \<open>HML_disj \<Phi> \<equiv> HML_neg (HML_conj (cimage HML_neg \<Phi>))\<close>


subsubsection \<open>Aside: The Type of Countable Sets\<close>

text \<open>Since sets \<open>set\<close> and countable sets \<open>cset\<close> are different types in Isabelle, they have different membership relation terms. We introduce the following notation for membership of countable sets.\<close>

notation cin (\<open>_ \<in>\<^sub>c _\<close> [100, 100] 100)

text \<open>The following propositions should clarify how the type constructor \<open>cset\<close> and its morphisms are used. Note how the first proposition requires the assumption \<open>countable X\<close>, whereas the second one does not. \<close>

proposition 
  fixes X::\<open>'x set\<close>
  assumes \<open>countable X\<close>
  shows \<open>x \<in> X  \<Longleftrightarrow>  x \<in>\<^sub>c acset X\<close> 
  using assms by (simp add: cin.rep_eq)
proposition
  fixes X::\<open>'x cset\<close>
  shows \<open>x \<in>\<^sub>c X  \<Longleftrightarrow>  x \<in> rcset X\<close> 
  by (simp add: cin.rep_eq)


subsubsection \<open>Semantics\<close>

text \<open>The semantic satisfaction relation is formalised by the following function. Since the relation is not monotonic (due to negation terms), it cannot be directly defined in Isabelle as an inductive predicate, so we use the \<open>function\<close> command instead. This, then, requires us to prove that the function is well-defined (i.e.\@ the function definition completely and compatibly covers all constructors of our data type) and total (i.e.\@ it terminates). It is easy to see that the former is the case for the function below.\<close>

context lts begin

function HML_sat :: \<open>'s \<Rightarrow> ('a)HML_formula \<Rightarrow> bool\<close> 
  (\<open>_ \<Turnstile> _\<close> [50, 50] 50)
  where
    HML_sat_conj: \<open>(p \<Turnstile> HML_conj \<Phi>) = (\<forall> \<phi>. \<phi> \<in>\<^sub>c \<Phi> \<longrightarrow> p \<Turnstile> \<phi>)\<close> 
  | HML_sat_neg:  \<open>(p \<Turnstile> HML_neg \<phi>) = (\<not> p \<Turnstile> \<phi>)\<close> 
  | HML_sat_poss: \<open>(p \<Turnstile> HML_poss \<alpha> \<phi>) = (\<exists> p'. p \<longmapsto>\<alpha> p' \<and> p' \<Turnstile> \<phi>)\<close>
  using HML_formula.exhaust by (auto, blast)

text \<open>In order to prove that the function always terminates, we need to show that each sequence of recursive invocations reaches a base case%
\footnote{For our satisfaction function, the recursive base case is, of course, the empty conjunction, since
$\forall\varphi.\; \varphi \in \emptyset \longrightarrow p \vDash \varphi$
is a tautology.}
after finitely many steps. We do this by proving that the relation between process-formula pairs given by the recursive definition of the function is (contained within) a well-founded relation.
A relation $R \subseteq X \times X$ is called well-founded if each non-empty subset $X' \subseteq X$ has a minimal element $m$ that is not \enquote{$R$-greater} than any element of $X'$, i.e.\@ $\forall x \in X'.\; (x,m) \notin R$.
A property of well-founded relations is that all descending chains $(x_0, x_1, x_2, \dots)$ (with $(x_i, x_{i+1}) \in R$) starting at any element $x_0 \in X$ are finite. This, then, implies that each sequence of recursive invocations terminates after finitely many steps.\<close>

inductive_set HML_wf_rel :: \<open>('s \<times> ('a)HML_formula) rel\<close> 
  where
    \<open>\<phi> \<in>\<^sub>c \<Phi> \<Longrightarrow> ((p, \<phi>), (p, HML_conj \<Phi>)) \<in> HML_wf_rel\<close> 
  | \<open>((p, \<phi>), (p, HML_neg \<phi>)) \<in> HML_wf_rel\<close> 
  | \<open>((p, \<phi>), (p', HML_poss \<alpha> \<phi>)) \<in> HML_wf_rel\<close>

lemma HML_wf_rel_is_wf: \<open>wf HML_wf_rel\<close> 
  unfolding wf_def
proof (rule allI, rule impI, rule allI)
  fix P::\<open>'s \<times> ('a)HML_formula \<Rightarrow> bool\<close> and t::\<open>'s \<times> ('a)HML_formula\<close>
  obtain p \<phi> where \<open>t = (p, \<phi>)\<close> by force
  assume \<open>\<forall>x. (\<forall>y. (y, x) \<in> HML_wf_rel \<longrightarrow> P y) \<longrightarrow> P x\<close>
  hence \<open>P (p, \<phi>)\<close>
    apply (induct \<phi> arbitrary: p)
    apply (smt (verit, ccfv_SIG) HML_formula.distinct(1) HML_formula.distinct(3) HML_formula.inject(1) HML_wf_rel_def case_prodE' cin.rep_eq HML_wf_rel.cases mem_Collect_eq split_conv)
    apply (metis HML_formula.distinct(1) HML_formula.distinct(5) HML_formula.inject(2) HML_wf_rel.cases surj_pair)
    apply (smt (verit, del_insts) HML_formula.distinct(3) HML_formula.distinct(5) HML_formula.inject(3) HML_wf_rel.cases case_prodD case_prodE' HML_wf_rel_def mem_Collect_eq)
    done
  thus \<open>P t\<close> using \<open>t = (p, \<phi>)\<close> by simp
qed

termination\<^marker>\<open>tag (proof) visible\<close> HML_sat using HML_wf_rel_is_wf 
  by (standard, (simp add: HML_wf_rel.intros)+)


text \<open>The semantic clauses for our additional constants are now easily derivable.\<close>

lemma HML_sat_top:
  shows \<open>p \<Turnstile> HML_true\<close>
  using bot_cset.abs_eq by auto
lemma HML_sat_bot:
  shows \<open>\<not> p \<Turnstile> HML_false\<close>
  using HML_sat_top by auto
lemma HML_sat_disj:
  shows \<open>(p \<Turnstile> HML_disj \<Phi>) = (\<exists> \<phi>. \<phi> \<in>\<^sub>c \<Phi> \<and> p \<Turnstile> \<phi>)\<close>
  by auto


subsubsection \<open>Modal Characterisation of Strong Bisimilarity\<close>

text \<open>First, we introduce HML-equivalence as follows.\<close>

definition HML_equivalent :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close>
  where \<open>HML_equivalent p q \<equiv> (\<forall> \<phi>. (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))\<close>

text \<open>Since formulas are closed under negation, the following lemma holds.\<close>

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

text \<open>HML-equivalence is clearly symmetrical.\<close>

lemma HML_equivalent_symm:
  assumes \<open>HML_equivalent p q\<close>
  shows \<open>HML_equivalent q p\<close>
  using HML_equivalent_def assms by presburger

text \<open>We can now formally prove the modal characterisation of strong bisimilarity, i.e.: two processes are HML-equivalent iff they are strongly bisimilar. The proof follows the strategy from @{cite resyst}. I chose to include these proofs in the thesis document, because they translate quite beautifully, in my opinion, and are not so long as to hamper with the flow of reading.

We show the $\Longrightarrow$-case first, by induction over \<open>\<phi>\<close>.\<close>

lemma\<^marker>\<open>tag (proof) visible\<close> strong_bisimilarity_implies_HM_equivalence:
  assumes \<open>p \<leftrightarrow> q\<close> \<open>p \<Turnstile> \<phi>\<close>
  shows \<open>q \<Turnstile> \<phi>\<close>
  using assms
proof (induct \<phi> arbitrary: p q)
  case (HML_conj \<Phi>)
  then show ?case 
    by (meson HML_sat_conj cin.rep_eq)
next
  case (HML_neg \<phi>)
  then show ?case
    by (meson HML_sat_neg strongly_bisimilar_symm)
next
  case (HML_poss \<alpha> \<phi>)
  then show ?case
    by (meson HML_sat_poss strongly_bisimilar_step(1))
qed

text \<open>Before we can show the $\Longleftarrow$-case, we need to prove the following lemma: for some binary predicate $P$, if for every element $a$ of a set $A$, there exists an element $x$ such that $P(a,x)$ is true, then we can obtain a set $X$ that contains these $x$ (for all $a \in A$) and has the same cardinality as $A$. 

Since more than one $x$ might exist for each $a$ such that $P(a,x)$ is true, the set
$\{ x \mid a \in A \wedge P(a,x) \}$
might have greater cardinality than $A$. In order to obtain a set $X$ of same cardinality as A, we need to invoke the axiom of choice in our proof.\<close>

lemma\<^marker>\<open>tag (proof) visible\<close> obtaining_set:
  assumes 
    \<open>\<forall> a \<in> A. \<exists> x. P a x\<close> 
    \<open>countable A\<close>
  obtains X where 
    \<open>\<forall> a \<in> A. \<exists> x \<in> X. P a x\<close> 
    \<open>\<forall> x \<in> X. \<exists> a \<in> A. P a x\<close> 
    \<open>countable X\<close>
proof
  \<comment> \<open>the \<open>SOME\<close> operator (Hilbert's selection operator $\varepsilon$) invokes the axiom of choice\<close>
  define xm where \<open>xm \<equiv> \<lambda> a. SOME x. P a x\<close>
  define X where \<open>X \<equiv> {xm a | a. a \<in> A}\<close>

  show \<open>\<forall>a\<in>A. \<exists>x\<in>X. P a x\<close>
    using X_def xm_def assms(1) by\<^marker>\<open>tag proof\<close> (metis (mono_tags, lifting) mem_Collect_eq someI)
  show \<open>\<forall>x \<in> X. \<exists>a\<in>A. P a x\<close>
    using X_def xm_def assms(1) by\<^marker>\<open>tag proof\<close> (smt (verit, best) mem_Collect_eq someI_ex)
  show \<open>countable X\<close> 
    using X_def xm_def assms(2) by\<^marker>\<open>tag proof\<close> (simp add: Setcompr_eq_image)
qed

text \<open>We can now show, assuming image-countability of the given LTS, that HML-equivalence is a strong bisimulation. The proof utilises classical contradiction: 
if HML-equivalence were no strong bisimulation, there would be some processes $p$ and $q$ that are HML-equivalent, with $p \xrightarrow{\alpha} p'$ for some $p'$ (i.e.\@ $p' \in \text{Der}(p, \alpha)$), but for all $q' \in \text{Der}(q, \alpha)$, $p'$ and $q'$ are not HML-equivalent. 
Then, for each $q' \in \text{Der}(q, \alpha)$, there would be a distinguishing formula $\varphi_{q'}$ which $p'$ satisfies but $q'$ does not. 
Using our \<open>obtaining_set\<close> lemma, we can obtain the set 
$\Phi = \{ \varphi_{q'} \}_{q' \in \text{Der}(q, \alpha)}$
(which is countable, since $\text{Der}(q, \alpha)$ is countable, by the image-countability assumption).
Since we allow for conjunction of countable cardinality, $\bigwedge \Phi$ is a valid formula. 
By construction, $p$ can make an $\alpha$-transition into a state that satisfies $\bigwedge \Phi$ 
(i.e.\@ $p \vDash \langle\alpha\rangle \bigwedge \Phi$), whereas q cannot 
(i.e.\@ $q \not\vDash \langle\alpha\rangle \bigwedge \Phi$).
This is a contradiction, since, by assumption, $p$ and $q$ are HML-equivalent. 
Therefore, HML-equivalence must be a strong bisimulation.\<close>

lemma\<^marker>\<open>tag (proof) visible\<close> HML_equivalence_is_SB:
  assumes
    \<open>image_countable\<close>
  shows
    \<open>SB HML_equivalent\<close>
proof -
  {
    fix p q p' \<alpha>
    assume \<open>HML_equivalent p q\<close> \<open>p \<longmapsto>\<alpha> p'\<close>
    assume \<open>\<forall>q' \<in> Der(q, \<alpha>). \<not> HML_equivalent p' q'\<close>
    
    hence "exists_\<phi>\<^bsub>q'\<^esub>": \<open>\<forall>q' \<in> Der(q, \<alpha>). \<exists>\<phi>. p' \<Turnstile> \<phi> \<and> \<not> q' \<Turnstile> \<phi>\<close>
      using distinguishing_formula by blast

    from \<open>image_countable\<close> have \<open>countable Der(q, \<alpha>)\<close> 
      using image_countable_def by simp

    from obtaining_set[
          where ?A = \<open>Der(q, \<alpha>)\<close>
            and ?P = \<open>\<lambda> q' \<phi>. p' \<Turnstile> \<phi> \<and> \<not> q' \<Turnstile> \<phi>\<close>, 
          OF "exists_\<phi>\<^bsub>q'\<^esub>" \<open>countable Der(q, \<alpha>)\<close>]
    obtain \<Phi> where *:
      \<open>\<forall>\<phi> \<in> \<Phi>. \<exists>q' \<in> Der(q, \<alpha>). p' \<Turnstile> \<phi> \<and> \<not> q' \<Turnstile> \<phi>\<close> 
      \<open>\<forall>q' \<in> Der(q, \<alpha>). \<exists>\<phi> \<in> \<Phi>. p' \<Turnstile> \<phi> \<and> \<not> q' \<Turnstile> \<phi>\<close> 
      \<open>countable \<Phi>\<close>
      by (this, blast+)
  
    have \<open>p \<Turnstile> HML_poss \<alpha> (HML_conj (acset \<Phi>))\<close>
      using \<open>p \<longmapsto>\<alpha> p'\<close> *(1,3) HML_sat.simps(1,3)
        acset_inverse mem_Collect_eq cin.rep_eq
      by metis

    moreover have \<open>\<not> q \<Turnstile> HML_poss \<alpha> (HML_conj (acset \<Phi>))\<close>
      using *(2,3) cin.rep_eq 
      by fastforce

    ultimately have False 
      using \<open>HML_equivalent p q\<close> 
      unfolding HML_equivalent_def
      by meson
  }

  \<comment> \<open>We showed the case for \<open>p \<longmapsto>\<alpha> p'\<close>, but not \<open>q \<longmapsto>\<alpha> q'\<close>.\<close>
  \<comment> \<open>Clearly, this case is covered by the symmetry of HML-equivalence.\<close>
  from this show \<open>SB HML_equivalent\<close> unfolding SB_def 
    using HML_equivalent_symm by blast
qed

text \<open>We can now conclude the modal characterisation of strong bisimilarity.\<close>
  
theorem\<^marker>\<open>tag (proof) visible\<close> modal_characterisation_of_strong_bisimilarity: 
  assumes \<open>image_countable\<close>
  shows \<open>(p \<leftrightarrow> q)  \<Longleftrightarrow>  (\<forall> \<phi>. p \<Turnstile> \<phi> \<longleftrightarrow> q \<Turnstile> \<phi>)\<close>
proof
  show \<open>(p \<leftrightarrow> q) \<Longrightarrow> \<forall>\<phi>. (p \<Turnstile> \<phi>) = (q \<Turnstile> \<phi>)\<close>
    using strong_bisimilarity_implies_HM_equivalence 
      strongly_bisimilar_symm 
    by blast
next
  show \<open>\<forall>\<phi>. (p \<Turnstile> \<phi>) = (q \<Turnstile> \<phi>) \<Longrightarrow> (p \<leftrightarrow> q)\<close> 
    using HML_equivalence_is_SB[OF assms] 
      HML_equivalent_def strongly_bisimilar_def 
    by blast
qed

end \<comment> \<open>of context lts\<close>
(*<*)
end \<comment> \<open>of theory\<close>
(*>*)