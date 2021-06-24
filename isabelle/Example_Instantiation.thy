(*<*)
theory Example_Instantiation
  imports
    Reduction_of_Bisimilarity
begin
(*>*)

chapter \<open>Example Instantiation\<close>
text \<open>\label{chap:example_instantiation}\<close>

text \<open>To complete the proofs from \cref{chap:reductions}, I will show that mappings \<open>stabilise\<close> (\<open>\<epsilon>(_)\<close>) and \<open>in_env\<close> (\<open>\<theta>?[_](_)\<close>), whose existence we assumed up to now, do, in fact, exist. I will define example mappings and show that, together with these, arbitrary \<open>lts_timeout\<close> can be interpreted as \<open>lts_timeout_mappable\<close>, thereby showing that the reductions are valid for arbitrary \LTSt{}s.

First, we define the types for $\Proc_\vartheta$ and $\Act_\vartheta$ in dependence on arbitrary types \<open>'s\<close> and \<open>'a\<close> for $\Proc$ and $\Act$, respectively:\<close>

datatype ('s,'a)Proc_\<theta> = triggered 's | stable \<open>'a set\<close> 's | DumpState
datatype ('a)Act_\<theta> = act 'a | t_\<epsilon> | \<epsilon> \<open>'a set\<close> | DumpAction

text \<open>Since $\Act \neq \Act_\vartheta$, we define a new predicate \<open>tran_mappable\<close>.\<close>
context lts_timeout begin

inductive tran_mappable
  :: \<open>'s \<Rightarrow> ('a)Act_\<theta> \<Rightarrow> 's \<Rightarrow> bool\<close> 
  where \<open>tran p \<alpha> p' \<Longrightarrow> tran_mappable p (act \<alpha>) p'\<close>

text \<open>We can now specify mappings \<open>stabilise\<close> and \<open>in_env\<close>, mapping those \<open>X\<close> for which $\varepsilon_X$ and $\vartheta_X$ are undefined to the \<open>DumpAction\<close>/\<open>DumpState\<close>.\<close>

function stabilise :: \<open>('a)Act_\<theta> set \<Rightarrow> ('a)Act_\<theta>\<close>
  where 
    \<open>\<forall> \<alpha>\<in>X. (\<exists> \<alpha>'. \<alpha> = act \<alpha>') \<Longrightarrow> stabilise X = \<epsilon> {\<alpha>' . act \<alpha>' \<in> X}\<close>
  | \<open>\<exists> \<alpha>\<in>X. (\<nexists> \<alpha>'. \<alpha> = act \<alpha>') \<Longrightarrow> stabilise X = DumpAction\<close> 
  by metis+
termination using "termination" by blast

text \<open>\pagebreak\<close>
function in_env :: \<open>('a)Act_\<theta> set option \<Rightarrow> 's \<Rightarrow> ('s,'a)Proc_\<theta>\<close>
  where 
    \<open>in_env None p = triggered p\<close>
  | \<open>\<forall> \<alpha>\<in>X. (\<exists> \<alpha>'. \<alpha> = act \<alpha>') \<Longrightarrow> 
      in_env (Some X) p = stable {\<alpha>' . act \<alpha>' \<in> X} p\<close>
  | \<open>\<exists> \<alpha>\<in>X. (\<nexists> \<alpha>'. \<alpha> = act \<alpha>') \<Longrightarrow> 
      in_env (Some X) p = DumpState\<close>
  by (auto, meson Proc_\<theta>.exhaust option.exhaust_sel)
termination using "termination" by blast

text \<open>We show that, with these mappings, any \<open>lts_timeout\<close> (the context we are in) is an \<open>lts_timeout_mappable\<close>: when the variables that were fixed in the locale definition are instantiated by the terms and mappings from the current context, we prove that the assumptions of the locale definition hold. Thus, the reduction works for all \LTSt{}s.\<close>

(* For the following proofs, I gave up on writing readable proofs and simply used what sledgehammer gave me. This is the only part of the the thesis where I do this; sorry... *)
(*<*)
lemma\<^marker>\<open>tag (proof) unimportant\<close> l1:
  fixes X Y x
  assumes a1: \<open>X \<subseteq> lts_timeout.visible_actions tran_mappable (act \<tau>) (act t)\<close>
  assumes a2: \<open>stabilise X = stabilise Y\<close>
  assumes a3: \<open>x \<in> X\<close>
  shows \<open>x \<in> Y\<close>
proof -
  from a1 have \<open>\<forall> x \<in> X. (\<exists> \<alpha>. x = act \<alpha>)\<close>
    by (smt (verit, best) tau_not_t Act_\<theta>.inject(1) lts_timeout.intro lts_timeout.visible_actions_def mem_Collect_eq subset_iff tran_mappable.cases)
  thus \<open>x \<in> Y\<close>
    by (metis (no_types, lifting) Act_\<theta>.distinct(11) Act_\<theta>.inject(2) a2 a3 mem_Collect_eq stabilise.elims)
qed

lemma\<^marker>\<open>tag (proof) unimportant\<close> l2:
  fixes X Y x
  assumes a1: \<open>X \<subseteq> lts_timeout.visible_actions tran_mappable (act \<tau>) (act t)\<close>
  assumes a2: \<open>stabilise X = stabilise Y\<close>
  assumes a3: \<open>x \<in> Y\<close>
  shows \<open>x \<in> X\<close>
proof -
  from a1 have \<open>\<forall> x \<in> X. (\<exists> \<alpha>. x = act \<alpha>)\<close>
    by (smt (verit, best) tau_not_t Act_\<theta>.inject(1) lts_timeout.intro lts_timeout.visible_actions_def mem_Collect_eq subset_iff tran_mappable.cases)
  thus \<open>x \<in> X\<close>
    by (metis (no_types, lifting) Act_\<theta>.distinct(11) Act_\<theta>.inject(2) a2 a3 mem_Collect_eq stabilise.elims)
qed
(*>*)
  
lemma is_mappable: \<open>lts_timeout_mappable 
  tran_mappable (act \<tau>) (act t) t_\<epsilon> stabilise in_env\<close>
  apply standard
  apply auto 
  using stabilise.elims tau_not_t apply fastforce
  using stabilise.elims apply blast
  using stabilise.elims apply blast
  apply (metis Act_\<theta>.distinct(7) Act_\<theta>.distinct(9) stabilise.elims)
  using l1 apply blast
  using l2 apply blast 
  apply (metis Proc_\<theta>.distinct(1) Proc_\<theta>.distinct(3) in_env.simps(2) in_env.simps(3))
  apply (metis (no_types, lifting) Proc_\<theta>.distinct(6) Proc_\<theta>.inject(2) l1 in_env.simps(2) in_env.simps(3) stabilise.simps(1) stabilise.simps(2))
  subgoal proof -
    fix X Y p q x
    assume a1: \<open>X \<subseteq> lts_timeout.visible_actions tran_mappable (act \<tau>) (act t)\<close>
    assume a2: \<open>in_env (Some X) p = in_env (Some Y) q\<close>
    assume a3: \<open>x \<in> Y\<close>

    from a1 have q1: \<open>\<forall> x\<in>X. (\<exists> \<alpha>. x = act \<alpha>)\<close>
      by (metis empty_iff insert_iff l1 l2 stabilise.simps(2))
    hence p1: \<open>in_env (Some X) p = stable {\<alpha> . act \<alpha> \<in> X} p\<close>
      using in_env.simps(2) by presburger

    show \<open>x \<in> X\<close> proof (cases \<open>in_env (Some Y) q = DumpState\<close>)
      case True
      with a2 have \<open>in_env (Some X) p = DumpState\<close> by simp
      hence \<open>\<exists> x\<in>X. (\<nexists> \<alpha>. x = act \<alpha>)\<close>
        by (metis Proc_\<theta>.distinct(6) in_env.simps(2))
      with a1 have False
        by (smt (verit, best) tau_not_t Act_\<theta>.inject(1) in_mono lts_timeout.intro lts_timeout.visible_actions_def mem_Collect_eq tran_mappable.cases)
      then show ?thesis ..
    next
      case False
      hence \<open>in_env (Some Y) q = stable {\<alpha> . act \<alpha> \<in> Y} q\<close>
        by (metis in_env.simps(2) in_env.simps(3))
      hence q2: \<open>\<forall> x\<in>Y. (\<exists> \<alpha>. x = act \<alpha>)\<close>
        using "False" in_env.simps(3) by blast
      hence p2: \<open>in_env (Some Y) q = stable {\<alpha> . act \<alpha> \<in> Y} q\<close>
        using in_env.simps(2) by presburger
      with p1 a2 have \<open>stable {\<alpha> . act \<alpha> \<in> X} p = stable {\<alpha> . act \<alpha> \<in> Y} q\<close> by simp
      hence \<open>{\<alpha> . act \<alpha> \<in> X} = {\<alpha> . act \<alpha> \<in> Y}\<close> by force
      with q1 q2 have \<open>stabilise X = stabilise Y\<close> by simp
      from l2[OF a1 this a3] show ?thesis .
    qed
  qed
  subgoal proof -
    (* This is an automatically sledgehammer-generated Isar proof in all its beauty... \<open>sorry\<close> *)
    fix X Y p q
    assume a1: "X \<subseteq> lts_timeout.visible_actions tran_mappable (act \<tau>) (act t)"
    assume a2: "in_env (Some X) p = in_env (Some Y) q"
    obtain aa where
      f3: "\<forall>A p. aa A \<in> A \<and> (\<forall>a. aa A \<noteq> act a) \<or> in_env (Some A) p = stable {a. act a \<in> A} p"
      by moura
    obtain pp :: "('a)Act_\<theta> \<Rightarrow> ('s \<Rightarrow> ('a)Act_\<theta> \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's" and ppa :: "('a)Act_\<theta> \<Rightarrow> ('s \<Rightarrow> ('a)Act_\<theta> \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's" where
      "\<forall>x0 x1. (\<exists>v4 v5. x1 v4 x0 v5) = x1 (pp x0 x1) x0 (ppa x0 x1)"
      by moura
    then have "aa X \<in> X \<and> (\<forall>a. aa X \<noteq> act a) \<longrightarrow> aa X \<noteq> act \<tau> \<and> aa X \<noteq> act t \<and> tran_mappable (pp (aa X) tran_mappable) (aa X) (ppa (aa X) tran_mappable)"
      using a1
      by (smt (verit, ccfv_threshold) Act_\<theta>.inject(1) lts_timeout.intro lts_timeout.visible_actions_def mem_Collect_eq subsetD tau_not_t)
    then have f4: "in_env (Some X) p = stable {a. act a \<in> X} p"
      using f3 by (meson tran_mappable.cases)
    then have "in_env (Some Y) q \<noteq> DumpState"
      using a2 by (metis Proc_\<theta>.distinct(6))
    then have "in_env (Some Y) q = stable {a. act a \<in> Y} q"
      using f3 by (meson in_env.simps(3))
    then show \<open>p = q\<close>
      using f4 a2 by (metis (no_types) Proc_\<theta>.inject(2))
  qed
  apply (metis Act_\<theta>.distinct(4) Act_\<theta>.simps(8) stabilise.elims tran_mappable.simps)
  apply (simp add: tran_mappable.simps)
  done

end \<comment> \<open>of \<open>context lts_timeout\<close>\<close>


subsubsection \<open>A Tiny Example \LTSt{}\<close>

text \<open>\lts{
    \node[state]    (p0)                            {$p_0$};
    \node[state]    (p1) [below left of=p0]         {$p_1$};
    \node[state]    (p2) [below right of=p0]        {$p_2$};
    \node[state]    (q0) [right of=p0,xshift=3cm]   {$q_0$};
    \node[state]    (q1) [below of=q0]         {$q_1$};
    
    \path   (p0) edge node[above left]  {$\tau$}(p1)
                 edge node              {$t$}   (p2)
            (q0) edge node[above left]  {$\tau$}(q1);
}\<close>

datatype Proc = p0|p1|p2|q0|q1
datatype Act = \<tau>|t
inductive Tran :: \<open>Proc \<Rightarrow> Act \<Rightarrow> Proc \<Rightarrow> bool\<close>
  where 
    \<open>Tran p0 \<tau> p1\<close>
  | \<open>Tran p0 t p2\<close>
  | \<open>Tran q0 \<tau> q1\<close>

text \<open>We interpret the \<open>Tran\<close> predicate as an \<open>lts_timeout\<close>, and then together with our mappings as an \<open>lts_timeout_mappable\<close>.\<close>

interpretation\<^marker>\<open>tag (proof) visible\<close> tiny_lts: 
  lts_timeout Tran \<tau> t
  by (simp add: lts_timeout.intro)
interpretation\<^marker>\<open>tag (proof) visible\<close> tiny_lts_mappable: 
  lts_timeout_mappable tiny_lts.tran_mappable \<open>act \<tau>\<close> \<open>act t\<close> \<open>t_\<epsilon>\<close> 
  tiny_lts.stabilise tiny_lts.in_env 
  using tiny_lts.is_mappable .
\<comment> \<open>(notation assignments omitted from thesis document)\<close>

(*<*)
notation tiny_lts.tran_mappable ("_ \<longmapsto>_ _" [70, 70, 70] 80)
notation tiny_lts.stabilise (\<open>\<epsilon>[_]\<close>) 
notation tiny_lts_mappable.triggered_env (\<open>\<theta>'(_')\<close>)
notation tiny_lts_mappable.stable_env (\<open>\<theta>[_]'(_')\<close>)
notation tiny_lts_mappable.strongly_reactive_bisimilar (\<open>_ \<leftrightarrow>\<^sub>r _\<close> [70, 70] 70)
notation tiny_lts_mappable.strongly_X_bisimilar (\<open>_ \<leftrightarrow>\<^sub>r\<^sup>_ _\<close> [70, 70, 70] 70)
notation tiny_lts_mappable.tran_theta (\<open>_ \<longmapsto>\<^sup>\<theta>_ _\<close> [70, 70, 70] 70)
abbreviation strongly_bisimilar_theta 
  (\<open>_ \<leftrightarrow> _\<close> [70, 70] 70)
  where \<open>strongly_bisimilar_theta \<equiv> lts.strongly_bisimilar tiny_lts_mappable.tran_theta\<close>
abbreviation idle 
  where \<open>idle \<equiv> tiny_lts_mappable.idle\<close>
(*>*)

text \<open>We can now prove a few lemmas about our example \LTSt{} that we would need for any bisimilarity proofs. I abstained from actually including a bisimilarity proof, but these lemmas should, hopefully, suffice to convince you that it would be possible.\<close>

lemma\<^marker>\<open>tag (proof) visible\<close> \<open>tiny_lts_mappable.visible_actions = \<emptyset>\<close> 
proof -
  have \<open>tiny_lts.visible_actions = \<emptyset>\<close>
    using tiny_lts.visible_actions_def 
      Act.exhaust Collect_cong empty_def
    by auto
  moreover have \<open>tiny_lts_mappable.visible_actions 
      = image (\<lambda> \<alpha>. act \<alpha>) tiny_lts.visible_actions\<close>
    using Act.exhaust 
      tiny_lts.tran_mappable.simps 
      tiny_lts.visible_actions_def 
      tiny_lts_mappable.visible_actions_def 
    by auto
  ultimately show ?thesis by force
qed

lemma\<^marker>\<open>tag (proof) visible\<close> \<open>\<nexists> P'. \<theta>[\<emptyset>](p0) \<longmapsto>\<^sup>\<theta>(act t) P'\<close>
proof safe
  fix P'
  assume \<open>\<theta>[\<emptyset>](p0) \<longmapsto>\<^sup>\<theta>(act t) P'\<close>
  hence \<open>idle p0 \<emptyset>\<close> 
    using tiny_lts_mappable.generation_sys_timeout by blast

  have \<open>p0 \<longmapsto>(act \<tau>) p1\<close> using Tran.intros(1)
    by (simp add: tiny_lts.tran_mappable.intros)

  with \<open>idle p0 \<emptyset>\<close> show False 
    unfolding tiny_lts_mappable.initial_actions_def by blast
qed

(*<*)
end \<comment> \<open>of \<open>theory\<close>\<close>
(*>*)