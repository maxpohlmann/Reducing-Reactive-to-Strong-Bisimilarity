(*<*)
theory Reductions
  imports Pure
begin
(*>*)

chapter \<open>The Reductions\<close>
text \<open>\label{chap:reductions}\<close>

text \<open>In @{cite rbs}, van~Glabbeek presents various characterisations of reactive bisimilarity, three of which have been presented in previous sections (SRBs, GSRBs, and the modal characterisation). Another one introduces \emph{environment operators} $\theta_X$ (for $X \subseteq A$), which \enquote{place a process in \textins{a \emph{stable}} environment that allows exactly the actions in $X$ to occur} @{cite \<open>section 4\<close> rbs}. The precise semantics are given by structural operational rules, e.g.: $p \xrightarrow{\tau} p' \Longrightarrow \theta_X(p) \xrightarrow{\tau} \theta_X(p')$. However, for the characterisation of reactive bisimilarity, the definition of another kind of relations, namely \emph{time-out bisimulations}, is required. 

This inspired me to come up with a mapping (from \LTSt{}s to LTSs) that explicitly models the entire behaviour of the environment (including triggered environments that may stabilise into arbitrary stable environments) and its interaction with the reactive system. Concretely, the resulting LTS will contain a state for each state of the original \LTSt{} in every possible environment. By doing this, the resulting LTS will not be a model of a reactive system, but of the closed system consisting of the original underlying system and its environment, modelling all possible combined states and the transitions between those.

Since the entire semantics of \LTSt{}s will be incorporated in the mapping, the observable behaviour of the closed system will be equivalent for underlying reactive systems that are strongly reactive bisimilar. In other words: two processes of an \LTSt{} are strongly reactive bisimilar iff their corresponding processes in the mapped LTS are strongly bisimilar. This mapping will be presented in \cref{sec:mapping_lts} and the reduction established in \cref{sec:reduction_bisimilarity}.

As a natural consequence, a reduction for the satisfaction of \HMLt{} formulas can be given as well.
In \cref{sec:mapping_formulas}, I will present a mapping from \HMLt{} formulas to HML formulas such that, as we will see in \cref{sec:reduction_satisfaction}, a mapped formula holds in a process of a mapped LTS iff the original formula holds in the corresponding process of the original \LTSt{}.\<close>

(*<*)
end
(*>*)