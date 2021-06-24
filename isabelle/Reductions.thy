(*<*)
theory Reductions
  imports Pure
begin
(*>*)

chapter \<open>The Reductions\<close>
text \<open>\label{chap:reductions}\<close>

text \<open>In @{cite rbs}, various characterisations of reactive bisimilarity are presented, three of which we have seen in previous sections (SRBs, GSRBs, and the modal characterisation). Another one introduces \emph{environment operators} $\theta_X$, which \enquote{place a process in \textins{a \emph{stable}} environment that allows exactly the actions in $X$ to occur} @{cite \<open>section 4\<close> rbs}. The precise semantics are given by structural operational rules, e.g.: $p \xrightarrow{\tau} p' \Longrightarrow \theta_X(p) \xrightarrow{\tau} \theta_X(p')$. For the characterisation of reactive bisimilarity, the definition of another kind of relations, namely \emph{time-out bisimulations}, is required. 

This inspired me to come up with a mapping (from \LTSt{}s to LTSs) that explicitly models the entire behaviour of the environment and its interaction with the reactive system. Concretely, the resulting LTS will contain a state for each state of the original \LTSt{} in every possible environment (including indeterminate ones). Therefore, the resulting LTS will not be a model of a reactive system, but of the closed system consisting of the original underlying system and its environment.

This approach basically treats the environment as an unknown process placed in parallel with the system; this has also been suggested by van~Glabbeek in @{cite \<open>section 2\<close> rbs}. There, however, the action $t$ must still be treated as a special action with special semantics. For the reduction presented in the next sections, the entire semantics of \LTSt{}s will be incorporated in the mapping, where all actions are then treated equally, and so that two processes of an \LTSt{} are strongly reactive bisimilar iff their corresponding processes in the mapped LTS are strongly bisimilar. The mapping will be presented in \cref{sec:mapping_lts} and the reduction established in \cref{sec:reduction_bisimilarity}.

As a natural consequence, a reduction for the satisfaction of \HMLt{} formulas can be given as well:
in \cref{sec:mapping_formulas}, I will present a mapping from \HMLt{} formulas to HML formulas such that, as we will see in \cref{sec:reduction_satisfaction}, a mapped formula holds in a process of a mapped LTS iff the original formula holds in the corresponding process of the original \LTSt{}.\<close>

(*<*)
end
(*>*)