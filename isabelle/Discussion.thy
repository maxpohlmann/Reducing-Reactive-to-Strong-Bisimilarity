(*<*)
theory Discussion
  imports Pure
begin
(*>*)

chapter \<open>Discussion\<close>
text \<open>\label{chap:discussion}\<close>

text \<open>We have shown that checking strong reactive/$X$-bisimilarity (in an \LTSt{}) is reducable to checking strong bisimilarity. This result may be useful in the context of automated tools for checking equivalences on LTSs.
Since, the mapping creates a state for every subset of the visible actions $A$, for each original state, plus another triggered state (i.e.\@ 
$|\Proc_\vartheta| = |\Proc| \cdot (1+2^{|A|})$),
checking reactive bisimilarity by using the mapping would be exponentially harder (in the worst case) than simply checking ordinary bisimilarity. However, at least for SRBs, the size of the relations also grows exponentially with the number of visible actions (due to the clause $(p,q)\in\mathcal{R} \Longrightarrow (p,X,q)\in\mathcal{R}$ for $X\subseteq A$), so a a naïve implementation using SRBs would not necessarily be more efficient. Below, I propose an optimisation that significantly reduces the number of states for a large number of LTSs.

As I mentioned in \cref{sec:mapping_lts}, the mapped LTS represents the closed system consisting of the original reactive system and its environment. Hence, the reduction does in no way challenge the semantic value offered by \LTSt{}s, e.g.\@ for protocol specifications. Rather, when shown as a graph, the mapping offers a useful view at systems specified as \LTSt{}s that explicilty shows them in all possible \enquote{situations}. In a mapped LTS, for example, it is easy to find states that are unreachable, or reachable only in certain environments, whereas the reachability of states in an \LTSt{} may not be directly obvious, as we saw in the example on \cpageref{fig:mapping_example}. Admittedly, the mapping gets very crowded even for small \LTSt{}s; on a local level or merely as a thinking aid, however, the \enquote{explicitness} of the mapping may be useful.

The formula mapping is probably less useful in that regard, due to the large number of disjunctions. It might, however, also be useful in the context of automated tools.\<close>


subsubsection \<open>Possible Optimisations\<close>

text \<open>Let $\mathcal{I}^*(p)$ be the set of visible actions that can be encountered as initial actions after arbitrary sequences of $\tau$- and $t$-transitions starting at $p$.

More concretely, for $n \in \mathbb{N}$, let 
\begin{align*}
    p_0 \xrightarrow{X}\!\!\raisebox{1pt}{*}\; p_n &\equiv \exists p_1,\dots,p_{n-1} .\;
    \forall i \in [0,n\!-\!1] .\; \exists \alpha\!\in\!X .\; p_i \xrightarrow{\alpha} p_{i+1}; \\
    \text{reach}(p,X) &\equiv \{ p' \mid p \xrightarrow{X}\!\!\raisebox{1pt}{*}\; p' \}; \\
    \mathcal{I}^*(p) &\equiv \bigcup_{p' \in \text{reach}(p,\{\tau,t\})} \mathcal{I}(p').
\end{align*}
Then%
\footnote{Note that $p \in \text{reach}(p,X)$ for all $p$ and $X$.}
we can modify first rule of the process mapping (from \cref{sec:mapping_lts}) by changing the side condition from $X \subseteq A$ to $X \subseteq \mathcal{I}^*(p)$, yielding:

$$
(1)\,\frac{}{\vartheta(p) \xrightarrow{\varepsilon_X}_\vartheta \vartheta_X(p)} \; X \subseteq \mathcal{I}^*(p).
$$

This way, we only include environment stabilisations that are relevant for the current process: all transitions other than $\tau$ and $t$ will always trigger a change in the environment; hence, after having stabilised, the actions in $\mathcal{I}^*(p)$ are the only ones the process $p$ could ever perform before triggering the environment.

In the worst case, the number of mapping-states is still exponential in the size of the alphabet, i.e.\@ $|\Proc_\vartheta| = \mathcal{O}(|\Proc| \cdot 2^{|\Act|})$. For a large number of \LTSt{}s, however, this alteration would reduce the number of mapping-states significantly.

Unfortunately, I did not manage to prove the reduction with this altered mapping, but I am convinced that it is possible.\<close>


subsubsection \<open>Necessity of Special Actions\<close>

paragraph \<open>Environment Time-Outs \boldmath{$t_\varepsilon$}\<close>
text \<open>It should be possible to replace the action $t_\varepsilon$ by the normal time-out action $t$ in the mapping. Since, in the present version, all $t_\varepsilon$-transitions end in a $\vartheta(p)$-state, where always at least an $\varepsilon_\emptyset$-transition can be performed, whereas all $t$-transitions end in a $\vartheta_X(p)$-state, where no $\varepsilon_Y$-transition can ever be performed, the distinction between environment time-outs and system time-outs should be possible without distinguishing the actions $t$ and $t_\varepsilon$.\<close>

paragraph \<open>Environment Stabilisations \boldmath{$\varepsilon_X$}\<close>
text \<open>In the first version of the mapping, I used a single stabilisation action $s_\varepsilon$, but got stuck trying to prove that $\vartheta(p) \leftrightarrow \vartheta(q)$ implies $\forall X \subseteq A .\; \vartheta_X(p) \leftrightarrow \vartheta_X(q)$, which lead me to define the family of stabilisation actions instead. Sadly, I did not manage to find a counterexample where the reduction using this simpler mapping does not work. 

However, in the context of \HMLt{}, there would be no obvious way to define the formula mapping for $\sigma(\langle X \rangle \varphi)$; in the present version, the mapping relies on being able to use $\varepsilon_X$ in this case (see \cref{sec:mapping_formulas}). Hence, I have come believe that the $\varepsilon_X$-actions are indeed required in their present form.

Furthermore, although including the environment information both in the states $\vartheta_X(p)$ as well as the stabilisation actions $\varepsilon_X$ may seem redundant, it might be required. As we discussed in \cref{sec:strong_bisimilarity}, the intensional identity of the state is not \enquote{knowable for bisimilarity}; rather, only the observable transitions are relevant. Hence, it is plausible that the information about allowed actions is required to be included in the transition labels themselves, in order for the reduction to work.\<close>

(*<*)
end
(*>*)