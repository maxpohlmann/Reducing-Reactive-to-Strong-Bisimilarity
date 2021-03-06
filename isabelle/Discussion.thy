(*<*)
theory Discussion
  imports Pure
begin
(*>*)

chapter \<open>Discussion\<close>
text \<open>\label{chap:discussion}\<close>

text \<open>We have shown that checking strong reactive/$X$-bisimilarity (in an \LTSt{}) is reducible to checking strong bisimilarity. This result may be useful in the context of automated tools for checking equivalences on LTSs.
Since, the mapping creates a state for every subset of the visible actions $A$, for each original state, plus another triggered state (i.e.\@ 
$|\Proc_\vartheta| = |\Proc| \cdot (1+2^{|A|})$),
checking reactive bisimilarity by using the mapping would be exponentially harder (in the worst case) than simply checking ordinary bisimilarity. However, at least for SRBs, the size of the relations also grows exponentially with the number of visible actions (due to the clause $(p,q)\in\mathcal{R} \Longrightarrow (p,X,q)\in\mathcal{R}$ for $X\subseteq A$), so a a naïve implementation using SRBs would not necessarily be more efficient. Below, I propose an optimisation that significantly reduces the number of states for a large number of LTSs.

If two processes of a mapped LTS are not strongly bisimilar, an automated tool might produce a distinguishing HML formula. Due to the clear semantics of the actions introduced as part of my mapping, such formulas would be easy to interpret (to understand which sequence of actions distinguishes the two processes).

As mentioned previously, the mapped LTS represents the closed system consisting of the original reactive system and its environment. Hence, the reduction does in no way challenge the semantic value offered by \LTSt{}s, e.g.\@ for protocol specifications. Rather, when shown as a graph, the mapping might complement such specifications by offering a useful view that explicitly shows the specified system in all possible environments. In a mapped LTS, for example, it is easy to find states that are unreachable, or reachable only in certain environments, whereas the reachability of states in an \LTSt{} may not be directly obvious, as we saw in the example on \cpageref{fig:mapping_example}. Admittedly, the mapping gets very crowded even for small \LTSt{}s; on a local level, however, the explicitness of the mapping may be useful. Lastly, it might be helpful simply for understanding \LTSt{} semantics.

The formula mapping is probably less useful in that regard, due to the large number of disjunctions. It might, however, also be useful in the context of automated tools.\<close>


subsubsection \<open>Possible Optimisations\<close>

text \<open>Let $\mathcal{I}^*(p)$ be the set of visible actions that can be encountered as initial actions after arbitrary sequences of $\tau$- and $t$-transitions starting at $p$.

More concretely, for $n \in \mathbb{N}$, let 
\begin{align*}
    p_0 \xrightarrow{X}\!\!\raisebox{1pt}{*}\; p_n &:\Leftrightarrow \exists p_1,\dots,p_{n-1} .\;
    \forall i \in [0,n\!-\!1] .\; \exists \alpha\!\in\!X .\; p_i \xrightarrow{\alpha} p_{i+1}, \\
    \text{reach}(p,X) &:= \{ p' \mid p \xrightarrow{X}\!\!\raisebox{1pt}{*}\; p' \}, \\
    \mathcal{I}^*(p) &:= \bigcup_{p' \in \text{reach}(p,\{\tau,t\})} \mathcal{I}(p').
\end{align*}
Then%
\footnote{Note that $p \in \text{reach}(p,X)$ for all $p$ and $X$.}
we can modify the second rule of the process mapping (from \cref{sec:mapping_lts}) by changing the side condition from $X \subseteq A$ to $X \subseteq \mathcal{I}^*(p)$, yielding:

$$
(2)\,\frac{}{\vartheta(p) \xrightarrow{\varepsilon_X}_\vartheta \vartheta_X(p)} \; X \subseteq \mathcal{I}^*(p).
$$

This way, we only include environment stabilisations that are relevant for the current process: all transitions other than $\tau$ and $t$ will always trigger a change in the environment; hence, after having stabilised, the actions in $\mathcal{I}^*(p)$ are the only ones the process $p$ could ever perform before triggering the environment.

In the worst case, the number of mapping states is still exponential in the size of the alphabet, i.e.\@ $|\Proc_\vartheta| = \mathcal{O}(|\Proc| \cdot 2^{|\Act|})$. For a large number of \LTSt{}s, however, this alteration would reduce the number of mapping states significantly.

For reasons of time, I did not attempt to prove the reduction with this altered mapping, but firmly believe that it is possible.\<close>


subsubsection \<open>Necessity of Special Actions\<close>

paragraph \<open>Environment Time-Outs \boldmath{$t_\varepsilon$}\<close>
text \<open>It should be possible to replace the action $t_\varepsilon$ by the normal time-out action $t$ in the mapping. Since, in the present version, all $t_\varepsilon$-transitions end in a $\vartheta(p)$-state, where always at least an $\varepsilon_\emptyset$-transition can be performed, whereas all $t$-transitions end in a $\vartheta_X(p)$-state, where no $\varepsilon_\emptyset$-transition can ever be performed, the distinction between environment time-outs and system time-outs should be possible without distinguishing the actions $t$ and $t_\varepsilon$.
\pagebreak\<close>

paragraph \<open>Environment Stabilisations \boldmath{$\varepsilon_X$}\<close>
text \<open>In the first version of the mapping, I used a single stabilisation action $s_\varepsilon$, but got stuck trying to prove that $\vartheta(p) \leftrightarrow \vartheta(q)$ implies $\forall X \subseteq A .\; \vartheta_X(p) \leftrightarrow \vartheta_X(q)$. 

Concretely, in such a version of the mapping with only one stabilisation action, the bisimilarity property would allow us to conclude from \linebreak $\vartheta(p) \leftrightarrow \vartheta(q)$ only that $\forall X \subseteq A .\; \exists Y \subseteq A .\; \vartheta_X(p) \leftrightarrow \vartheta_Y(q)$. Since $\vartheta_X(p)$ then cannot have transitions with labels in $X \!\setminus\! Y$, because $\vartheta_Y(q)$ could not mirror these transitions (and also the other way around for transitions of $\vartheta_Y(q)$ with labels in $Y \!\setminus\! X$), I attempted to prove that this implies $\forall X \subseteq A .\; \vartheta_X(p) \leftrightarrow \vartheta_X(q)$. However, the fact that $p$ and $q$ might have $\tau$- or $t$-transitions necessitates that one also considers the transitions of those derivative states. Arbitrarily long sequences of $\tau$-/$t$-transitions are then the crux of this lemma.
After many days of unsuccessful proof attempts, I admitted defeat and defined the family of stabilisation actions instead. Sadly, I did not manage to find a counterexample where the reduction using this simpler mapping does not work, either.

However, in the context of \HMLt{}, there would be no obvious way to define the formula mapping for $\sigma(\langle X \rangle \varphi)$; in the present version, the mapping relies on being able to use $\varepsilon_X$ in this case (see \cref{sec:mapping_formulas}). Hence, I have to come believe that the $\varepsilon_X$-actions might indeed be required in their present form.

Furthermore, although including the environment information both in the states $\vartheta_X(p)$ as well as the stabilisation actions $\varepsilon_X$ may seem redundant, it might be necessary. As we discussed in \cref{sec:strong_bisimilarity}, the intensional identity of the state is not \enquote{knowable for bisimilarity}; rather, only the observable transitions are relevant. Hence, it is plausible that the information about allowed actions is actually required to be included in the transition labels themselves, in order for the reduction to work.\<close>

subsubsection \<open>Isabelle Formalisations\<close>

text \<open>The Isabelle formalisations that were done as part of this thesis have been the first formalisations of \LTSt{}s and related concepts. 

The only Isabelle formalisation of a Hennessy-Milner logic published on the \emph{Isabelle Archive of Formal Proofs} was presented in @{cite weber2021modal}.
The variant of HML formalised there includes \emph{state predicates} evaluated on \emph{nominal transition systems} (i.e.\@ each state of the transition system is associated with a set of satisfied state predicates); the formalisations are considerably more complex than those done in this thesis. 

Potential future projects requiring only \enquote{purely modal} Hennessy-Milner logic might benefit from the simplicity of these formalisations. Thus, the formalisation of (simple) Hennessy-Milner logic in \cref{sec:HML} or of infinitary Hennessy-Milner logic in \cref{chap:HML_infinitary} might be useful in future research.\<close>

(*<*)
end
(*>*)