(*<*)
theory Labelled_Transition_Systems
  imports
    "HOL-Library.Countable_Set"
begin

(* All other theories import this one, so I will introduce some notation here. *)
notation Set.empty (\<open>\<emptyset>\<close>)
notation (input)
  HOL.eq  (infixr "\<Longleftrightarrow>" 25)
(*>*)


section \<open>Labelled Transition Systems\<close>
text \<open>\label{sec:LTS}\<close>

text \<open>A Labelled Transition System (LTS) consists of a set of processes (or states) $\Proc$, a set of actions $\Act$, and a relation of transitions $\cdot\xrightarrow{\cdot}\cdot \subseteq \Proc\times\Act\times\Proc$ which directedly connect two processes by an action (the action being the label of the transition) @{cite resyst}. We call a transition labelled by an action $\alpha$ an \emph{$\alpha$-transition}.

LTSs can model reactive systems, as discussed in \cref{chap:introduction}. A process of an LTS, then, corresponds to a momentary state of a reactive system. The outgoing transitions of each process correspond to the actions the reactive system could perform in that state (yielding a subsequent process/state), if facilitated by the environment. The choice between the facilitated transitions of a process is non-deterministic.

This facilitation by the environment can be thought of as a set of actions that the environment allows in a given moment, or, more intuitively, as a set of simultaneous inputs from the environment to which the system may react. We call the actions not allowed by the environment in a given moment \emph{blocked}.

The environment can also observe which transitions a system performs and change the set of allowed actions in response.

In classical treatments of LTSs, the actions that the environment allows, blocks, or reacts to, are often considered only implicitly. The reason we put this emphasis on the environment here will become apparent in \cref{sec:LTSt}.

\example{%
The process $p$ can perform any of the $a$-transitions in environments allowing $a$ and the $b$-transition in environments allowing $b$. All derivative (subsequent) states cannot perform any transition.

\lts{
    \node[state]    (p0)                        {$p$};
    \node[state]    (p1) [below left of=p0]     {$p_1$};
    \node[state]    (p2) [below of=p0]          {$p_2$};
    \node[state]    (p3) [below right of=p0]    {$p_3$};
    
    \path   (p0) edge node[above left]          {$a$}   (p1)
                 edge node[above right]         {$a$}   (p2)
                 edge node[above right]         {$b$}   (p3);
}}

A \emph{hidden action}, denoted by $\tau$, allows for additional semantics: a $\tau$-transition can be performed by a process regardless of the set of actions allowed by the current environment. Depending on the specific semantic context, the performance of a hidden action may also be unobservable (hence the name).\<close>

subsubsection \<open>Some Definitions\<close>

text \<open>The $\alpha$-derivatives of a state are those states that can be reached with one $\alpha$-transition:
$$\mathit{Der}(p, \alpha) = \{ p' \mid p \xrightarrow{\alpha} p' \}.$$

An LTS is image-finite iff all derivative sets are finite:
$$\forall p \in \Proc, \alpha \in \Act .\; \mathit{Der}(p, \alpha) \text{ is finite}.$$

Similarly, we can say an LTS is image-countable iff all derivative sets are countable:
$$\forall p \in \Proc, \alpha \in \Act .\; \mathit{Der}(p, \alpha) \text{ is countable}.$$\<close>

subsubsection \<open>Note on Metavariable usage\<close>

text \<open>States of an LTS range over $p, q, p', q', \dots$, where $p$ and $p'$ are used for states connected by some transition (i.e.\@ $p \xrightarrow{\alpha} p'$), whereas $p$ and $q$ are used for states possibly related by some equivalence (e.g.\@ $p \leftrightarrow q$), as will be discussed in the next section.

An arbitrary action of an LTS will be referenced by $\alpha$, whereas an arbitrary \emph{visible} action will be referenced by $a$.\<close>

subsubsection \<open>Practical Example\<close>

text \<open>Before we look at the Isabelle formalisation of LTSs, let us take a detour away from purely theoretical deliberations and consider a real-world machine that may be modelled by an LTS. We can imagine a very simple snack-selling vending machine that accepts only one type of coin and has individual buttons for each of the snacks. When a coin is inserted and a button pressed, the machine dispenses the desired snack and is then ready to accept coins once again. Because the dispensing of the snack itself requires no interaction from the user, we model it as a $\tau$-transition.

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
                 
    \draw (p2) to[out=150, in=210, looseness=1, edge node={node [left] {$\tau$}}] (p0);
    \draw (p4) to[out=30, in=-30, looseness=1, edge node={node [right] {$\tau$}}] (p0);
    \draw (p3) to[out=-20, in=0, looseness=2.5, edge node={node [right] {$\tau$}}] (p0);
}\<close>


subsection \<open>Isabelle\<close>

text \<open>In the following Isabelle formalisation of LTSs, the sets of states and actions are denoted by type variables \<open>'s\<close> and \<open>'a\<close>, respectively. A specific LTS on these sets is then determined entirely by its set of transitions, denoted by the predicate \<open>tran\<close>. We can also associate it with a more readable notation (\<open>p \<longmapsto>\<alpha> p'\<close> for $p \xrightarrow{\alpha} p'$).\<close>

locale lts = 
  fixes tran :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close> 
    ("_ \<longmapsto>_ _" [70, 70, 70] 80)
begin

text \<open>The other concepts above can be formalised in a straight-forward manner:\<close>

abbreviation derivatives :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's set\<close> 
  (\<open>Der'(_, _')\<close> [50, 50] 1000)
  where \<open>Der(p, \<alpha>) \<equiv> {p'. p \<longmapsto>\<alpha> p'}\<close>

text \<open>The following properties concern the entire LTS at hand (given by the locale context) and will be useful when we want to state lemmas that only hold for LTSs that satisfy these properties.\<close>

definition image_finite :: \<open>bool\<close>
  where \<open>image_finite \<equiv> (\<forall> p \<alpha>. finite Der(p, \<alpha>))\<close>

definition image_countable :: \<open>bool\<close>
  where \<open>image_countable \<equiv> (\<forall> p \<alpha>. countable Der(p, \<alpha>))\<close>

end \<comment> \<open>of \<open>locale lts\<close>\<close>


text \<open>We formalise LTSs with hidden actions as an extension of ordinary LTSs with a fixed action \<open>\<tau>\<close>.\<close>

locale lts_tau = lts tran 
  for tran :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close> + 
  fixes \<tau> :: \<open>'a\<close>

(*<*)
end \<comment> \<open>of theory\<close>
(*>*)