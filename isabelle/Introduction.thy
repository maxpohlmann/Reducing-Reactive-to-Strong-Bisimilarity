(*<*)
theory Introduction
  imports 
    Pure
begin
(*>*)

chapter \<open>Introduction\<close>
text \<open>\label{chap:introduction}\<close>

text \<open>In this thesis, I show that it is possible to reduce the problem of checking strong reactive bisimilarity, as introduced by Rob van Glabbeek in @{cite rbs}, to checking ordinary strong bisimilarity. I do this by specifying a mapping that yields a model of the closed system consisting of some original (reactive) system and its environment. 
I formalised all concepts discussed in this thesis, and conducted all the proofs, in the interactive proof assistant Isabelle.

Reactive systems are systems that continuously interact with their envi\-ronment (e.g.\@ a user) and whose behaviour is largely dependent on this interaction @{cite harel85}.
They can be modelled using labelled transition systems (LTSs) @{cite keller76}; roughly, an LTS is a labelled directed graph, whose nodes correspond to states of a reactive system and whose edges correspond to transitions between those states.%
\footnote{The topics of this thesis are applicable to any such graphs in an abstract way. However, I will continue to use motivations and terminology derived from the interpretation of LTSs as reactive systems.}

A user interacting with some system can only perceive it in terms of the interactions it reacts to, i.e.\@ the internal state of the system is hidden from the user. This begets a notion of behavioural/observational equivalence: two non-identical systems may exhibit equivalent behaviour as observed by the user. The simplest such equivalence is known as \emph{strong bisimilarity}.

In classical LTSs, a system cannot react to the absence of interaction, as it would be assumed to simply wait for any interaction. Intuitively, however, a system may be equipped with a clock and perform some activity when it has seen no interaction from the user for a specified time. Such a system would not be describable with classical LTS semantics. Amongst these systems are, e.g., systems implementing mutual exclusion protocols @{cite rbs}.

\pagebreak
In @{cite vanglabbeek2021failure}, Rob van~Glabbeek introduces labelled transition systems with time-outs (\LTSt{})%
\footnote{He does not use that specific term or abbreviation, however.}%
, which allow for modelling such systems as well.
The appertaining equivalence is given in @{cite rbs} as \emph{strong reactive bisimilarity}.

For the first main result of this thesis, I show that it is possible to reduce checking strong reactive bisimilarity to checking strong bisimilarity. This is in line with reductions of other behavioural equivalences to strong bisimilarity. For example, a strategy used to reduce \emph{weak bisimilarity} to strong bisimilarity is called \emph{saturation} and is described in @{cite \<open>section 3.2.5\<close> advBC_algorithmics}.

The strategy used for reducing reactive bisimilarity to strong bisimilarity is based on the fact that the concept of strong reactive bisimilarity requires an explicit consideration of the environments in which specified systems may exist. Concretely, I specify a mapping from \LTSt{}s to LTSs, where each state of the mapped LTS corresponds to a state of the original \LTSt{} in some specific environment. This approach has been hinted at by van~Glabbeek at various points in @{cite rbs}, but has not been made explicit.

The reduction of reactive bisimilarity could be of use in the context of automated model checking tools: there are known algorithms for checking equivalences (e.g.\@ see @{cite advBC_algorithmics}) and tools with efficient implementations thereof;%
\footnote{e.g.\@ see LTSmin at \code{\href{https://github.com/utwente-fmt/ltsmin}{github.com/utwente-fmt/ltsmin}}}
instead of implementing an algorithm for checking strong reactive bisimilarity from scratch, an implementation of the reduction would allow the use of these existing implementations.
Moreover, the mapping used for the reduction may aid in the analysis of system specifications using \LTSt{}s, by providing a more explicit view at the system.

Another interesting way to examine the behaviour of an LTS is through the use of modal logics, where formulas describe certain properties and are evaluated on states of an LTS. A commonly used modal logic is known as Hennessy-Milner logic (HML). 
An extension of HML for evaluation on states of an \LTSt{} is also given in @{cite rbs}; I will refer to this extension as Hennessy-Milner logic with time-outs (\HMLt{}).

For the second main result of this thesis, I show that it is possible to reduce formula satisfaction of \HMLt{} on \LTSt{}s to formula satisfaction of HML on LTSs (using another mapping for formulas, along with the mapping from the first reduction).
\newpage\<close>

subsubsection \<open>How This Thesis is Structured / Isabelle\<close>

text \<open>The remainder of this thesis is split into \nameref{chap:foundations} (\cref{chap:foundations}), where LTSs, bisimilarity, and Hennessy-Milner logic, all without and with time-outs, are discussed and formalised, and \nameref{chap:reductions} (\cref{chap:reductions}), where the reduction of bisimilarity and the reduction of formula satisfaction are presented in detail and proved.

All the main topics of this thesis have been formalised, and all proofs conducted, using the interactive proof assistant Isabelle. More information on Isabelle and a short introduction to the most important concepts can be found in \cref{chap:isabelle}.

This thesis document itself was generated using the Isabelle document preparation system (see @{cite isa_system}), which generates \LaTeX{} markup from Isabelle code (and, of course, integrates markup written manually). This allowed me to integrate all the Isabelle code directly into the thesis document.
However, almost all proofs are hidden (and replaced simply by \<open>\<proof>\<close>) and some lemmas excluded. In these cases, an indication of the proof strategy used is given in text. A web version of this thesis, that includes all formalisations, propositions, and proofs, as well as all the text, can be found on GitHub Pages, with one page for each section of this thesis.%
\footnote{see \code{\href{https://maxpohlmann.github.io/Reducing-Reactive-to-Strong-Bisimilarity}%
{maxpohlmann.github.io/Reducing-Reactive-to-Strong-Bisimilarity}}}

All of the sections of \cref{chap:foundations,chap:reductions} are split into two parts: one containing a prosaic and mathematical description of the topics, and one containing the (documented) formalisation/implementation in Isabelle. I try to clearly distinguish between mathematical structures and their implementation. Although the two are, necessarily, closely related, they are not identical. The former is written in \LaTeX{} math mode in this $italic\;font$, the latter is Isabelle code in this \<open>monospaced font\<close>.\<close>

(*<*)
end
(*>*)