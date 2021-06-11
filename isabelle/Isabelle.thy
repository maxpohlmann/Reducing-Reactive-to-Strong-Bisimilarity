(*<*)
theory Isabelle
  imports 
    HOL.HOL
    HOL.Int
    HOL.Nat
begin
(*>*)

chapter \<open>Isabelle\<close>
text \<open>\label{chap:isabelle}\<close>

text \<open>Isabelle is an interactive proof assistant and Isabelle/HOL is an implementation of \emph{higher-order logic} in Isabelle. With it, one can interactively prove propositions about theories that are formalised in terms of higher-order logic. Many theories have been formalised (and many theorems proven) in Isabelle/HOL and are publicly available.\footnote{see Isabelle's Archive of Formal Proofs at \code{\href{https://www.isa-afp.org}{isa-afp.org}}}

In this appendix, I will give a short introduction into the most important concepts of Isabelle. For an extensive tutorial, see @{cite prog_prove}. A complete documentation can be found in @{cite isar_ref}.
\vspace{-.3cm}\<close>

subsubsection \<open>Simple Definitions\<close>

text \<open>The command \<open>definition\<close> defines a term by establishing an equality, denoted by \<open>\<equiv>\<close>. This term can be a function or a constant (i.e.\@ 0-ary function). Predicates are functions to Boolean values.

Definitions are annotated by their type. As an example, we define the predicate \<open>even\<close>, which maps an integer to a Boolean value.\<close>

definition even :: \<open>int \<Rightarrow> bool\<close>
  where \<open>even n \<equiv> \<exists> m::int . n = 2 * m\<close>

text \<open>Functions can be defined in uncurried form (e.g.\@ \<open>(int \<times> int) \<Rightarrow> bool\<close>) or in curried form (e.g.\@ \<open>int \<Rightarrow> int \<Rightarrow> bool\<close>). As a very trivial example, we can define equality predicates for integers. Compared to the curried version, the uncurried version does not allow for easy pattern matching. This is why, in this thesis, I usually specify functions in curried form.\<close>

definition equal_uncurried :: \<open>(int \<times> int) \<Rightarrow> bool\<close>
  where \<open>equal_uncurried pair \<equiv> \<exists> n m. pair = (n, m) \<and> n = m\<close>

definition equal_curried :: \<open>int \<Rightarrow> int \<Rightarrow> bool\<close>
  where \<open>equal_curried n m \<equiv> n = m\<close>

text \<open>We can also use type variables (prefixed with an apostrophe, e.g.\@ \<open>'a\<close>) instead of concrete types to get more abstract terms.\<close>

definition equal_abstract :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where \<open>equal_abstract a b \<equiv> a = b\<close>

text \<open>For a less trivial example, we define a predicate \<open>symmetric\<close> that determines whether a given relation is symmetric. An arbitrary homogeneous relation in curried form has the type \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>.\<close>

definition symmetric :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where \<open>symmetric R \<equiv> \<forall> a b. R a b \<longrightarrow> R b a\<close>

text \<open>We can also assign notation to a term during the definition, where \<open>_\<close> is a placeholder (and the numbers behind the notation specification represent priorities for parsing, which may be ignored by the reader).\<close>

definition approx :: \<open>int \<Rightarrow> int \<Rightarrow> bool\<close>
  (\<open>_ \<approx> _\<close> [50, 50] 50)
  where \<open>n \<approx> m \<equiv> n=m-1 \<or> n=m \<or> n=m+1\<close>

text \<open>Abbreviations are used the same way as definitions, except that, in order to use the equality established by definitions in proofs, we need to explicitly refer to the definition, whereas abbreviations are always expanded internally by the proof system. An example a little further down below should clarify the distinction.\<close>

abbreviation reflexive :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where \<open>reflexive R \<equiv> \<forall> a. R a a\<close>

subsubsection \<open>Proving Propositions\<close>

text \<open>Propositions can be given using any of the commands \<open>proposition\<close>, \<open>lemma\<close>, \<open>theorem\<close>, \<open>corollary\<close>, and require a proof.

Since Isabelle is an \emph{interactive} proof assistant, proofs are usually meant to be spelled out in code so as to be readable by humans, and the validity of individual steps is verified by certain automated proof methods (e.g.\@ \<open>simp\<close>, \<open>arith\<close>, \<open>auto\<close>, \<open>fast\<close>, \<open>blast\<close>, \dots). 

As an example, we will show that the relation \<open>approx\<close> is \<open>symmetric\<close>.

Since \<open>symmetric\<close> was defined using the command \<open>definition\<close>, we need to explicitly unfold it, where \<open>symmetric_def\<close> is the fact (about the equality) introduced by the definition.

The method specified after the command \<open>proof\<close> adjusts the proof goal in some way. Ideally, the proof steps should be clear to the reader even without seeing what exactly the automated methods are doing. I have explained each of the steps using comments below.
\pagebreak\<close>

proposition\<^marker>\<open>tag (proof) visible\<close> \<open>symmetric approx\<close>
  unfolding symmetric_def
proof (clarify)
  \<comment> \<open>We want to show that for any \<open>n\<close> and \<open>m\<close> with \<open>n \<approx> m\<close>, we have \<open>m \<approx> n\<close>.\<close>
  fix n m
  assume \<open>n \<approx> m\<close>
  \<comment> \<open>Using the definition of \<open>approx\<close>, we know this about \<open>n\<close> and \<open>m\<close>.\<close>
  hence \<open>n=m-1 \<or> n=m \<or> n=m+1\<close> unfolding approx_def .
  thus \<open>m \<approx> n\<close>
  \<comment> \<open>With disjunction elimination, we examine each case in a sub-proof.\<close>
  proof (elim disjE)
    assume \<open>n = m - 1\<close>
    hence \<open>m = n + 1\<close> by arith
    thus \<open>m \<approx> n\<close> unfolding approx_def by blast
  next
    assume \<open>n = m\<close>
    thus \<open>m \<approx> n\<close> using approx_def by blast
  next
    assume \<open>n = m + 1\<close>
    hence \<open>m = n - 1\<close> by arith
    thus \<open>m \<approx> n\<close> using approx_def by blast
  qed
qed

text \<open>This proof was probably more detailed than was necessary. By unfolding the other definition as well, this proposition can be proven directly with the proof method \<open>arith\<close>.\<close>

proposition\<^marker>\<open>tag (proof) visible\<close> \<open>symmetric approx\<close>
  unfolding symmetric_def approx_def by arith

text \<open>To see the difference between definitions and abbreviations, note that the following proposition is provable without unfolding \<open>reflexive_def\<close> (since \<open>reflexive\<close> is an abbreviation, there is no such fact in this context).\<close>

proposition\<^marker>\<open>tag (proof) visible\<close> \<open>reflexive approx\<close>
  unfolding approx_def by auto

text \<open>In practice, of course, one has to strike a balance between transparency/comprehensibility and conciseness of proofs.\<close>

subsubsection \<open>Inductive Definitions\<close>

text \<open>Inductively defined predicates can be given using premise-conclusion pairs and multiple clauses.\<close>

inductive even_ind :: \<open>int \<Rightarrow> bool\<close>
  where
    \<open>even_ind 0\<close>
  | \<open>even_ind n \<Longrightarrow> even_ind (n+2)\<close>

subsubsection \<open>Function Definitions\<close>

text \<open>The command \<open>function\<close> also establishes equalities, but usually in more complex ways, so that it may not obvious whether a function is well-defined. Hence, the well-definedness needs to be proved explicitly. (These proofs are usually solved by the automated proof methods.)

The function is then assumed to be partial. The command \<open>termination\<close> introduces proof obligations to show that the function always terminates (and is thus total). For the example below, this is again proved automatically.

After proving well-definedness and totality, we have access to facts about the function that can be used in proofs, e.g.\@ induction principles. More details can be found in \cref{sec:HML}, where we define a non-trivial \<open>function\<close>.\<close>

function\<^marker>\<open>tag (proof) visible\<close> factorial :: \<open>nat \<Rightarrow> nat\<close>
  where
    \<open>n = 0 \<Longrightarrow> factorial n = 1\<close>
  | \<open>n > 0 \<Longrightarrow> factorial n = n * factorial (n-1)\<close>
  by auto

termination\<^marker>\<open>tag (proof) visible\<close> factorial using "termination" by force

subsubsection \<open>Data Types\<close>

text \<open>With the command \<open>datatype\<close>, new types can be defined, possibly in dependence on existing types, by defining a set of (object) constructor functions. For example, we can (re-)define the type of natural numbers.\<close>

datatype natural_number =
  Zero \<comment> \<open>0-ary base constructor\<close>
| Suc \<open>natural_number\<close> \<comment> \<open>unary recursive/inductive constructor\<close>

text \<open>We can define type constructors, i.e.\@ types depending on other types (to be distinguished from the object constructors above) by parameterising the type with type variables.\<close>

datatype ('a)list =
  Empty
| Cons \<open>'a\<close> \<open>('a)list\<close>

subsubsection \<open>Locales\<close>

text \<open>Locales define a context consisting of type variables, object variables, and assumptions. These can be accessed in the entire context. Locales can also be instantiated by specifying concrete types (or type variables from another context) for the type variables, and extended to form new locales. We can reenter the context of a locale later on, using the command \<open>context\<close>.

\Cref{sec:LTS} provides a good example for how locales are used in Isabelle to formalise linear transition systems.\<close>

(*<*)
end
(*>*)