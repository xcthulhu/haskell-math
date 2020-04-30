section \<open>Combinatory Logic\<close>

(*:maxLineLen=80:*)

theory Combinators
  imports "./Minimal_Logic"
begin

subsection \<open>Definitions\<close>

text \<open>Combinatory logic, following Curry (TODO: citeme), can be formulated as 
      follows.\<close>

datatype Var = Var nat ("\<X>")

datatype SKComb =
    Var_Comb Var ("\<^bold>\<langle>_\<^bold>\<rangle>" [100] 100)
  | S_Comb ("S")
  | K_Comb ("K")
  | Comb_App "SKComb" "SKComb"  (infixl "\<cdot>" 75)

text \<open> Note that in addition to \<^term>\<open>S\<close> and \<^term>\<open>K\<close> combinators, 
       \<^typ>\<open>SKComb\<close> provides terms for \<^emph>\<open>variables\<close>. This is helpful when 
       studying \<open>\<lambda>\<close>-abstraction embedding.\<close>

subsection \<open>Typing\<close>


text \<open>The fragment of the \<^typ>\<open>SKComb\<close> types without
      \<^term>\<open>Var_Comb\<close> terms can be given \<^emph>\<open>simple types\<close>:\<close>

datatype 'a Simple_Type =
    Atom 'a  ("\<^bold>\<lbrace> _ \<^bold>\<rbrace>" [100] 100)
  | To "'a Simple_Type" "'a Simple_Type" (infixr "\<^bold>\<Rightarrow>" 70)

inductive
Simply_Typed_SKComb
   :: "SKComb \<Rightarrow> 'a Simple_Type \<Rightarrow> bool" (infix "\<Colon>" 65)
where
    S_type : "S \<Colon> (\<phi> \<^bold>\<Rightarrow> \<psi> \<^bold>\<Rightarrow> \<chi>) \<^bold>\<Rightarrow> (\<phi> \<^bold>\<Rightarrow> \<psi>) \<^bold>\<Rightarrow> \<phi> \<^bold>\<Rightarrow> \<chi>"
  | K_type : "K \<Colon> \<phi> \<^bold>\<Rightarrow> \<psi> \<^bold>\<Rightarrow> \<phi>"
  | Application_type : "E\<^sub>1 \<Colon> \<phi> \<^bold>\<Rightarrow> \<psi> \<Longrightarrow> E\<^sub>2 \<Colon> \<phi> \<Longrightarrow> E\<^sub>1 \<cdot> E\<^sub>2 \<Colon> \<psi>"

subsection \<open>Lambda Abstraction\<close>

text \<open>Here a simple embedding of the \<open>\<lambda>\<close>-calculus into combinator logic is 
      presented.\<close>

text \<open>The SKI embedding below is originally due to David Turner
      @{cite turnerAnotherAlgorithmBracket1979}.\<close>

text \<open>Abstraction over combinators where the abstracted variable is not free 
      are simplified using the \<^term>\<open>K\<close> combinator.\<close>

primrec free_variables_in_SKComb :: "SKComb \<Rightarrow> Var set" ("free\<^sub>S\<^sub>K")
  where
    "free\<^sub>S\<^sub>K (\<^bold>\<langle>x\<^bold>\<rangle>) = {x}"
  | "free\<^sub>S\<^sub>K S = {}"
  | "free\<^sub>S\<^sub>K K = {}"
  | "free\<^sub>S\<^sub>K (E\<^sub>1 \<cdot> E\<^sub>2) = (free\<^sub>S\<^sub>K E\<^sub>1) \<union> (free\<^sub>S\<^sub>K E\<^sub>2)"

primrec Turner_Abstraction 
  :: "Var \<Rightarrow> SKComb \<Rightarrow> SKComb" ("\<^bold>\<lambda>_. _" [90,90] 90)
  where
    abst_S: "\<^bold>\<lambda>x. S = K \<cdot> S"
  | abst_K: "\<^bold>\<lambda>x. K = K \<cdot> K"
  | abst_var: "\<^bold>\<lambda>x. \<^bold>\<langle>y\<^bold>\<rangle> = (if x = y then S \<cdot> K \<cdot> K else K \<cdot> \<^bold>\<langle>y\<^bold>\<rangle>)"
  | abst_app: 
     "\<^bold>\<lambda> x. (E\<^sub>1 \<cdot> E\<^sub>2) = (if (x \<in> free\<^sub>S\<^sub>K (E\<^sub>1 \<cdot> E\<^sub>2)) 
                       then S \<cdot> (\<^bold>\<lambda> x. E\<^sub>1) \<cdot> (\<^bold>\<lambda> x. E\<^sub>2) 
                       else K \<cdot> (E\<^sub>1 \<cdot> E\<^sub>2))"

subsection \<open>Common Combinators\<close>

text \<open>This section presents various common combinators.  Some combinators are 
      simple enough to express in using \<^term>\<open>S\<close> and \<^term>\<open>K\<close>, however others 
      are more easily expressed using \<open>\<lambda>\<close>-abstraction.
      TODO: Cite Haskell Curry's PhD thesis.\<close>

text \<open>A useful lemma is the type of the \<^emph>\<open>identity\<close> combinator, designated by
      \<^emph>\<open>I\<close> in the literature.\<close>

lemma Identity_type: "S \<cdot> K \<cdot> K \<Colon> \<phi> \<^bold>\<Rightarrow> \<phi>"
  using K_type S_type Application_type by blast

text \<open>Another significant combinator is the  combinator, which corresponds to
      \<^verbatim>\<open>flip\<close> in Haskell.\<close>

lemma C_type: 
  "\<^bold>\<lambda> \<X> 1. \<^bold>\<lambda> \<X> 2. \<^bold>\<lambda> \<X> 3. (\<^bold>\<langle>\<X> 1\<^bold>\<rangle> \<cdot> \<^bold>\<langle>\<X> 3\<^bold>\<rangle> \<cdot> \<^bold>\<langle>\<X> 2\<^bold>\<rangle>) 
       \<Colon> (\<phi> \<^bold>\<Rightarrow> \<psi> \<^bold>\<Rightarrow> \<chi>) \<^bold>\<Rightarrow> \<psi> \<^bold>\<Rightarrow> \<phi> \<^bold>\<Rightarrow> \<chi>"
  by (simp, meson Identity_type Simply_Typed_SKComb.simps)

text \<open>Haskell also has a function \<^verbatim>\<open>(.)\<close>, which is referred to as the \<^emph>\<open>B\<close>
      combinator.\<close>

lemma B_type: "S \<cdot> (K \<cdot> S) \<cdot> K \<Colon> (\<psi> \<^bold>\<Rightarrow> \<chi>) \<^bold>\<Rightarrow> (\<phi> \<^bold>\<Rightarrow> \<psi>) \<^bold>\<Rightarrow> \<phi> \<^bold>\<Rightarrow> \<chi>"
  by (meson Simply_Typed_SKComb.simps)

text \<open>The final combinator given is the \<^emph>\<open>B\<close> combinator.\<close>

lemma W_type: 
  "\<^bold>\<lambda> \<X> 1. \<^bold>\<lambda> \<X> 2. (\<^bold>\<langle>\<X> 1\<^bold>\<rangle> \<cdot> \<^bold>\<langle>\<X> 2\<^bold>\<rangle> \<cdot> \<^bold>\<langle>\<X> 2\<^bold>\<rangle>) \<Colon> (\<phi> \<^bold>\<Rightarrow> \<phi> \<^bold>\<Rightarrow> \<chi>) \<^bold>\<Rightarrow> \<phi> \<^bold>\<Rightarrow> \<chi>"
  by (simp, meson Identity_type Simply_Typed_SKComb.simps)

subsection \<open> The Curry Howard Correspondence \<close>

text \<open> The (polymorphic) typing for a combinator \<^term>\<open>X\<close> is given by the 
       relation \<^term>\<open>X \<Colon> \<phi>\<close>. \<close>

text \<open> Combinator types form an instance of minimal logic. \<close>

interpretation Combinator_Minimal_Logic: Minimal_Logic "\<lambda> \<phi>. \<exists> X. X \<Colon> \<phi>" "(\<^bold>\<Rightarrow>)"
proof qed (meson Simply_Typed_SKComb.intros)+

text \<open> The minimal logic generated by combinator logic is \<^emph>\<open>free\<close> in the 
       following sense: If \<^term>\<open>X \<Colon> \<phi>\<close> holds for some combinator \<^term>\<open>X\<close> 
       then \<^term>\<open>\<phi>\<close> may be interpreted as logical consequence in any given 
       minimal logic instance. \<close>

text \<open> The fact that any valid type in combinator logic may be interpreted in 
       minimal logic is a form of the \<^emph>\<open>Curry-Howard correspondence\<close>. TODO: Cite \<close>

primrec (in Minimal_Logic) Simple_Type_interpretation
                           :: "'a Simple_Type \<Rightarrow> 'a" ("\<^bold>\<lparr> _ \<^bold>\<rparr>" [50]) where
     "\<^bold>\<lparr> Atom p \<^bold>\<rparr> = p"
   | "\<^bold>\<lparr> \<phi> \<^bold>\<Rightarrow> \<psi> \<^bold>\<rparr> = \<^bold>\<lparr> \<phi> \<^bold>\<rparr> \<rightarrow> \<^bold>\<lparr> \<psi> \<^bold>\<rparr>"

lemma (in Minimal_Logic) Curry_Howard_correspondence:
  "X \<Colon> \<phi> \<Longrightarrow> \<turnstile> \<^bold>\<lparr> \<phi> \<^bold>\<rparr>"
  by (induct rule: Simply_Typed_SKComb.induct,
      (simp add: Axiom_1 Axiom_2 Modus_Ponens)+)

end
