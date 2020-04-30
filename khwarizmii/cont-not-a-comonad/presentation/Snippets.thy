theory Snippets
  imports "~~/src/HOL/Library/LaTeXsugar"
          "../Logic/Intuitionistic/Minimal/Combinators"
          "../Logic/Intuitionistic/Minimal/Kripke_Semantics"
begin

text \<open>
\DefineSnippet{refl axiom}{
@{thm[mode=Axiom] refl} {\sc refl}
}%EndSnippet
\<close>

text \<open>
\DefineSnippet{simple_type_predicate}{
\<^term>\<open>(\<Colon>)\<close>
}%EndSnippet

\DefineSnippet{simple_type_predicate_typ}{
@{typ [source] "SKComb \<Rightarrow> 'a Simple_Type \<Rightarrow> bool"}
}%EndSnippet

\DefineSnippet{S_type}{
@{thm[mode=Axiom] S_type} {\sc S\_type}
}%EndSnippet

\DefineSnippet{K_type}{
@{thm[mode=Axiom] K_type} {\sc K\_type}
}%EndSnippet

\DefineSnippet{Application_type}{
@{thm[mode=Rule] Application_type} {\sc Application\_type}
}%EndSnippet

\DefineSnippet{free_variables}{
\begin{tabular}{l@ {~~@{text "="}~~}l}
@{thm (lhs) free_variables_in_SKComb.simps(1)} & @{thm (rhs) free_variables_in_SKComb.simps(1)}\\
@{thm (lhs) free_variables_in_SKComb.simps(2)} & @{thm (rhs) free_variables_in_SKComb.simps(2)}\\
@{thm (lhs) free_variables_in_SKComb.simps(3)} & @{thm (rhs) free_variables_in_SKComb.simps(3)}\\
@{thm (lhs) free_variables_in_SKComb.simps(4)} & @{thm (rhs) free_variables_in_SKComb.simps(4)}
\end{tabular}
}%EndSnippet

\DefineSnippet{Turner_Abstraction}{
\begin{tabular}{l@ {~~@{text "="}~~}p{0.45\linewidth}}
@{thm (lhs) abst_S} & @{thm (rhs) abst_S}\\
@{thm (lhs) abst_K} & @{thm (rhs) abst_K}\\
@{thm (lhs) abst_var} & @{thm (rhs) abst_var}\\
@{thm (lhs) abst_app} & @{thm (rhs) abst_app}
\end{tabular}
}%EndSnippet

\DefineSnippet{C_Combinator}{
@{thm C_type}
}%EndSnippet

\<close>


text \<open>
\DefineSnippet{Tarski_Truth}{
\<open>\<Turnstile>\<close>
}%EndSnippet

\DefineSnippet{eq}{
\<open>=\<close>
}%EndSnippet

\DefineSnippet{Intuitionistic_Kripke_Semantics_1_lhs}{
@{thm (lhs) Intuitionistic_Kripke_Semantics.simps(1)}
}%EndSnippet

\DefineSnippet{Intuitionistic_Kripke_Semantics_1_rhs}{
@{thm (rhs) Intuitionistic_Kripke_Semantics.simps(1)}
}%EndSnippet

\DefineSnippet{Intuitionistic_Kripke_Semantics_2_lhs}{
@{thm (lhs) Intuitionistic_Kripke_Semantics.simps(2)}
}%EndSnippet

\DefineSnippet{Intuitionistic_Kripke_Semantics_2_rhs}{
@{thm (rhs) Intuitionistic_Kripke_Semantics.simps(2)}
}%EndSnippet

\DefineSnippet{Intuitionistic_Kripke_Semantics}{
\begin{tabular}{l@ {~~@{text "="}~~}p{0.33\linewidth}}
@{thm (lhs) Intuitionistic_Kripke_Semantics.simps(1)} & @{thm (rhs) Intuitionistic_Kripke_Semantics.simps(1)}\\
@{thm (lhs) Intuitionistic_Kripke_Semantics.simps(2)} & @{thm (rhs) Intuitionistic_Kripke_Semantics.simps(2)}
\end{tabular}
}%EndSnippet

\DefineSnippet{Reflexive_Transitive_Closure}{
\<^term>\<open>(R \<MM>)\<^sup>*\<^sup>*\<close>
}%EndSnippet

\DefineSnippet{Model}{
\<^term>\<open>\<MM>\<close>
}%EndSnippet

\DefineSnippet{Relation}{
\<^term>\<open>R\<close>
}%EndSnippet

\DefineSnippet{Kripke_model_monotone}{
@{thm[mode=Rule] Kripke_model_monotone}
}%EndSnippet

\DefineSnippet{phi}{
\<^term>\<open>\<phi>\<close>
}%EndSnippet

\DefineSnippet{x}{
\<^term>\<open>x\<close>
}%EndSnippet

\DefineSnippet{y}{
\<^term>\<open>y\<close>
}%EndSnippet

\DefineSnippet{Kripke_models_K}{
@{thm[mode=Axiom] Kripke_models_K}
}%EndSnippet

\DefineSnippet{Kripke_models_S}{
@{thm[mode=Axiom] Kripke_models_S}
}%EndSnippet

\DefineSnippet{Kripke_models_Modus_Ponens}{
@{thm[mode=Rule] Kripke_models_Modus_Ponens}
}%EndSnippet

\DefineSnippet{Combinator_Typing_Kripke_Soundness_alt}{
@{thm[mode=IfThen] Combinator_Typing_Kripke_Soundness_alt}
}%EndSnippet

\DefineSnippet{Kripke_Cont_Monad_prem_1}{
@{thm (prem 1) Kripke_Cont_Monad}
}%EndSnippet

\DefineSnippet{Kripke_Cont_Monad_prem_2}{
@{thm (prem 2) Kripke_Cont_Monad}
}%EndSnippet

\DefineSnippet{Kripke_Cont_Monad_prem_3}{
@{thm (prem 3, rhs) Kripke_Cont_Monad}
}%EndSnippet

\DefineSnippet{Kripke_Cont_Monad_concl}{
@{thm (concl) Kripke_Cont_Monad}
}%EndSnippet

\DefineSnippet{Kripke_Cont_Monad_1}{
\<^term>\<open>\<not> \<MM> b \<Turnstile> \<^bold>\<lbrace> p \<^bold>\<rbrace> \<^bold>\<Rightarrow> \<^bold>\<lbrace> q \<^bold>\<rbrace>\<close>
}%EndSnippet

\DefineSnippet{Kripke_Cont_Monad_1_a}{
\<^term>\<open>\<MM> b \<Turnstile> \<^bold>\<lbrace> p \<^bold>\<rbrace>\<close>
}%EndSnippet

\DefineSnippet{Kripke_Cont_Monad_1_b}{
\<^term>\<open>\<not> \<MM> b \<Turnstile> \<^bold>\<lbrace> q \<^bold>\<rbrace>\<close>
}%EndSnippet

\DefineSnippet{Kripke_Cont_Monad_1_c}{
\<^term>\<open>(R \<MM>)\<^sup>*\<^sup>* b y \<equiv> b = y\<close>
}%EndSnippet

\DefineSnippet{a}{
\<^term>\<open>a\<close>
}%EndSnippet

\DefineSnippet{b}{
\<^term>\<open>b\<close>
}%EndSnippet

\DefineSnippet{p}{
\<^term>\<open>p\<close>
}%EndSnippet

\DefineSnippet{q}{
\<^term>\<open>q\<close>
}%EndSnippet


\DefineSnippet{Kripke_Cont_Monad_2}{
\<^term>\<open>\<not> \<MM> a \<Turnstile> \<^bold>\<lbrace> p \<^bold>\<rbrace> \<^bold>\<Rightarrow> \<^bold>\<lbrace> q \<^bold>\<rbrace>\<close>
}%EndSnippet

\DefineSnippet{Kripke_Cont_Monad_2_a}{
\<^term>\<open>(R \<MM>)\<^sup>*\<^sup>* a x\<close>
}%EndSnippet

\DefineSnippet{Kripke_Cont_Monad_2_b}{
\<^term>\<open>\<MM> x \<Turnstile> \<^bold>\<lbrace> p \<^bold>\<rbrace>\<close>
}%EndSnippet

\DefineSnippet{Kripke_Cont_Monad_2_c}{
\<^term>\<open>\<not> \<MM> x \<Turnstile> \<^bold>\<lbrace> q \<^bold>\<rbrace>\<close>
}%EndSnippet

\DefineSnippet{Kripke_Cont_Monad_2_d}{
\<^term>\<open>x = b\<close>
}%EndSnippet

\DefineSnippet{Kripke_Cont_Monad_2_e}{
\<^term>\<open>\<forall> x. (R \<MM>)\<^sup>*\<^sup>* a x \<longrightarrow> \<not> \<MM> x \<Turnstile> \<^bold>\<lbrace> p \<^bold>\<rbrace> \<^bold>\<Rightarrow> \<^bold>\<lbrace> q \<^bold>\<rbrace>\<close>
}%EndSnippet

\DefineSnippet{Kripke_Cont_Monad_2_f}{
\<^term>\<open>\<MM> a \<Turnstile> (\<^bold>\<lbrace> p \<^bold>\<rbrace> \<^bold>\<Rightarrow> \<^bold>\<lbrace> q \<^bold>\<rbrace>) \<^bold>\<Rightarrow> \<^bold>\<lbrace> q \<^bold>\<rbrace>\<close>
}%EndSnippet

\DefineSnippet{Kripke_Cont_Monad_3}{
\<^term>\<open>\<not> \<MM> a \<Turnstile> \<^bold>\<lbrace> p \<^bold>\<rbrace>\<close>
}%EndSnippet

\DefineSnippet{no_extract_prem}{
@{thm (prem 1) no_extract}
}%EndSnippet

\DefineSnippet{no_extract_concl}{
@{thm (concl) no_extract}
}%EndSnippet

\<close>

text_raw \<open>\DefineSnippet{Kripke_Model}{\<close>
record ('a, 'b) Kripke_Model =
  R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  V :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{SKCombDef}{\<close>
datatype Var = Var nat ("\<X>")

datatype SKComb =
    Var_Comb Var ("\<^bold>\<langle>_\<^bold>\<rangle>" [100] 100)
  | S_Comb ("S")
  | K_Comb ("K")
  | Comb_App "SKComb" "SKComb"  (infixl "\<cdot>" 75)

datatype 'a Simple_Type =
    Atom 'a  ("\<^bold>\<lbrace> _ \<^bold>\<rbrace>" [100] 100)
  | To "'a Simple_Type" "'a Simple_Type" (infixr "\<^bold>\<Rightarrow>" 70)
text_raw \<open>}%EndSnippet\<close>

end
