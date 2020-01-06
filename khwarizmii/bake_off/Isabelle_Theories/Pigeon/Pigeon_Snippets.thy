theory Pigeon_Snippets
  imports "Pigeon"
          (*
          
          "~~/src/HOL/Library/LaTeXsugar"
          *)
begin

text \<open>
\DefineSnippet{Pigeon HOL}{
@{thm [display] pigeon_hol}
}%EndSnippet

\DefineSnippet{Permutation Lemma}{
@{thm bounded_above_perm}
}%EndSnippet

\DefineSnippet{Cons}{
@{term "n # ns"}
}%EndSnippet

\DefineSnippet{Length}{
@{term "length (n # ns)"}
}%EndSnippet

\DefineSnippet{Elem}{
@{term "m \<in> set (n # ns)"}
}%EndSnippet

\DefineSnippet{Conj}{
@{term "x \<and> y"}
}%EndSnippet

\DefineSnippet{Universal Quantifier}{
@{term "\<forall>n' \<in> set (n # ns). p n'"}
}%EndSnippet

\DefineSnippet{Existential Quantifier}{
@{term "\<exists>m \<in> set (n # ns). p m"}
}%EndSnippet

\DefineSnippet{List Range}{
@{term "[1..<m]"}
}%EndSnippet

\DefineSnippet{Permutation}{
@{term "ns \<simeq> [1..<m]"}
}%EndSnippet

\DefineSnippet{ns Term}{
@{term "ns"}
}%EndSnippet

\DefineSnippet{x Term}{
@{term "x"}
}%EndSnippet

\DefineSnippet{P x Term}{
@{term "P x"}
}%EndSnippet

\DefineSnippet{Forall P x Term}{
@{term "\<forall>x. P x"}
}%EndSnippet

\DefineSnippet{allI}{
@{thm allI}
}%EndSnippet

\DefineSnippet{allI Premise}{
@{thm (prem 1) allI}
}%EndSnippet

\DefineSnippet{impI}{
@{thm impI}
}%EndSnippet

\DefineSnippet{P Term}{
@{term "P"}
}%EndSnippet

\DefineSnippet{Q Term}{
@{term "Q"}
}%EndSnippet

\DefineSnippet{P Implies Q Term}{
@{term "P \<longrightarrow> Q"}
}%EndSnippet

\DefineSnippet{Sub-lemma Statement}{
@{term "\<forall>ns' n. ns \<simeq> n # ns' \<longrightarrow> length ns \<notin> set ns' \<longrightarrow> ns \<simeq> [1..<length ns + 1]"}
}%EndSnippet

\DefineSnippet{Positive Case}{
@{term "length ns \<in> set ns'"}
}%EndSnippet

\DefineSnippet{Negative Case}{
@{term "length ns \<notin> set ns'"}
}%EndSnippet

\DefineSnippet{remove1}{
@{const remove1}\ @{text "::"}\ @{typeof remove1}
}%EndSnippet

\<close>

end