section \<open> Minimal Logic \<close>

theory Minimal_Logic
  imports Main
begin

(*:maxLineLen=80:*)

text \<open> This theory presents \<^emph>\<open>minimal logic\<close>, the implicational fragment of intuitionistic logic. \<close>

subsection \<open> Axiomatization \<close>

text \<open> Minimal logic is given by the following Hilbert-style axiom system: \<close>

class Minimal_Logic =
  fixes deduction :: "'a \<Rightarrow> bool"             ("\<turnstile> _" [60] 55)
  fixes implication :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"       (infixr "\<rightarrow>" 70)
  assumes Axiom_1: "\<turnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> \<phi>"
  assumes Axiom_2: "\<turnstile> (\<phi> \<rightarrow> \<psi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi> \<rightarrow> \<chi>"
  assumes Modus_Ponens: "\<turnstile> \<phi> \<rightarrow> \<psi> \<Longrightarrow> \<turnstile> \<phi> \<Longrightarrow> \<turnstile> \<psi>"


text \<open> A convenience class to have is @{class "Minimal_Logic"} extended with a single named
        constant, intended to be \<^emph>\<open>falsum\<close>.  Other classes extending this class will provide
        rules for how this constant interacts with other terms. \<close>

class Minimal_Logic_With_Falsum = Minimal_Logic +
  fixes falsum :: "'a"                      ("\<bottom>")

subsection \<open> Common Rules \<close>

lemma (in Minimal_Logic) trivial_implication: "\<turnstile> \<phi> \<rightarrow> \<phi>"
  by (meson Axiom_1 Axiom_2 Modus_Ponens)

lemma (in Minimal_Logic) flip_implication: "\<turnstile> (\<phi> \<rightarrow> \<psi> \<rightarrow> \<chi>) \<rightarrow> \<psi> \<rightarrow> \<phi> \<rightarrow> \<chi>"
  by (meson Axiom_1 Axiom_2 Modus_Ponens)

lemma (in Minimal_Logic) hypothetical_syllogism: "\<turnstile> (\<psi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi> \<rightarrow> \<chi>"
  by (meson Axiom_1 Axiom_2 Modus_Ponens)

lemma (in Minimal_Logic) flip_hypothetical_syllogism:
  shows "\<turnstile> (\<psi> \<rightarrow> \<phi>) \<rightarrow> (\<phi> \<rightarrow> \<chi>) \<rightarrow> (\<psi> \<rightarrow> \<chi>)"
  using Modus_Ponens flip_implication hypothetical_syllogism by blast

lemma (in Minimal_Logic) implication_absorption: "\<turnstile> (\<phi> \<rightarrow> \<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi> \<rightarrow> \<psi>"
  by (meson Axiom_1 Axiom_2 Modus_Ponens)

subsection \<open> Lists of Assumptions \<close>

subsubsection \<open> List Implication \<close>

text \<open> Implication given a list of assumptions can be expressed recursively \<close>

primrec (in Minimal_Logic) list_implication :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a" (infix ":\<rightarrow>" 80) where
    "[] :\<rightarrow> \<phi> = \<phi>"
  | "(\<psi> # \<Psi>) :\<rightarrow> \<phi> = \<psi> \<rightarrow> \<Psi> :\<rightarrow> \<phi>"

subsubsection \<open> Definition of Deduction \<close>

text \<open> Deduction from a list of assumptions can be expressed in terms of @{term "(:\<rightarrow>)"}. \<close>

definition (in Minimal_Logic) list_deduction :: "'a list \<Rightarrow> 'a \<Rightarrow> bool" (infix ":\<turnstile>" 60) where
  "\<Gamma> :\<turnstile> \<phi> \<equiv> \<turnstile> \<Gamma> :\<rightarrow> \<phi>"

subsubsection \<open> Interpretation as Minimal Logic \<close>

text \<open> The relation @{term "(:\<turnstile>)"} may naturally be interpreted as a @{term "proves"}
        predicate for an instance of minimal logic for a fixed list of assumptions @{term "\<Gamma>"}. \<close>

text \<open> Analogues of the two axioms of minimal logic can be naturally stated using
        list implication. \<close>

lemma (in Minimal_Logic) list_implication_Axiom_1: "\<turnstile> \<phi> \<rightarrow> \<Gamma> :\<rightarrow> \<phi>"
  by (induct \<Gamma>, (simp, meson Axiom_1 Axiom_2 Modus_Ponens)+)

lemma (in Minimal_Logic) list_implication_Axiom_2: "\<turnstile> \<Gamma> :\<rightarrow> (\<phi> \<rightarrow> \<psi>) \<rightarrow> \<Gamma> :\<rightarrow> \<phi> \<rightarrow> \<Gamma> :\<rightarrow> \<psi>"
  by (induct \<Gamma>, (simp, meson Axiom_1 Axiom_2 Modus_Ponens hypothetical_syllogism)+)

text \<open> The lemmas @{thm list_implication_Axiom_1} and  @{thm list_implication_Axiom_2} jointly
        give rise to an interpretation of minimal logic, where a list of assumptions
        @{term "\<Gamma>"} plays the role of a \<^emph>\<open>background theory\<close> of @{term "(:\<turnstile>)"}. \<close>

context Minimal_Logic begin
interpretation List_Deduction_Logic: Minimal_Logic "\<lambda> \<phi>. \<Gamma> :\<turnstile> \<phi>" "(\<rightarrow>)"
proof qed (meson list_deduction_def
                 Axiom_1
                 Axiom_2
                 Modus_Ponens
                 list_implication_Axiom_1
                 list_implication_Axiom_2)+
end

text \<open> The following \<^emph>\<open>weakening\<close> rule can also be derived. \<close>

lemma (in Minimal_Logic) list_deduction_weaken: "\<turnstile> \<phi> \<Longrightarrow> \<Gamma> :\<turnstile> \<phi>"
  unfolding list_deduction_def
  using Modus_Ponens list_implication_Axiom_1
  by blast

text \<open> In the case of the empty list, the converse may be established. \<close>

lemma (in Minimal_Logic) list_deduction_base_theory [simp]: "[] :\<turnstile> \<phi> \<equiv> \<turnstile> \<phi>"
  unfolding list_deduction_def
  by simp

lemma (in Minimal_Logic) list_deduction_modus_ponens: "\<Gamma> :\<turnstile> \<phi> \<rightarrow> \<psi> \<Longrightarrow> \<Gamma> :\<turnstile> \<phi> \<Longrightarrow> \<Gamma> :\<turnstile> \<psi>"
  unfolding list_deduction_def
  using Modus_Ponens list_implication_Axiom_2
  by blast

subsection \<open> The Deduction Theorem \<close>

text \<open> One result in the meta-theory of minimal logic is the \<^emph>\<open>deduction theorem\<close>,
        which is a mechanism for moving antecedents back and forth from collections of
        assumptions. \<close>

text \<open> To develop the deduction theorem, the following two lemmas generalize
        @{thm "flip_implication"}. \<close>

lemma (in Minimal_Logic) list_flip_implication1: "\<turnstile> (\<phi> # \<Gamma>) :\<rightarrow> \<chi> \<rightarrow> \<Gamma> :\<rightarrow> (\<phi> \<rightarrow> \<chi>)"
  by (induct \<Gamma>,
      (simp, meson Axiom_1 Axiom_2 Modus_Ponens flip_implication hypothetical_syllogism)+)

lemma (in Minimal_Logic) list_flip_implication2: "\<turnstile> \<Gamma> :\<rightarrow> (\<phi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> # \<Gamma>) :\<rightarrow> \<chi>"
  by (induct \<Gamma>,
      (simp, meson Axiom_1 Axiom_2 Modus_Ponens flip_implication hypothetical_syllogism)+)

text \<open> Together the two lemmas above suffice to prove a form of the deduction theorem: \<close>

theorem (in Minimal_Logic) list_deduction_theorem: "(\<phi> # \<Gamma>) :\<turnstile> \<psi> = \<Gamma> :\<turnstile> \<phi> \<rightarrow> \<psi>"
  unfolding list_deduction_def
  by (metis Modus_Ponens list_flip_implication1 list_flip_implication2)

subsection \<open> Monotonic Growth in Deductive Power \<close>

text \<open> In logic, for two sets of assumptions @{term "\<Phi>"} and @{term "\<Psi>"},
        if @{term "\<Psi> \<subseteq> \<Phi>"} then the latter theory @{term "\<Phi>"} is said to be \<^emph>\<open>stronger\<close>
        than former theory @{term "\<Psi>"}.  In principle, anything a weaker theory can prove a
        stronger theory can prove.  One way of saying this is that deductive power increases
        monotonically with as the set of underlying assumptions grow. \<close>

text \<open> The monotonic growth of deductive power can be expressed as a meta-theorem
        in minimal logic. \<close>

text \<open> The lemma @{thm "list_flip_implication2"} presents a means of \<^emph>\<open>introducing\<close>
        assumptions into a list of assumptions when those assumptions have arrived at an
        implication.  The next lemma presents a means of \<^emph>\<open>discharging\<close> those assumptions,
        which can be used in the monotonic growth theorem to be proved. \<close>

lemma (in Minimal_Logic) list_implication_removeAll:
  "\<turnstile> \<Gamma> :\<rightarrow> \<psi> \<rightarrow> (removeAll \<phi> \<Gamma>) :\<rightarrow> (\<phi> \<rightarrow> \<psi>)"
proof -
  have "\<forall> \<psi>. \<turnstile> \<Gamma> :\<rightarrow> \<psi> \<rightarrow> (removeAll \<phi> \<Gamma>) :\<rightarrow> (\<phi> \<rightarrow> \<psi>)"
  proof(induct \<Gamma>)
    case Nil
    then show ?case by (simp, meson Axiom_1)
  next
    case (Cons \<chi> \<Gamma>)
    assume inductive_hypothesis: "\<forall> \<psi>. \<turnstile> \<Gamma> :\<rightarrow> \<psi> \<rightarrow> removeAll \<phi> \<Gamma> :\<rightarrow> (\<phi> \<rightarrow> \<psi>)"
    moreover {
      assume "\<phi> \<noteq> \<chi>"
      with inductive_hypothesis
      have "\<forall> \<psi>. \<turnstile> (\<chi> # \<Gamma>) :\<rightarrow> \<psi> \<rightarrow> removeAll \<phi> (\<chi> # \<Gamma>) :\<rightarrow> (\<phi> \<rightarrow> \<psi>)"
        by (simp, meson Modus_Ponens hypothetical_syllogism)
    }
    moreover {
      fix \<psi>
      assume \<phi>_equals_\<chi>: "\<phi> = \<chi>"
      moreover with inductive_hypothesis
      have "\<turnstile> \<Gamma> :\<rightarrow> (\<chi> \<rightarrow> \<psi>) \<rightarrow> removeAll \<phi> (\<chi> # \<Gamma>) :\<rightarrow> (\<phi> \<rightarrow> \<chi> \<rightarrow> \<psi>)" by simp
      hence "\<turnstile> \<Gamma> :\<rightarrow> (\<chi> \<rightarrow> \<psi>) \<rightarrow> removeAll \<phi> (\<chi> # \<Gamma>) :\<rightarrow> (\<phi> \<rightarrow> \<psi>)"
        by (metis calculation Modus_Ponens implication_absorption list_flip_implication1
                  list_flip_implication2 list_implication.simps(2))
      ultimately have "\<turnstile> (\<chi> # \<Gamma>) :\<rightarrow> \<psi> \<rightarrow> removeAll \<phi> (\<chi> # \<Gamma>) :\<rightarrow> (\<phi> \<rightarrow> \<psi>)"
        by (simp, metis Modus_Ponens hypothetical_syllogism list_flip_implication1
                        list_implication.simps(2))
    }
    ultimately show ?case by simp
  qed
  thus ?thesis by blast
qed

text \<open> From lemma above presents what is needed to prove that deductive power for lists is
        monotonic. \<close>

theorem (in Minimal_Logic) list_implication_monotonic:
  "set \<Sigma> \<subseteq> set \<Gamma> \<Longrightarrow> \<turnstile> \<Sigma> :\<rightarrow> \<phi> \<rightarrow> \<Gamma> :\<rightarrow> \<phi>"
proof -
  assume "set \<Sigma> \<subseteq> set \<Gamma>"
  moreover have "\<forall> \<Sigma> \<phi>. set \<Sigma> \<subseteq> set \<Gamma> \<longrightarrow> \<turnstile> \<Sigma> :\<rightarrow> \<phi> \<rightarrow> \<Gamma> :\<rightarrow> \<phi>"
  proof(induct \<Gamma>)
    case Nil
    then show ?case
      by (metis list_implication.simps(1) list_implication_Axiom_1 set_empty subset_empty)
  next
    case (Cons \<psi> \<Gamma>)
    assume inductive_hypothesis: "\<forall>\<Sigma> \<phi>. set \<Sigma> \<subseteq> set \<Gamma> \<longrightarrow> \<turnstile> \<Sigma> :\<rightarrow> \<phi> \<rightarrow> \<Gamma> :\<rightarrow> \<phi>"
    {
      fix \<Sigma>
      fix \<phi>
      assume \<Sigma>_subset_relation: "set \<Sigma> \<subseteq> set (\<psi> # \<Gamma>)"
      have "\<turnstile> \<Sigma> :\<rightarrow> \<phi> \<rightarrow> (\<psi> # \<Gamma>) :\<rightarrow> \<phi>"
      proof -
        {
          assume "set \<Sigma> \<subseteq> set \<Gamma>"
          hence ?thesis
            by (metis inductive_hypothesis Axiom_1 Modus_Ponens flip_implication
                      list_implication.simps(2))
        }
        moreover {
          let ?\<Delta> = "removeAll \<psi> \<Sigma>"
          assume "~ (set \<Sigma> \<subseteq> set \<Gamma>)"
          hence "set ?\<Delta> \<subseteq> set \<Gamma>" using \<Sigma>_subset_relation by auto
          hence "\<turnstile> ?\<Delta> :\<rightarrow> (\<psi> \<rightarrow> \<phi>) \<rightarrow> \<Gamma> :\<rightarrow> (\<psi> \<rightarrow> \<phi>)" using inductive_hypothesis by auto
          hence "\<turnstile> ?\<Delta> :\<rightarrow> (\<psi> \<rightarrow> \<phi>) \<rightarrow> (\<psi> # \<Gamma>) :\<rightarrow> \<phi>"
            by (metis Modus_Ponens
                      flip_implication
                      list_flip_implication2
                      list_implication.simps(2))
          moreover have "\<turnstile> \<Sigma> :\<rightarrow> \<phi> \<rightarrow> ?\<Delta> :\<rightarrow> (\<psi> \<rightarrow> \<phi>)"
            by (simp add: local.list_implication_removeAll)
          ultimately have ?thesis
            using Modus_Ponens hypothetical_syllogism by blast
        }
        ultimately show ?thesis by blast
     qed
    }
    thus ?case by simp
  qed
  ultimately show ?thesis by simp
qed

text \<open> A direct consequence is that deduction from lists of assumptions is monotonic as well: \<close>

theorem (in Minimal_Logic) list_deduction_monotonic:
  "set \<Sigma> \<subseteq> set \<Gamma> \<Longrightarrow> \<Sigma> :\<turnstile> \<phi> \<Longrightarrow> \<Gamma> :\<turnstile> \<phi>"
  unfolding list_deduction_def
  using Modus_Ponens list_implication_monotonic
  by blast

subsection \<open> The Deduction Theorem Revisited \<close>

text \<open> The monotonic nature of deduction allows us to prove another form of the deduction
        theorem, where the assumption being discharged is completely removed from the list of
        assumptions. \<close>

theorem (in Minimal_Logic) alternate_list_deduction_theorem:
  "(\<phi> # \<Gamma>) :\<turnstile> \<psi> = (removeAll \<phi> \<Gamma>) :\<turnstile> \<phi> \<rightarrow> \<psi>"
  by (metis list_deduction_def
            Modus_Ponens
            filter_is_subset
            list_deduction_monotonic
            list_deduction_theorem
            list_implication_removeAll
            removeAll.simps(2)
            removeAll_filter_not_eq)

subsection \<open> Reflection \<close>

text \<open> In logic the \<^emph>\<open>reflection\<close> principle sometimes refers to when a collection of
        assumptions can deduce any of its members. It is automatically derivable from
        @{thm "list_deduction_monotonic"} among the other rules provided. \<close>

lemma (in Minimal_Logic) list_deduction_reflection: "\<phi> \<in> set \<Gamma> \<Longrightarrow> \<Gamma> :\<turnstile> \<phi>"
  by (metis list_deduction_def
            insert_subset
            list.simps(15)
            list_deduction_monotonic
            list_implication.simps(2)
            list_implication_Axiom_1
            order_refl)

subsection \<open> The Cut Rule \<close>

text \<open> \<^emph>\<open>Cut\<close> is a rule commonly presented in sequent calculi, dating back to Gerhard
        Gentzen's "Investigations in Logical Deduction" (1934) TODO: Cite me \<close>

text \<open> The cut rule is not generally necessary in sequent calculi. It can often be shown
        that the rule can be eliminated without reducing the power of the underlying logic.
        However, as demonstrated by George Boolos' \<^emph>\<open>Don't Eliminate Cute\<close> 
        (1984) (TODO: Cite me),
        removing the rule can often lead to very inefficient proof systems. \<close>

text \<open> Here the rule is presented just as a meta theorem. \<close>

theorem (in Minimal_Logic) list_deduction_cut_rule: 
  "(\<phi> # \<Gamma>) :\<turnstile> \<psi> \<Longrightarrow> \<Delta> :\<turnstile> \<phi> \<Longrightarrow> \<Gamma> @ \<Delta> :\<turnstile> \<psi>"
  by (metis 
       (no_types, lifting)
       Un_upper1
       Un_upper2
       list_deduction_modus_ponens
       list_deduction_monotonic
       list_deduction_theorem
       set_append)

text \<open> The cut rule can also be strengthened to entire lists of propositions. \<close>

theorem (in Minimal_Logic) strong_list_deduction_cut_rule:
  "(\<Phi> @ \<Gamma>) :\<turnstile> \<psi> \<Longrightarrow> \<forall> \<phi> \<in> set \<Phi>. \<Delta> :\<turnstile> \<phi> \<Longrightarrow> \<Gamma> @ \<Delta> :\<turnstile> \<psi>"
proof -
  have "\<forall> \<psi>. (\<Phi> @ \<Gamma> :\<turnstile> \<psi> \<longrightarrow> (\<forall> \<phi> \<in> set \<Phi>. \<Delta> :\<turnstile> \<phi>) \<longrightarrow> \<Gamma> @ \<Delta> :\<turnstile> \<psi>)"
    proof(induct \<Phi>)
      case Nil
      then show ?case
        by (metis Un_iff append.left_neutral list_deduction_monotonic set_append subsetI)
    next
      case (Cons \<chi> \<Phi>)
      assume inductive_hypothesis: 
         "\<forall> \<psi>. \<Phi> @ \<Gamma> :\<turnstile> \<psi> \<longrightarrow> (\<forall>\<phi>\<in>set \<Phi>. \<Delta> :\<turnstile> \<phi>) \<longrightarrow> \<Gamma> @ \<Delta> :\<turnstile> \<psi>"
      {
        fix \<psi> \<chi>
        assume "(\<chi> # \<Phi>) @ \<Gamma> :\<turnstile> \<psi>"
        hence A: "\<Phi> @ \<Gamma> :\<turnstile> \<chi> \<rightarrow> \<psi>"  using list_deduction_theorem by auto
        assume "\<forall>\<phi> \<in> set (\<chi> # \<Phi>). \<Delta> :\<turnstile> \<phi>"
        hence B: "\<forall> \<phi> \<in> set \<Phi>. \<Delta> :\<turnstile> \<phi>"
          and C: "\<Delta> :\<turnstile> \<chi>" by auto
        from A B have "\<Gamma> @ \<Delta> :\<turnstile> \<chi> \<rightarrow> \<psi>" using inductive_hypothesis by blast
        with C have "\<Gamma> @ \<Delta> :\<turnstile> \<psi>"
          by (meson list.set_intros(1)
                    list_deduction_cut_rule
                    list_deduction_modus_ponens
                    list_deduction_reflection)
      }
      thus ?case by simp
    qed
    moreover assume "(\<Phi> @ \<Gamma>) :\<turnstile> \<psi>"
  moreover assume "\<forall> \<phi> \<in> set \<Phi>. \<Delta> :\<turnstile> \<phi>"
  ultimately show ?thesis by blast
qed

subsection \<open> Sets of Assumptions \<close>

text \<open> While deduction in terms of lists of assumptions is straight-forward 
       to define, deduction (and the \<^emph>\<open>deduction theorem\<close>) is commonly given in 
       terms of \<^emph>\<open>sets\<close> of propositions.  This formulation is suited to 
       establishing strong completeness theorems and compactness theorems. \<close>

text \<open> The presentation of deduction from a set follows the presentation of list deduction given
        for @{term "(:\<turnstile>)"}. \<close>

subsection \<open> Definition of Deduction \<close>

text \<open> Just as deduction from a list @{term "(:\<turnstile>)"} can be defined in terms of @{term "(:\<rightarrow>)"},
        deduction from a \<^emph>\<open>set\<close> of assumptions can be expressed in terms of @{term "(:\<turnstile>)"}. \<close>

definition (in Minimal_Logic) set_deduction :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<tturnstile>" 60) where
  "\<Gamma> \<tturnstile> \<phi> \<equiv> \<exists> \<Psi>. set(\<Psi>) \<subseteq> \<Gamma> \<and> \<Psi> :\<turnstile> \<phi>"

subsubsection \<open> Interpretation as Minimal Logic \<close>

text \<open> As in the case of @{term "(:\<turnstile>)"}, the relation @{term "(\<tturnstile>)"} may be interpreted as
        a @{term "proves"} predicate for a fixed set of assumptions @{term "\<Gamma>"}. \<close>

text \<open> The following lemma is given in order to establish this, which asserts that
        every minimal logic tautology @{term "\<turnstile> \<phi>"} is also a tautology for @{term "\<Gamma> \<tturnstile> \<phi>"}. \<close>

lemma (in Minimal_Logic) set_deduction_weaken: "\<turnstile> \<phi> \<Longrightarrow> \<Gamma> \<tturnstile> \<phi>"
  using list_deduction_base_theory set_deduction_def by fastforce

text \<open> In the case of the empty set, the converse may be established. \<close>

lemma (in Minimal_Logic) set_deduction_base_theory: "{} \<tturnstile> \<phi> \<equiv> \<turnstile> \<phi>"
  using list_deduction_base_theory set_deduction_def by auto

text \<open> Next, a form of \<^emph>\<open>modus ponens\<close> is provided for @{term "(\<tturnstile>)"}. \<close>

lemma (in Minimal_Logic) set_deduction_modus_ponens: "\<Gamma> \<tturnstile> \<phi> \<rightarrow> \<psi> \<Longrightarrow> \<Gamma> \<tturnstile> \<phi> \<Longrightarrow> \<Gamma> \<tturnstile> \<psi>"
proof -
  assume "\<Gamma> \<tturnstile> \<phi> \<rightarrow> \<psi>"
  then obtain \<Phi> where A: "set \<Phi> \<subseteq> \<Gamma>" and B: "\<Phi> :\<turnstile> \<phi> \<rightarrow> \<psi>"
    using set_deduction_def by blast
  assume "\<Gamma> \<tturnstile> \<phi>"
  then obtain \<Psi> where C: "set \<Psi> \<subseteq> \<Gamma>" and D: "\<Psi> :\<turnstile> \<phi>"
    using set_deduction_def by blast
  from B D have "\<Phi> @ \<Psi> :\<turnstile> \<psi>"
    using list_deduction_cut_rule list_deduction_theorem by blast
  moreover from A C have "set (\<Phi> @ \<Psi>) \<subseteq> \<Gamma>" by simp
  ultimately show ?thesis
    using set_deduction_def by blast
qed

context Minimal_Logic begin
interpretation Set_Deduction_Logic: Minimal_Logic "\<lambda> \<phi>. \<Gamma> \<tturnstile> \<phi>" "(\<rightarrow>)"
proof
   fix \<phi> \<psi>
   show "\<Gamma> \<tturnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> \<phi>"  by (metis Axiom_1 set_deduction_weaken)
next
    fix \<phi> \<psi> \<chi>
    show "\<Gamma> \<tturnstile> (\<phi> \<rightarrow> \<psi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi> \<rightarrow> \<chi>"  by (metis Axiom_2 set_deduction_weaken)
next
    fix \<phi> \<psi>
    show "\<Gamma> \<tturnstile> \<phi> \<rightarrow> \<psi> \<Longrightarrow> \<Gamma> \<tturnstile> \<phi> \<Longrightarrow> \<Gamma> \<tturnstile> \<psi>" using set_deduction_modus_ponens by metis
qed
end

subsection \<open> The Deduction Theorem \<close>

text \<open> The next result gives the deduction theorem for @{term "(\<tturnstile>)"}. \<close>

theorem (in Minimal_Logic) set_deduction_theorem: "insert \<phi> \<Gamma> \<tturnstile> \<psi> = \<Gamma> \<tturnstile> \<phi> \<rightarrow> \<psi>"
proof -
  have "\<Gamma> \<tturnstile> \<phi> \<rightarrow> \<psi> \<Longrightarrow> insert \<phi> \<Gamma> \<tturnstile> \<psi>"
    by (metis set_deduction_def insert_mono list.simps(15) list_deduction_theorem)
  moreover {
    assume "insert \<phi> \<Gamma> \<tturnstile> \<psi>"
    then obtain \<Phi> where "set \<Phi> \<subseteq> insert \<phi> \<Gamma>" and "\<Phi> :\<turnstile> \<psi>"
      using set_deduction_def by auto
    hence "set (removeAll \<phi> \<Phi>) \<subseteq> \<Gamma>" by auto
    moreover from \<open>\<Phi> :\<turnstile> \<psi>\<close> have "removeAll \<phi> \<Phi> :\<turnstile> \<phi> \<rightarrow> \<psi>"
      using Modus_Ponens list_implication_removeAll list_deduction_def
      by blast
    ultimately have "\<Gamma> \<tturnstile> \<phi> \<rightarrow> \<psi>"
      using set_deduction_def by blast
  }
  ultimately show "insert \<phi> \<Gamma> \<tturnstile> \<psi> = \<Gamma> \<tturnstile> \<phi> \<rightarrow> \<psi>" by metis
qed

subsection \<open> Monotonic Growth in Deductive Power \<close>

text \<open> In contrast to the @{term "(:\<turnstile>)"} relation, the proof that the deductive power
        of @{term "(\<tturnstile>)"} grows monotonically with its assumptions may be fully automated. \<close>

theorem set_deduction_monotonic: "\<Sigma> \<subseteq> \<Gamma> \<Longrightarrow> \<Sigma> \<tturnstile> \<phi> \<Longrightarrow> \<Gamma> \<tturnstile> \<phi>"
  by (meson dual_order.trans set_deduction_def)

subsection \<open> The Deduction Theorem Revisited \<close>

text \<open> As a consequence of the fact that @{thm "set_deduction_monotonic"} automatically provable,
        the alternate \<^emph>\<open>deduction theorem\<close> where the discharged assumption is completely
        removed from the set of assumptions is just a consequence of the more conventional
        @{thm "set_deduction_theorem"} and some basic set identities. \<close>

theorem (in Minimal_Logic) alternate_set_deduction_theorem:
  "insert \<phi> \<Gamma> \<tturnstile> \<psi> = \<Gamma> - {\<phi>} \<tturnstile> \<phi> \<rightarrow> \<psi>"
  by (metis insert_Diff_single set_deduction_theorem)

subsection \<open> Reflection \<close>

text \<open> Just as in the case of @{term "(:\<turnstile>)"}, deduction from sets of assumptions
        makes true the \<^emph>\<open>reflection principle\<close> and is automatically provable. \<close>

theorem (in Minimal_Logic) set_deduction_reflection: "\<phi> \<in> \<Gamma> \<Longrightarrow> \<Gamma> \<tturnstile> \<phi>"
  by (metis Set.set_insert
            list_implication.simps(1)
            list_implication_Axiom_1
            set_deduction_theorem
            set_deduction_weaken)

subsection \<open> The Cut Rule \<close>

text \<open> The final principle of @{term "(\<tturnstile>)"} presented is the \<^emph>\<open>cut rule\<close>. \<close>

text \<open> First, the weak form of the rule is established. \<close>

theorem (in Minimal_Logic) set_deduction_cut_rule:
  "insert \<phi> \<Gamma> \<tturnstile> \<psi> \<Longrightarrow> \<Delta> \<tturnstile> \<phi> \<Longrightarrow> \<Gamma> \<union> \<Delta> \<tturnstile> \<psi>"
proof -
  assume "insert \<phi> \<Gamma> \<tturnstile> \<psi>"
  hence "\<Gamma> \<tturnstile> \<phi> \<rightarrow> \<psi>" using set_deduction_theorem by auto
  hence "\<Gamma> \<union> \<Delta> \<tturnstile> \<phi> \<rightarrow> \<psi>" using set_deduction_def by auto
  moreover assume "\<Delta> \<tturnstile> \<phi>"
  hence "\<Gamma> \<union> \<Delta> \<tturnstile> \<phi>" using set_deduction_def by auto
  ultimately show ?thesis using set_deduction_modus_ponens by metis
qed

text \<open> Another lemma is shown next in order to establish the strong form 
       of the cut rule. The lemma shows the existence of a \<^emph>\<open>covering list\<close> of 
       assumptions \<^term>\<open>\<Psi>\<close> in the event some set of assumptions 
       \<^term>\<open>\<Delta>\<close> proves everything in a finite set of assumptions 
       \<^term>\<open>\<Phi>\<close>. \<close>

lemma (in Minimal_Logic) finite_set_deduction_list_deduction:
  "finite \<Phi> \<Longrightarrow>
   \<forall> \<phi> \<in> \<Phi>. \<Delta> \<tturnstile> \<phi> \<Longrightarrow>
   \<exists>\<Psi>. set \<Psi> \<subseteq> \<Delta> \<and> (\<forall>\<phi> \<in> \<Phi>. \<Psi> :\<turnstile> \<phi>)"
proof(induct \<Phi> rule: finite_induct)
  case empty thus ?case by (metis all_not_in_conv empty_subsetI set_empty)
next
  case (insert \<chi> \<Phi>)
  assume "\<forall>\<phi> \<in> \<Phi>. \<Delta> \<tturnstile> \<phi> \<Longrightarrow> \<exists>\<Psi>. set \<Psi> \<subseteq> \<Delta> \<and> (\<forall>\<phi> \<in> \<Phi>. \<Psi> :\<turnstile> \<phi>)"
     and "\<forall>\<phi> \<in> insert \<chi> \<Phi>. \<Delta> \<tturnstile> \<phi>"
  hence "\<exists>\<Psi>. set \<Psi> \<subseteq> \<Delta> \<and> (\<forall>\<phi>\<in>\<Phi>. \<Psi> :\<turnstile> \<phi>)" and "\<Delta> \<tturnstile> \<chi>" by simp+
  then obtain \<Psi>\<^sub>1 \<Psi>\<^sub>2 where 
    "set (\<Psi>\<^sub>1 @ \<Psi>\<^sub>2) \<subseteq> \<Delta>" and 
    "\<forall>\<phi> \<in> \<Phi>. \<Psi>\<^sub>1 :\<turnstile> \<phi>" and 
    "\<Psi>\<^sub>2 :\<turnstile> \<chi>"
    using set_deduction_def by auto
  moreover from this have "\<forall>\<phi> \<in> (insert \<chi> \<Phi>). \<Psi>\<^sub>1 @ \<Psi>\<^sub>2 :\<turnstile> \<phi>"
    by (metis 
         insert_iff 
         le_sup_iff 
         list_deduction_monotonic 
         order_refl set_append)
  ultimately show ?case by blast
qed

text \<open> With @{thm finite_set_deduction_list_deduction} the strengthened 
       form of the cut rule can be given. \<close>

theorem (in Minimal_Logic) strong_set_deduction_cut_rule:
  "\<Phi> \<union> \<Gamma> \<tturnstile> \<psi> \<Longrightarrow> \<forall> \<phi> \<in> \<Phi>. \<Delta> \<tturnstile> \<phi> \<Longrightarrow> \<Gamma> \<union> \<Delta> \<tturnstile> \<psi>"
proof -
  assume "\<Phi> \<union> \<Gamma> \<tturnstile> \<psi>"
  then obtain \<Sigma> where 
    A: "set \<Sigma>  \<subseteq> \<Phi> \<union> \<Gamma>" and 
    B: "\<Sigma> :\<turnstile> \<psi>" 
    using set_deduction_def 
    by auto+
  obtain \<Phi>' \<Gamma>' where 
    C: "set \<Phi>' = set \<Sigma> \<inter> \<Phi>" and 
    D: "set \<Gamma>' = set \<Sigma> \<inter> \<Gamma>"
    by (metis inf_sup_aci(1) inter_set_filter)+
  then have "set (\<Phi>' @ \<Gamma>') = set \<Sigma>" using A by auto
  hence E: "\<Phi>' @ \<Gamma>' :\<turnstile> \<psi>" using B list_deduction_monotonic by blast
  assume "\<forall> \<phi> \<in> \<Phi>. \<Delta> \<tturnstile> \<phi>"
  hence "\<forall> \<phi> \<in> set \<Phi>'. \<Delta> \<tturnstile> \<phi>" using C by auto
  from this obtain \<Delta>' where "set \<Delta>' \<subseteq> \<Delta>" and "\<forall> \<phi> \<in> set \<Phi>'. \<Delta>' :\<turnstile> \<phi>"
    using finite_set_deduction_list_deduction by blast
  with strong_list_deduction_cut_rule D E
  have "set (\<Gamma>' @ \<Delta>') \<subseteq> \<Gamma> \<union> \<Delta>" and "\<Gamma>' @ \<Delta>' :\<turnstile> \<psi>" by auto
  thus ?thesis using set_deduction_def by blast
qed

subsection \<open>Maximally Consistent Sets For Minimal Logic\<close>

definition (in Minimal_Logic)
  Formula_Consistent :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" ("_-Consistent _" [100] 100) 
  where [simp]: "\<phi>-Consistent \<Gamma> \<equiv> ~ (\<Gamma> \<tturnstile> \<phi>)"

lemma (in Minimal_Logic) Formula_Consistent_Extension:
  assumes "\<phi>-Consistent \<Gamma>"
  shows "(\<phi>-Consistent insert \<psi> \<Gamma>) \<or> (\<phi>-Consistent insert (\<psi> \<rightarrow> \<phi>) \<Gamma>)"
proof -
  {
    assume "~ \<phi>-Consistent insert \<psi> \<Gamma>"
    hence "\<Gamma> \<tturnstile> \<psi> \<rightarrow> \<phi>"
      using set_deduction_theorem
      unfolding Formula_Consistent_def
      by simp
    hence "\<phi>-Consistent insert (\<psi> \<rightarrow> \<phi>) \<Gamma>"
     by (metis Un_absorb assms Formula_Consistent_def set_deduction_cut_rule)
  }
  thus ?thesis by blast
qed

definition (in Minimal_Logic)
  Formula_Maximally_Consistent_Set 
    :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" ("_-MCS _" [100] 100) 
    where
      [simp]: "\<phi>-MCS \<Gamma> \<equiv> (\<phi>-Consistent \<Gamma>) \<and> (\<forall> \<psi>. \<psi> \<in> \<Gamma> \<or> (\<psi> \<rightarrow> \<phi>) \<in> \<Gamma>)"

theorem (in Minimal_Logic) Formula_Maximally_Consistent_Extension:
  assumes "\<phi>-Consistent \<Gamma>"
  shows "\<exists> \<Omega>. (\<phi>-MCS \<Omega>) \<and> \<Gamma> \<subseteq> \<Omega>"
proof -
  let ?\<Gamma>_Extensions = "{\<Sigma>. (\<phi>-Consistent \<Sigma>) \<and> \<Gamma> \<subseteq> \<Sigma>}"
  have "\<exists> \<Omega> \<in> ?\<Gamma>_Extensions. \<forall>\<Sigma> \<in> ?\<Gamma>_Extensions. \<Omega> \<subseteq> \<Sigma> \<longrightarrow> \<Sigma> = \<Omega>"
  proof (rule subset_Zorn)
    fix \<C> :: "'a set set"
    assume subset_chain_\<C>: "subset.chain ?\<Gamma>_Extensions \<C>"
    hence \<C>:  "\<forall> \<Sigma> \<in> \<C>. \<Gamma> \<subseteq> \<Sigma>" "\<forall> \<Sigma> \<in> \<C>. \<phi>-Consistent \<Sigma>"
      unfolding subset.chain_def by blast+
    show "\<exists> \<Omega> \<in> ?\<Gamma>_Extensions. \<forall> \<Sigma> \<in> \<C>. \<Sigma> \<subseteq> \<Omega>"
    proof cases
      assume "\<C> = {}" thus ?thesis using assms by blast
    next
      let ?\<Omega> = "\<Union> \<C>"
      assume "\<C> \<noteq> {}"
      hence "\<Gamma> \<subseteq> ?\<Omega>" by (simp add: \<C>(1) less_eq_Sup)
      moreover have "\<phi>-Consistent ?\<Omega>"
      proof -
        {
          assume "~ \<phi>-Consistent ?\<Omega>"
          then obtain \<omega> where \<omega>: "finite \<omega>" "\<omega> \<subseteq> ?\<Omega>" "~ \<phi>-Consistent \<omega>"
            unfolding Formula_Consistent_def
                      set_deduction_def
            by auto
          from \<omega>(1) \<omega>(2) have "\<exists> \<Sigma> \<in> \<C>. \<omega> \<subseteq> \<Sigma>"
          proof (induct \<omega> rule: finite_induct)
            case empty thus ?case using \<open>\<C> \<noteq> {}\<close> by blast
          next
            case (insert \<psi> \<omega>)
            from this obtain \<Sigma>\<^sub>1 \<Sigma>\<^sub>2 where
              \<Sigma>\<^sub>1: "\<omega> \<subseteq> \<Sigma>\<^sub>1" "\<Sigma>\<^sub>1 \<in> \<C>" and
              \<Sigma>\<^sub>2: "\<psi> \<in> \<Sigma>\<^sub>2" "\<Sigma>\<^sub>2 \<in> \<C>"
              by auto
            hence "\<Sigma>\<^sub>1 \<subseteq> \<Sigma>\<^sub>2 \<or> \<Sigma>\<^sub>2 \<subseteq> \<Sigma>\<^sub>1"
              using subset_chain_\<C>
              unfolding subset.chain_def
              by blast
            hence "(insert \<psi> \<omega>) \<subseteq> \<Sigma>\<^sub>1 \<or> (insert \<psi> \<omega>) \<subseteq> \<Sigma>\<^sub>2" 
              using \<Sigma>\<^sub>1 \<Sigma>\<^sub>2 by blast
            thus ?case using \<Sigma>\<^sub>1 \<Sigma>\<^sub>2 by blast
          qed
          hence "\<exists> \<Sigma> \<in> \<C>. (\<phi>-Consistent \<Sigma>) \<and> ~ (\<phi>-Consistent \<Sigma>)"
            using \<C>(2) \<omega>(3)
            unfolding Formula_Consistent_def
                      set_deduction_def
            by auto
          hence "False" by auto
        }
        thus ?thesis by blast
      qed
      ultimately show ?thesis by blast
    qed
  qed
  then obtain \<Omega> where \<Omega>: "\<Omega> \<in> ?\<Gamma>_Extensions"
                          "\<forall>\<Sigma> \<in> ?\<Gamma>_Extensions. \<Omega> \<subseteq> \<Sigma> \<longrightarrow> \<Sigma> = \<Omega>" by auto+
  {
    fix \<psi>
    have "(\<phi>-Consistent insert \<psi> \<Omega>) \<or> (\<phi>-Consistent insert (\<psi> \<rightarrow> \<phi>) \<Omega>)"
         "\<Gamma> \<subseteq> insert \<psi> \<Omega>"
         "\<Gamma> \<subseteq> insert (\<psi> \<rightarrow> \<phi>) \<Omega>"
      using \<Omega>(1) Formula_Consistent_Extension Formula_Consistent_def 
      by auto
    hence "insert \<psi> \<Omega> \<in> ?\<Gamma>_Extensions 
           \<or> insert (\<psi> \<rightarrow> \<phi>) \<Omega> \<in> ?\<Gamma>_Extensions" 
      by blast
    hence "\<psi> \<in> \<Omega> \<or> (\<psi> \<rightarrow> \<phi>) \<in> \<Omega>" using \<Omega>(2) by blast
  }
  thus ?thesis 
    using \<Omega>(1) 
    unfolding Formula_Maximally_Consistent_Set_def 
    by blast
qed

lemma (in Minimal_Logic) Formula_Maximally_Consistent_Set_reflection:
  "\<phi>-MCS \<Gamma> \<Longrightarrow> \<psi> \<in> \<Gamma> = \<Gamma> \<tturnstile> \<psi>"
proof -
  assume "\<phi>-MCS \<Gamma>"
  {
    assume "\<Gamma> \<tturnstile> \<psi>"
    moreover from \<open>\<phi>-MCS \<Gamma>\<close> have "\<psi> \<in> \<Gamma> \<or> (\<psi> \<rightarrow> \<phi>) \<in> \<Gamma>" "~ \<Gamma> \<tturnstile> \<phi>"
      unfolding Formula_Maximally_Consistent_Set_def Formula_Consistent_def
      by auto
    ultimately have "\<psi> \<in> \<Gamma>"
      using set_deduction_reflection set_deduction_modus_ponens
      by metis
  }
  thus "\<psi> \<in> \<Gamma> = \<Gamma> \<tturnstile> \<psi>"
    using set_deduction_reflection
    by metis
qed

theorem (in Minimal_Logic) 
  Formula_Maximally_Consistent_Set_implication_elimination:
  assumes "\<phi>-MCS \<Omega>"
  shows "(\<psi> \<rightarrow> \<chi>) \<in> \<Omega> \<Longrightarrow> \<psi> \<in> \<Omega> \<Longrightarrow> \<chi> \<in> \<Omega>"
  using assms
        Formula_Maximally_Consistent_Set_reflection
        set_deduction_modus_ponens
  by blast

end
