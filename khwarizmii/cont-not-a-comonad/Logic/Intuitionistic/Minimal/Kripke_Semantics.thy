section \<open> Kripke Semantics For Intuitionistic Logic \<close>

theory Kripke_Semantics
  imports Main
          "./Combinators"
begin

(*:maxLineLen=80:*)

record ('a, 'b) Kripke_Model =
  R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  V :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

primrec
Intuitionistic_Kripke_Semantics
  :: "('a, 'b) Kripke_Model \<Rightarrow> 'a \<Rightarrow> 'b Simple_Type \<Rightarrow> bool" 
     ("_ _ \<Turnstile> _" [60,60,60] 60)
  where
    "(\<MM> x \<Turnstile> \<^bold>\<lbrace> v \<^bold>\<rbrace>) = (\<exists> w. (R \<MM>)\<^sup>*\<^sup>* w x \<and> (V \<MM>) w v)"
  | "(\<MM> x \<Turnstile> \<phi> \<^bold>\<Rightarrow> \<psi>) = (\<forall> y. (R \<MM>)\<^sup>*\<^sup>* x y \<longrightarrow> \<MM> y \<Turnstile> \<phi> \<longrightarrow> \<MM> y \<Turnstile> \<psi>)"

lemma Kripke_model_monotone:
  "(R \<MM>)\<^sup>*\<^sup>* x y \<Longrightarrow> \<MM> x \<Turnstile> \<phi> \<Longrightarrow> \<MM> y \<Turnstile> \<phi>"
  by (induct \<phi> arbitrary: y; simp)
     (meson rtranclp_trans)+

lemma Kripke_models_impl_flatten:
  "\<MM> x \<Turnstile> \<phi> \<^bold>\<Rightarrow> \<psi> \<^bold>\<Rightarrow> \<chi> = 
    (\<forall> y. (R \<MM>)\<^sup>*\<^sup>* x y \<longrightarrow> \<MM> y \<Turnstile> \<phi> \<longrightarrow> \<MM> y \<Turnstile> \<psi> \<longrightarrow> \<MM> y \<Turnstile> \<chi>)"
  by (rule iffI ; simp)
     (meson Kripke_model_monotone rtranclp_trans)

lemma Kripke_models_K:
  "\<MM> x \<Turnstile> \<phi> \<^bold>\<Rightarrow> \<psi> \<^bold>\<Rightarrow> \<phi>"
  by (meson Kripke_models_impl_flatten)

lemma Kripke_models_S:
  "\<MM> x \<Turnstile> (\<phi> \<^bold>\<Rightarrow> \<psi> \<^bold>\<Rightarrow> \<chi>) \<^bold>\<Rightarrow> (\<phi> \<^bold>\<Rightarrow> \<psi>) \<^bold>\<Rightarrow> \<phi> \<^bold>\<Rightarrow> \<chi>"
  by (simp, meson rtranclp.rtrancl_refl rtranclp_trans)

lemma Kripke_models_Modus_Ponens:
  "\<MM> x \<Turnstile> \<phi> \<^bold>\<Rightarrow> \<psi> \<Longrightarrow> \<MM> x \<Turnstile> \<phi> \<Longrightarrow> \<MM> x \<Turnstile> \<psi>"
  by auto

theorem Combinator_Typing_Kripke_Soundness:
  "X \<Colon> \<phi> \<Longrightarrow> \<MM> x \<Turnstile> \<phi>"
  by (induct rule: Simply_Typed_SKComb.induct)
     (meson Kripke_models_S, meson Kripke_models_K, auto)

lemma Combinator_Typing_Kripke_Soundness_alt: 
  "\<exists> X . X \<Colon> \<phi> \<Longrightarrow> \<forall> \<MM> x. \<MM> x \<Turnstile> \<phi>"
  by (meson Combinator_Typing_Kripke_Soundness)

lemma Kripke_Cont_Monad:
  assumes "a \<noteq> b"
  and "p \<noteq> q"
  and "\<MM> = \<lparr> R = (\<lambda> x y. x = a \<and> y = b), V = (\<lambda> x y. x = b \<and> y = p) \<rparr>"
  shows "\<not> \<MM> a \<Turnstile> ((\<^bold>\<lbrace> p \<^bold>\<rbrace> \<^bold>\<Rightarrow> \<^bold>\<lbrace> q \<^bold>\<rbrace>) \<^bold>\<Rightarrow> \<^bold>\<lbrace> q \<^bold>\<rbrace>) \<^bold>\<Rightarrow> \<^bold>\<lbrace> p \<^bold>\<rbrace>"
proof -
  have  "\<not> \<MM> b \<Turnstile> \<^bold>\<lbrace> p \<^bold>\<rbrace> \<^bold>\<Rightarrow> \<^bold>\<lbrace> q \<^bold>\<rbrace>"
        "\<not> \<MM> a \<Turnstile> \<^bold>\<lbrace> p \<^bold>\<rbrace> \<^bold>\<Rightarrow> \<^bold>\<lbrace> q \<^bold>\<rbrace>"
    unfolding assms(3)
    using assms(1) assms(2) by auto
  hence "\<forall> x. (R \<MM>)\<^sup>*\<^sup>* a x \<longrightarrow> \<not> \<MM> x \<Turnstile> \<^bold>\<lbrace> p \<^bold>\<rbrace> \<^bold>\<Rightarrow> \<^bold>\<lbrace> q \<^bold>\<rbrace>"
    unfolding assms(3)
    by (simp, metis (mono_tags, lifting) rtranclp.simps)
  hence "\<MM> a \<Turnstile> (\<^bold>\<lbrace> p \<^bold>\<rbrace> \<^bold>\<Rightarrow> \<^bold>\<lbrace> q \<^bold>\<rbrace>) \<^bold>\<Rightarrow> \<^bold>\<lbrace> q \<^bold>\<rbrace>"
    by fastforce
  moreover have "\<not> \<MM> a \<Turnstile> \<^bold>\<lbrace> p \<^bold>\<rbrace>"
    unfolding assms(3)
    using assms(1) converse_rtranclpE by fastforce
  ultimately show ?thesis
    by (meson Kripke_models_Modus_Ponens)
qed

lemma no_extract:
  assumes "p \<noteq> q"
  shows "\<nexists> X . X \<Colon> ((\<^bold>\<lbrace> p \<^bold>\<rbrace> \<^bold>\<Rightarrow> \<^bold>\<lbrace> q \<^bold>\<rbrace>) \<^bold>\<Rightarrow> \<^bold>\<lbrace> q \<^bold>\<rbrace>) \<^bold>\<Rightarrow> \<^bold>\<lbrace> p \<^bold>\<rbrace>"
  using assms
  by (metis
        Combinator_Typing_Kripke_Soundness
        Kripke_Cont_Monad)   

end