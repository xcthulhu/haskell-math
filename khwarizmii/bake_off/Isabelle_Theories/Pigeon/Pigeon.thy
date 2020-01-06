theory Pigeon
  imports "~~/src/HOL/Library/Permutation"
begin

(*<*)
no_notation perm (\<open>_ <~~> _\<close>  [50, 50] 50)
notation perm (infix "\<simeq>" 50)
(*>*)

lemma bounded_above_perm:
  fixes ns :: "nat list"
  assumes "distinct ns"
      and "\<forall> n \<in> set ns. 0 < n \<and> n \<le> length ns"
    shows "ns \<simeq> [1..<length ns + 1]"
  using assms
proof (induct "length ns" arbitrary: ns)
  case 0
  then show ?case by auto
next
  case (Suc m)
  have \<dagger>: "    \<forall>ns' n. ns \<simeq> n # ns'
           \<longrightarrow> length ns \<notin> set ns' 
           \<longrightarrow> ns \<simeq> [1..<length ns + 1]"
  proof (rule allI, rule allI, 
        rule impI, rule impI)
    fix n :: nat
    fix ns' :: "nat list"
    assume "ns \<simeq> n # ns'" 
       and "length ns \<notin> set ns'"
    hence "\<forall>n\<in>set ns'. 0 < n \<and> n \<le> m"
      by (metis Suc.hyps(2) Suc.prems(2) 
                le_SucE notin_set_remove1 
                perm_set_eq remove_hd)
    hence "ns' \<simeq> [1..<length ns]"
      by (metis \<open>ns \<simeq> n # ns'\<close> 
                One_nat_def Suc.hyps(1) 
                Suc.hyps(2) Suc.prems(1) 
                Suc_inject distinct.simps(2) 
                length_Cons list.size(4) 
                perm_distinct_iff 
                perm_length)
    have "n \<notin> set ns'"
      by (meson \<open>ns \<simeq> n # ns'\<close> 
                Suc.prems(1) 
                distinct.simps(2) 
                perm_distinct_iff)
    hence "n \<ge> length ns"
      by (metis \<open>ns \<simeq> n # ns'\<close> 
                \<open>ns' \<simeq> [1..<length ns]\<close> 
                One_nat_def 
                Suc.prems(2) Suc_leI 
                atLeastLessThan_iff 
                leI list.set_intros(1) 
                perm_set_eq set_upt)
    hence "n = length ns"
      using \<open>ns \<simeq> n # ns'\<close> 
           Suc.prems(2) 
           perm_set_eq 
      by force
    hence "n # ns' \<simeq> [1..<length ns + 1]"
      by (metis \<open>ns' \<simeq> [1..<length ns]\<close> 
                Suc.hyps(2) Suc_eq_plus1 
                Suc_eq_plus1_left 
                add.right_neutral
                add_le_cancel_right 
                leI not_less0 perm.Cons 
                perm.trans perm_append_single
                perm_sym upt_Suc)
    thus "ns \<simeq> [1..<length ns + 1]"
      using \<open>ns \<simeq> n # ns'\<close> by blast
  qed
  from Suc obtain n ns' 
    where "ns = n # ns'"
    by (meson Suc_length_conv)
  have "distinct ns'" 
       "\<forall>n\<in>set ns'. 0 < n \<and> n \<le> length ns" 
       "length ns' = m"
    using Suc(2) Suc(3) Suc(4)
    unfolding \<open>ns = n # ns'\<close>
    by auto
  show ?case
  proof (cases "length ns \<in> set ns'")
    case False
    thus ?thesis
      using \<dagger> \<open>ns = n # ns'\<close> by blast
  next
    let ?ns'' = "remove1 (length ns) (n # ns')"
    case True
    hence "(n # ns') \<simeq> length ns # ?ns''"
      using perm_remove by force
    moreover have "length ns \<notin> set ?ns''"
      using True Suc \<open>ns = n # ns'\<close> by simp
    ultimately show ?thesis
      using \<dagger> \<open>ns = n # ns'\<close> by blast  
  qed
qed

lemma pigeon_hol:
  fixes n :: nat
  fixes ns :: "nat list"
  assumes "distinct (n # ns)"
      and "\<forall> n' \<in> set (n # ns). 0 < n'"
    shows "\<exists> m \<in> set (n # ns). 
             length (n # ns) \<le> m"
proof (cases "\<forall> n' \<in> set (n # ns). 
                n' \<le> length (n # ns)")
  case False
  then show ?thesis
    using nat_le_linear by blast 
next
  case True
  hence "(n # ns) \<simeq> [1..<length (n # ns) + 1]"
    using assms bounded_above_perm by metis
  moreover have 
    "length (n # ns) 
       \<in> set [1..<length (n # ns) + 1]"
    by (induct ns, auto)
  ultimately show ?thesis
    using perm_set_eq by blast
qed

end