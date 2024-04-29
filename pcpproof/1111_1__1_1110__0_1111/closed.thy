theory closed
  imports Main "PCPLib.PCP" "PCPLib.PCPTrans" "aut1_conf" "aut2_conf" "aut1_conf_step_1111_1" "aut1_conf_step_1_1110" "aut1_conf_step_0_1111" "aut2_conf_step_1111_1" "aut2_conf_step_1_1110" "aut2_conf_step_0_1111"  "pcp_instance" "aut1_contains_aut7" "aut1_contains_aut8" "accept_aut2_conf_DN_10" "accept_aut2_conf_DN_0" "aut1_contains_aut10" "aut2_contains_aut12" "accept_aut1_conf_UP_11" "aut2_contains_aut16" "aut2_contains_aut18" inv
begin

theorem closed:
  "pcp_step_configs pcp_instance inv \<subseteq> inv"
proof -
  have "\<forall>s t. s \<in> inv \<longrightarrow> List.member pcp_instance t \<longrightarrow> (step_config t s) \<subseteq> inv"
  proof (rule allI, rule allI, rule impI, rule impI)
    fix s t
    assume ASM: "s \<in> inv" "List.member pcp_instance t"

    consider  (t0) "t=tile_0" |  (t1) "t=tile_1" |  (t2) "t=tile_2"  
      using ASM(2) pcp_instance_def member_rec(1) member_rec(2) by metis

    then show "(step_config t s) \<subseteq> inv"
    proof (cases)
    
      case t0
      
      consider  (s0) "s\<in>lang_autconf aut1_conf" |  (s1) "s\<in>lang_autconf aut2_conf"  
        using inv_def ASM(1) by auto
      then show ?thesis proof (cases)
      
        case s0
        have A1:"lang_autconf (fst (step_autconf_tile aut1_conf t)) = lang_autconf aut7_conf"
          by (simp only: aut1_conf_step_1111_1.is_stepped_autconf t0 )

        then have A2:"... \<subseteq> lang_autconf aut1_conf"
          apply (simp only: aut1_conf_def aut7_conf_def )
          using  aut1_contains_aut7 by auto

        have B1:"snd (step_autconf_tile aut1_conf t) = aut1_conf_step_1111_1.stepped_confs" 
          by (simp only: aut1_conf_step_1111_1.is_stepped_configs t0 )
        
        then have B2:"... \<subseteq> {}" 
          by (simp add:  aut1_conf_step_1111_1.stepped_confs_def)
        
        then show ?thesis 
          using step_autconf_tile_eq_l[of aut1_conf t "lang_autconf (fst (step_autconf_tile aut1_conf t))" "snd (step_autconf_tile aut1_conf t)" ]  
            A1 B1 A2 B2  inv_def s0 by fastforce
        next
      
        case s1
        have A1:"lang_autconf (fst (step_autconf_tile aut2_conf t)) = lang_autconf aut12_conf"
          by (simp only: aut2_conf_step_1111_1.is_stepped_autconf t0 )

        then have A2:"... \<subseteq> lang_autconf aut2_conf"
          apply (simp only: aut2_conf_def aut12_conf_def )
          using  aut2_contains_aut12 by auto

        have B1:"snd (step_autconf_tile aut2_conf t) = aut2_conf_step_1111_1.stepped_confs" 
          by (simp only: aut2_conf_step_1111_1.is_stepped_configs t0 )
        
        then have B2:"... \<subseteq> (lang_autconf aut1_conf)\<union>{}" 
          by (simp add: accept_aut1_conf_UP_11 aut2_conf_step_1111_1.stepped_confs_def)
        
        then show ?thesis 
          using step_autconf_tile_eq_l[of aut2_conf t "lang_autconf (fst (step_autconf_tile aut2_conf t))" "snd (step_autconf_tile aut2_conf t)" ]  
            A1 B1 A2 B2  inv_def s1 by fastforce
        next
      
      qed

      next
      
      case t1
      
      consider  (s0) "s\<in>lang_autconf aut1_conf" |  (s1) "s\<in>lang_autconf aut2_conf"  
        using inv_def ASM(1) by auto
      then show ?thesis proof (cases)
      
        case s0
        have A1:"lang_autconf (fst (step_autconf_tile aut1_conf t)) = lang_autconf aut8_conf"
          by (simp only: aut1_conf_step_1_1110.is_stepped_autconf t1 )

        then have A2:"... \<subseteq> lang_autconf aut1_conf"
          apply (simp only: aut1_conf_def aut8_conf_def )
          using  aut1_contains_aut8 by auto

        have B1:"snd (step_autconf_tile aut1_conf t) = aut1_conf_step_1_1110.stepped_confs" 
          by (simp only: aut1_conf_step_1_1110.is_stepped_configs t1 )
        
        then have B2:"... \<subseteq> (lang_autconf aut2_conf)\<union>(lang_autconf aut2_conf)\<union>{}" 
          by (simp add: accept_aut2_conf_DN_10 accept_aut2_conf_DN_0 aut1_conf_step_1_1110.stepped_confs_def)
        
        then show ?thesis 
          using step_autconf_tile_eq_l[of aut1_conf t "lang_autconf (fst (step_autconf_tile aut1_conf t))" "snd (step_autconf_tile aut1_conf t)" ]  
            A1 B1 A2 B2  inv_def s0 by fastforce
        next
      
        case s1
        have A1:"lang_autconf (fst (step_autconf_tile aut2_conf t)) = lang_autconf aut16_conf"
          by (simp only: aut2_conf_step_1_1110.is_stepped_autconf t1 )

        then have A2:"... \<subseteq> lang_autconf aut2_conf"
          apply (simp only: aut2_conf_def aut16_conf_def )
          using  aut2_contains_aut16 by auto

        have B1:"snd (step_autconf_tile aut2_conf t) = aut2_conf_step_1_1110.stepped_confs" 
          by (simp only: aut2_conf_step_1_1110.is_stepped_configs t1 )
        
        then have B2:"... \<subseteq> {}" 
          by (simp add:  aut2_conf_step_1_1110.stepped_confs_def)
        
        then show ?thesis 
          using step_autconf_tile_eq_l[of aut2_conf t "lang_autconf (fst (step_autconf_tile aut2_conf t))" "snd (step_autconf_tile aut2_conf t)" ]  
            A1 B1 A2 B2  inv_def s1 by fastforce
        next
      
      qed

      next
      
      case t2
      
      consider  (s0) "s\<in>lang_autconf aut1_conf" |  (s1) "s\<in>lang_autconf aut2_conf"  
        using inv_def ASM(1) by auto
      then show ?thesis proof (cases)
      
        case s0
        have A1:"lang_autconf (fst (step_autconf_tile aut1_conf t)) = lang_autconf aut10_conf"
          by (simp only: aut1_conf_step_0_1111.is_stepped_autconf t2 )

        then have A2:"... \<subseteq> lang_autconf aut1_conf"
          apply (simp only: aut1_conf_def aut10_conf_def )
          using  aut1_contains_aut10 by auto

        have B1:"snd (step_autconf_tile aut1_conf t) = aut1_conf_step_0_1111.stepped_confs" 
          by (simp only: aut1_conf_step_0_1111.is_stepped_configs t2 )
        
        then have B2:"... \<subseteq> {}" 
          by (simp add:  aut1_conf_step_0_1111.stepped_confs_def)
        
        then show ?thesis 
          using step_autconf_tile_eq_l[of aut1_conf t "lang_autconf (fst (step_autconf_tile aut1_conf t))" "snd (step_autconf_tile aut1_conf t)" ]  
            A1 B1 A2 B2  inv_def s0 by fastforce
        next
      
        case s1
        have A1:"lang_autconf (fst (step_autconf_tile aut2_conf t)) = lang_autconf aut18_conf"
          by (simp only: aut2_conf_step_0_1111.is_stepped_autconf t2 )

        then have A2:"... \<subseteq> lang_autconf aut2_conf"
          apply (simp only: aut2_conf_def aut18_conf_def )
          using  aut2_contains_aut18 by auto

        have B1:"snd (step_autconf_tile aut2_conf t) = aut2_conf_step_0_1111.stepped_confs" 
          by (simp only: aut2_conf_step_0_1111.is_stepped_configs t2 )
        
        then have B2:"... \<subseteq> {}" 
          by (simp add:  aut2_conf_step_0_1111.stepped_confs_def)
        
        then show ?thesis 
          using step_autconf_tile_eq_l[of aut2_conf t "lang_autconf (fst (step_autconf_tile aut2_conf t))" "snd (step_autconf_tile aut2_conf t)" ]  
            A1 B1 A2 B2  inv_def s1 by fastforce
        next
      
      qed

      next
      
    qed
  qed
  then have "\<forall>s \<in> inv. (pcp_step_config pcp_instance s) \<subseteq> inv"
    using member_def by fastforce
  then show ?thesis by auto
qed


end