(*
This file is generated by Cogent

*)

theory Driver_SCorres_Normal
imports "Driver_Shallow_Normal"
"Driver_Deep_Normal"
"CogentShallow.Shallow_Tac"
begin

overloading
  valRel_TimeoutInput \<equiv> valRel
begin
  definition valRel_TimeoutInput: "\<And>\<xi> x v. valRel_TimeoutInput \<xi> (x :: ('t_p1, 't_p2, 't_p3) TimeoutInput) v \<equiv> \<exists>f_p1 f_p2 f_p3. v = VRecord [f_p1, f_p2, f_p3] \<and> valRel \<xi> (TimeoutInput.p1\<^sub>f x) f_p1 \<and> valRel \<xi> (TimeoutInput.p2\<^sub>f x) f_p2 \<and> valRel \<xi> (TimeoutInput.p3\<^sub>f x) f_p3"
end

overloading
  valRel_Meson_timer \<equiv> valRel
begin
  definition valRel_Meson_timer: "\<And>\<xi> x v. valRel_Meson_timer \<xi> (x :: ('t_regs, 't_disable) Meson_timer) v \<equiv> \<exists>f_regs f_disable. v = VRecord [f_regs, f_disable] \<and> valRel \<xi> (Meson_timer.regs\<^sub>f x) f_regs \<and> valRel \<xi> (Meson_timer.disable\<^sub>f x) f_disable"
end

overloading
  valRel_Meson_timer_reg \<equiv> valRel
begin
  definition valRel_Meson_timer_reg: "\<And>\<xi> x v. valRel_Meson_timer_reg \<xi> (x :: ('t_timer_a_en, 't_timer_a, 't_timer_a_mode, 't_timer_a_input_clk, 't_timer_e, 't_timer_e_hi, 't_timer_e_input_clk) Meson_timer_reg) v \<equiv> \<exists>f_timer_a_en f_timer_a f_timer_a_mode f_timer_a_input_clk f_timer_e f_timer_e_hi f_timer_e_input_clk. v = VRecord [f_timer_a_en, f_timer_a, f_timer_a_mode, f_timer_a_input_clk, f_timer_e, f_timer_e_hi, f_timer_e_input_clk] \<and> valRel \<xi> (Meson_timer_reg.timer_a_en\<^sub>f x) f_timer_a_en \<and> valRel \<xi> (Meson_timer_reg.timer_a\<^sub>f x) f_timer_a \<and> valRel \<xi> (Meson_timer_reg.timer_a_mode\<^sub>f x) f_timer_a_mode \<and> valRel \<xi> (Meson_timer_reg.timer_a_input_clk\<^sub>f x) f_timer_a_input_clk \<and> valRel \<xi> (Meson_timer_reg.timer_e\<^sub>f x) f_timer_e \<and> valRel \<xi> (Meson_timer_reg.timer_e_hi\<^sub>f x) f_timer_e_hi \<and> valRel \<xi> (Meson_timer_reg.timer_e_input_clk\<^sub>f x) f_timer_e_input_clk"
end

overloading
  valRel_Timeout_timebase \<equiv> valRel
begin
  definition valRel_Timeout_timebase: "valRel_Timeout_timebase \<xi> (v :: ('a, 'b, 'c, 'd) Timeout_timebase) v' \<equiv> case_Timeout_timebase (\<lambda>x. \<exists>x'. v' = VSum ''COGENT_TIMEOUT_TIMEBASE_100_US'' x' \<and> valRel \<xi> x x') (\<lambda>x. \<exists>x'. v' = VSum ''COGENT_TIMEOUT_TIMEBASE_10_US'' x' \<and> valRel \<xi> x x') (\<lambda>x. \<exists>x'. v' = VSum ''COGENT_TIMEOUT_TIMEBASE_1_MS'' x' \<and> valRel \<xi> x x') (\<lambda>x. \<exists>x'. v' = VSum ''COGENT_TIMEOUT_TIMEBASE_1_US'' x' \<and> valRel \<xi> x x') v"
end

overloading
  valRel_Timestamp_timebase \<equiv> valRel
begin
  definition valRel_Timestamp_timebase: "valRel_Timestamp_timebase \<xi> (v :: ('a, 'b, 'c, 'd, 'e) Timestamp_timebase) v' \<equiv> case_Timestamp_timebase (\<lambda>x. \<exists>x'. v' = VSum ''COGENT_TIMESTAMP_TIMEBASE_100_US'' x' \<and> valRel \<xi> x x') (\<lambda>x. \<exists>x'. v' = VSum ''COGENT_TIMESTAMP_TIMEBASE_10_US'' x' \<and> valRel \<xi> x x') (\<lambda>x. \<exists>x'. v' = VSum ''COGENT_TIMESTAMP_TIMEBASE_1_MS'' x' \<and> valRel \<xi> x x') (\<lambda>x. \<exists>x'. v' = VSum ''COGENT_TIMESTAMP_TIMEBASE_1_US'' x' \<and> valRel \<xi> x x') (\<lambda>x. \<exists>x'. v' = VSum ''COGENT_TIMESTAMP_TIMEBASE_SYSTEM'' x' \<and> valRel \<xi> x x') v"
end

lemma valRel_Timeout_timebase_COGENT_TIMEOUT_TIMEBASE_100_US[simp] :
  "valRel \<xi> (Timeout_timebase.COGENT_TIMEOUT_TIMEBASE_100_US x) (VSum ''COGENT_TIMEOUT_TIMEBASE_100_US'' x') = valRel \<xi> x x'"
  apply (simp add: valRel_Timeout_timebase)
  done

lemma valRel_Timeout_timebase_COGENT_TIMEOUT_TIMEBASE_10_US[simp] :
  "valRel \<xi> (Timeout_timebase.COGENT_TIMEOUT_TIMEBASE_10_US x) (VSum ''COGENT_TIMEOUT_TIMEBASE_10_US'' x') = valRel \<xi> x x'"
  apply (simp add: valRel_Timeout_timebase)
  done

lemma valRel_Timeout_timebase_COGENT_TIMEOUT_TIMEBASE_1_MS[simp] :
  "valRel \<xi> (Timeout_timebase.COGENT_TIMEOUT_TIMEBASE_1_MS x) (VSum ''COGENT_TIMEOUT_TIMEBASE_1_MS'' x') = valRel \<xi> x x'"
  apply (simp add: valRel_Timeout_timebase)
  done

lemma valRel_Timeout_timebase_COGENT_TIMEOUT_TIMEBASE_1_US[simp] :
  "valRel \<xi> (Timeout_timebase.COGENT_TIMEOUT_TIMEBASE_1_US x) (VSum ''COGENT_TIMEOUT_TIMEBASE_1_US'' x') = valRel \<xi> x x'"
  apply (simp add: valRel_Timeout_timebase)
  done

lemma valRel_Timestamp_timebase_COGENT_TIMESTAMP_TIMEBASE_100_US[simp] :
  "valRel \<xi> (Timestamp_timebase.COGENT_TIMESTAMP_TIMEBASE_100_US x) (VSum ''COGENT_TIMESTAMP_TIMEBASE_100_US'' x') = valRel \<xi> x x'"
  apply (simp add: valRel_Timestamp_timebase)
  done

lemma valRel_Timestamp_timebase_COGENT_TIMESTAMP_TIMEBASE_10_US[simp] :
  "valRel \<xi> (Timestamp_timebase.COGENT_TIMESTAMP_TIMEBASE_10_US x) (VSum ''COGENT_TIMESTAMP_TIMEBASE_10_US'' x') = valRel \<xi> x x'"
  apply (simp add: valRel_Timestamp_timebase)
  done

lemma valRel_Timestamp_timebase_COGENT_TIMESTAMP_TIMEBASE_1_MS[simp] :
  "valRel \<xi> (Timestamp_timebase.COGENT_TIMESTAMP_TIMEBASE_1_MS x) (VSum ''COGENT_TIMESTAMP_TIMEBASE_1_MS'' x') = valRel \<xi> x x'"
  apply (simp add: valRel_Timestamp_timebase)
  done

lemma valRel_Timestamp_timebase_COGENT_TIMESTAMP_TIMEBASE_1_US[simp] :
  "valRel \<xi> (Timestamp_timebase.COGENT_TIMESTAMP_TIMEBASE_1_US x) (VSum ''COGENT_TIMESTAMP_TIMEBASE_1_US'' x') = valRel \<xi> x x'"
  apply (simp add: valRel_Timestamp_timebase)
  done

lemma valRel_Timestamp_timebase_COGENT_TIMESTAMP_TIMEBASE_SYSTEM[simp] :
  "valRel \<xi> (Timestamp_timebase.COGENT_TIMESTAMP_TIMEBASE_SYSTEM x) (VSum ''COGENT_TIMESTAMP_TIMEBASE_SYSTEM'' x') = valRel \<xi> x x'"
  apply (simp add: valRel_Timestamp_timebase)
  done

lemmas valRel_records =
  valRel_TimeoutInput
  TimeoutInput.defs
  valRel_Meson_timer
  Meson_timer.defs
  valRel_Meson_timer_reg
  Meson_timer_reg.defs

lemmas valRel_variants =
  valRel_Timeout_timebase
  valRel_Timestamp_timebase

context shallow begin

lemma scorres_con_Timeout_timebase__COGENT_TIMEOUT_TIMEBASE_1_MS :
  "scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres (Timeout_timebase.COGENT_TIMEOUT_TIMEBASE_1_MS x) (Con ts ''COGENT_TIMEOUT_TIMEBASE_1_MS'' x') \<gamma> \<xi>"
  apply (erule scorres_con)
  apply simp
  done

lemma scorres_con_Timestamp_timebase__COGENT_TIMESTAMP_TIMEBASE_1_US :
  "scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres (Timestamp_timebase.COGENT_TIMESTAMP_TIMEBASE_1_US x) (Con ts ''COGENT_TIMESTAMP_TIMEBASE_1_US'' x') \<gamma> \<xi>"
  apply (erule scorres_con)
  apply simp
  done

lemmas scorres_cons =
  scorres_con_Timeout_timebase__COGENT_TIMEOUT_TIMEBASE_1_MS
  scorres_con_Timestamp_timebase__COGENT_TIMESTAMP_TIMEBASE_1_US

lemma scorres_struct_TimeoutInput :
  "\<And>\<gamma> \<xi> s_p1 s_p2 s_p3 d_p1 d_p2 d_p3.
  scorres s_p1 d_p1 \<gamma> \<xi> \<Longrightarrow>
  scorres s_p2 d_p2 \<gamma> \<xi> \<Longrightarrow>
  scorres s_p3 d_p3 \<gamma> \<xi> \<Longrightarrow>
  scorres (TimeoutInput.make s_p1 s_p2 s_p3) (Struct ts [d_p1, d_p2, d_p3]) \<gamma> \<xi>"
  apply (clarsimp simp: scorres_def valRel_TimeoutInput TimeoutInput.defs elim!: v_sem_elims)
  done

lemma scorres_struct_Meson_timer :
  "\<And>\<gamma> \<xi> s_regs s_disable d_regs d_disable.
  scorres s_regs d_regs \<gamma> \<xi> \<Longrightarrow>
  scorres s_disable d_disable \<gamma> \<xi> \<Longrightarrow>
  scorres (Meson_timer.make s_regs s_disable) (Struct ts [d_regs, d_disable]) \<gamma> \<xi>"
  apply (clarsimp simp: scorres_def valRel_Meson_timer Meson_timer.defs elim!: v_sem_elims)
  done

lemma scorres_struct_Meson_timer_reg :
  "\<And>\<gamma> \<xi> s_timer_a_en s_timer_a s_timer_a_mode s_timer_a_input_clk s_timer_e s_timer_e_hi s_timer_e_input_clk d_timer_a_en d_timer_a d_timer_a_mode d_timer_a_input_clk d_timer_e d_timer_e_hi d_timer_e_input_clk.
  scorres s_timer_a_en d_timer_a_en \<gamma> \<xi> \<Longrightarrow>
  scorres s_timer_a d_timer_a \<gamma> \<xi> \<Longrightarrow>
  scorres s_timer_a_mode d_timer_a_mode \<gamma> \<xi> \<Longrightarrow>
  scorres s_timer_a_input_clk d_timer_a_input_clk \<gamma> \<xi> \<Longrightarrow>
  scorres s_timer_e d_timer_e \<gamma> \<xi> \<Longrightarrow>
  scorres s_timer_e_hi d_timer_e_hi \<gamma> \<xi> \<Longrightarrow>
  scorres s_timer_e_input_clk d_timer_e_input_clk \<gamma> \<xi> \<Longrightarrow>
  scorres (Meson_timer_reg.make s_timer_a_en s_timer_a s_timer_a_mode s_timer_a_input_clk s_timer_e s_timer_e_hi s_timer_e_input_clk) (Struct ts [d_timer_a_en, d_timer_a, d_timer_a_mode, d_timer_a_input_clk, d_timer_e, d_timer_e_hi, d_timer_e_input_clk]) \<gamma> \<xi>"
  apply (clarsimp simp: scorres_def valRel_Meson_timer_reg Meson_timer_reg.defs elim!: v_sem_elims)
  done

lemmas scorres_structs =
  scorres_struct_TimeoutInput
  scorres_struct_Meson_timer
  scorres_struct_Meson_timer_reg

lemma shallow_tac_rec_field_TimeoutInput__p1 :
  "shallow_tac_rec_field \<xi> (TimeoutInput.p1\<^sub>f :: ('t_p1, 't_p2, 't_p3) TimeoutInput \<Rightarrow> 't_p1) TimeoutInput.p1\<^sub>f_update 0"
  apply (fastforce intro!: shallow_tac_rec_fieldI simp: valRel_TimeoutInput)
  done

lemma shallow_tac_rec_field_TimeoutInput__p2 :
  "shallow_tac_rec_field \<xi> (TimeoutInput.p2\<^sub>f :: ('t_p1, 't_p2, 't_p3) TimeoutInput \<Rightarrow> 't_p2) TimeoutInput.p2\<^sub>f_update 1"
  apply (fastforce intro!: shallow_tac_rec_fieldI simp: valRel_TimeoutInput)
  done

lemma shallow_tac_rec_field_TimeoutInput__p3 :
  "shallow_tac_rec_field \<xi> (TimeoutInput.p3\<^sub>f :: ('t_p1, 't_p2, 't_p3) TimeoutInput \<Rightarrow> 't_p3) TimeoutInput.p3\<^sub>f_update 2"
  apply (fastforce intro!: shallow_tac_rec_fieldI simp: valRel_TimeoutInput)
  done

lemma shallow_tac_rec_field_Meson_timer__regs :
  "shallow_tac_rec_field \<xi> (Meson_timer.regs\<^sub>f :: ('t_regs, 't_disable) Meson_timer \<Rightarrow> 't_regs) Meson_timer.regs\<^sub>f_update 0"
  apply (fastforce intro!: shallow_tac_rec_fieldI simp: valRel_Meson_timer)
  done

lemma shallow_tac_rec_field_Meson_timer__disable :
  "shallow_tac_rec_field \<xi> (Meson_timer.disable\<^sub>f :: ('t_regs, 't_disable) Meson_timer \<Rightarrow> 't_disable) Meson_timer.disable\<^sub>f_update 1"
  apply (fastforce intro!: shallow_tac_rec_fieldI simp: valRel_Meson_timer)
  done

lemma shallow_tac_rec_field_Meson_timer_reg__timer_a_en :
  "shallow_tac_rec_field \<xi> (Meson_timer_reg.timer_a_en\<^sub>f :: ('t_timer_a_en, 't_timer_a, 't_timer_a_mode, 't_timer_a_input_clk, 't_timer_e, 't_timer_e_hi, 't_timer_e_input_clk) Meson_timer_reg \<Rightarrow> 't_timer_a_en) Meson_timer_reg.timer_a_en\<^sub>f_update 0"
  apply (fastforce intro!: shallow_tac_rec_fieldI simp: valRel_Meson_timer_reg)
  done

lemma shallow_tac_rec_field_Meson_timer_reg__timer_a :
  "shallow_tac_rec_field \<xi> (Meson_timer_reg.timer_a\<^sub>f :: ('t_timer_a_en, 't_timer_a, 't_timer_a_mode, 't_timer_a_input_clk, 't_timer_e, 't_timer_e_hi, 't_timer_e_input_clk) Meson_timer_reg \<Rightarrow> 't_timer_a) Meson_timer_reg.timer_a\<^sub>f_update 1"
  apply (fastforce intro!: shallow_tac_rec_fieldI simp: valRel_Meson_timer_reg)
  done

lemma shallow_tac_rec_field_Meson_timer_reg__timer_a_mode :
  "shallow_tac_rec_field \<xi> (Meson_timer_reg.timer_a_mode\<^sub>f :: ('t_timer_a_en, 't_timer_a, 't_timer_a_mode, 't_timer_a_input_clk, 't_timer_e, 't_timer_e_hi, 't_timer_e_input_clk) Meson_timer_reg \<Rightarrow> 't_timer_a_mode) Meson_timer_reg.timer_a_mode\<^sub>f_update 2"
  apply (fastforce intro!: shallow_tac_rec_fieldI simp: valRel_Meson_timer_reg)
  done

lemma shallow_tac_rec_field_Meson_timer_reg__timer_a_input_clk :
  "shallow_tac_rec_field \<xi> (Meson_timer_reg.timer_a_input_clk\<^sub>f :: ('t_timer_a_en, 't_timer_a, 't_timer_a_mode, 't_timer_a_input_clk, 't_timer_e, 't_timer_e_hi, 't_timer_e_input_clk) Meson_timer_reg \<Rightarrow> 't_timer_a_input_clk) Meson_timer_reg.timer_a_input_clk\<^sub>f_update 3"
  apply (fastforce intro!: shallow_tac_rec_fieldI simp: valRel_Meson_timer_reg)
  done

lemma shallow_tac_rec_field_Meson_timer_reg__timer_e :
  "shallow_tac_rec_field \<xi> (Meson_timer_reg.timer_e\<^sub>f :: ('t_timer_a_en, 't_timer_a, 't_timer_a_mode, 't_timer_a_input_clk, 't_timer_e, 't_timer_e_hi, 't_timer_e_input_clk) Meson_timer_reg \<Rightarrow> 't_timer_e) Meson_timer_reg.timer_e\<^sub>f_update 4"
  apply (fastforce intro!: shallow_tac_rec_fieldI simp: valRel_Meson_timer_reg)
  done

lemma shallow_tac_rec_field_Meson_timer_reg__timer_e_hi :
  "shallow_tac_rec_field \<xi> (Meson_timer_reg.timer_e_hi\<^sub>f :: ('t_timer_a_en, 't_timer_a, 't_timer_a_mode, 't_timer_a_input_clk, 't_timer_e, 't_timer_e_hi, 't_timer_e_input_clk) Meson_timer_reg \<Rightarrow> 't_timer_e_hi) Meson_timer_reg.timer_e_hi\<^sub>f_update 5"
  apply (fastforce intro!: shallow_tac_rec_fieldI simp: valRel_Meson_timer_reg)
  done

lemma shallow_tac_rec_field_Meson_timer_reg__timer_e_input_clk :
  "shallow_tac_rec_field \<xi> (Meson_timer_reg.timer_e_input_clk\<^sub>f :: ('t_timer_a_en, 't_timer_a, 't_timer_a_mode, 't_timer_a_input_clk, 't_timer_e, 't_timer_e_hi, 't_timer_e_input_clk) Meson_timer_reg \<Rightarrow> 't_timer_e_input_clk) Meson_timer_reg.timer_e_input_clk\<^sub>f_update 6"
  apply (fastforce intro!: shallow_tac_rec_fieldI simp: valRel_Meson_timer_reg)
  done

lemmas scorres_rec_fields =
  shallow_tac_rec_field_TimeoutInput__p1
  shallow_tac_rec_field_TimeoutInput__p2
  shallow_tac_rec_field_TimeoutInput__p3
  shallow_tac_rec_field_Meson_timer__regs
  shallow_tac_rec_field_Meson_timer__disable
  shallow_tac_rec_field_Meson_timer_reg__timer_a_en
  shallow_tac_rec_field_Meson_timer_reg__timer_a
  shallow_tac_rec_field_Meson_timer_reg__timer_a_mode
  shallow_tac_rec_field_Meson_timer_reg__timer_a_input_clk
  shallow_tac_rec_field_Meson_timer_reg__timer_e
  shallow_tac_rec_field_Meson_timer_reg__timer_e_hi
  shallow_tac_rec_field_Meson_timer_reg__timer_e_input_clk

local_setup \<open>
gen_scorres_lemmas "Driver_ShallowShared" "Driver_Shallow_Normal" "Driver_Deep_Normal" Cogent_abstract_functions Cogent_functions
\<close>


end

end
