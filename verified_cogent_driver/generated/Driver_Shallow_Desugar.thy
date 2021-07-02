(*
This file is generated by Cogent

*)

theory Driver_Shallow_Desugar
imports "Driver_ShallowShared"
begin

definition
  reset_timer_e_cogent :: " Meson_timer_reg\<^sub>T \<Rightarrow>  Meson_timer_reg\<^sub>T"
where
  "reset_timer_e_cogent ds\<^sub>0 \<equiv> HOL.Let ds\<^sub>0 (\<lambda>r. Meson_timer_reg.timer_e\<^sub>f_update (\<lambda>_. (0 :: 32 word)) r)"

definition
  meson_get_time :: " Meson_timer\<^sub>T \<Rightarrow> 64 word"
where
  "meson_get_time ds\<^sub>0 \<equiv> HOL.Let ds\<^sub>0 (\<lambda>timer. HOL.Let (ucast (Meson_timer_reg.timer_e_hi\<^sub>f (Meson_timer.regs\<^sub>f timer)) :: 64 word) (\<lambda>initial_high. HOL.Let (ucast (Meson_timer_reg.timer_e\<^sub>f (Meson_timer.regs\<^sub>f timer)) :: 64 word) (\<lambda>low. HOL.Let (ucast (Meson_timer_reg.timer_e_hi\<^sub>f (Meson_timer.regs\<^sub>f timer)) :: 64 word) (\<lambda>high. HOL.Let (HOL.If ((~=) high initial_high) (ucast (Meson_timer_reg.timer_e\<^sub>f (Meson_timer.regs\<^sub>f timer)) :: 64 word) low) (\<lambda>low'. HOL.Let ((OR) (checked_shift shiftl high (32 :: 64 word)) low') (\<lambda>ticks. HOL.Let ((*) ticks (1000 :: 64 word)) (\<lambda>time. time)))))))"

definition
  meson_init :: "( Meson_timer\<^sub>T,  VAddr) T1 \<Rightarrow>  Meson_timer\<^sub>T"
where
  "meson_init ds\<^sub>0 \<equiv> HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>0 T1.p1\<^sub>f) (\<lambda>(timer,ds\<^sub>1). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>1 T1.p2\<^sub>f) (\<lambda>(vaddr,ds\<^sub>2). HOL.Let (config_get_regs vaddr) (\<lambda>regs. Meson_timer.regs\<^sub>f_update (\<lambda>_. reset_timer_e (Meson_timer_reg.timer_e_input_clk\<^sub>f_update (\<lambda>_. (Timestamp_timebase.TIMESTAMP_TIMEBASE_1_US () ::  Timestamp_timebase\<^sub>T)) (Meson_timer_reg.timer_a_input_clk\<^sub>f_update (\<lambda>_. (Timeout_timebase.TIMEOUT_TIMEBASE_1_MS () ::  Timeout_timebase\<^sub>T)) regs))) timer)))"

definition
  meson_set_timeout :: "( Meson_timer\<^sub>T, 16 word, bool) T0 \<Rightarrow>  Meson_timer\<^sub>T"
where
  "meson_set_timeout ds\<^sub>0 \<equiv> HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>0 T0.p1\<^sub>f) (\<lambda>(ds\<^sub>1,ds\<^sub>2). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>2 T0.p2\<^sub>f) (\<lambda>(timeout,ds\<^sub>3). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>3 T0.p3\<^sub>f) (\<lambda>(periodic,ds\<^sub>4). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>1 Meson_timer.regs\<^sub>f) (\<lambda>(regs,timer). HOL.Let (Meson_timer_reg.timer_a\<^sub>f_update (\<lambda>_. (ucast timeout :: 32 word)) (Meson_timer_reg.timer_a_mode\<^sub>f_update (\<lambda>_. periodic) regs)) (\<lambda>regs'. Let\<^sub>d\<^sub>s (Meson_timer.disable\<^sub>f timer) (\<lambda>ds\<^sub>5. HOL.If ds\<^sub>5 (Meson_timer.disable\<^sub>f_update (\<lambda>_. False) (Meson_timer.regs\<^sub>f_update (\<lambda>_. Meson_timer_reg.timer_a_en\<^sub>f_update (\<lambda>_. True) regs') timer)) (Meson_timer.regs\<^sub>f_update (\<lambda>_. regs') timer)))))))"

definition
  meson_stop_timer :: " Meson_timer\<^sub>T \<Rightarrow>  Meson_timer\<^sub>T"
where
  "meson_stop_timer ds\<^sub>0 \<equiv> HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>0 Meson_timer.regs\<^sub>f) (\<lambda>(regs,timer). Meson_timer.disable\<^sub>f_update (\<lambda>_. True) (Meson_timer.regs\<^sub>f_update (\<lambda>_. Meson_timer_reg.timer_a_en\<^sub>f_update (\<lambda>_. False) regs) timer))"

end