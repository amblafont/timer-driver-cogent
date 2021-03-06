(*
This file is generated by Cogent

*)

theory Driver_ShallowTuplesProof
imports "Driver_Shallow_Desugar"
"Driver_Shallow_Desugar_Tuples"
"CogentShallow.ShallowTuples"
begin

ML \<open>
structure ShallowTuplesRules_Driver =
  Named_Thms (
    val name = Binding.name "ShallowTuplesRules_Driver"
    val description = ""
  )
\<close>
setup \<open> ShallowTuplesRules_Driver.setup \<close>


ML \<open>
structure ShallowTuplesThms_Driver =
  Named_Thms (
    val name = Binding.name "ShallowTuplesThms_Driver"
    val description = ""
  )
\<close>
setup \<open> ShallowTuplesThms_Driver.setup \<close>


overloading shallow_tuples_rel_TimeoutInput \<equiv> shallow_tuples_rel begin
  definition "shallow_tuples_rel_TimeoutInput (x :: ('x1, 'x2, 'x3) Driver_ShallowShared.TimeoutInput) (xt :: 'xt1 \<times> 'xt2 \<times> 'xt3) \<equiv>
    shallow_tuples_rel (Driver_ShallowShared.TimeoutInput.p1\<^sub>f x) (prod.fst xt) \<and>
    shallow_tuples_rel (Driver_ShallowShared.TimeoutInput.p2\<^sub>f x) (prod.fst (prod.snd xt)) \<and>
    shallow_tuples_rel (Driver_ShallowShared.TimeoutInput.p3\<^sub>f x) (prod.snd (prod.snd xt))"
end
lemma shallow_tuples_rule__TimeoutInput_make [ShallowTuplesRules_Driver]:
  "\<lbrakk>
     shallow_tuples_rel x1 xt1;
     shallow_tuples_rel x2 xt2;
     shallow_tuples_rel x3 xt3
  \<rbrakk> \<Longrightarrow> shallow_tuples_rel (Driver_ShallowShared.TimeoutInput.make x1 x2 x3) (xt1, xt2, xt3)"
  by (simp add: shallow_tuples_rel_TimeoutInput_def Driver_ShallowShared.TimeoutInput.defs Px_px)
lemma shallow_tuples_rule__TimeoutInput__p1\<^sub>f [ShallowTuplesThms_Driver]:
  "shallow_tuples_rel (x :: ('x1, 'x2, 'x3) Driver_ShallowShared.TimeoutInput) (xt :: 'xt1 \<times> 'xt2 \<times> 'xt3) \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.TimeoutInput.p1\<^sub>f x) (prod.fst xt)"
  by (simp add: shallow_tuples_rel_TimeoutInput_def)
lemma shallow_tuples_rule__TimeoutInput__p2\<^sub>f [ShallowTuplesThms_Driver]:
  "shallow_tuples_rel (x :: ('x1, 'x2, 'x3) Driver_ShallowShared.TimeoutInput) (xt :: 'xt1 \<times> 'xt2 \<times> 'xt3) \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.TimeoutInput.p2\<^sub>f x) (prod.fst (prod.snd xt))"
  by (simp add: shallow_tuples_rel_TimeoutInput_def)
lemma shallow_tuples_rule__TimeoutInput__p3\<^sub>f [ShallowTuplesThms_Driver]:
  "shallow_tuples_rel (x :: ('x1, 'x2, 'x3) Driver_ShallowShared.TimeoutInput) (xt :: 'xt1 \<times> 'xt2 \<times> 'xt3) \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.TimeoutInput.p3\<^sub>f x) (prod.snd (prod.snd xt))"
  by (simp add: shallow_tuples_rel_TimeoutInput_def)


overloading shallow_tuples_rel_Meson_timer \<equiv> shallow_tuples_rel begin
  definition "shallow_tuples_rel_Meson_timer (x :: ('x1, 'x2) Driver_ShallowShared.Meson_timer) (xt :: ('xt1, 'xt2) Driver_ShallowShared_Tuples.Meson_timer) \<equiv>
    shallow_tuples_rel (Driver_ShallowShared.Meson_timer.regs\<^sub>f x) (Driver_ShallowShared_Tuples.Meson_timer.regs\<^sub>f xt) \<and>
    shallow_tuples_rel (Driver_ShallowShared.Meson_timer.disable\<^sub>f x) (Driver_ShallowShared_Tuples.Meson_timer.disable\<^sub>f xt)"
end
lemma shallow_tuples_rule_make__Meson_timer [ShallowTuplesRules_Driver]:
  "\<lbrakk>
     shallow_tuples_rel x1 xt1;
     shallow_tuples_rel x2 xt2
  \<rbrakk> \<Longrightarrow> shallow_tuples_rel (Driver_ShallowShared.Meson_timer.make x1 x2) \<lparr>Driver_ShallowShared_Tuples.Meson_timer.regs\<^sub>f = xt1, disable\<^sub>f = xt2\<rparr>"
  by (simp add: shallow_tuples_rel_Meson_timer_def Driver_ShallowShared.Meson_timer.defs Driver_ShallowShared_Tuples.Meson_timer.defs)
lemma shallow_tuples_rule__Meson_timer__regs\<^sub>f [ShallowTuplesThms_Driver]:
  "shallow_tuples_rel (x :: ('x1, 'x2) Driver_ShallowShared.Meson_timer) (xt :: ('xt1, 'xt2) Driver_ShallowShared_Tuples.Meson_timer) \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.Meson_timer.regs\<^sub>f x) (Driver_ShallowShared_Tuples.Meson_timer.regs\<^sub>f xt)"
  by (simp add: shallow_tuples_rel_Meson_timer_def)
lemma shallow_tuples_rule__Meson_timer__disable\<^sub>f [ShallowTuplesThms_Driver]:
  "shallow_tuples_rel (x :: ('x1, 'x2) Driver_ShallowShared.Meson_timer) (xt :: ('xt1, 'xt2) Driver_ShallowShared_Tuples.Meson_timer) \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.Meson_timer.disable\<^sub>f x) (Driver_ShallowShared_Tuples.Meson_timer.disable\<^sub>f xt)"
  by (simp add: shallow_tuples_rel_Meson_timer_def)
lemma shallow_tuples_rule__Meson_timer__regs\<^sub>f__update [ShallowTuplesRules_Driver]:
  "\<lbrakk> shallow_tuples_rel (x :: ('x1, 'x2) Driver_ShallowShared.Meson_timer) (xt :: ('xt1, 'xt2) Driver_ShallowShared_Tuples.Meson_timer);
     shallow_tuples_rel v vt
   \<rbrakk> \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.Meson_timer.regs\<^sub>f_update (\<lambda>_. v) x) (Driver_ShallowShared_Tuples.Meson_timer.regs\<^sub>f_update (\<lambda>_. vt) xt)"
  by (simp add: shallow_tuples_rel_Meson_timer_def)
lemma shallow_tuples_rule__Meson_timer__disable\<^sub>f__update [ShallowTuplesRules_Driver]:
  "\<lbrakk> shallow_tuples_rel (x :: ('x1, 'x2) Driver_ShallowShared.Meson_timer) (xt :: ('xt1, 'xt2) Driver_ShallowShared_Tuples.Meson_timer);
     shallow_tuples_rel v vt
   \<rbrakk> \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.Meson_timer.disable\<^sub>f_update (\<lambda>_. v) x) (Driver_ShallowShared_Tuples.Meson_timer.disable\<^sub>f_update (\<lambda>_. vt) xt)"
  by (simp add: shallow_tuples_rel_Meson_timer_def)


overloading shallow_tuples_rel_Meson_timer_reg \<equiv> shallow_tuples_rel begin
  definition "shallow_tuples_rel_Meson_timer_reg (x :: ('x1, 'x2, 'x3, 'x4, 'x5, 'x6, 'x7) Driver_ShallowShared.Meson_timer_reg) (xt :: ('xt1, 'xt2, 'xt3, 'xt4, 'xt5, 'xt6, 'xt7) Driver_ShallowShared_Tuples.Meson_timer_reg) \<equiv>
    shallow_tuples_rel (Driver_ShallowShared.Meson_timer_reg.timer_a_en\<^sub>f x) (Driver_ShallowShared_Tuples.Meson_timer_reg.timer_a_en\<^sub>f xt) \<and>
    shallow_tuples_rel (Driver_ShallowShared.Meson_timer_reg.timer_a\<^sub>f x) (Driver_ShallowShared_Tuples.Meson_timer_reg.timer_a\<^sub>f xt) \<and>
    shallow_tuples_rel (Driver_ShallowShared.Meson_timer_reg.timer_a_mode\<^sub>f x) (Driver_ShallowShared_Tuples.Meson_timer_reg.timer_a_mode\<^sub>f xt) \<and>
    shallow_tuples_rel (Driver_ShallowShared.Meson_timer_reg.timer_a_input_clk\<^sub>f x) (Driver_ShallowShared_Tuples.Meson_timer_reg.timer_a_input_clk\<^sub>f xt) \<and>
    shallow_tuples_rel (Driver_ShallowShared.Meson_timer_reg.timer_e\<^sub>f x) (Driver_ShallowShared_Tuples.Meson_timer_reg.timer_e\<^sub>f xt) \<and>
    shallow_tuples_rel (Driver_ShallowShared.Meson_timer_reg.timer_e_hi\<^sub>f x) (Driver_ShallowShared_Tuples.Meson_timer_reg.timer_e_hi\<^sub>f xt) \<and>
    shallow_tuples_rel (Driver_ShallowShared.Meson_timer_reg.timer_e_input_clk\<^sub>f x) (Driver_ShallowShared_Tuples.Meson_timer_reg.timer_e_input_clk\<^sub>f xt)"
end
lemma shallow_tuples_rule_make__Meson_timer_reg [ShallowTuplesRules_Driver]:
  "\<lbrakk>
     shallow_tuples_rel x1 xt1;
     shallow_tuples_rel x2 xt2;
     shallow_tuples_rel x3 xt3;
     shallow_tuples_rel x4 xt4;
     shallow_tuples_rel x5 xt5;
     shallow_tuples_rel x6 xt6;
     shallow_tuples_rel x7 xt7
  \<rbrakk> \<Longrightarrow> shallow_tuples_rel (Driver_ShallowShared.Meson_timer_reg.make x1 x2 x3 x4 x5 x6 x7) \<lparr>Driver_ShallowShared_Tuples.Meson_timer_reg.timer_a_en\<^sub>f = xt1, timer_a\<^sub>f = xt2 , timer_a_mode\<^sub>f = xt3 , timer_a_input_clk\<^sub>f = xt4 , timer_e\<^sub>f = xt5 , timer_e_hi\<^sub>f = xt6 , timer_e_input_clk\<^sub>f = xt7\<rparr>"
  by (simp add: shallow_tuples_rel_Meson_timer_reg_def Driver_ShallowShared.Meson_timer_reg.defs Driver_ShallowShared_Tuples.Meson_timer_reg.defs)
lemma shallow_tuples_rule__Meson_timer_reg__timer_a_en\<^sub>f [ShallowTuplesThms_Driver]:
  "shallow_tuples_rel (x :: ('x1, 'x2, 'x3, 'x4, 'x5, 'x6, 'x7) Driver_ShallowShared.Meson_timer_reg) (xt :: ('xt1, 'xt2, 'xt3, 'xt4, 'xt5, 'xt6, 'xt7) Driver_ShallowShared_Tuples.Meson_timer_reg) \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.Meson_timer_reg.timer_a_en\<^sub>f x) (Driver_ShallowShared_Tuples.Meson_timer_reg.timer_a_en\<^sub>f xt)"
  by (simp add: shallow_tuples_rel_Meson_timer_reg_def)
lemma shallow_tuples_rule__Meson_timer_reg__timer_a\<^sub>f [ShallowTuplesThms_Driver]:
  "shallow_tuples_rel (x :: ('x1, 'x2, 'x3, 'x4, 'x5, 'x6, 'x7) Driver_ShallowShared.Meson_timer_reg) (xt :: ('xt1, 'xt2, 'xt3, 'xt4, 'xt5, 'xt6, 'xt7) Driver_ShallowShared_Tuples.Meson_timer_reg) \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.Meson_timer_reg.timer_a\<^sub>f x) (Driver_ShallowShared_Tuples.Meson_timer_reg.timer_a\<^sub>f xt)"
  by (simp add: shallow_tuples_rel_Meson_timer_reg_def)
lemma shallow_tuples_rule__Meson_timer_reg__timer_a_mode\<^sub>f [ShallowTuplesThms_Driver]:
  "shallow_tuples_rel (x :: ('x1, 'x2, 'x3, 'x4, 'x5, 'x6, 'x7) Driver_ShallowShared.Meson_timer_reg) (xt :: ('xt1, 'xt2, 'xt3, 'xt4, 'xt5, 'xt6, 'xt7) Driver_ShallowShared_Tuples.Meson_timer_reg) \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.Meson_timer_reg.timer_a_mode\<^sub>f x) (Driver_ShallowShared_Tuples.Meson_timer_reg.timer_a_mode\<^sub>f xt)"
  by (simp add: shallow_tuples_rel_Meson_timer_reg_def)
lemma shallow_tuples_rule__Meson_timer_reg__timer_a_input_clk\<^sub>f [ShallowTuplesThms_Driver]:
  "shallow_tuples_rel (x :: ('x1, 'x2, 'x3, 'x4, 'x5, 'x6, 'x7) Driver_ShallowShared.Meson_timer_reg) (xt :: ('xt1, 'xt2, 'xt3, 'xt4, 'xt5, 'xt6, 'xt7) Driver_ShallowShared_Tuples.Meson_timer_reg) \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.Meson_timer_reg.timer_a_input_clk\<^sub>f x) (Driver_ShallowShared_Tuples.Meson_timer_reg.timer_a_input_clk\<^sub>f xt)"
  by (simp add: shallow_tuples_rel_Meson_timer_reg_def)
lemma shallow_tuples_rule__Meson_timer_reg__timer_e\<^sub>f [ShallowTuplesThms_Driver]:
  "shallow_tuples_rel (x :: ('x1, 'x2, 'x3, 'x4, 'x5, 'x6, 'x7) Driver_ShallowShared.Meson_timer_reg) (xt :: ('xt1, 'xt2, 'xt3, 'xt4, 'xt5, 'xt6, 'xt7) Driver_ShallowShared_Tuples.Meson_timer_reg) \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.Meson_timer_reg.timer_e\<^sub>f x) (Driver_ShallowShared_Tuples.Meson_timer_reg.timer_e\<^sub>f xt)"
  by (simp add: shallow_tuples_rel_Meson_timer_reg_def)
lemma shallow_tuples_rule__Meson_timer_reg__timer_e_hi\<^sub>f [ShallowTuplesThms_Driver]:
  "shallow_tuples_rel (x :: ('x1, 'x2, 'x3, 'x4, 'x5, 'x6, 'x7) Driver_ShallowShared.Meson_timer_reg) (xt :: ('xt1, 'xt2, 'xt3, 'xt4, 'xt5, 'xt6, 'xt7) Driver_ShallowShared_Tuples.Meson_timer_reg) \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.Meson_timer_reg.timer_e_hi\<^sub>f x) (Driver_ShallowShared_Tuples.Meson_timer_reg.timer_e_hi\<^sub>f xt)"
  by (simp add: shallow_tuples_rel_Meson_timer_reg_def)
lemma shallow_tuples_rule__Meson_timer_reg__timer_e_input_clk\<^sub>f [ShallowTuplesThms_Driver]:
  "shallow_tuples_rel (x :: ('x1, 'x2, 'x3, 'x4, 'x5, 'x6, 'x7) Driver_ShallowShared.Meson_timer_reg) (xt :: ('xt1, 'xt2, 'xt3, 'xt4, 'xt5, 'xt6, 'xt7) Driver_ShallowShared_Tuples.Meson_timer_reg) \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.Meson_timer_reg.timer_e_input_clk\<^sub>f x) (Driver_ShallowShared_Tuples.Meson_timer_reg.timer_e_input_clk\<^sub>f xt)"
  by (simp add: shallow_tuples_rel_Meson_timer_reg_def)
lemma shallow_tuples_rule__Meson_timer_reg__timer_a_en\<^sub>f__update [ShallowTuplesRules_Driver]:
  "\<lbrakk> shallow_tuples_rel (x :: ('x1, 'x2, 'x3, 'x4, 'x5, 'x6, 'x7) Driver_ShallowShared.Meson_timer_reg) (xt :: ('xt1, 'xt2, 'xt3, 'xt4, 'xt5, 'xt6, 'xt7) Driver_ShallowShared_Tuples.Meson_timer_reg);
     shallow_tuples_rel v vt
   \<rbrakk> \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.Meson_timer_reg.timer_a_en\<^sub>f_update (\<lambda>_. v) x) (Driver_ShallowShared_Tuples.Meson_timer_reg.timer_a_en\<^sub>f_update (\<lambda>_. vt) xt)"
  by (simp add: shallow_tuples_rel_Meson_timer_reg_def)
lemma shallow_tuples_rule__Meson_timer_reg__timer_a\<^sub>f__update [ShallowTuplesRules_Driver]:
  "\<lbrakk> shallow_tuples_rel (x :: ('x1, 'x2, 'x3, 'x4, 'x5, 'x6, 'x7) Driver_ShallowShared.Meson_timer_reg) (xt :: ('xt1, 'xt2, 'xt3, 'xt4, 'xt5, 'xt6, 'xt7) Driver_ShallowShared_Tuples.Meson_timer_reg);
     shallow_tuples_rel v vt
   \<rbrakk> \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.Meson_timer_reg.timer_a\<^sub>f_update (\<lambda>_. v) x) (Driver_ShallowShared_Tuples.Meson_timer_reg.timer_a\<^sub>f_update (\<lambda>_. vt) xt)"
  by (simp add: shallow_tuples_rel_Meson_timer_reg_def)
lemma shallow_tuples_rule__Meson_timer_reg__timer_a_mode\<^sub>f__update [ShallowTuplesRules_Driver]:
  "\<lbrakk> shallow_tuples_rel (x :: ('x1, 'x2, 'x3, 'x4, 'x5, 'x6, 'x7) Driver_ShallowShared.Meson_timer_reg) (xt :: ('xt1, 'xt2, 'xt3, 'xt4, 'xt5, 'xt6, 'xt7) Driver_ShallowShared_Tuples.Meson_timer_reg);
     shallow_tuples_rel v vt
   \<rbrakk> \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.Meson_timer_reg.timer_a_mode\<^sub>f_update (\<lambda>_. v) x) (Driver_ShallowShared_Tuples.Meson_timer_reg.timer_a_mode\<^sub>f_update (\<lambda>_. vt) xt)"
  by (simp add: shallow_tuples_rel_Meson_timer_reg_def)
lemma shallow_tuples_rule__Meson_timer_reg__timer_a_input_clk\<^sub>f__update [ShallowTuplesRules_Driver]:
  "\<lbrakk> shallow_tuples_rel (x :: ('x1, 'x2, 'x3, 'x4, 'x5, 'x6, 'x7) Driver_ShallowShared.Meson_timer_reg) (xt :: ('xt1, 'xt2, 'xt3, 'xt4, 'xt5, 'xt6, 'xt7) Driver_ShallowShared_Tuples.Meson_timer_reg);
     shallow_tuples_rel v vt
   \<rbrakk> \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.Meson_timer_reg.timer_a_input_clk\<^sub>f_update (\<lambda>_. v) x) (Driver_ShallowShared_Tuples.Meson_timer_reg.timer_a_input_clk\<^sub>f_update (\<lambda>_. vt) xt)"
  by (simp add: shallow_tuples_rel_Meson_timer_reg_def)
lemma shallow_tuples_rule__Meson_timer_reg__timer_e\<^sub>f__update [ShallowTuplesRules_Driver]:
  "\<lbrakk> shallow_tuples_rel (x :: ('x1, 'x2, 'x3, 'x4, 'x5, 'x6, 'x7) Driver_ShallowShared.Meson_timer_reg) (xt :: ('xt1, 'xt2, 'xt3, 'xt4, 'xt5, 'xt6, 'xt7) Driver_ShallowShared_Tuples.Meson_timer_reg);
     shallow_tuples_rel v vt
   \<rbrakk> \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.Meson_timer_reg.timer_e\<^sub>f_update (\<lambda>_. v) x) (Driver_ShallowShared_Tuples.Meson_timer_reg.timer_e\<^sub>f_update (\<lambda>_. vt) xt)"
  by (simp add: shallow_tuples_rel_Meson_timer_reg_def)
lemma shallow_tuples_rule__Meson_timer_reg__timer_e_hi\<^sub>f__update [ShallowTuplesRules_Driver]:
  "\<lbrakk> shallow_tuples_rel (x :: ('x1, 'x2, 'x3, 'x4, 'x5, 'x6, 'x7) Driver_ShallowShared.Meson_timer_reg) (xt :: ('xt1, 'xt2, 'xt3, 'xt4, 'xt5, 'xt6, 'xt7) Driver_ShallowShared_Tuples.Meson_timer_reg);
     shallow_tuples_rel v vt
   \<rbrakk> \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.Meson_timer_reg.timer_e_hi\<^sub>f_update (\<lambda>_. v) x) (Driver_ShallowShared_Tuples.Meson_timer_reg.timer_e_hi\<^sub>f_update (\<lambda>_. vt) xt)"
  by (simp add: shallow_tuples_rel_Meson_timer_reg_def)
lemma shallow_tuples_rule__Meson_timer_reg__timer_e_input_clk\<^sub>f__update [ShallowTuplesRules_Driver]:
  "\<lbrakk> shallow_tuples_rel (x :: ('x1, 'x2, 'x3, 'x4, 'x5, 'x6, 'x7) Driver_ShallowShared.Meson_timer_reg) (xt :: ('xt1, 'xt2, 'xt3, 'xt4, 'xt5, 'xt6, 'xt7) Driver_ShallowShared_Tuples.Meson_timer_reg);
     shallow_tuples_rel v vt
   \<rbrakk> \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.Meson_timer_reg.timer_e_input_clk\<^sub>f_update (\<lambda>_. v) x) (Driver_ShallowShared_Tuples.Meson_timer_reg.timer_e_input_clk\<^sub>f_update (\<lambda>_. vt) xt)"
  by (simp add: shallow_tuples_rel_Meson_timer_reg_def)


overloading shallow_tuples_rel_Timeout_timebase \<equiv> shallow_tuples_rel begin
  definition "shallow_tuples_rel_Timeout_timebase (x :: ('x1, 'x2, 'x3, 'x4) Driver_ShallowShared.Timeout_timebase) (xt :: ('xt1, 'xt2, 'xt3, 'xt4) Driver_ShallowShared_Tuples.Timeout_timebase) \<equiv>
    (\<exists>v vt. shallow_tuples_rel v vt \<and> x = Driver_ShallowShared.Timeout_timebase.COGENT_TIMEOUT_TIMEBASE_100_US v \<and> xt = Driver_ShallowShared_Tuples.Timeout_timebase.COGENT_TIMEOUT_TIMEBASE_100_US vt) \<or>
    (\<exists>v vt. shallow_tuples_rel v vt \<and> x = Driver_ShallowShared.Timeout_timebase.COGENT_TIMEOUT_TIMEBASE_10_US v \<and> xt = Driver_ShallowShared_Tuples.Timeout_timebase.COGENT_TIMEOUT_TIMEBASE_10_US vt) \<or>
    (\<exists>v vt. shallow_tuples_rel v vt \<and> x = Driver_ShallowShared.Timeout_timebase.COGENT_TIMEOUT_TIMEBASE_1_MS v \<and> xt = Driver_ShallowShared_Tuples.Timeout_timebase.COGENT_TIMEOUT_TIMEBASE_1_MS vt) \<or>
    (\<exists>v vt. shallow_tuples_rel v vt \<and> x = Driver_ShallowShared.Timeout_timebase.COGENT_TIMEOUT_TIMEBASE_1_US v \<and> xt = Driver_ShallowShared_Tuples.Timeout_timebase.COGENT_TIMEOUT_TIMEBASE_1_US vt)"
end
lemma shallow_tuples_rule_case__Timeout_timebase [ShallowTuplesThms_Driver]:
  "\<lbrakk> shallow_tuples_rel x xt;
     \<And>v vt. shallow_tuples_rel v vt \<Longrightarrow> shallow_tuples_rel (f1 v) (ft1 vt);
     \<And>v vt. shallow_tuples_rel v vt \<Longrightarrow> shallow_tuples_rel (f2 v) (ft2 vt);
     \<And>v vt. shallow_tuples_rel v vt \<Longrightarrow> shallow_tuples_rel (f3 v) (ft3 vt);
     \<And>v vt. shallow_tuples_rel v vt \<Longrightarrow> shallow_tuples_rel (f4 v) (ft4 vt)
   \<rbrakk> \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.case_Timeout_timebase f1 f2 f3 f4 x) (Driver_ShallowShared_Tuples.case_Timeout_timebase ft1 ft2 ft3 ft4 xt)"
  by (fastforce simp: shallow_tuples_rel_Timeout_timebase_def
        split: Driver_ShallowShared.Timeout_timebase.splits Driver_ShallowShared_Tuples.Timeout_timebase.splits)
lemma shallow_tuples_rule__Timeout_timebase__COGENT_TIMEOUT_TIMEBASE_100_US [ShallowTuplesRules_Driver]:
  "shallow_tuples_rel x xt \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.Timeout_timebase.COGENT_TIMEOUT_TIMEBASE_100_US x) (Driver_ShallowShared_Tuples.Timeout_timebase.COGENT_TIMEOUT_TIMEBASE_100_US xt)"
  by (simp add: shallow_tuples_rel_Timeout_timebase_def)
lemma shallow_tuples_rule__Timeout_timebase__COGENT_TIMEOUT_TIMEBASE_10_US [ShallowTuplesRules_Driver]:
  "shallow_tuples_rel x xt \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.Timeout_timebase.COGENT_TIMEOUT_TIMEBASE_10_US x) (Driver_ShallowShared_Tuples.Timeout_timebase.COGENT_TIMEOUT_TIMEBASE_10_US xt)"
  by (simp add: shallow_tuples_rel_Timeout_timebase_def)
lemma shallow_tuples_rule__Timeout_timebase__COGENT_TIMEOUT_TIMEBASE_1_MS [ShallowTuplesRules_Driver]:
  "shallow_tuples_rel x xt \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.Timeout_timebase.COGENT_TIMEOUT_TIMEBASE_1_MS x) (Driver_ShallowShared_Tuples.Timeout_timebase.COGENT_TIMEOUT_TIMEBASE_1_MS xt)"
  by (simp add: shallow_tuples_rel_Timeout_timebase_def)
lemma shallow_tuples_rule__Timeout_timebase__COGENT_TIMEOUT_TIMEBASE_1_US [ShallowTuplesRules_Driver]:
  "shallow_tuples_rel x xt \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.Timeout_timebase.COGENT_TIMEOUT_TIMEBASE_1_US x) (Driver_ShallowShared_Tuples.Timeout_timebase.COGENT_TIMEOUT_TIMEBASE_1_US xt)"
  by (simp add: shallow_tuples_rel_Timeout_timebase_def)


overloading shallow_tuples_rel_Timestamp_timebase \<equiv> shallow_tuples_rel begin
  definition "shallow_tuples_rel_Timestamp_timebase (x :: ('x1, 'x2, 'x3, 'x4, 'x5) Driver_ShallowShared.Timestamp_timebase) (xt :: ('xt1, 'xt2, 'xt3, 'xt4, 'xt5) Driver_ShallowShared_Tuples.Timestamp_timebase) \<equiv>
    (\<exists>v vt. shallow_tuples_rel v vt \<and> x = Driver_ShallowShared.Timestamp_timebase.COGENT_TIMESTAMP_TIMEBASE_100_US v \<and> xt = Driver_ShallowShared_Tuples.Timestamp_timebase.COGENT_TIMESTAMP_TIMEBASE_100_US vt) \<or>
    (\<exists>v vt. shallow_tuples_rel v vt \<and> x = Driver_ShallowShared.Timestamp_timebase.COGENT_TIMESTAMP_TIMEBASE_10_US v \<and> xt = Driver_ShallowShared_Tuples.Timestamp_timebase.COGENT_TIMESTAMP_TIMEBASE_10_US vt) \<or>
    (\<exists>v vt. shallow_tuples_rel v vt \<and> x = Driver_ShallowShared.Timestamp_timebase.COGENT_TIMESTAMP_TIMEBASE_1_MS v \<and> xt = Driver_ShallowShared_Tuples.Timestamp_timebase.COGENT_TIMESTAMP_TIMEBASE_1_MS vt) \<or>
    (\<exists>v vt. shallow_tuples_rel v vt \<and> x = Driver_ShallowShared.Timestamp_timebase.COGENT_TIMESTAMP_TIMEBASE_1_US v \<and> xt = Driver_ShallowShared_Tuples.Timestamp_timebase.COGENT_TIMESTAMP_TIMEBASE_1_US vt) \<or>
    (\<exists>v vt. shallow_tuples_rel v vt \<and> x = Driver_ShallowShared.Timestamp_timebase.COGENT_TIMESTAMP_TIMEBASE_SYSTEM v \<and> xt = Driver_ShallowShared_Tuples.Timestamp_timebase.COGENT_TIMESTAMP_TIMEBASE_SYSTEM vt)"
end
lemma shallow_tuples_rule_case__Timestamp_timebase [ShallowTuplesThms_Driver]:
  "\<lbrakk> shallow_tuples_rel x xt;
     \<And>v vt. shallow_tuples_rel v vt \<Longrightarrow> shallow_tuples_rel (f1 v) (ft1 vt);
     \<And>v vt. shallow_tuples_rel v vt \<Longrightarrow> shallow_tuples_rel (f2 v) (ft2 vt);
     \<And>v vt. shallow_tuples_rel v vt \<Longrightarrow> shallow_tuples_rel (f3 v) (ft3 vt);
     \<And>v vt. shallow_tuples_rel v vt \<Longrightarrow> shallow_tuples_rel (f4 v) (ft4 vt);
     \<And>v vt. shallow_tuples_rel v vt \<Longrightarrow> shallow_tuples_rel (f5 v) (ft5 vt)
   \<rbrakk> \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.case_Timestamp_timebase f1 f2 f3 f4 f5 x) (Driver_ShallowShared_Tuples.case_Timestamp_timebase ft1 ft2 ft3 ft4 ft5 xt)"
  by (fastforce simp: shallow_tuples_rel_Timestamp_timebase_def
        split: Driver_ShallowShared.Timestamp_timebase.splits Driver_ShallowShared_Tuples.Timestamp_timebase.splits)
lemma shallow_tuples_rule__Timestamp_timebase__COGENT_TIMESTAMP_TIMEBASE_100_US [ShallowTuplesRules_Driver]:
  "shallow_tuples_rel x xt \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.Timestamp_timebase.COGENT_TIMESTAMP_TIMEBASE_100_US x) (Driver_ShallowShared_Tuples.Timestamp_timebase.COGENT_TIMESTAMP_TIMEBASE_100_US xt)"
  by (simp add: shallow_tuples_rel_Timestamp_timebase_def)
lemma shallow_tuples_rule__Timestamp_timebase__COGENT_TIMESTAMP_TIMEBASE_10_US [ShallowTuplesRules_Driver]:
  "shallow_tuples_rel x xt \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.Timestamp_timebase.COGENT_TIMESTAMP_TIMEBASE_10_US x) (Driver_ShallowShared_Tuples.Timestamp_timebase.COGENT_TIMESTAMP_TIMEBASE_10_US xt)"
  by (simp add: shallow_tuples_rel_Timestamp_timebase_def)
lemma shallow_tuples_rule__Timestamp_timebase__COGENT_TIMESTAMP_TIMEBASE_1_MS [ShallowTuplesRules_Driver]:
  "shallow_tuples_rel x xt \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.Timestamp_timebase.COGENT_TIMESTAMP_TIMEBASE_1_MS x) (Driver_ShallowShared_Tuples.Timestamp_timebase.COGENT_TIMESTAMP_TIMEBASE_1_MS xt)"
  by (simp add: shallow_tuples_rel_Timestamp_timebase_def)
lemma shallow_tuples_rule__Timestamp_timebase__COGENT_TIMESTAMP_TIMEBASE_1_US [ShallowTuplesRules_Driver]:
  "shallow_tuples_rel x xt \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.Timestamp_timebase.COGENT_TIMESTAMP_TIMEBASE_1_US x) (Driver_ShallowShared_Tuples.Timestamp_timebase.COGENT_TIMESTAMP_TIMEBASE_1_US xt)"
  by (simp add: shallow_tuples_rel_Timestamp_timebase_def)
lemma shallow_tuples_rule__Timestamp_timebase__COGENT_TIMESTAMP_TIMEBASE_SYSTEM [ShallowTuplesRules_Driver]:
  "shallow_tuples_rel x xt \<Longrightarrow>
   shallow_tuples_rel (Driver_ShallowShared.Timestamp_timebase.COGENT_TIMESTAMP_TIMEBASE_SYSTEM x) (Driver_ShallowShared_Tuples.Timestamp_timebase.COGENT_TIMESTAMP_TIMEBASE_SYSTEM xt)"
  by (simp add: shallow_tuples_rel_Timestamp_timebase_def)


lemma shallow_tuples__reset_timer_e [ShallowTuplesThms_Driver]:
  "shallow_tuples_rel Driver_Shallow_Desugar.reset_timer_e Driver_Shallow_Desugar_Tuples.reset_timer_e"
  apply (rule shallow_tuples_rel_funI)
  apply (unfold Driver_Shallow_Desugar.reset_timer_e_def Driver_Shallow_Desugar_Tuples.reset_timer_e_def id_def)
  apply ((unfold take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def Let\<^sub>d\<^sub>s_def Let_def split_def)?,(simp only: fst_conv snd_conv)?)
  by (assumption |
      rule shallow_tuples_basic_bucket ShallowTuplesRules_Driver
           ShallowTuplesThms_Driver ShallowTuplesThms_Driver[THEN shallow_tuples_rel_funD])+


lemma shallow_tuples__meson_get_time_cogent [ShallowTuplesThms_Driver]:
  "shallow_tuples_rel Driver_Shallow_Desugar.meson_get_time_cogent Driver_Shallow_Desugar_Tuples.meson_get_time_cogent"
  apply (rule shallow_tuples_rel_funI)
  apply (unfold Driver_Shallow_Desugar.meson_get_time_cogent_def Driver_Shallow_Desugar_Tuples.meson_get_time_cogent_def id_def)
  apply ((unfold take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def Let\<^sub>d\<^sub>s_def Let_def split_def)?,(simp only: fst_conv snd_conv)?)
  by (assumption |
      rule shallow_tuples_basic_bucket ShallowTuplesRules_Driver
           ShallowTuplesThms_Driver ShallowTuplesThms_Driver[THEN shallow_tuples_rel_funD])+


lemma shallow_tuples__meson_init_cogent [ShallowTuplesThms_Driver]:
  "shallow_tuples_rel Driver_Shallow_Desugar.meson_init_cogent Driver_Shallow_Desugar_Tuples.meson_init_cogent"
  apply (rule shallow_tuples_rel_funI)
  apply (unfold Driver_Shallow_Desugar.meson_init_cogent_def Driver_Shallow_Desugar_Tuples.meson_init_cogent_def id_def)
  apply ((unfold take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def Let\<^sub>d\<^sub>s_def Let_def split_def)?,(simp only: fst_conv snd_conv)?)
  by (assumption |
      rule shallow_tuples_basic_bucket ShallowTuplesRules_Driver
           ShallowTuplesThms_Driver ShallowTuplesThms_Driver[THEN shallow_tuples_rel_funD])+


lemma shallow_tuples__meson_set_timeout_cogent [ShallowTuplesThms_Driver]:
  "shallow_tuples_rel Driver_Shallow_Desugar.meson_set_timeout_cogent Driver_Shallow_Desugar_Tuples.meson_set_timeout_cogent"
  apply (rule shallow_tuples_rel_funI)
  apply (unfold Driver_Shallow_Desugar.meson_set_timeout_cogent_def Driver_Shallow_Desugar_Tuples.meson_set_timeout_cogent_def id_def)
  apply ((unfold take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def Let\<^sub>d\<^sub>s_def Let_def split_def)?,(simp only: fst_conv snd_conv)?)
  by (assumption |
      rule shallow_tuples_basic_bucket ShallowTuplesRules_Driver
           ShallowTuplesThms_Driver ShallowTuplesThms_Driver[THEN shallow_tuples_rel_funD])+


lemma shallow_tuples__meson_stop_timer_cogent [ShallowTuplesThms_Driver]:
  "shallow_tuples_rel Driver_Shallow_Desugar.meson_stop_timer_cogent Driver_Shallow_Desugar_Tuples.meson_stop_timer_cogent"
  apply (rule shallow_tuples_rel_funI)
  apply (unfold Driver_Shallow_Desugar.meson_stop_timer_cogent_def Driver_Shallow_Desugar_Tuples.meson_stop_timer_cogent_def id_def)
  apply ((unfold take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def Let\<^sub>d\<^sub>s_def Let_def split_def)?,(simp only: fst_conv snd_conv)?)
  by (assumption |
      rule shallow_tuples_basic_bucket ShallowTuplesRules_Driver
           ShallowTuplesThms_Driver ShallowTuplesThms_Driver[THEN shallow_tuples_rel_funD])+


end
