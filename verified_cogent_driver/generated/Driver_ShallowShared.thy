(*
This file is generated by Cogent

*)

theory Driver_ShallowShared
imports "Cogent.Util"
"CogentShallow.ShallowUtil"
begin

typedecl  VAddr

record ('a, 'b, 'c) T0 =
  p1\<^sub>f :: "'a"
  p2\<^sub>f :: "'b"
  p3\<^sub>f :: "'c"

record ('a, 'b) T1 =
  p1\<^sub>f :: "'a"
  p2\<^sub>f :: "'b"

record ('a, 'b) Meson_timer =
  regs\<^sub>f :: "'a"
  disable\<^sub>f :: "'b"

record ('a, 'b, 'c, 'd, 'e, 'f, 'g) Meson_timer_reg =
  timer_a_en\<^sub>f :: "'a"
  timer_a\<^sub>f :: "'b"
  timer_a_mode\<^sub>f :: "'c"
  timer_a_input_clk\<^sub>f :: "'d"
  timer_e\<^sub>f :: "'e"
  timer_e_hi\<^sub>f :: "'f"
  timer_e_input_clk\<^sub>f :: "'g"

datatype ('a, 'b, 'c, 'd) Timeout_timebase =
  TIMEOUT_TIMEBASE_100_US "'a"|
  TIMEOUT_TIMEBASE_10_US "'b"|
  TIMEOUT_TIMEBASE_1_MS "'c"|
  TIMEOUT_TIMEBASE_1_US "'d"

datatype ('a, 'b, 'c, 'd, 'e) Timestamp_timebase =
  TIMESTAMP_TIMEBASE_100_US "'a"|
  TIMESTAMP_TIMEBASE_10_US "'b"|
  TIMESTAMP_TIMEBASE_1_MS "'c"|
  TIMESTAMP_TIMEBASE_1_US "'d"|
  TIMESTAMP_TIMEBASE_SYSTEM "'e"

type_synonym  Timestamp_timebase\<^sub>T = "(unit, unit, unit, unit, unit) Timestamp_timebase"

type_synonym  Timeout_timebase\<^sub>T = "(unit, unit, unit, unit) Timeout_timebase"

type_synonym  Meson_timer_reg\<^sub>T = "(bool, 32 word, bool,  Timeout_timebase\<^sub>T, 32 word, 32 word,  Timestamp_timebase\<^sub>T) Meson_timer_reg"

type_synonym  Meson_timer\<^sub>T = "( Meson_timer_reg\<^sub>T, bool) Meson_timer"

consts config_get_regs :: " VAddr \<Rightarrow>  Meson_timer_reg\<^sub>T"

consts reset_timer_e :: " Meson_timer_reg\<^sub>T \<Rightarrow>  Meson_timer_reg\<^sub>T"

end
