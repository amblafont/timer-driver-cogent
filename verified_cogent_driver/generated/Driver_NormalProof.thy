(*
This file is generated by Cogent

*)

theory Driver_NormalProof
imports "CogentShallow.Shallow_Normalisation_Tac"
"Driver_Shallow_Desugar"
"Driver_Shallow_Normal"
begin

ML \<open>
val Cogent_functions = ["reset_timer_e_cogent","meson_get_time","meson_init","meson_set_timeout","meson_stop_timer"]
\<close>

ML \<open>
val normalisation_thms = normalisation_tac_all @{context} "Driver_Shallow_Desugar" "Driver_Shallow_Normal" [] [] Cogent_functions
\<close>


end
