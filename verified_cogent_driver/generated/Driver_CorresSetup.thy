(*
This file is generated by Cogent

*)

theory Driver_CorresSetup
imports "CogentCRefinement.Deep_Embedding_Auto"
"CogentCRefinement.Cogent_Corres"
"CogentCRefinement.Tidy"
"CogentCRefinement.Heap_Relation_Generation"
"CogentCRefinement.Type_Relation_Generation"
"CogentCRefinement.Dargent_Custom_Get_Set"
"Driver_ACInstall"
"Driver_TypeProof"
begin

(* C type and value relations *)

instantiation unit_t_C :: cogent_C_val
begin
  definition type_rel_unit_t_C_def: "\<And> r. type_rel r (_ :: unit_t_C itself) \<equiv> r = RUnit"
  definition val_rel_unit_t_C_def: "\<And> uv. val_rel uv (_ :: unit_t_C) \<equiv> uv = UUnit"
  instance ..
end

instantiation bool_t_C :: cogent_C_val
begin
definition type_rel_bool_t_C_def: "\<And> typ. type_rel typ (_ :: bool_t_C itself) \<equiv> (typ = RPrim Bool)"
definition val_rel_bool_t_C_def:
   "\<And> uv x. val_rel uv (x :: bool_t_C) \<equiv> (boolean_C x = 0 \<or> boolean_C x = 1) \<and>
     uv = UPrim (LBool (boolean_C x \<noteq> 0))"
instance ..
end
context update_sem_init begin
lemmas corres_if = corres_if_base[where bool_val' = boolean_C,
                     OF _ _ val_rel_bool_t_C_def[THEN meta_eq_to_obj_eq, THEN iffD1]]
end

lemmas val_rel_simps[ValRelSimp] =
  val_rel_word
  val_rel_ptr_def
  val_rel_unit_def
  val_rel_unit_t_C_def
  val_rel_bool_t_C_def
  val_rel_fun_tag

lemmas type_rel_simps[TypeRelSimp] =
  type_rel_word
  type_rel_ptr_def
  type_rel_unit_def
  type_rel_unit_t_C_def
  type_rel_bool_t_C_def

(* C heap type class *)
class cogent_C_heap = cogent_C_val +
  fixes is_valid    :: "lifted_globals \<Rightarrow> 'a ptr \<Rightarrow> bool"
  fixes heap        :: "lifted_globals \<Rightarrow> 'a ptr \<Rightarrow> 'a"
(* generate direct definitions of custom getter/setters (for custom layouts) by
   inspecting their monadic definitions *)
setup \<open> generate_isa_getset_records_for_file "driver.c" @{locale driver} \<close>
local_setup \<open> local_setup_val_rel_type_rel_put_them_in_buckets "driver.c" \<close>
local_setup \<open> local_setup_instantiate_cogent_C_heaps_store_them_in_buckets "driver.c" \<close>
locale Driver = "driver" + update_sem_init
begin


(* The get/set lemmas that must be proven *)
ML \<open>val lems = mk_getset_lems "driver.c" @{context} \<close>
ML \<open>lems  |> map (string_of_getset_lem @{context})|> map tracing\<close>

(* This proves the get/set lemmas *)
local_setup \<open>local_setup_getset_lemmas "driver.c" \<close>


(* Relation between program heaps *)
definition
  heap_rel_ptr ::
  "(funtyp, abstyp, ptrtyp) store \<Rightarrow> lifted_globals \<Rightarrow>
   ('a :: cogent_C_heap) ptr \<Rightarrow> bool"
where
  "\<And> \<sigma> h p.
    heap_rel_ptr \<sigma> h p \<equiv>
   (\<forall> uv.
     \<sigma> (ptr_val p) = Some uv \<longrightarrow>
     type_rel (uval_repr uv) TYPE('a) \<longrightarrow>
     is_valid h p \<and> val_rel uv (heap h p))"

lemma heap_rel_ptr_meta:
  "heap_rel_ptr = heap_rel_meta is_valid heap"
  by (simp add: heap_rel_ptr_def[abs_def] heap_rel_meta_def[abs_def])

local_setup \<open> local_setup_heap_rel "driver.c" \<close>

definition state_rel :: "((funtyp, abstyp, ptrtyp) store \<times> lifted_globals) set"
where
  "state_rel  = {(\<sigma>, h). heap_rel \<sigma> h}"

(* Proving correctness of getters *)
local_setup \<open> local_setup_getter_correctness "driver.c" \<close>
(* Generating the specialised take and put lemmas *)

local_setup \<open> local_setup_take_put_member_case_esac_specialised_lemmas "driver.c" \<close>
local_setup \<open> fold tidy_C_fun_def' Cogent_functions \<close>

end (* of locale *)


end
