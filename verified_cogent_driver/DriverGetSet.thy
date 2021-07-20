theory DriverGetSet
  imports Main "HOL-Word.Word" "Word_Lib.Word_Lib" 
 "generated/Driver_CorresSetup"
begin
ML \<open> structure GetSetSanity = Named_Thms_Ext
 (val name = @{binding "GetSetSanity"}
  val description = "Sanity checks about custom getters and setters.") \<close>
setup \<open>GetSetSanity.setup\<close>
context Driver begin


(* Getters and setters (for a custom laid out record) get a monadic embedding through
AutoCorres. Direct (non-monadic) definitions are also inferred. Their
names are prefixed with "deref"
The lemmas in GetSetDefs provide the definitions of both versions
*)
thm GetSetDefs
find_consts name:deref

(* Get/set lemmas are gathered in GetSetSimp*)
thm GetSetSimp
(* Some examples: 
- correspondence between the monadic embedding and the direct definition
- getting and setting a different field 
- getting and setting the same field
*)
thm 
d12_set_timer_a_input_clk_def_alt
t3_C_get_timer_a_input_clk_set_timer_e_input_clk
t3_C_get_timer_a_input_clk_set_timer_a_input_clk

(* To prove that custom getters and setters are doing the right thing,
one can reason about their direct definitions *)

definition find_position :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat"
  where "find_position si offset  = (offset div si, offset mod si)"

fun get_bit :: "(('a::len0) word)['n::finite] \<Rightarrow> nat \<Rightarrow> bool"
  where "get_bit arr pos = 
                (let (byte, off) = find_position LENGTH('a) pos in
                 arr.[byte] !! off )"

fun raw_get_bit :: "(('a::len0) word)['n::finite] \<Rightarrow> nat \<Rightarrow> 'a word"
  where "raw_get_bit arr pos = 
                (let (byte, off) = find_position LENGTH('a) pos in
                 arr.[byte] && 2^off )"



definition size_of_arr :: "(('a::len0) word)['n::finite] \<Rightarrow> nat"
  where "size_of_arr _ = CARD('n)"

definition size_of_arr_bits :: "(('a::len0) word)['n::finite] \<Rightarrow> nat"
  where "size_of_arr_bits _ = LENGTH('a)*CARD('n)"
ML \<open>
val uvals = 
Symtab.lookup (UVals.get @{theory}) "driver_pp_inferred.c"
|> the
(* Filter those with custom layouts*)
 |> get_uval_custom_layout_records
\<close>
ML \<open>
 val uval0 = hd uvals
\<close>
thm val_rel_t3_C_def
term t3_C
ML \<open>fst\<close>
ML \<open>
val (info0, lay0) = 
case get_uval_layout uval0 of
CustomLayout (info, 
Const ("Option.option.Some", _) $ 
( Const ("Cogent.ptr_layout.LayRecord", _) $ 
layout)) => 
(info, 
layout |> HOLogic.dest_list
|> map HOLogic.dest_prod
|> map (apfst HOLogic.dest_string)
|> Symtab.make
)

val field0 = hd info0
val layfield0 = Symtab.lookup lay0 (# name field0) |> the
\<close>

ML \<open>
val get_data =
get_uval_name uval0 ^ "_C.data_C"
\<close>

ML \<open>
fun getter_sanity_tac ctxt = 
 let
    val gets = Proof_Context.get_thms ctxt
    val get  = Proof_Context.get_thm ctxt
  in
 (* K (print_tac ctxt "debut")
THEN' *)
 (asm_full_simp_tac (ctxt addsimps [(get "find_position_def")])
THEN'
 (fn i => 
TRY (REPEAT_ALL_NEW (eresolve_tac ctxt @{thms exE conjE}) i))
(* THEN' K (print_tac ctxt "coucou") *)
THEN' custom_get_set_different_field_tac ctxt
) end
\<close>
lemma wesh : "x < LENGTH('a) \<Longrightarrow> (((2 ^ x) :: ('a :: len0)  word) !! n) = (x = n)"
  by sorry
ML \<open>
fun setter_sanity_tac ctxt = 
 let
    val gets = Proof_Context.get_thms ctxt
    val get  = Proof_Context.get_thm ctxt
  in
  K (print_tac ctxt "debut")
THEN' 
 (asm_full_simp_tac (ctxt addsimps
 [get "find_position_def", get "size_of_arr_bits_def"]))
THEN'
(asm_full_simp_tac ((clear_simpset ctxt) addsimps
 (gets "numeral.simps")))
THEN' asm_full_simp_tac ctxt
(* THEN'  K (print_tac ctxt "suite") *)
THEN'
 (fn i => 
TRY (REPEAT_ALL_NEW (eresolve_tac ctxt @{thms exE conjE}) i))
(* THEN'  K (print_tac ctxt "resuite") *)
(* THEN'  (fn i => 
TRY (REPEAT_ALL_NEW (eresolve_tac ctxt @{thms less_zeroE less_SucE}) i)) *)

 (* THEN' K (print_tac ctxt "coucou")  *)
THEN_ALL_NEW custom_get_set_different_field_tac (ctxt addsimps @{thms wesh})
 end
\<close>
ML \<open>
fun prove_thm ctxt assms concl tactic = 
let
val clean = HOLogic.mk_Trueprop o strip_atype
val thm0 = mk_meta_imps (map clean assms) (concl |> clean) ctxt
val names =  Variable.add_free_names ctxt thm0 []
in
Goal.prove ctxt names [] thm0
( fn {context, prems} => tactic context 1)
end
\<close>
ML \<open>
fun make_getter_sanity_thm ctxt layfield (field_info : field_layout) = 
let
val ass = 
  @{term 
  "\<lambda>  lay data. 
   (\<forall> x\<in> set(layout_taken_bit_list lay). 
  get_bit (data s) x = get_bit (data t) x)
  "
  } $ layfield $ (Syntax.read_term ctxt get_data)
val concl = @{term "\<lambda> getter . getter s = getter t"  }
        $ # isa_getter field_info
in
prove_thm ctxt [ass] concl getter_sanity_tac
end

\<close>
ML \<open>
fun make_setter_sanity_thm ctxt layfield (field_info : field_layout) = 
let
 val data = Syntax.read_term ctxt get_data
val ass1 = 
  @{term 
  "\<lambda>  data .x < size_of_arr_bits (data s) 
  "
  } $ data
val ass2 = 
  @{term 
  "\<lambda>  lay .x \<notin> set (layout_taken_bit_list lay) 
  "
  } $ layfield
val concl = @{term "\<lambda> data setter . 
   raw_get_bit (data (setter s b)) x = raw_get_bit (data s) x"  }
        $ data
        $ # isa_setter field_info
in
prove_thm ctxt [ass1, ass2] concl (fn ctxt => fn _ => print_tac ctxt "coucuo" THEN cheat_tactic ctxt)(* setter_sanity_tac *)
end
\<close>
ML \<open>
fun make_getset_sanity_thms ctxt (uval : field_layout uval) : (thm * thm) list =
let
val (info, lays) = 
case get_uval_layout uval of
CustomLayout (info, 
Const ("Option.option.Some", _) $ 
( Const ("Cogent.ptr_layout.LayRecord", _) $ 
layout)) => 
(info, 
layout |> HOLogic.dest_list
|> map HOLogic.dest_prod
|> map (apfst HOLogic.dest_string)
|> Symtab.make
)
in
map (
fn field => 
let val lay = Symtab.lookup lays (# name field) |> the in
(make_getter_sanity_thm ctxt  lay field,
make_setter_sanity_thm ctxt lay field)
end
)
 
 info

end
\<close>
term layout_taken_bit_list
term "x :: 33 word"
definition layout_taken_words :: "nat \<Rightarrow> ptr_layout \<Rightarrow> nat list"
  where "layout_taken_words l p = map (\<lambda>b. b div l) (layout_taken_bit_list p)"
term Arrays.foldli
term Arrays.index
find_consts "_ list" "_ word"
find_consts "_ word" name:cat
lemma 
(* " x < size_of_arr_bits (data_C s) \<Longrightarrow>
x > 18 \<Longrightarrow>
    x \<notin> set (layout_taken_bit_list (LayBitRange (Suc 0, 15))) \<Longrightarrow>
*)facile:
"n < size_of_arr (data_C s) \<Longrightarrow> n \<notin> set (layout_taken_words 32 ( (LayBitRange (Suc 0, 15)))) \<Longrightarrow>
    (data_C (deref_d32_set_timer_a_en s b)) .[n] =  (data_C s).[n]"
(*   raw_get_bit (data_C (deref_d32_set_timer_a_en s b)) x = raw_get_bit (data_C s) x" *)
  apply (simp add:find_position_def size_of_arr_def layout_taken_words_def)
  (* apply(simp only:numeral.simps) *)
  apply simp
  apply(erule exE conjE)+
(*  apply(erule  less_zeroE less_SucE)+ *)
  apply(tactic \<open>custom_get_set_different_field_tac @{context} 1\<close>)
  done



lemma yop_find_pos : "0 < q \<Longrightarrow> x < n \<Longrightarrow> 
\<exists> p r. find_position q x = (p, r) \<and>
r < q \<and> p \<le> n div q \<and> (p = n div q \<longrightarrow> r < n mod q)
"
  apply(simp add:find_position_def div_le_mono)
  apply(intro impI)
  apply (simp flip: minus_mult_div_eq_mod)  
  by (metis less_diff_iff times_div_less_eq_dividend)

lemma yop_find_pos_split : "0 < q \<Longrightarrow> x < n \<Longrightarrow> P (case find_position q x of (p,r) \<Rightarrow> f p r)
  = ((\<forall> p r. find_position q x = (p, r) \<longrightarrow>
r < q \<longrightarrow> p < n div q \<longrightarrow>  P (f p r))
\<and> (\<forall> r. find_position q x = (n div q, r) \<longrightarrow> r < n mod q \<longrightarrow> P (f (n div q) r) ))
"
  apply (frule(1) yop_find_pos[of q x n])
  apply(erule exE conjE)+
  apply simp
  
  apply rule+
    
    apply clarsimp+
  done

lemma yop_find_pos_split' : " P (case find_position q x of (p,r) \<Rightarrow> f p r)
  = ((\<forall> p r. find_position q x = (p, r) \<longrightarrow>
r < q \<longrightarrow> p < n div q \<longrightarrow>  P (f p r))
\<and> (\<forall> r. find_position q x = (n div q, r) \<longrightarrow> r < n mod q \<longrightarrow> P (f (n div q) r) ))
"
  by sorry



lemma yop_find_pos_split'' : " P (case find_position q x of (p,r) \<Rightarrow> f p r)
  = ((\<forall> p r. find_position q x = (p, r) \<longrightarrow>
r < q \<longrightarrow> p < n div q \<longrightarrow>  P (f p r))
\<and> (\<forall> r. find_position q x = (n div q, r) \<longrightarrow> r < n mod q \<longrightarrow> P (f (n div q) r) )
\<and> (\<forall> p r. find_position q x = (p, r) \<longrightarrow> (x \<ge> n \<or> q = 0) \<longrightarrow> P (f p r) )
)
"
  apply simp
  apply rule+
    apply simp
   apply(rule)+
    apply clarsimp+
  thm le_less_linear[of n x, THEN disjE]
  apply(rule le_less_linear[of n x, THEN disjE])
  apply (simp add: find_position_def)
  apply clarsimp+
  apply(rule gt_or_eq_0[of q, THEN disjE])
   apply (frule(1) yop_find_pos[of q x n])
 apply(erule exE conjE)+
  apply simp
 
    
   apply clarsimp+
  apply (simp add: find_position_def)
  done

lemma yop_find_pos_split'2 : " P (find_position q x)
  = ((\<forall> p r. find_position q x = (p, r) \<longrightarrow>
r < q \<longrightarrow> p < n div q \<longrightarrow>  P (p, r))
\<and> (\<forall> r. find_position q x = (n div q, r) \<longrightarrow> r < n mod q \<longrightarrow> P ( (n div q), r) )
\<and> (\<forall> p r. find_position q x = (p, r) \<longrightarrow> (x \<ge> n \<or> q = 0) \<longrightarrow> P ( p, r) )
)
"
  apply simp
  apply rule+
    apply simp
   apply(rule)+
    apply clarsimp+
  thm le_less_linear[of n x, THEN disjE]
  apply(rule le_less_linear[of n x, THEN disjE])
  apply (simp add: find_position_def)
  apply clarsimp+
  apply(rule gt_or_eq_0[of q, THEN disjE])
   apply (frule(1) yop_find_pos[of q x n])
 apply(erule exE conjE)+
  apply simp
 
    
   apply clarsimp+
  apply (simp add: find_position_def)
  done

thm nat.split
lemma "  (case find_position q x of (byte, off) \<Rightarrow> (data_C s.[off] && 2 ^ byte)) =
    (case find_position q x of (byte, off) \<Rightarrow> data_C s.[byte] && 2 ^ off) "
apply( split yop_find_pos_split'2)
lemma "0 < q \<Longrightarrow> x < n \<Longrightarrow> (case find_position q x of (p,r) \<Rightarrow> f p r) =  (case find_position q x of (p,r) \<Rightarrow> g p r)"
  apply(simp split:yop_find_pos_split'') 

lemma find_position_inj : " x \<noteq> y  \<Longrightarrow> n > 0 \<Longrightarrow> find_position n x \<noteq> find_position n y"
  by sorry

lemma find_position_inj' : "    n > 0 \<Longrightarrow> (x \<noteq> y) = (find_position n x \<noteq> find_position n y)"
  by sorry

lemma "(case (n::nat) of 0 \<Rightarrow> True | _ \<Rightarrow> False) = (case (n::nat) of 0 \<Rightarrow> False | _ \<Rightarrow> True)"
  apply (simp )
  apply(simp split:nat.split)
lemma 
 " 
x < 640 \<Longrightarrow>
    x \<notin> set (layout_taken_bit_list (LayBitRange (Suc 0, 15))) \<Longrightarrow>
     raw_get_bit (data_C (deref_d32_set_timer_a_en s b)) x =  raw_get_bit (data_C s) x" 
(*  (data_C (deref_d32_set_timer_a_en s b)).[0]!! ( x) =  (data_C s).[0] !! x " *)
(* (data_C (deref_d32_set_timer_a_en s b)).[0] && (1 << x) =  (data_C s).[0] && (1 << x)" *)
  apply (simp add: size_of_arr_def layout_taken_words_def)
  thm yop_find_pos_split[of _ _ 32]
  thm yop_find_pos_split'[of _ _ _ _ 32]
thm yop_find_pos_split'2[of _ _ _  32]
  apply( split yop_find_pos_split'2[of _ _ _  32])
  apply simp
  apply (intro allI impI)+
thm find_position_inj[of _ _ 32, simplified]
  apply(drule find_position_inj[of _ _ 32, simplified])
  apply (simp add:find_position_def)
apply(simp split:yop_find_pos_split''[of _ _ _ _ 32])
 (* apply(simp only:numeral.simps) *)
  apply simp
  apply(erule exE conjE)+
 (* apply(erule  less_zeroE less_SucE)+  *)
(* est ce que ca marche? *)
  apply(tactic \<open>custom_get_set_different_field_tac (@{context} addsimps @{thms wesh}) 1\<close>)+
  done

definition find_position' where "find_position' = find_position"

definition raw_get_bit' :: "(('a::len0) word)['n::finite] \<Rightarrow> nat \<Rightarrow> 'a word"
  where "raw_get_bit' arr pos = 
                (let (byte, off) = find_position' LENGTH('a) pos in
                 arr.[byte] && 2^off )"

(*
lemma case_find_position : "\<exists> q r. find_position n x = (q, r)"
  by auto *)
term filter
find_theorems "(_ :: _ list)" "_ \<or> _"
term list_ex

find_consts "(_ \<times> _) set \<Rightarrow> ('a \<Rightarrow> _ set)"
find_consts "(_ \<times> _) list \<Rightarrow> (_ \<times> _ list) list"
term Equiv_Relations.proj
find_theorems Equiv_Relations.proj
find_theorems Relation.Image 
find_consts "(_ \<times> _) list"
term filter
definition byKey :: "('a \<times> 'c) list \<Rightarrow> ('a \<times> 'c list) list"
  where "byKey l = 
 map (\<lambda> a. (a, map snd (filter (\<lambda>(a', _). a' = a) l)))
(remdups (map fst l))"

term "byKey :: (nat \<times> nat) list \<Rightarrow> (nat \<times> nat list) list"

lemma easyinste : "
(x :: nat) \<notin> set l \<Longrightarrow> 
find_position' n x = (p, r) \<Longrightarrow> 
p \<notin> set (map (fst o find_position n) l) 
\<or>
list_ex (\<lambda> (a,b).
p = a \<and> r \<notin> set b) (byKey (map (find_position n) l)) 
"

  by sorry

find_consts "_ list" name:one
term list_all

lemma smallerthan : "
(x :: nat) < m  \<Longrightarrow> 
find_position' n x = (p, r) \<Longrightarrow> 
p < m div n  \<or> (p = m div n \<and> r < m mod n)
"
  by sorry

lemma find_pos_le : "find_position' n x = (p, r) \<Longrightarrow> r < n "
  by sorry

lemma impCE'':
  assumes major: "P \<longrightarrow> Q"
    and minor: "P \<Longrightarrow> Q \<Longrightarrow> R" "\<not> P \<Longrightarrow> R"
  shows R
  apply (rule excluded_middle [of P, THEN disjE])
   apply (iprover intro: minor major [THEN mp])+
  done 
thm prod.split
lemma "x < size_of_arr_bits (data_C s) \<Longrightarrow>
    x \<notin> set (layout_taken_bit_list (LayBitRange (32, 32))) \<Longrightarrow>
    raw_get_bit' (data_C (deref_d30_set_timer_a s b)) x = raw_get_bit' (data_C s) x "
  apply (cases "find_position' 32 x")
  apply(frule find_pos_le)
  
  apply(drule smallerthan)
   apply assumption
  apply(erule easyinste[THEN disjE])  
   apply assumption


  find_theorems "_ \<longrightarrow> _" name:CE
  apply(erule impCE'')

  apply(simp add:find_position_def raw_get_bit'_def size_of_arr_bits_def byKey_def)
 apply(erule impCE'')
   apply(tactic \<open>custom_get_set_different_field_tac (@{context} addsimps @{thms wesh   }) 1\<close>)
apply(simp add:find_position_def raw_get_bit'_def size_of_arr_bits_def byKey_def)
  apply(tactic \<open>custom_get_set_different_field_tac (@{context} addsimps @{thms wesh   }) 1\<close>)
  done
thm impCE
ca marche  
  thm  case_find_position[THEN exE]
  apply(rule case_find_position[THEN exE])
  apply (simp add: size_of_arr_bits_def layout_taken_words_def)
  thm yop_find_pos_split'2[of _ _ _  32]
  apply( split yop_find_pos_split'2[of _ _ _  640])
  apply simp
  apply(simp add: find_position_inj'[of 32 x])
apply (simp add:find_position_def)
  apply (intro allI impI)+
  thm find_position_inj'[of 32 x]
apply(simp split:yop_find_pos_split''[of _ _ _ _ 32])
)
  apply rule+

  apply(simp add:find_position_def)
  apply(erule conjE)+
  find_theorems "_ \<noteq> _" "_ \<or> _" "_ = _"
  apply(rule excluded_middle[of "x div 32 = Suc 0", THEN disjE])
   apply simp
   apply(tactic \<open>custom_get_set_different_field_tac (@{context} addsimps @{thms wesh   }) 1\<close>)
  apply simp
   apply simp
   apply(tactic \<open>custom_get_set_different_field_tac (@{context} addsimps @{thms wesh   }) 1\<close>)

  done



ML \<open>
val thms = make_getset_sanity_thms @{context} uval0
\<close>
end

local_setup \<open> fn lthy =>
foldl
(fn (ctxt, (thm1, thm2)) => 
GetSetSanity.add_local 
(GetSetSanity.add_local ctxt thm1)
 thm2
)
lthy thms
\<close>
ML \<open>GetSetSanity.add_local \<close>
ML \<open>foldl\<close>
local_setup \<open> fn lthy =>
foldl
(fn ((thm1, thm2), ctxt) => 
GetSetSanity.add_local thm2
(GetSetSanity.add_local thm1 ctxt)
)
lthy thms
\<close>
thm GetSetSanity

lemma "
x < size_of_arr_bits(t3_C.data_C s) \<Longrightarrow>
x \<notin> set (layout_taken_bit_list (LayBitRange (Suc 0, 15))) \<Longrightarrow>
raw_get_bit (t3_C.data_C (deref_d32_set_timer_a_en s b)) x = raw_get_bit (data_C s) x"
  value "20 * (32::int)"
 apply(simp add: find_position_def size_of_arr_bits_def)
  apply(simp only:numeral.simps)
  apply simp
  
  apply(elim less_zeroE  less_SucE) 
            
  apply(tactic \<open>custom_get_set_different_field_tac @{context} 1\<close>)+
  done

lemma "data_C s.[0] && 0x8000 = data_C t.[0] && 0x8000 \<Longrightarrow> 
  deref_d36_get_timer_a s = deref_d36_get_timer_a t"
  apply(tactic \<open>custom_get_set_different_field_tac @{context} 1\<close>)
  apply (intro conjI)+
lemma "data_C s.[0] !! 15 = data_C t.[0] !! 15 \<Longrightarrow>
 deref_d36_get_timer_a s = deref_d36_get_timer_a t"
apply(tactic \<open>custom_get_set_different_field_tac @{context} 1\<close>)
term deref_d34_get_timer_a_en
ML \<open>GetSetSimp.add_local \<close>
lemma "\<forall>x\<in>set (layout_taken_bit_list (LayBitRange (Suc 0, 15))). get_bit (data_C s) x = get_bit (data_C t) x \<Longrightarrow>
deref_d34_get_timer_a_en s = deref_d34_get_timer_a_en t"
  apply (simp add:find_position_def)
  apply (erule conjE)+
apply(tactic \<open>custom_get_set_different_field_tac @{context} 1\<close>)
local_setup \<open>
fn lthy => 
 GetSetSanity.add_local
(make_getter_sanity_thm lthy layfield0 field0)
lthy
\<close>
thm GetSetSanity
ML \<open>
get_uval_name uval0

\<close>
ML \<open>Syntax.read_term @{context} (get_uval_name uval0 ^ "_C.data_C")\<close>
(* *)

ML \<open>HOLogic.dest_prod\<close>

end

end
