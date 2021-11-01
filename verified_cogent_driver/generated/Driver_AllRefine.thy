(*
This file is generated by Cogent

*)

theory Driver_AllRefine
imports "Driver_NormalProof"
"Driver_SCorres_Normal"
"Driver_CorresProof"
"Driver_MonoProof"
"CogentCRefinement.Cogent_Corres_Shallow_C"
begin

(*
 * Derive simple typing rules from earlier ttyping proofs.
 * From f_typecorrect we derive f_typecorrect'.
 * For unification reasons later on, we also ensure that (fst f_type) is simplified
 * to [] (ttyping has been proved for the monomorphic program).
 *)
local_setup \<open>
let val typeproof_thy = "Driver_TypeProof"
in
fold (fn f => fn ctxt => let
    val tt_thm = Proof_Context.get_thm ctxt (typeproof_thy ^ "." ^ f ^ "_typecorrect")
    val f_type = Syntax.read_term ctxt (typeproof_thy ^ "." ^ f ^ "_type")
    val f_type_def = Proof_Context.get_thm ctxt (typeproof_thy ^ "." ^ f ^ "_type_def")
    val nl_empty = Goal.prove ctxt [] [] (@{mk_term "prod.fst ?t \<equiv> 0" t} f_type)
                    (K (simp_tac (ctxt addsimps [f_type_def]) 1))
    val k_empty = Goal.prove ctxt [] [] (@{mk_term "prod.fst (prod.snd ?t) \<equiv> []" t} f_type)
                    (K (simp_tac (ctxt addsimps [f_type_def]) 1))
    val c_empty = Goal.prove ctxt [] [] (@{mk_term "prod.fst (prod.snd (prod.snd ?t)) \<equiv> {}" t} f_type)
                    (K (simp_tac (ctxt addsimps [f_type_def]) 1))
    val t_thm = (tt_thm RS @{thm ttyping_imp_typing})
                |> rewrite_rule ctxt [@{thm snd_conv[THEN eq_reflection]}, nl_empty, k_empty, c_empty]
    in Local_Theory.note ((Binding.name (f ^ "_typecorrect'"), []), [t_thm]) ctxt |> snd
    end)
    (filter (member op= Cogent_functions) entry_func_names)
end
\<close>


(* C-refinement (exported to f_corres).
 * If there are multiple \<xi>-levels, we use the highest one. *)
context Driver begin
ML \<open>
fun both f (x, y) = (f x, f y);

val cogent_entry_func_props =
  Symtab.dest prop_tab
  |> filter (member (op=) entry_func_names o #1 o snd)
  |> filter (member (op=) Cogent_functions o #1 o snd)
  |> sort_by (#1 o snd)
  |> partition_eq (fn (p1,p2) => #1 (snd p1) = #1 (snd p2))
  |> map (sort (option_ord int_ord o
                both (fn p => unprefix (#1 (snd p) ^ "_corres_") (fst p)
                              |> Int.fromString))
          #> List.last)
\<close>
local_setup \<open>
fold (fn (f, p) => Utils.define_lemmas ("corres_" ^ #1 p)
                     [Symtab.lookup finalised_thms f |> the |> the] #> snd)
     cogent_entry_func_props
\<close>
end

(* Monomorphisation (exported to f_monomorphic) *)
context value_sem begin
local_setup \<open>
fold (fn (f, thm) => Utils.define_lemmas (f ^ "_monomorphic") [thm] #> snd)
     (Symtab.dest monoexpr_thms |> filter (member op= entry_func_names o fst))
\<close>
end

(* Normalisation. Not exporting from a locale,
 * but the proofs below want to use Isabelle names. *)
local_setup \<open>
fold (fn (f, thm) => Utils.define_lemmas (f ^ "_normalised") [thm] #> snd)
     (Symtab.dest normalisation_thms |> filter (member op= entry_func_names o fst))
\<close>


(* Initialise final locale. *)
locale Driver_cogent_shallow =
  "driver" + correspondence +
  constrains val_abs_typing :: "'b \<Rightarrow> name \<Rightarrow> type list \<Rightarrow> bool"
         and upd_abs_typing :: "abstyp \<Rightarrow> name \<Rightarrow> type list \<Rightarrow> sigil \<Rightarrow> ptrtyp set \<Rightarrow> ptrtyp set \<Rightarrow> (funtyp, abstyp, ptrtyp) store \<Rightarrow> bool"
         and abs_repr       :: "abstyp \<Rightarrow> name \<times> repr list"
         and abs_upd_val    :: "abstyp \<Rightarrow> 'b \<Rightarrow> char list \<Rightarrow> Cogent.type list \<Rightarrow> sigil \<Rightarrow> 32 word set \<Rightarrow> 32 word set \<Rightarrow> (char list, abstyp, 32 word) store \<Rightarrow> bool"


sublocale Driver_cogent_shallow \<subseteq> Driver _ upd_abs_typing abs_repr
  by (unfold_locales)

sublocale Driver_cogent_shallow \<subseteq> shallow val_abs_typing
  by (unfold_locales)

sublocale Driver_cogent_shallow \<subseteq> correspondence_init
  by (unfold_locales)


context Driver_cogent_shallow begin

(* Generate end-to-end refinement theorems, exported to corres_shallow_C_f *)
local_setup \<open>
filter (member op= Cogent_functions) entry_func_names
|> fold (fn f => fn lthy => let
     val thm = make_corres_shallow_C "Driver_Shallow_Desugar" "Driver_TypeProof" lthy f
     val (_, lthy) = Local_Theory.notes [((Binding.name ("corres_shallow_C_" ^ f), []), [([thm], [])])] lthy
     in lthy end)
\<close>


print_theorems

end

end
