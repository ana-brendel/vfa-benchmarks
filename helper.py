import os
import sys
import shutil

fullVFA = "/home/anabrendel/lfind/vfa-benchmarks/vfa-full"
main = "/home/anabrendel/lfind/vfa-benchmarks"

def makefile(folder):
    cmd = f"cd {folder} && coq_makefile -f _CoqProject -o Makefile"
    os.system(cmd)

def make(folder):
    cmd = f"cd {folder} && make"
    os.system(cmd)

def write_content(file, content):
    with open(file,"w") as f:
        f.write("\n".join(content))

testFolders = []
for t in os.listdir(main):
    if t != "vfa-full" and t != "helper.py" and not t.startswith(".") and t != "README.md" and t != "Preface":
        testFolders.append(t)

benches_perm = [
    #"perm_lemma_Permutation_app_comm_IN_butterfly-1",
    #"perm_lemma_Permutation_app_comm_IN_butterfly-3",
    #"perm_lemma_Permutation_app_head_IN_butterfly-1",
    #"perm_lemma_Permutation_refl_IN_maybe_swap_perm-1",
    #"perm_lemma_app_assoc_IN_butterfly-4",
    "perm_lemma_app_assoc_IN_butterfly-2", # search space still explodes
    #"perm_lemma_app_assoc_IN_butterfly-3",
    #"perm_lemma_ltb_lt_IN_blt_reflect",
    #"perm_lemma_Permutation_refl_IN_butterfly",
    #"perm_lemma_app_assoc_IN_permut_example",
    "perm_lemma_app_assoc_IN_butterfly-1", # search space still explodes
    #"perm_lemma_leb_le_IN_beq_reflect",
    #"perm_lemma_Permutation_refl_IN_maybe_swap_perm-2",
    "perm_lemma_Permutation_app_head_IN_butterfly-2",
    #"perm_lemma_eqb_eq_IN_beq_reflect",
    #"perm_lemma_iff_reflect_IN_beq_reflect",
    "perm_lemma_Permutation_app_comm_IN_permut_example", # didn't complete
    #"perm_lemma_iff_reflect_IN_blt_reflect",
    #"perm_lemma_maybe_swap_perm_IN_maybe_swap_correct",
    #"perm_lemma_Permutation_refl_IN_permut_example",
    "perm_lemma_Permutation_app_comm_IN_butterfly-2",
    #"perm_lemma_Permutation_refl_IN_maybe_swap_perm-3",
    "perm_lemma_iff_reflect_IN_ble_reflect"
]

benches_sort = [
    "sort_lemma_sortedd_remove_cons_1_IN_insert_sortedd",
    "sort_lemma_sortedd_remove_cons_2_IN_insert_sortedd",
    "sort_lemma_sortedd_remove_cons_3_IN_insert_sortedd",
    "sort_lemma_sortedd_remove_cons_4_IN_insert_sortedd",
    "sort_lemma_sortedd_remove_cons_5_IN_insert_sortedd",
    "sort_lemma_sortedd_single_1_IN_insert_sortedd",
    "sort_lemma_sortedd_single_2_IN_insert_sortedd",
    "sort_lemma_sortedd_remove_IN_insert_sortedd",
    "sort_lemma_simple_insert_IN_insert_sortedd",
    "sort_lemma_sortedd_nil_IN_sortedd_remove"
]

benches = [
    "selection_lemma_Permutation_refl_IN_select_perm",
    "selection_lemma_select_perm_IN_select_rest_length",
    "selection_lemma_Permutation_length_IN_select_rest_length",
    "selection_lemma_length_zero_iff_nil_IN_selsort_perm",
    "selection_lemma_Permutation_refl_IN_selsort_perm",
    "selection_lemma_select_perm_IN_selsort_perm",
    "selection_lemma_select_rest_length_IN_selsort_perm",
    "selection_lemma_selsort_perm_IN_selection_sort_perm",
    "selection_lemma_select_exists_1_IN_select_fst_leq",
    "selection_lemma_select_exists_2_IN_select_fst_leq",
    "selection_lemma_lt_n_Sm_le_1_IN_select_fst_leq",
    "selection_lemma_lt_n_Sm_le_2_IN_select_fst_leq",
    "selection_lemma_lt_S_1_IN_select_fst_leq",
    "selection_lemma_lt_S_2_IN_select_fst_leq",
    "selection_lemma_le_lt_n_Sm_IN_select_fst_leq",
    #"selection_lemma_le_trans_IN_select_fst_leq", --> error cd
    "selection_lemma_select_exists_IN_le_all__le_one",
    "selection_lemma_select_perm_IN_le_all__le_one",
    "selection_lemma_in_inv_IN_le_all__le_one",
    "selection_lemma_Forall_forall_IN_le_all__le_one",
    "selection_lemma_select_exists_1_IN_select_smallest",
    "selection_lemma_le_trans_IN_select_smallest",
    "selection_lemma_select_fst_leq_1_IN_select_smallest",
    "selection_lemma_select_exists_2_IN_select_smallest",
    "selection_lemma_lt_n_Sm_le_IN_select_smallest",
    "selection_lemma_lt_S_IN_select_smallest",
    "selection_lemma_le_lt_trans_IN_select_smallest",
    "selection_lemma_select_fst_leq_2_IN_select_smallest",
    "selection_lemma_or_comm_1_IN_select_in",
    "selection_lemma_or_assoc_IN_select_in",
    "selection_lemma_or_comm_2_IN_select_in",
    "selection_lemma_select_exists_IN_select_in",
    "selection_lemma_select_perm_IN_select_in",
    "selection_lemma_Permutation_in_IN_select_in",
    "selection_lemma_Permutation_sym_IN_select_in",
    "selection_lemma_selsort_perm_IN_cons_of_small_maintains_sort",
    "selection_lemma_le_all__le_one_IN_cons_of_small_maintains_sort",
    # "selection_lemma_Pemutation_in_IN_cons_of_small_maintains_sort", --> error cd
    "selection_lemma_Permutation_sym_IN_cons_of_small_maintains_sort",
    "selection_lemma_select_exists_IN_selsort_sorted",
    "selection_lemma_cons_of_small_maintains_sort_IN_selsort_sorted"
    "selection_lemma_select_rest_length_1_IN_selsort_sorted",
    "selection_lemma_select_smallest_IN_selsort_sorted",
    "selection_lemma_select_rest_length_2_IN_selsort_sorted",
    "selection_lemma_selsort_sorted_IN_selection_sort_sorted",
    "selection_lemma_selection_sort_perm_IN_selection_sort_is_correct",
    "selection_lemma_selection_sort_sorted_IN_selection_sort_is_correct",
    "selection_lemma_length_zero_iff_nil_IN_selsortt_perm",
    "selection_lemma_Permutation_refl_IN_selsortt_perm",
    "selection_lemma_select_perm_IN_selsortt_perm",
    "selection_lemma_select_rest_length_IN_selsortt_perm",
    "selection_lemma_list_has_length_IN_cons_of_small_maintains_sortt",
    "selection_lemma_selsortt_perm_IN_cons_of_small_maintains_sortt",
    "selection_lemma_le_all__le_one_IN_cons_of_small_maintains_sortt",
    "selection_lemma_Permutation_in_IN_cons_of_small_maintains_sortt",
    "selection_lemma_Permutation_sym_IN_cons_of_small_maintains_sortt",
    "selection_lemma_select_exists_IN_selsortt_sorted",
    "selection_lemma_cons_of_small_maintains_sortt_IN_selsortt_sorted",
    "selection_lemma_select_smallest_IN_selsortt_sorted",
    "selection_lemma_select_rest_length_IN_selsortt_sorted",
    "selection_lemma_list_has_length_IN_selsortt_is_correct",
    "selection_lemma_selsortt_perm_IN_selsortt_is_correct",
    "selection_lemma_selsortt_sorted_IN_selsortt_is_correct",
    "selection_lemma_cons_of_small_maintains_sort_IN_selsort_sorted",
    "selection_lemma_select_rest_length_1_IN_selsort_sorted"
]

decide = "/home/anabrendel/lfind/vfa-benchmarks/Selection/benchmarks/sources/selection_lemma_cons_of_small_maintains_sort_IN_selsort_sorted/decide.v"
src = "/home/anabrendel/lfind/vfa-benchmarks/Selection/benchmarks/sources"
file = "/home/anabrendel/lfind/vfa-benchmarks/Selection/benchmarks/Selection.v"
mod_src = "/home/anabrendel/lfind/vfa-benchmarks/Selection/benchmarks/modified-locations"

for t in os.listdir(mod_src):
    f = os.path.join(mod_src,t)
    # d = os.path.join(f,"decide.v")
    # shutil.copy(decide,d)
    make(f)
    # print(f)