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

benches = [
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

decide = "/home/anabrendel/lfind/_QUICKCHICK_PROOFS_/perm_decide.v"
src = "/home/anabrendel/lfind/vfa-benchmarks/Perm/benchmarks/sources"

for t in os.listdir(src):
    if t.startswith("perm"):
        l = t.removeprefix("perm_lemma_")
        m = l.split("_IN_")
        print(m[1])
    # test = os.path.join(src,t)
    # print(test)
    # make(test)