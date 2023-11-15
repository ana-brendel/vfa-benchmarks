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
    "sort_lemma_insert_sorted_IN_sort_sorted",
    "sort_lemma_insert_perm_IN_sort_perm",
    "sort_lemma_sort_perm_IN_insertion_sort_correct",
    "sort_lemma_sort_sorted_IN_insertion_sort_correct",
    "sort_lemma_sorted_remove_cons_1_IN_insert_sortedd",
    "sort_lemma_sorted_remove_cons_2_IN_insert_sortedd",
    "sort_lemma_sorted_remove_cons_3_IN_insert_sortedd",
    "sort_lemma_sorted_remove_cons_4_IN_insert_sortedd",
    "sort_lemma_sorted_remove_cons_5_IN_insert_sortedd",
    "sort_lemma_sorted_remove_1_IN_insert_sortedd",
    "sort_lemma_sorted_remove_2_IN_insert_sortedd",
    "sort_lemma_insert_sortedd_IN_sort_sortedd"
]

decide = "/home/anabrendel/lfind/vfa-benchmarks/Sort/benchmarks/sources/sort_lemma_sorted_remove_cons_1_IN_insert_sortedd/decide.v"
src = "/home/anabrendel/lfind/vfa-benchmarks/Sort/benchmarks/sources"

for t in os.listdir(src):
    test = os.path.join(src,t)
    make(test)