import os
import sys
import shutil

fullVFA = "/home/anabrendel/lfind/vfa-benchmarks/vfa-full"
main = "/home/anabrendel/lfind/vfa-benchmarks"

def write_content(file, content):
    with open(file,"w") as f:
        f.write("\n".join(content))

testFolders = []
for t in os.listdir(main):
    if t != "vfa-full" and t != "helper.py" and not t.startswith(".") and t != "README.md" and t != "Preface":
        testFolders.append(t)

for t in testFolders:
    path = os.path.join(main,t)
    cmd = f"cd {path} && make"
    # os.system(cmd)

m = [
    'maps_lemma_beq_nat_refl_IN_t_update_eq',
    'maps_lemma_beq_nat_refl_IN_eqb_eq',
    'maps_lemma_eqb_eq_IN_t_update_same',
    'maps_lemma_iff_reflect_IN_beq_idP',
    'maps_lemma_eqb_eq_IN_beq_idP',
    'maps_lemma_t_apply_empty_IN_apply_empty',
    'maps_lemma_t_update_eq_IN_update_eq',
    'maps_lemma_t_update_neq_IN_update_neg',
    'maps_lemma_t_update_shadow_IN_updat_shadow',
    'maps_lemma_t_update_same_IN_update_same',
    'maps_lemma_t_update_permute_IN_update_permute'
]

benches = "/home/anabrendel/lfind/vfa-benchmarks/Maps/benchmarks"

src = "/home/anabrendel/lfind/vfa-benchmarks/Maps/benchmarks/Maps.v"
p = "/home/anabrendel/lfind/vfa-benchmarks/Maps/_CoqProject"

for t in m:
    folder = os.path.join(benches,t)
    # cmd = f"cd {folder} && coq_makefile -f _CoqProject -o Makefile"
    cmd = f"cd {folder} && make"
    os.system(cmd)