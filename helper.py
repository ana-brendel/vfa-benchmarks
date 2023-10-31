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


benches = "/home/anabrendel/lfind/vfa-benchmarks/Maps/benchmarks"
perm_benches = "/home/anabrendel/lfind/vfa-benchmarks/Perm/benchmarks"

src = "/home/anabrendel/lfind/vfa-benchmarks/Maps/benchmarks/Maps.v"
p = "/home/anabrendel/lfind/vfa-benchmarks/Maps/_CoqProject"

l = "/home/anabrendel/lfind/vfa-benchmarks/Perm/benchmarks/perm_lemma_app_assoc_IN_butterfly-1/show_list.v"
n = "/home/anabrendel/lfind/vfa-benchmarks/Perm/benchmarks/perm_lemma_app_assoc_IN_butterfly-1/show_nat.v"

# for t in m:
#     folder = os.path.join(benches,t)
#     # cmd = f"cd {folder} && coq_makefile -f _CoqProject -o Makefile"
#     cmd = f"cd {folder} && make"
#     os.system(cmd)

for t in os.listdir(perm_benches):
    if "butterfly" not in t:
        full = os.path.join(perm_benches,t)
        cmd = f"cd {full} && make"
        os.system(cmd)