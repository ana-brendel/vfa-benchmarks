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

benches = "/home/anabrendel/lfind/vfa-benchmarks/Perm/benchmarks"

src = "/home/anabrendel/lfind/vfa-benchmarks/Perm/Perm.v"
p = "/home/anabrendel/lfind/vfa-benchmarks/Perm/_CoqProject"

for t in os.listdir(benches):
    folder = os.path.join(benches,t)
    cmd = f"cd {folder} && make"
    os.system(cmd)