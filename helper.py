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
    os.system(f"cd {path} && make")
