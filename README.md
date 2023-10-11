# vfa-benchmarks
Benchmarks from the "Verified Functional Algorithms" [textbook](`https://softwarefoundations.cis.upenn.edu/vfa-current/index.html`)


In order to run locally:
1. `cd {path to folder}/vfa-benchmarks/vfa-full && make && make TARGET={path to folder}/vfa-benchmarks/ install`
2. You can call into each individual directory to build that file (ex. `cd .../vfa-benchmarks/ADT && make`)
3. To create your own make files, run: `cd {to folder}/{target folder} && coq_makefile -f _CoqProject -o Makefile`


General Notes:
* Note, each folder (corresponding to a file in VFA) uses the the full VFA project to get lemmas that are not included in that file (via `From VFA Require Import <file>.`). If you want file to be self contained (i.e. not relying on the VFA project's other files you'll need to copy over those lemmas and types).

* As more proofs are written in the individual test cases, we'll want to use `vfa_benchmark` (instead of `VFA` which has no full proofs) to import the different modules and then this will mean running `cd {path to folder}/vfa-benchmarks/{folder you want to run} && make && make TARGET={path to folder}/vfa-benchmarks/ install` to register those proofs