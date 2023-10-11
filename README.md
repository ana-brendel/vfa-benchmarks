# vfa-benchmarks
Benchmarks from the "Verified Functional Algorithms" textbook - `https://softwarefoundations.cis.upenn.edu/vfa-current/index.html`


In order to run locally:
1. `cd {path to folder}/vfa-benchmarks/vfa-full && make && make TARGET={path to folder}/vfa-benchmarks/ install`
2. You can call into each individual directory to build that file (ex. `cd .../vfa-benchmarks/ADT && make`)
3. To create your own make files, run: `cd {to folder}/{target folder} && coq_makefile -f _CoqProject -o Makefile`

Note, each folder (corresponding to a file in VFA) uses the the full VFA project to get lemmas that are not included in that file (via `From VFA Require Import <file>.`). If you want file to be self contained (i.e. not relying on the VFA project's other files you'll need to copy over those lemmas and types).