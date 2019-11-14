FROM coqorg/coq:latest
RUN git clone https://github.com/math-fehr/PresburgerAI-Coq.git ai
# need opam to setup paths to OPAM
RUN (opam env --shell=sh > opam-init.sh)
RUN (. ./opam-init.sh; cd ai; coq_makefile -f _CoqProject -o Makefile)
RUN (. ./opam-init.sh; cd ai;make -j)
RUN (. ./opam-init.sh; cd ai/docs; make -j docs)
