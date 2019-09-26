[![Build Status](https://travis-ci.com/bollu/PresburgerAI-Coq.svg?branch=master)](https://travis-ci.com/bollu/PresburgerAI-Coq)

# Module documentation, in alphabetical order

- [`AbstractDomain.v`](AbstractDomain.html)
- [`AbstractInterpreter.v`](AbstractInterpreter.html)
- [`Presburger.v`](Presburger.html) 
- [`SSA.v`](SSA.html)
- [`TotalMap.v`](TotalMap.html)
- [`TransferFunction.v`](TransferFunction.html)

## How to build documentation

Run the makefile to build the documentation. A `make` command should update
all the docs here. Then perform a `git add && git commit && git push`.

- `coq2html` borrowed from `https://github.com/xavierleroy/coq2html`, commit
  number `fc2bb9c`.
