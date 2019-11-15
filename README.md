**[documentation link](https://math-fehr.github.io/PresburgerAI-Coq/)**

# Building

Generate a makefile and run the makefilw with:

```
$ coq_makefile -f _CoqProject -o Makefile && make
```

##### Using `nix` for build environments

To use [nix](https://nixos.org/nix/), the purely functional package manager
to automatically setup the correct build environment, run `nix-shell` at
the folder with `default.nix` (top-level folder).


```
bash$ nix-shell
[nix-shell]: coq_makefile -f _CoqProject -o Makefile && make
```

This should _never fail_ if the `nix-shell` succeeds.
