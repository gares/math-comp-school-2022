## To build your file with opam

```
make opam         # copy the output
make lesson1.html
```

## To build your file with nix

- First install nix and cachix once and for all as in https://github.com/coq-community/coq-nix-toolbox#standalone

- To compile something after cloning the repo
  ```
  nix-shell
  make lesson1.html
  ```

- To get a shell without cloning the repo:
  ```
  nix-shell https://github.com/gares/math-comp-school-2022/tarball/master
  ```

## To upload your file

```
make upload FILES=lesson1.html
```

To test your file go to

https://www-sop.inria.fr/teams/marelle/MC-2022/lesson1.html

or type

make serve
