{ lib, mkCoqDerivation, coq, mathcomp-algebra,
  coq-elpi, mathcomp-zify, version ? null }:

with lib; mkCoqDerivation {
  namePrefix = [ "coq" "mathcomp" ];
  pname = "algebra-tactics";
  owner = "math-comp";
  inherit version;
  defaultVersion = "proux01:hierarchy-builder";

  propagatedBuildInputs = [ mathcomp-algebra coq-elpi mathcomp-zify ];

  meta = {
    description = "A Library for algebra tactics";
    maintainers = with maintainers; [ cohencyril ];
  };
}
