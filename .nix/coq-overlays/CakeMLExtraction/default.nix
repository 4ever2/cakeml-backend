{
  lib,
  mkCoqDerivation,
  coq,
  ceres-bs,
  equations,
  metarocq-erasure-plugin,
  version ? null,
}:

(mkCoqDerivation {
  pname = "CakeMLExtraction";
  owner = "peregrine-project";
  repo = "cakeml-backend";
  opam-name = "rocq-cakeml-extraction";
  inherit version;
  defaultVersion = null;

  mlPlugin = false;
  useDune = false;

  buildInputs = [ equations metarocq-erasure-plugin ceres-bs ];
  propagatedBuildInputs = [ coq.ocamlPackages.findlib ];

  meta = with lib; {
    homepage = "https://peregrine-project.github.io/";
    description = "CakeML backend for Peregrine";
    maintainers = with maintainers; [ _4ever2 ];
  };
})
