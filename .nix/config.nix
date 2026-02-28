{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  attribute = "CakeMLExtraction";

  no-rocq-yet = true;

  default-bundle = "9.0";

  bundles."9.0" = {
    coqPackages.coq.override.version = "9.0";
    rocqPacakges.rocq-core.override.version = "9.0";
    coqPackages.metarocq.override.version = "1.4-9.0";
    coqPackages.ceres-bs.override.version = "master";
  };

  bundles."9.0".push-branches = ["main"];

  cachix.coq = {};
  cachix.math-comp = {};
  cachix.coq-community = {};
  cachix.metarocq = {};
  cachix.peregrine = {};
}
