{ agdaPackages }: with agdaPackages; rec {

  categorical-crypto = mkDerivation {
    pname = "categorical-crypto";
    version = "0.1";
    src = ./.;
    meta = { };
    libraryFile = "categorical-crypto.agda-lib";
    buildInputs = [
      standard-library
      standard-library-classes
      standard-library-meta
      agda-categories
    ];
  };

  default = categorical-crypto;
}
