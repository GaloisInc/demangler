{
  description = "Haskell C++ name demangler";

  nixConfig.bash-prompt-suffix = "demangler.env} ";

  inputs = {
    nixpkgs.url = github:nixos/nixpkgs/23.05;
    levers = {
      url = "github:kquick/nix-levers";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    sayable = {
      url = "github:kquick/sayable";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.levers.follows = "levers";
    };
  };

  outputs = { self, nixpkgs, levers, sayable }:
    let shellWith = pkgs: adds: drv: drv.overrideAttrs(old:
          { buildInputs = old.buildInputs ++ adds pkgs; });
        # Add additional packages useful for a development shell, generally
        # representing test packages or non-propagated build dependencies of
        # various sub-packages.
        shellPkgs = pkgs: [ # pkgs.haskell.compiler.integer-simple.ghc8107
                            # pkgs.haskell.packages.ghc8107.profiteur
                            pkgs.cabal-install
                            pkgs.clang
                            pkgs.llvm
                          ];
    in rec
      {
        apps = levers.eachSystem (s:
          rec
          {
            demangle = {
              type = "app";
              program = "${self.packages.${s}.demangler}/bin/demangle";
            };
            default = demangle;
          });

        devShells =
          let oneshell = s: n:
                let pkgs = import nixpkgs { system=s; };
                in levers.variedTargets
                  { ghcver = levers.validGHCVersions pkgs.haskell.compiler; }
                  ( { ghcver, ... } @ vargs:
                    let pkgtgt = if n == "default"
                                 then self.packages.${s}.${n}.default
                                 else self.packages.${s}.${n}.${ghcver}.default;
                    in shellWith pkgs shellPkgs
                      (pkgtgt.env.overrideAttrs (a:
                        {
                          # Set envvars here...
                        }
                      ))
                  );
          in
            levers.eachSystem
              (s:
                let pkgs = import nixpkgs { system=s; };
                    names = builtins.attrNames (self.packages.${s});
                    shells = pkgs.lib.genAttrs names (oneshell s);
                in shells // { default = devShells.${s}.demangler.default; }
              );

        packages = levers.eachSystem (system:  # KWQ: add taphRep
          let mkHaskell = levers.mkHaskellPkg {
                inherit nixpkgs system;
              };
              haskellAdj = drv:
                with pkgs.haskell.lib;
                enableLibraryProfiling (enableExecutableProfiling (dontHaddock (dontCheck drv)));
              pkgs = import nixpkgs { inherit system; };
              wrap = levers.pkg_wrapper system pkgs;
          in rec
            {
              default = demangler;
              TESTS = wrap "demangler-TESTS" [ demangler_tests ];
              DOC = wrap "demangler-DOC" [ demangler_doc ];
              demangler = mkHaskell "demangler" self {
                inherit sayable;
                adjustDrv = args: haskellAdj;
              };
              demangler_tests = mkHaskell "demangler_tests" self {
                inherit sayable;
                adjustDrv = args: drv:
                  with pkgs.haskell.lib;
                  doBenchmark (doCheck (haskellAdj drv));
              };
              demangler_doc = mkHaskell "demangler_doc" self {
                inherit sayable;
                adjustDrv = args: drv:
                  pkgs.haskell.lib.doHaddock (haskellAdj drv);
              };
            });
      };
}
