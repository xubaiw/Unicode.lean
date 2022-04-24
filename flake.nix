{
  description = "Unicode for Lean";

  inputs = {
    lean = {
      # url = "github:leanprover/lean4";
      url = "github:yatima-inc/lean4/acs/nix-extra-drv-args";
    };
    nixpkgs.url = "github:nixos/nixpkgs/nixos-21.11";
    flake-utils = {
      url = "github:numtide/flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    Mathlib-lean = {
      url = "github:yatima-inc/mathlib4";
      # Compile dependencies with the same lean version
      inputs.lean.follows = "lean";
    };
  };

  outputs = { self, lean, flake-utils, nixpkgs
    , Mathlib-lean
    }:
    let
      supportedSystems = [
        "aarch64-linux"
        "aarch64-darwin"
        "i686-linux"
        "x86_64-darwin"
        "x86_64-linux"
      ];
      inherit (flake-utils) lib;
    in
    lib.eachSystem supportedSystems (system:
      let
        leanPkgs = lean.packages.${system};
        pkgs = nixpkgs.legacyPackages.${system};
        name = "Unicode";  # must match the name of the top-level .lean file
        project = leanPkgs.buildLeanPackage {
          inherit name;
          deps = [ Mathlib-lean.project.${system} ];
          # Where the lean files are located
          src = ./src;
          extraDrvArgs = {
            UCD_DIR = ./UCD;
          };
        };
        test = leanPkgs.buildLeanPackage {
          name = "Tests";
          deps = [ project ];
          # Where the lean files are located
          src = ./test;
        };
        joinDepsDerivations = getSubDrv:
          pkgs.lib.concatStringsSep ":" (map (d: "${getSubDrv d}") (project.allExternalDeps));
      in
      {
        inherit project test;
        packages = project // {
          ${name} = project.sharedLib;
          test = test.executable;
        };

        defaultPackage = self.packages.${system}.${name};
        devShell = pkgs.mkShell {
          inputsFrom = [ project.executable ];
          buildInputs = with pkgs; [
            leanPkgs.lean-dev
          ];
          LEAN_PATH = "./src:./test";
          LEAN_SRC_PATH = "./src:./test";
        };
      });
}
