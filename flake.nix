{
  description = "learnability VEX reference environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    angr-nix.url = "github:heartpunk/angr-nix/2f20f9ed68506bd151ed171e505942ac9a2a0b43";
  };

  outputs = { self, nixpkgs, angr-nix }:
    let
      systems = [
        "aarch64-darwin"
        "aarch64-linux"
        "x86_64-linux"
      ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f system);
    in {
      devShells = forAllSystems (system:
        let
          pkgs = import nixpkgs { inherit system; };
        in {
          default = pkgs.mkShell {
            packages = [
              angr-nix.packages.${system}.default
              pkgs.uv
              pkgs.jq
            ];
            env = {
              UV_NO_MANAGED_PYTHON = "1";
              UV_PYTHON_DOWNLOADS = "never";
            };
          };
        });
    };
}
