{
  system ? builtins.currentSystem,
  sources ? import ./npins,
}:
let
  pkgs = import sources.nixpkgs { inherit system; };
in
pkgs.mkShell {
  nativeBuildInputs = with pkgs; [
    (agda.withPackages (p: [ p.standard-library ]))
    npins
  ];
}
