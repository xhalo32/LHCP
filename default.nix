{
  sources ? import ./npins,
  system ? builtins.currentSystem,
  pkgs ? import sources.nixpkgs {
    inherit system;
    config = { };
    overlays = [ ];
  },
}:
{
  shell = pkgs.mkShell {
    buildInputs = with pkgs; [
      leanblueprint
      texliveBasic
    ];
  };

  formatter = pkgs.nixpkgs-fmt;
}
