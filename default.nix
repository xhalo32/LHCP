{
  sources ? import ./npins,
  system ? builtins.currentSystem,
  pkgs ? import sources.nixpkgs {
    inherit system;
    config = { };
    overlays = [ ];
  },
}:
let
  watch-blueprint = pkgs.writeShellScriptBin "watch-blueprint" ''
    rm -rf blueprint/web
    leanblueprint web
    echo "Watching for changes in blueprint/src/..."
    ${pkgs.inotify-tools}/bin/inotifywait -e close_write,moved_to,create -m -r blueprint/src |
      while read -r directory events filename; do
        if [[ "$filename" = *tex ]]; then
          echo "Change detected in $directory$filename"
          rm -rf blueprint/web
          leanblueprint web
        fi
      done
  '';
in
{
  shell = pkgs.mkShell {
    buildInputs = with pkgs; [
      leanblueprint
      texliveMedium
      elan
      watch-blueprint

      uv
      graphviz
      python3Packages.livereload
    ];
  };

  formatter = pkgs.nixpkgs-fmt;
}
